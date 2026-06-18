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
use vstd::assert_maps_equal;
use vstd::assert_sets_equal;
use vstd::map_lib::lemma_values_finite;

use vstd::multiset::Multiset;
use crate::abstract_system::MsgHistory_v::{KeyedMessage, MsgHistory};
use crate::abstract_system::StampedMap_v::LSN;
use crate::spec::AsyncDisk_t::{
    Address, AsyncDisk, DiskRequest, DiskResponse, RawPage, inv_next as async_disk_inv_next,
};
use crate::spec::FloatingSeq_t::FloatingSeq;
use crate::spec::KeyType_t::Key;
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
    CachedBranch, LoadedPathReceipt, loaded_grow_write_nodes, loaded_seal_write_nodes,
    loaded_split_write_nodes, root_summary_from_read, root_summary_read_valid,
};
use crate::implementation::CachedJournal_v::{
    CachedJournal, au_walk_reads_cover,
    au_walk_larger_disk_matches_valid_subdisk,
    au_walk_reads_cover_build_matches_full_by_value,
    au_walk_reads_cover_sub_entries,
    au_walk_reads_cover_supermap,
    build_lsn_au_index_from_reads_au_walk_depth,
    build_lsn_au_index_from_reads_au_walk_depth_supermap,
    build_lsn_au_index_from_reads_au_walk_values_in_sub_entries,
};
use crate::implementation::CachingDisk_v::{
    addresses_in_aus, CachingDisk, PageStatus as CachingDiskPageStatus,
};
use crate::implementation::CachingDiskAdapterRefinement_v::{
    cache_filled_addr, cache_filled_page, cache_internal_refines_caching_disk_internal,
    cache_internal_refines_caching_disk_internal_by_domains,
    filled_cache_pages, filled_cache_read_only_access_unchanged, filled_cache_status,
    project_cache_pages_by_addrs, project_cache_status_by_addrs, project_persistent_by_addrs,
};
use crate::implementation::AnotherAtomicJournalRefinement_v::{
    async_disk_superblock_image_i, async_disk_superblock_page_wf,
    atomic_persistent_superblock_image_i, atomic_superblock_prepared_i,
    branch_writes_disjoint_from_journal_projection,
    cache_access_outside_journal_projection_unchanged, cache_read_only_access_projection_unchanged,
    durable_superblock_image_i,
    journal_component_refinement_inv,
    journal_owned_disk_records_do_not_impersonate_index,
    crash_aware_caching_disk_journal_i, frozen_journal_image_i, journal_caching_disk_i,
    journal_caching_disk_state_i,
    journal_disk_cache_i, journal_disk_persistent_i,
    journal_disk_status_i, journal_image_i, journal_image_persistent_i, journal_image_projection_aus_i,
    journal_image_persistent_unchanged_for_same_projection,
    journal_image_projection_aus_loaded_index_unchanged, journal_image_projection_domain_i,
    journal_execute_put_refines, journal_fill_aus_refines, journal_observe_clean_aus_refines,
    journal_query_end_lsn_refines,
    live_journal_projection_addrs, mini_allocator_allocated_addrs,
    journal_projection_addrs, journal_persistent_projection_addrs,
    journal_projection_aus, journal_projection_domains_unchanged_by_cache_access_outside,
    journal_projection_uses_live, on_disk_journal_addrs_i, on_disk_journal_aus_i,
    on_disk_journal_tj_i, persistent_journal_image_i, journal_projection_tight,
    journal_projection_uses_shared_async_disk, snapshot_walk_domain_none_empty,
    snapshot_walk_domain_union_outside_same,
};
use crate::implementation::AnotherAtomicBranchRefinement_v::{
    atomic_branch_metadata_loaded_flag, atomic_branch_metadata_loaded_flag_from_metadata_loaded,
    branch_append_from_execute_put_refines, branch_append_refines,
    branch_caching_disk_i, branch_caching_disk_state_i, branch_component_refinement_inv,
    branch_disk_cache_i, branch_disk_persistent_i, branch_disk_status_i, branch_fill_aus_refines,
    branch_image_i, branch_image_persistent_i, branch_image_projection_addrs_i,
    branch_grow_refines, branch_interpreted_summary_i, branch_load_metadata_refines,
    branch_mini_allocator_allocated_addrs,
    branch_persistent_projection_addrs, branch_projection_addrs, branch_projection_aus,
    branch_projection_summary_i,
    branch_query_refines, branch_seal_refines, branch_split_refines,
    branch_raw_visible_i, branch_visible_nodes_i, crash_aware_caching_disk_branch_i,
    frozen_branch_image_i, loaded_branch_projection_unchanged,
    observe_persisted_branch_roots_refines, persistent_branch_image_i,
    sealed_roots_pointer_domain_preserved_by_write_outside,
};
use crate::implementation::CrashAwareCachingDiskJournal_v::{
    CrashAwareCachingDiskJournal,
};
use crate::implementation::CachingDiskJournal_v::{
    CachingDiskJournal, snapshot_walk_domain, snapshot_walk_domain_restrict_domain_same,
    snapshot_walk_ptr,
};
use crate::implementation::CachingDiskBranch_v as CachingDiskBranchModule;
use crate::implementation::CrashAwareCachingDiskBranch_v::CrashAwareCachingDiskBranch;
use crate::implementation::AnotherProgramModel_v::AnotherProgramModel;
use crate::implementation::AnotherAtomicState_v::{
    AnotherAtomicState, AtomicBranchState, AtomicJournalState, DiskEvent, InternalEvent,
    ProgramEvent, atomic_branch_support_addrs,
};
use crate::implementation::AbstractSuperblock_v::{
    AbstractSuperblockImage, marshal_abstract_superblock, marshalled_abstract_superblock_raw_wf,
};
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::JournalTypes_v::{to_journal_records, to_journal_records_restrict};
use crate::journal::LinkedJournal_v::DiskView;
use crate::allocation_layer::AllocationJournal_v::JournalImage;
use crate::allocation_layer::AllocationBranch_v::Summary;
use crate::allocation_layer::AllocationBranchBetree_v::summary_aus;
use crate::betree::Utils_v::{
    lemma_union_set_of_sets_contains, lemma_union_set_of_sets_subset, union_set_of_sets,
};
use crate::implementation::RecoveryState_v::RecoveryState;
use crate::disk::GenericDisk_v::{set_addrs_disjoint_aus, to_aus, to_aus_domain, to_aus_finite, AU};

verus!{

// ================================================================
// Shared helpers
// ================================================================

// TODO: put into vstd/multiset_lib.rs
pub open spec fn multiset_to_set<V>(m: Multiset<V>) -> Set<V> {
    Set::new(|v| m.contains(v))
}

pub proof fn to_aus_empty()
    ensures
        to_aus(Set::<Address>::empty()) == Set::<AU>::empty(),
{
    let empty_addrs = Set::<Address>::empty();
    let image = Map::new(|addr: Address| empty_addrs.contains(addr), |addr: Address| addr.au);
    assert_maps_equal!(image, Map::<Address, AU>::empty(), addr => {
        assert(!empty_addrs.contains(addr));
    });
    assert(to_aus(empty_addrs) == image.values());
    assert(image.values() == Map::<Address, AU>::empty().values());
    assert(Map::<Address, AU>::empty().values() == Set::<AU>::empty());
}

pub proof fn to_aus_subset_of_aus_from_addr_subset(addrs: Set<Address>, aus: Set<AU>)
    requires
        addrs <= addresses_in_aus(aus),
    ensures
        to_aus(addrs) <= aus,
{
    assert forall |au: AU| #[trigger] to_aus(addrs).contains(au)
        implies aus.contains(au) by {
        let addr = choose |addr: Address| #![auto]
            addrs.contains(addr) && addr.au == au;
        assert(addresses_in_aus(aus).contains(addr));
    }
}

pub proof fn atomic_branch_support_addrs_subset_branch_projection(
    model: SystemModel::State<AnotherProgramModel>,
)
    requires
        atomic_branch_metadata_loaded_flag(model.program.state.branch),
    ensures
        atomic_branch_support_addrs(model.program.state.branch) <= branch_projection_addrs(model),
{
    assert(branch_projection_summary_i(model) == model.program.state.branch.branch_summary);
    assert forall |addr: Address| #[trigger] atomic_branch_support_addrs(
        model.program.state.branch,
    ).contains(addr)
        implies branch_projection_addrs(model).contains(addr) by {
        if addresses_in_aus(summary_aus(model.program.state.branch.branch_summary)).contains(addr) {
            assert(addresses_in_aus(summary_aus(branch_projection_summary_i(model))).contains(addr));
        } else {
            assert(crate::implementation::AnotherAtomicState_v::mini_allocator_allocated_addrs(
                model.program.state.branch.mini_allocator,
            ).contains(addr));
            assert(branch_mini_allocator_allocated_addrs(
                model.program.state.branch.mini_allocator,
            ).contains(addr));
        }
    }
}

pub proof fn branch_projection_addrs_eq_atomic_support_addrs(
    model: SystemModel::State<AnotherProgramModel>,
)
    requires
        atomic_branch_metadata_loaded_flag(model.program.state.branch),
    ensures
        branch_projection_addrs(model) =~= atomic_branch_support_addrs(model.program.state.branch),
{
    assert(branch_projection_summary_i(model) == model.program.state.branch.branch_summary);
    assert_sets_equal!(
        branch_projection_addrs(model),
        atomic_branch_support_addrs(model.program.state.branch),
        addr => {
            if branch_projection_addrs(model).contains(addr) {
                if addresses_in_aus(summary_aus(branch_projection_summary_i(model))).contains(addr) {
                    assert(addresses_in_aus(summary_aus(model.program.state.branch.branch_summary)).contains(addr));
                } else {
                    assert(branch_mini_allocator_allocated_addrs(
                        model.program.state.branch.mini_allocator,
                    ).contains(addr));
                    assert(crate::implementation::AnotherAtomicState_v::mini_allocator_allocated_addrs(
                        model.program.state.branch.mini_allocator,
                    ).contains(addr));
                }
            }
            if atomic_branch_support_addrs(model.program.state.branch).contains(addr) {
                atomic_branch_support_addrs_subset_branch_projection(model);
            }
        }
    );
}

pub proof fn cache_access_reads_available_in_branch_projection_from_support(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    component_reads: Map<Address, RawPage>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre.program.state.cache.inv(),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads, writes},
        ),
        component_reads <= reads,
        component_reads.dom() <= atomic_branch_support_addrs(pre.program.state.branch),
        atomic_branch_metadata_loaded_flag(pre.program.state.branch),
    ensures
        component_reads <= branch_disk_cache_i(pre),
{
    atomic_branch_support_addrs_subset_branch_projection(pre);
    assert forall |addr: Address| #[trigger] component_reads.contains_key(addr)
        implies branch_disk_cache_i(pre).contains_key(addr)
            && branch_disk_cache_i(pre)[addr] == component_reads[addr] by {
        assert(reads.contains_key(addr));
        assert(reads[addr] == component_reads[addr]);
        Cache::State::access_read_valid(
            pre.program.state.cache,
            post.program.state.cache,
            reads,
            writes,
            addr,
        );
        assert(pre.program.state.cache.valid_read(addr, reads[addr]));
        pre.program.state.cache.build_lookup_map_ensures();
        assert(pre.program.state.cache.lookup_map == pre.program.state.cache.build_lookup_map());
        assert(cache_filled_addr(pre.program.state.cache, addr)) by {
            assert(pre.program.state.cache.lookup_map.contains_key(addr));
            assert(pre.program.state.cache.entries[
                pre.program.state.cache.lookup_map[addr]
            ] is Filled);
            assert(pre.program.state.cache.entries.contains_key(
                pre.program.state.cache.lookup_map[addr],
            ));
        }
        assert(filled_cache_pages(pre.program.state.cache).contains_key(addr));
        assert(filled_cache_pages(pre.program.state.cache)[addr] == reads[addr]);
        assert(atomic_branch_support_addrs(pre.program.state.branch).contains(addr));
        assert(branch_projection_addrs(pre).contains(addr));
        assert(project_cache_pages_by_addrs(
            pre.program.state.cache,
            branch_projection_addrs(pre),
        ).contains_key(addr));
        assert(project_cache_pages_by_addrs(
            pre.program.state.cache,
            branch_projection_addrs(pre),
        )[addr] == reads[addr]);
    }
}

pub proof fn cache_evicted_addr_lookup_slot(
    cache: Cache::State,
    evicted_slots: Set<Slot>,
    addr: Address,
)
    requires
        cache.build_lookup_map_props(cache.lookup_map),
        cache.lookup_map.contains_key(addr),
        evicted_slots <= cache.entries.dom(),
        forall |slot: Slot| #[trigger] evicted_slots.contains(slot) ==> cache.entries[slot] is Filled,
        Map::new(
            |slot: Slot| evicted_slots.contains(slot),
            |slot: Slot| cache.entries[slot].get_addr(),
        ).values().contains(addr),
    ensures
        evicted_slots.contains(cache.lookup_map[addr]),
{
    let evicted_map = Map::new(
        |slot: Slot| evicted_slots.contains(slot),
        |slot: Slot| cache.entries[slot].get_addr(),
    );
    let slot = choose |slot: Slot| #![auto]
        evicted_map.contains_key(slot) && evicted_map[slot] == addr;
    assert(evicted_slots.contains(slot));
    assert(cache.entries.contains_key(slot));
    assert(cache.entries[slot] is Filled);
    assert(cache.entries[slot].get_addr() == addr);
    assert(cache.lookup_map[addr] == slot);
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
        &&& model.recovery_state is RecoveryComplete
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

pub open spec fn branch_projected_aus_are_owned_data(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    &&& AnotherAtomicState::reserved_aus().disjoint(branch_projection_aus(model))
    &&& model.program.state.journal_owned_aus().disjoint(branch_projection_aus(model))
    &&& model.program.state.free_aus.disjoint(branch_projection_aus(model))
}

pub open spec fn journal_projected_aus_are_component_data(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    &&& AnotherAtomicState::reserved_aus().disjoint(journal_projection_aus(model))
    &&& model.program.state.branch_owned_aus().disjoint(journal_projection_aus(model))
}

pub open spec fn branch_loaded_metadata_agrees_with_visible(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    model.program.state.superblock_metadata_known() ==> {
        &&& CachingDiskBranchModule::branch_summary_reads_valid(
            model.program.state.branch.image.sealed_roots,
            branch_visible_nodes_i(model),
        )
        &&& CachingDiskBranchModule::loaded_branch_summary_agrees(
            model.program.state.branch.image.sealed_roots,
            branch_visible_nodes_i(model),
            model.program.state.branch.branch_summary,
        )
    }
}

pub open spec fn journal_loaded_index_matches_persistent_subdisk(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    model.program.state.journal_metadata_loaded() ==> {
        let journal = model.program.state.journal.journal;
        let snapshot = journal.snapshot;
        let image = persistent_journal_image_i(model);
        &&& image.snapshot == snapshot
        &&& journal.status.unwrap().lsn_au_index =~=
            image.i().tj.disk_view.build_lsn_au_index_au_walk(
                snapshot.freshest_rec(),
                snapshot.first(),
            )
    }
}

pub open spec fn journal_index_aus_have_unique_lsns(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    !model.program.state.client_ready() && journal_projection_uses_live(model) ==> {
        let journal = model.program.state.journal.journal;
        let snapshot = journal.snapshot;
        let disk_view = DiskView{
            boundary_lsn: snapshot.boundary_lsn,
            entries: to_journal_records(model.disk.content),
        };
        let index = journal.status.unwrap().lsn_au_index;
        forall |addr1: Address, addr2: Address, lsn: LSN|
            #![trigger
                disk_view.entries[addr1].contains_lsn(snapshot.boundary_lsn, lsn),
                disk_view.entries[addr2].contains_lsn(snapshot.boundary_lsn, lsn)
            ]
        {
            &&& disk_view.entries.contains_key(addr1)
            &&& disk_view.entries.contains_key(addr2)
            &&& index.values().contains(addr1.au)
            &&& index.values().contains(addr2.au)
            &&& disk_view.entries[addr1].contains_lsn(snapshot.boundary_lsn, lsn)
            &&& disk_view.entries[addr2].contains_lsn(snapshot.boundary_lsn, lsn)
        } ==> addr1 == addr2
    }
}

pub open spec fn journal_inflight_projection_wf(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    model.program.state.in_flight is Some ==> {
        &&& model.program.state.journal_metadata_loaded()
        &&& journal_projection_uses_live(model)
        &&& frozen_journal_image_i(model) is Some
        &&& frozen_journal_image_i(model).unwrap().persistent.dom()
            <= addresses_in_aus(model.program.state.journal.loaded_index_aus())
    }
}

pub open spec fn another_atomic_recovery_image_matches_disk(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    model.program.state.recovery_state is SuperblockAvailable ==> {
        &&& model.program.state.persistent_image is Some
        &&& model.program.state.persistent_image.unwrap() == durable_superblock_image_i(model)
    }
}

pub open spec fn another_atomic_recovery_image_seq_wf(model: AnotherAtomicState) -> bool
{
    model.recovery_state is SuperblockAvailable ==> {
        &&& model.persistent_image is Some
        &&& model.persistent_image.unwrap().wf()
        &&& model.journal.journal.snapshot == model.persistent_image.unwrap().journal_snapshot
        &&& model.branch.seq_end() == model.persistent_image.unwrap().branch_seq_end
        &&& model.journal.persistent_seq_end == model.persistent_image.unwrap().journal_seq_end
        &&& model.journal_metadata_loaded() ==>
            model.journal.journal.seq_end() == model.persistent_image.unwrap().journal_seq_end
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
    &&& another_atomic_recovery_image_seq_wf(model)
    &&& another_atomic_journal_mini_allocator_stage_wf(model)
    &&& another_atomic_sync_request_wf(model)
}

pub proof fn client_ready_implies_atomic_branch_metadata_loaded_flag(model: AnotherAtomicState)
    requires
        model.wf(),
        model.client_ready(),
    ensures
        atomic_branch_metadata_loaded_flag(model.branch),
{
    assert(model.recovery_state is RecoveryComplete);
    assert(model.recovery_metadata_wf());
    assert(model.branch_metadata_loaded());
    atomic_branch_metadata_loaded_flag_from_metadata_loaded(model.branch);
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
    &&& forall |id: ID| #![trigger atomic.outstanding_cache_reqs.contains_key(id)]
            atomic.outstanding_cache_reqs.contains_key(id)
            ==> disk_has_pending_id(disk, id)
    &&& forall |addr: Address| #[trigger] filled_cache_status(atomic.cache).contains_key(addr)
            && filled_cache_status(atomic.cache)[addr] == CachingDiskPageStatus::Clean
            && addr != spec_superblock_addr()
            ==> {
                &&& disk.content.contains_key(addr)
                &&& disk.content[addr] == cache_filled_page(atomic.cache, addr)
            }
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
            &&& atomic.client_ready()
            &&& atomic.in_flight is Some
            &&& atomic.in_flight.unwrap().req_id == id
            &&& disk.requests[id]->data
                == marshal_abstract_superblock(atomic.atomic_inflight_superblock_i())
            &&& atomic.atomic_inflight_superblock_i().wf()
            &&& AtomicJournalState::State::next(
                atomic.journal,
                atomic.journal,
                AtomicJournalState::Label::CommitPrepared,
            )
            &&& AtomicBranchState::State::next(
                atomic.branch,
                atomic.branch,
                AtomicBranchState::Label::CommitPrepared,
            )
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

pub open spec fn another_atomic_inflight_cache_id_disjoint(
    atomic: AnotherAtomicState,
) -> bool
{
    atomic.in_flight is Some ==>
        !atomic.outstanding_cache_reqs.contains_key(atomic.in_flight.unwrap().req_id)
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
        &&& !journal_image_static_domain_i(
            model,
            atomic_persistent_superblock_image_i(model),
        ).contains(addr)
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
        ==> journal_projection_uses_live(model))
    &&& (forall |addr: Address| #[trigger] filled_cache_status(model.program.state.cache).contains_key(addr)
        && filled_cache_status(model.program.state.cache)[addr] == CachingDiskPageStatus::Dirty
        ==> model.program.state.journal_metadata_loaded())
    &&& (forall |addr: Address| #[trigger] filled_cache_status(model.program.state.cache).contains_key(addr)
        && filled_cache_status(model.program.state.cache)[addr] == CachingDiskPageStatus::Writeback
        ==> model.program.state.journal_metadata_loaded())
    &&& (forall |addr: Address| #[trigger] filled_cache_status(model.program.state.cache).contains_key(addr) ==> {
        &&& journal_image_dirty_cache_disjoint_at(
            model,
            atomic_persistent_superblock_image_i(model),
            addr,
        )
        &&& model.program.state.in_flight is Some ==>
            journal_image_dirty_cache_disjoint_at(model, model.program.state.atomic_inflight_superblock_i(), addr)
    })
    &&& (forall |id: ID| #[trigger] model.disk.requests.contains_key(id) ==> {
        &&& journal_image_request_writeback_disjoint_at(
            model,
            atomic_persistent_superblock_image_i(model),
            id,
        )
        &&& model.program.state.in_flight is Some ==>
            journal_image_request_writeback_disjoint_at(model, model.program.state.atomic_inflight_superblock_i(), id)
    })
    &&& journal_allocable_addrs_image_disjoint(model)
}

pub open spec fn journal_dirty_writeback_pages_tracked(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    forall |addr: Address| #[trigger] filled_cache_status(model.program.state.cache).contains_key(addr)
        && (filled_cache_status(model.program.state.cache)[addr] == CachingDiskPageStatus::Dirty
            || filled_cache_status(model.program.state.cache)[addr] == CachingDiskPageStatus::Writeback)
        && model.program.state.journal_owned_aus().contains(addr.au)
        ==> mini_allocator_allocated_addrs(model.program.state.journal.mini_allocator).contains(addr)
}

pub open spec fn branch_image_static_domain_i(
    model: SystemModel::State<AnotherProgramModel>,
    image: AbstractSuperblockImage,
) -> Set<Address>
{
    if model.program.state.superblock_metadata_known()
        && atomic_branch_metadata_loaded_flag(model.program.state.branch)
    {
        let branch_image = branch_caching_disk_state_i(model).visible_image_for_metadata(
            CachingDiskBranchModule::CachingDiskBranchFrozenImage{
                sealed_roots: image.branch_roots,
                seq_end: image.branch_seq_end,
            },
        );
        if branch_image.loadable() {
            addresses_in_aus(summary_aus(branch_image.branch_summary()))
        } else {
            branch_image.sealed_stack_i().sealed_disk.entries.dom()
        }
    } else {
        branch_image_projection_addrs_i(model.disk.content, image.branch_roots)
    }
}

pub open spec fn branch_image_request_writeback_disjoint_at(
    model: SystemModel::State<AnotherProgramModel>,
    image: AbstractSuperblockImage,
    id: ID,
) -> bool
{
    model.disk.requests.contains_key(id)
        && model.disk.requests[id] is WriteReq
        && model.disk.requests[id]->to != spec_superblock_addr()
        ==> !branch_image_static_domain_i(model, image).contains(model.disk.requests[id]->to)
}

pub open spec fn branch_image_writeback_disjoint(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    forall |id: ID| #[trigger] model.disk.requests.contains_key(id) ==> {
        &&& branch_image_request_writeback_disjoint_at(
            model,
            atomic_persistent_superblock_image_i(model),
            id,
        )
        &&& model.program.state.in_flight is Some ==>
            branch_image_request_writeback_disjoint_at(
                model,
                model.program.state.atomic_inflight_superblock_i(),
                id,
            )
    }
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
    &&& another_atomic_inflight_cache_id_disjoint(model.program.state)
    &&& journal_image_writeback_disjoint(model)
    &&& journal_dirty_writeback_pages_tracked(model)
    &&& branch_image_writeback_disjoint(model)
    &&& journal_component_refinement_inv(model)
    &&& branch_component_refinement_inv(model)
    &&& journal_projected_aus_are_component_data(model)
    &&& branch_projected_aus_are_owned_data(model)
    &&& branch_loaded_metadata_agrees_with_visible(model)
    &&& journal_loaded_index_matches_persistent_subdisk(model)
    &&& journal_index_aus_have_unique_lsns(model)
    &&& journal_inflight_projection_wf(model)
    &&& another_atomic_recovery_image_matches_disk(model)
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
    assert(branch_projection_aus(model) =~= Set::<AU>::empty()) by {
        assert(branch_projection_summary_i(model)
            == model.program.state.branch.branch_summary);
        assert(model.program.state.branch.branch_summary.values()
            == Set::<Set<AU>>::empty());
        assert forall |au: AU| #[trigger] branch_projection_aus(model).contains(au)
            implies false by {
            if summary_aus(branch_projection_summary_i(model)).contains(au) {
                let summary = lemma_union_set_of_sets_contains(
                    branch_projection_summary_i(model).values(),
                    au,
                );
                assert(false);
            } else {
                assert(model.program.state.branch.mini_allocator.all_aus().contains(au));
                assert(false);
            }
        }
    }
    assert(branch_projected_aus_are_owned_data(model));

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
        to_aus_empty();
        assert(journal_projection_addrs(model) =~= Set::<Address>::empty());
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
    assert(journal_projected_aus_are_component_data(model));
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
        branch_projection_addrs(pre) <= branch_projection_addrs(post),
        branch_projection_addrs(post) <= branch_projection_addrs(pre) + writes.dom(),
        branch_disk_persistent_i(post) == branch_disk_persistent_i(pre),
        reads <= branch_disk_cache_i(pre),
        writes.dom() <= branch_projection_addrs(post),
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
        branch_projection_addrs(post) =~= branch_projection_addrs(pre),
        branch_persistent_projection_addrs(post) =~= branch_persistent_projection_addrs(pre),
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

pub proof fn recovery_complete_preserves_journal_component_refinement(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        AnotherAtomicState::recovery_complete(pre.program.state, post.program.state),
        post.disk == pre.disk,
    ensures
        journal_component_refinement_inv(post),
{
    AnotherAtomicState::recovery_complete_effect(
        pre.program.state,
        post.program.state,
    );
    AnotherAtomicState::recovery_complete_wf(
        pre.program.state,
        post.program.state,
    );
    assert(post.program.state.journal_metadata_loaded()
        == pre.program.state.journal_metadata_loaded());
    assert(post.program.state.in_flight == pre.program.state.in_flight);
    assert(post.program.state.journal.in_flight
        == pre.program.state.journal.in_flight);
    assert(post.program.state.branch.in_flight
        == pre.program.state.branch.in_flight);
    assert forall |addr: Address|
        #[trigger] post.program.state.journal.mini_allocator.can_allocate(addr)
        implies pre.program.state.journal.mini_allocator.can_allocate(addr) by {
        assert(post.program.state.journal.mini_allocator
            == pre.program.state.journal.mini_allocator);
    }
    journal_image_writeback_disjoint_preserved_by_unchanged_cache_disk_images(
        pre,
        post,
    );
    journal_query_end_lsn_refines(pre, post);
    CrashAwareCachingDiskJournal::State::inv_next(
        crash_aware_caching_disk_journal_i(pre),
        crash_aware_caching_disk_journal_i(post),
        CrashAwareCachingDiskJournal::Label::QueryEndLsn{
            end_lsn: pre.program.state.branch.seq_end(),
        },
    );
    assert(journal_component_refinement_inv(post));
}

pub proof fn branch_cache_access_preserves_journal_component_refinement(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        post.program.state.wf(),
        post.disk == pre.disk,
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads, writes},
        ),
        pre.program.state.superblock_metadata_known(),
        post.program.state.superblock_metadata_known(),
        post.program.state.client_ready() == pre.program.state.client_ready(),
        journal_projection_uses_live(post) == journal_projection_uses_live(pre),
        post.program.state.journal == pre.program.state.journal,
        post.program.state.in_flight == pre.program.state.in_flight,
        post.program.state.journal.in_flight == pre.program.state.journal.in_flight,
        post.program.state.branch.in_flight == pre.program.state.branch.in_flight,
        writes.dom().disjoint(journal_projection_addrs(pre)),
    ensures
        journal_component_refinement_inv(post),
{
    assert(post.program.state.journal_metadata_loaded()
        == pre.program.state.journal_metadata_loaded());
    assert(post.program.state.journal.journal.snapshot
        == pre.program.state.journal.journal.snapshot);
    assert(post.program.state.journal.mini_allocator
        == pre.program.state.journal.mini_allocator);
    assert(post.program.state.journal.loaded_index_aus()
        =~= pre.program.state.journal.loaded_index_aus());

    journal_projection_domains_unchanged_by_cache_access_outside(
        pre,
        post,
        reads,
        writes,
    );
    cache_access_outside_journal_projection_unchanged(
        pre,
        post,
        reads,
        writes,
    );

    let persistent_image = durable_superblock_image_i(pre);
    assert(durable_superblock_image_i(post) == persistent_image);
    if pre.program.state.journal_metadata_loaded() {
        journal_image_projection_aus_loaded_index_unchanged(pre, post, persistent_image);
    } else {
        assert(!post.program.state.journal_metadata_loaded());
        assert(journal_image_projection_aus_i(post, persistent_image)
            =~= journal_image_projection_aus_i(pre, persistent_image));
    }
    journal_image_persistent_unchanged_for_same_projection(pre, post, persistent_image);
    assert(persistent_journal_image_i(post) == persistent_journal_image_i(pre));

    if pre.program.state.in_flight is Some {
        assert(post.program.state.in_flight is Some);
        assert(post.program.state.atomic_inflight_superblock_i()
            == pre.program.state.atomic_inflight_superblock_i());
        let frozen_image = pre.program.state.atomic_inflight_superblock_i();
        if pre.program.state.journal_metadata_loaded() {
            journal_image_projection_aus_loaded_index_unchanged(pre, post, frozen_image);
        } else {
            assert(!post.program.state.journal_metadata_loaded());
            assert(journal_image_projection_aus_i(post, frozen_image)
                =~= journal_image_projection_aus_i(pre, frozen_image));
        }
        journal_image_persistent_unchanged_for_same_projection(pre, post, frozen_image);
        assert(frozen_journal_image_i(post) == frozen_journal_image_i(pre));
    } else {
        assert(post.program.state.in_flight is None);
        assert(frozen_journal_image_i(post) == frozen_journal_image_i(pre));
    }

    assert(journal_caching_disk_i(post) == journal_caching_disk_i(pre));
    assert(crash_aware_caching_disk_journal_i(post)
        == crash_aware_caching_disk_journal_i(pre));
    if !post.program.state.client_ready() {
        assert(!pre.program.state.client_ready());
        assert(pre.program.state.journal.mini_allocator
            == crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty());
        assert(post.program.state.journal.mini_allocator
            == crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty());
    }
    assert(journal_projection_tight(post));
    assert(journal_projection_uses_shared_async_disk(post));
    assert(journal_component_refinement_inv(post));
}

pub proof fn superblock_write_request_wf_preserved_by_unchanged_commit_components(
    pre_atomic: AnotherAtomicState,
    post_atomic: AnotherAtomicState,
    disk: AsyncDisk::State,
)
    requires
        another_atomic_superblock_write_request_wf(pre_atomic, disk),
        post_atomic.client_ready() == pre_atomic.client_ready(),
        post_atomic.in_flight == pre_atomic.in_flight,
        post_atomic.journal == pre_atomic.journal,
        post_atomic.branch == pre_atomic.branch,
    ensures
        another_atomic_superblock_write_request_wf(post_atomic, disk),
{
    if pre_atomic.in_flight is Some {
        assert(post_atomic.in_flight is Some);
        assert(post_atomic.journal.in_flight == pre_atomic.journal.in_flight);
        assert(post_atomic.branch.in_flight == pre_atomic.branch.in_flight);
        assert(post_atomic.journal.in_flight.unwrap()
            == pre_atomic.journal.in_flight.unwrap());
        assert(post_atomic.branch.in_flight.unwrap()
            == pre_atomic.branch.in_flight.unwrap());
    }
    assert(post_atomic.atomic_inflight_superblock_i()
        == pre_atomic.atomic_inflight_superblock_i());
    assert forall |id: ID| #![trigger disk.requests.contains_key(id)]
        disk.requests.contains_key(id)
        && disk.requests[id] is WriteReq
        && disk.requests[id]->to == spec_superblock_addr()
        implies {
            &&& post_atomic.client_ready()
            &&& post_atomic.in_flight is Some
            &&& post_atomic.in_flight.unwrap().req_id == id
            &&& disk.requests[id]->data
                == marshal_abstract_superblock(post_atomic.atomic_inflight_superblock_i())
            &&& post_atomic.atomic_inflight_superblock_i().wf()
            &&& AtomicJournalState::State::next(
                post_atomic.journal,
                post_atomic.journal,
                AtomicJournalState::Label::CommitPrepared,
            )
            &&& AtomicBranchState::State::next(
                post_atomic.branch,
                post_atomic.branch,
                AtomicBranchState::Label::CommitPrepared,
            )
        }
    by {
        assert(another_atomic_superblock_write_request_wf(pre_atomic, disk));
        assert(AtomicJournalState::State::next(
            pre_atomic.journal,
            pre_atomic.journal,
            AtomicJournalState::Label::CommitPrepared,
        ));
        assert(AtomicBranchState::State::next(
            pre_atomic.branch,
            pre_atomic.branch,
            AtomicBranchState::Label::CommitPrepared,
        ));
    }
}

pub proof fn atomic_inflight_superblock_unchanged(
    pre_atomic: AnotherAtomicState,
    post_atomic: AnotherAtomicState,
)
    requires
        post_atomic.in_flight == pre_atomic.in_flight,
        post_atomic.journal.in_flight == pre_atomic.journal.in_flight,
        post_atomic.branch.in_flight == pre_atomic.branch.in_flight,
    ensures
        post_atomic.atomic_inflight_superblock_i()
            == pre_atomic.atomic_inflight_superblock_i(),
{
    if pre_atomic.in_flight is Some {
        assert(post_atomic.in_flight is Some);
        assert(post_atomic.journal.in_flight.unwrap()
            == pre_atomic.journal.in_flight.unwrap());
        assert(post_atomic.branch.in_flight.unwrap()
            == pre_atomic.branch.in_flight.unwrap());
    }
}

pub proof fn atomic_journal_commit_prepared_from_facts(
    journal: AtomicJournalState::State,
)
    requires
        journal.in_flight is Some,
        journal.journal.status is Some,
        journal.in_flight.unwrap().snapshot.freshest_rec() is Some ==>
            journal.in_flight.unwrap().seq_end <= journal.journal.clean_watermark(),
    ensures
        AtomicJournalState::State::next(
            journal,
            journal,
            AtomicJournalState::Label::CommitPrepared,
        ),
{
    assert(AtomicJournalState::State::commit_prepared(
        journal,
        journal,
        AtomicJournalState::Label::CommitPrepared,
    ));
    assert(AtomicJournalState::State::next_by(
        journal,
        journal,
        AtomicJournalState::Label::CommitPrepared,
        AtomicJournalState::Step::commit_prepared(),
    )) by {
        reveal(AtomicJournalState::State::next_by);
    }
    reveal(AtomicJournalState::State::next);
}

pub proof fn atomic_branch_commit_prepared_from_facts(
    branch: AtomicBranchState::State,
)
    requires
        branch.in_flight is Some,
        branch.in_flight.unwrap().sealed_roots.len() <= branch.persisted_root_count,
        branch.in_flight.unwrap().sealed_roots.len() <= branch.image.sealed_roots.len(),
        branch.image.sealed_roots.subrange(
            0,
            branch.in_flight.unwrap().sealed_roots.len() as int,
        ) == branch.in_flight.unwrap().sealed_roots,
    ensures
        AtomicBranchState::State::next(
            branch,
            branch,
            AtomicBranchState::Label::CommitPrepared,
        ),
{
    assert(AtomicBranchState::State::commit_prepared(
        branch,
        branch,
        AtomicBranchState::Label::CommitPrepared,
    ));
    assert(AtomicBranchState::State::next_by(
        branch,
        branch,
        AtomicBranchState::Label::CommitPrepared,
        AtomicBranchState::Step::commit_prepared(),
    )) by {
        reveal(AtomicBranchState::State::next_by);
    }
    reveal(AtomicBranchState::State::next);
}

pub proof fn atomic_journal_commit_prepared_preserved(
    pre: AtomicJournalState::State,
    post: AtomicJournalState::State,
)
    requires
        AtomicJournalState::State::next(
            pre,
            pre,
            AtomicJournalState::Label::CommitPrepared,
        ),
        post.in_flight == pre.in_flight,
        post.journal.status is Some,
        pre.journal.clean_watermark() <= post.journal.clean_watermark(),
    ensures
        AtomicJournalState::State::next(
            post,
            post,
            AtomicJournalState::Label::CommitPrepared,
        ),
{
    reveal(AtomicJournalState::State::next);
    reveal(AtomicJournalState::State::next_by);
    let step = choose |step: AtomicJournalState::Step|
        AtomicJournalState::State::next_by(
            pre,
            pre,
            AtomicJournalState::Label::CommitPrepared,
            step,
        );
    match step {
        AtomicJournalState::Step::commit_prepared() => {
            assert(AtomicJournalState::State::commit_prepared(
                pre,
                pre,
                AtomicJournalState::Label::CommitPrepared,
            ));
            if pre.in_flight.unwrap().snapshot.freshest_rec() is Some {
                assert(pre.in_flight.unwrap().seq_end <= pre.journal.clean_watermark());
                assert(pre.in_flight.unwrap().seq_end <= post.journal.clean_watermark());
            }
        },
        _ => {
            assert(false);
        }
    }
    assert(post.in_flight is Some);
    atomic_journal_commit_prepared_from_facts(post);
}

pub proof fn atomic_branch_commit_prepared_preserved(
    pre: AtomicBranchState::State,
    post: AtomicBranchState::State,
)
    requires
        AtomicBranchState::State::next(
            pre,
            pre,
            AtomicBranchState::Label::CommitPrepared,
        ),
        post.in_flight == pre.in_flight,
        pre.in_flight.unwrap().sealed_roots.len() <= post.persisted_root_count,
        pre.in_flight.unwrap().sealed_roots.len() <= post.image.sealed_roots.len(),
        post.image.sealed_roots.subrange(
            0,
            pre.in_flight.unwrap().sealed_roots.len() as int,
        ) == pre.in_flight.unwrap().sealed_roots,
    ensures
        AtomicBranchState::State::next(
            post,
            post,
            AtomicBranchState::Label::CommitPrepared,
        ),
{
    assert(pre.in_flight is Some) by {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let step = choose |step: AtomicBranchState::Step|
            AtomicBranchState::State::next_by(
                pre,
                pre,
                AtomicBranchState::Label::CommitPrepared,
                step,
            );
        match step {
            AtomicBranchState::Step::commit_prepared() => {},
            _ => { assert(false); },
        }
    }
    assert(post.in_flight is Some);
    atomic_branch_commit_prepared_from_facts(post);
}

pub proof fn superblock_write_request_wf_preserved_by_prepared_components(
    pre_atomic: AnotherAtomicState,
    post_atomic: AnotherAtomicState,
    disk: AsyncDisk::State,
)
    requires
        another_atomic_superblock_write_request_wf(pre_atomic, disk),
        post_atomic.client_ready() == pre_atomic.client_ready(),
        post_atomic.in_flight == pre_atomic.in_flight,
        post_atomic.atomic_inflight_superblock_i() == pre_atomic.atomic_inflight_superblock_i(),
        post_atomic.in_flight is Some
            && disk.requests.contains_key(post_atomic.in_flight.unwrap().req_id)
            && disk.requests[post_atomic.in_flight.unwrap().req_id] is WriteReq
            && disk.requests[post_atomic.in_flight.unwrap().req_id]->to
                == spec_superblock_addr()
            ==> AtomicJournalState::State::next(
            post_atomic.journal,
            post_atomic.journal,
            AtomicJournalState::Label::CommitPrepared,
        ),
        post_atomic.in_flight is Some
            && disk.requests.contains_key(post_atomic.in_flight.unwrap().req_id)
            && disk.requests[post_atomic.in_flight.unwrap().req_id] is WriteReq
            && disk.requests[post_atomic.in_flight.unwrap().req_id]->to
                == spec_superblock_addr()
            ==> AtomicBranchState::State::next(
            post_atomic.branch,
            post_atomic.branch,
            AtomicBranchState::Label::CommitPrepared,
        ),
    ensures
        another_atomic_superblock_write_request_wf(post_atomic, disk),
{
    assert forall |id: ID| #![trigger disk.requests.contains_key(id)]
        disk.requests.contains_key(id)
        && disk.requests[id] is WriteReq
        && disk.requests[id]->to == spec_superblock_addr()
        implies {
            &&& post_atomic.client_ready()
            &&& post_atomic.in_flight is Some
            &&& post_atomic.in_flight.unwrap().req_id == id
            &&& disk.requests[id]->data
                == marshal_abstract_superblock(post_atomic.atomic_inflight_superblock_i())
            &&& post_atomic.atomic_inflight_superblock_i().wf()
            &&& AtomicJournalState::State::next(
                post_atomic.journal,
                post_atomic.journal,
                AtomicJournalState::Label::CommitPrepared,
            )
            &&& AtomicBranchState::State::next(
                post_atomic.branch,
                post_atomic.branch,
                AtomicBranchState::Label::CommitPrepared,
            )
        }
    by {
        assert(another_atomic_superblock_write_request_wf(pre_atomic, disk));
        assert(post_atomic.in_flight is Some);
    }
}

pub proof fn superblock_write_request_wf_when_not_client_ready(
    pre_atomic: AnotherAtomicState,
    post_atomic: AnotherAtomicState,
    disk: AsyncDisk::State,
)
    requires
        another_atomic_superblock_write_request_wf(pre_atomic, disk),
        !pre_atomic.client_ready(),
    ensures
        another_atomic_superblock_write_request_wf(post_atomic, disk),
{
    assert forall |id: ID| #![trigger disk.requests.contains_key(id)]
        disk.requests.contains_key(id)
        && disk.requests[id] is WriteReq
        && disk.requests[id]->to == spec_superblock_addr()
        implies {
            &&& post_atomic.client_ready()
            &&& post_atomic.in_flight is Some
            &&& post_atomic.in_flight.unwrap().req_id == id
            &&& disk.requests[id]->data
                == marshal_abstract_superblock(post_atomic.atomic_inflight_superblock_i())
            &&& post_atomic.atomic_inflight_superblock_i().wf()
            &&& AtomicJournalState::State::next(
                post_atomic.journal,
                post_atomic.journal,
                AtomicJournalState::Label::CommitPrepared,
            )
            &&& AtomicBranchState::State::next(
                post_atomic.branch,
                post_atomic.branch,
                AtomicBranchState::Label::CommitPrepared,
            )
        }
    by {
        assert(another_atomic_superblock_write_request_wf(pre_atomic, disk));
        assert(pre_atomic.client_ready());
        assert(false);
    }
}

pub proof fn branch_component_refinement_inv_preserved_by_unchanged_branch_projection(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
)
    requires
        branch_component_refinement_inv(pre),
        post.program.state.wf(),
        post.disk == pre.disk,
        post.program.state.cache == pre.program.state.cache,
        pre.program.state.in_flight is Some ==>
            post.program.state.atomic_inflight_superblock_i()
                == pre.program.state.atomic_inflight_superblock_i(),
        post.program.state.branch == pre.program.state.branch,
        post.program.state.in_flight == pre.program.state.in_flight,
        post.program.state.persistent_image == pre.program.state.persistent_image,
    ensures
        branch_component_refinement_inv(post),
{
    assert(async_disk_superblock_page_wf(post.disk.content));
    assert(atomic_persistent_superblock_image_i(post)
        == atomic_persistent_superblock_image_i(pre));
    assert(atomic_branch_metadata_loaded_flag(post.program.state.branch)
        == atomic_branch_metadata_loaded_flag(pre.program.state.branch));
    assert(branch_projection_summary_i(post) == branch_projection_summary_i(pre));
    assert(branch_projection_addrs(post) =~= branch_projection_addrs(pre)) by {
        assert_maps_equal!(
            branch_projection_summary_i(post),
            branch_projection_summary_i(pre),
            au => { }
        );
    }
    assert(branch_persistent_projection_addrs(post)
        =~= branch_persistent_projection_addrs(pre)) by {
        assert forall |addr: Address|
            #[trigger] branch_persistent_projection_addrs(post).contains(addr)
                <==> branch_persistent_projection_addrs(pre).contains(addr)
        by {
            assert(branch_projection_addrs(post).contains(addr)
                <==> branch_projection_addrs(pre).contains(addr));
            if post.disk.content.contains_key(addr) {
                assert(pre.disk.content.contains_key(addr));
            }
            if pre.disk.content.contains_key(addr) {
                assert(post.disk.content.contains_key(addr));
            }
        }
    }
    assert(branch_disk_cache_i(post) == branch_disk_cache_i(pre)) by {
        assert_maps_equal!(
            branch_disk_cache_i(post),
            branch_disk_cache_i(pre),
            addr => {
                assert(branch_projection_addrs(post).contains(addr)
                    <==> branch_projection_addrs(pre).contains(addr));
            }
        );
    }
    assert(branch_disk_status_i(post) == branch_disk_status_i(pre)) by {
        assert_maps_equal!(
            branch_disk_status_i(post),
            branch_disk_status_i(pre),
            addr => {
                assert(branch_projection_addrs(post).contains(addr)
                    <==> branch_projection_addrs(pre).contains(addr));
            }
        );
    }
    assert(branch_disk_persistent_i(post) == branch_disk_persistent_i(pre)) by {
        assert_maps_equal!(
            branch_disk_persistent_i(post),
            branch_disk_persistent_i(pre),
            addr => {
                assert(branch_persistent_projection_addrs(post).contains(addr)
                    <==> branch_persistent_projection_addrs(pre).contains(addr));
            }
        );
    }
    assert(branch_caching_disk_i(post) == branch_caching_disk_i(pre));
    assert(branch_caching_disk_state_i(post) == branch_caching_disk_state_i(pre));
    assert(persistent_branch_image_i(post) == persistent_branch_image_i(pre));
    assert(frozen_branch_image_i(post) == frozen_branch_image_i(pre));
    assert(atomic_superblock_prepared_i(post) == atomic_superblock_prepared_i(pre)) by {
        if pre.program.state.in_flight is Some {
            assert(post.program.state.in_flight is Some);
        }
        assert(post.program.state.atomic_inflight_superblock_i()
            == pre.program.state.atomic_inflight_superblock_i());
    }
    assert(crash_aware_caching_disk_branch_i(post)
        == crash_aware_caching_disk_branch_i(pre));
    assert(branch_component_refinement_inv(post));
}

pub proof fn journal_load_index_reads_match_disk(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    reads: Map<Address, RawPage>,
    discovered_aus: Set<AU>,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        AnotherAtomicState::journal_load_index(
            pre.program.state,
            post.program.state,
            reads,
            discovered_aus,
        ),
    ensures
        reads <= pre.disk.content,
        to_journal_records(reads) <= to_journal_records(pre.disk.content),
{
    AnotherAtomicState::journal_load_index_effect(
        pre.program.state,
        post.program.state,
        reads,
        discovered_aus,
    );
    assert(!pre.program.state.journal_metadata_loaded());
    let cache_lbl = Cache::Label::Access{reads, writes: Map::<Address, RawPage>::empty()};
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    assert(Cache::State::next_by(
        pre.program.state.cache,
        post.program.state.cache,
        cache_lbl,
        Cache::Step::access(),
    ));
    reveal(Cache::State::access);
    assert(Cache::State::access(
        pre.program.state.cache,
        post.program.state.cache,
        cache_lbl,
    ));
    assert forall |addr: Address| #[trigger] reads.contains_key(addr)
        implies {
            &&& pre.disk.content.contains_key(addr)
            &&& pre.disk.content[addr] == reads[addr]
        }
    by {
        assert(cache_lbl is Access);
        assert(cache_lbl->reads == reads);
        assert(cache_lbl->reads.contains_key(addr));
        assert(pre.program.state.cache.valid_read(addr, reads[addr]));
        assert(pre.program.state.cache.lookup_map.contains_key(addr));
        let slot = pre.program.state.cache.lookup_map[addr];
        assert(pre.program.state.cache.entries[slot] is Filled);
        assert(pre.program.state.cache.entries[slot]->data == reads[addr]);
        pre.program.state.cache.build_lookup_map_ensures();
        assert(pre.program.state.cache.lookup_map == pre.program.state.cache.build_lookup_map());
        assert(pre.program.state.cache.entries.contains_key(slot));
        assert(cache_filled_addr(pre.program.state.cache, addr));
        assert(cache_filled_page(pre.program.state.cache, addr) == reads[addr]);
        assert(filled_cache_status(pre.program.state.cache).contains_key(addr));
        assert(filled_cache_status(pre.program.state.cache)[addr]
            != CachingDiskPageStatus::Dirty) by {
            if filled_cache_status(pre.program.state.cache)[addr] == CachingDiskPageStatus::Dirty {
                assert(journal_image_writeback_disjoint(pre));
                assert(pre.program.state.journal_metadata_loaded());
                assert(false);
            }
        }
        assert(filled_cache_status(pre.program.state.cache)[addr]
            != CachingDiskPageStatus::Writeback) by {
            if filled_cache_status(pre.program.state.cache)[addr] == CachingDiskPageStatus::Writeback {
                assert(journal_image_writeback_disjoint(pre));
                assert(pre.program.state.journal_metadata_loaded());
                assert(false);
            }
        }
        assert(filled_cache_status(pre.program.state.cache)[addr]
            == CachingDiskPageStatus::Clean);
        assert(another_atomic_cache_disk_coupling(pre.program.state, pre.disk));
    }
    assert(reads <= pre.disk.content) by {
        assert_maps_equal!(reads, reads.restrict(reads.dom()), a => {});
        assert forall |addr: Address| #[trigger] reads.contains_key(addr)
            implies {
                &&& pre.disk.content.contains_key(addr)
                &&& pre.disk.content[addr] == reads[addr]
            } by {}
    }
    assert(to_journal_records(reads) <= to_journal_records(pre.disk.content)) by {
        assert forall |addr: Address| #[trigger] to_journal_records(reads).contains_key(addr)
            implies {
                &&& to_journal_records(pre.disk.content).contains_key(addr)
                &&& to_journal_records(pre.disk.content)[addr]
                    == to_journal_records(reads)[addr]
            } by {
            assert(reads.contains_key(addr));
            assert(pre.disk.content.contains_key(addr));
            assert(pre.disk.content[addr] == reads[addr]);
        }
    }
}

pub open spec fn journal_load_index_disk_walk_witness(
    model: SystemModel::State<AnotherProgramModel>,
    discovered_aus: Set<AU>,
    au_depth: nat,
    page_depth: nat,
) -> bool
{
    let disk_records = to_journal_records(model.disk.content);
    let snapshot = model.program.state.journal.journal.snapshot;
    &&& au_walk_reads_cover(
        disk_records,
        snapshot.boundary_lsn,
        snapshot.freshest_rec(),
        snapshot.first(),
        au_depth,
        page_depth,
    )
    &&& discovered_aus =~=
        build_lsn_au_index_from_reads_au_walk_depth(
            disk_records,
            snapshot.boundary_lsn,
            snapshot.freshest_rec(),
            snapshot.first(),
            au_depth,
            page_depth,
        ).values()
}

pub proof fn journal_load_index_discovered_aus_matches_disk_bounded_walk(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    reads: Map<Address, RawPage>,
    discovered_aus: Set<AU>,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        AnotherAtomicState::journal_load_index(
            pre.program.state,
            post.program.state,
            reads,
            discovered_aus,
        ),
        post.disk == pre.disk,
    ensures
        exists |au_depth: nat, page_depth: nat|
            #[trigger] journal_load_index_disk_walk_witness(
                pre,
                discovered_aus,
                au_depth,
                page_depth,
            ),
{
    AnotherAtomicState::journal_load_index_effect(
        pre.program.state,
        post.program.state,
        reads,
        discovered_aus,
    );
    journal_load_index_reads_match_disk(pre, post, reads, discovered_aus);
    let cj_lbl = CachedJournal::Label::LoadIndex{
        reads: to_journal_records(reads),
        discovered_aus,
    };
    assert(CachedJournal::State::next(
        pre.program.state.journal.journal,
        post.program.state.journal.journal,
        cj_lbl,
    ));
    reveal(CachedJournal::State::next);
    reveal(CachedJournal::State::next_by);
    let step = choose |step| CachedJournal::State::next_by(
        pre.program.state.journal.journal,
        post.program.state.journal.journal,
        cj_lbl,
        step,
    );
    match step {
        CachedJournal::Step::load_index(au_depth, page_depth) => {
            let ptr = pre.program.state.journal.journal.snapshot.freshest_rec();
            let bdy = pre.program.state.journal.journal.snapshot.boundary_lsn;
            let first = pre.program.state.journal.journal.snapshot.first();
            let read_records = to_journal_records(reads);
            let disk_records = to_journal_records(pre.disk.content);
            let read_index = build_lsn_au_index_from_reads_au_walk_depth(
                read_records,
                bdy,
                ptr,
                first,
                au_depth,
                page_depth,
            );
            let disk_index = build_lsn_au_index_from_reads_au_walk_depth(
                disk_records,
                bdy,
                ptr,
                first,
                au_depth,
                page_depth,
            );
            assert(discovered_aus == read_index.values());
            assert(au_walk_reads_cover(read_records, bdy, ptr, first, au_depth, page_depth));
            au_walk_reads_cover_supermap(
                read_records,
                disk_records,
                bdy,
                ptr,
                first,
                au_depth,
                page_depth,
            );
            assert(au_walk_reads_cover(disk_records, bdy, ptr, first, au_depth, page_depth));
            build_lsn_au_index_from_reads_au_walk_depth_supermap(
                read_records,
                disk_records,
                bdy,
                ptr,
                first,
                au_depth,
                page_depth,
            );
            assert(read_index =~= disk_index);
            assert(discovered_aus =~= disk_index.values());
            assert(journal_load_index_disk_walk_witness(
                pre,
                discovered_aus,
                au_depth,
                page_depth,
            ));
        },
        _ => { assert(false); },
    }
}

pub proof fn journal_load_index_discovered_aus_subset_projection(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    reads: Map<Address, RawPage>,
    discovered_aus: Set<AU>,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        AnotherAtomicState::journal_load_index(
            pre.program.state,
            post.program.state,
            reads,
            discovered_aus,
        ),
        post.disk == pre.disk,
    ensures
        discovered_aus <= journal_projection_aus(pre),
{
    AnotherAtomicState::journal_load_index_effect(
        pre.program.state,
        post.program.state,
        reads,
        discovered_aus,
    );
    journal_load_index_discovered_aus_matches_disk_bounded_walk(
        pre,
        post,
        reads,
        discovered_aus,
    );
    let (au_depth, page_depth) = choose |au_depth: nat, page_depth: nat|
        #[trigger] journal_load_index_disk_walk_witness(pre, discovered_aus, au_depth, page_depth);
    let disk_records = to_journal_records(pre.disk.content);
    let snapshot = pre.program.state.journal.journal.snapshot;
    let image = persistent_journal_image_i(pre);
    let tight_entries = image.i().tj.disk_view.entries;
    let durable_image = durable_superblock_image_i(pre);
    assert(pre.program.state.recovery_state is SuperblockAvailable);
    assert(pre.program.state.superblock_metadata_known());
    assert(pre.program.state.persistent_image.unwrap() == durable_image);
    assert(snapshot == durable_image.journal_snapshot);
    assert(image.snapshot == snapshot);
    assert(image.persistent <= pre.disk.content);
    assert(tight_entries <= to_journal_records(image.persistent)) by {
        assert_maps_equal!(
            tight_entries,
            tight_entries.restrict(tight_entries.dom()),
            addr => {}
        );
        assert forall |addr: Address| #[trigger] tight_entries.contains_key(addr)
            implies {
                &&& to_journal_records(image.persistent).contains_key(addr)
                &&& to_journal_records(image.persistent)[addr] == tight_entries[addr]
            } by {
            assert(image.i().tj.disk_view.entries.contains_key(addr));
            assert(image.i().tj.disk_view.entries <= to_journal_records(image.persistent));
        }
    }
    assert(to_journal_records(image.persistent) <= disk_records) by {
        assert forall |addr: Address| #[trigger] to_journal_records(image.persistent).contains_key(addr)
            implies {
                &&& disk_records.contains_key(addr)
                &&& disk_records[addr] == to_journal_records(image.persistent)[addr]
            } by {
            assert(image.persistent.contains_key(addr));
            assert(pre.disk.content.contains_key(addr));
            assert(pre.disk.content[addr] == image.persistent[addr]);
        }
    }
    assert(tight_entries <= disk_records) by {
        assert forall |addr: Address| #[trigger] tight_entries.contains_key(addr)
            implies {
                &&& disk_records.contains_key(addr)
                &&& disk_records[addr] == tight_entries[addr]
            } by {
            assert(to_journal_records(image.persistent).contains_key(addr));
            assert(to_journal_records(image.persistent)[addr] == tight_entries[addr]);
        }
    }
    assert(image.wf());
    assert(image.i().tj.disk_view == image.tj().disk_view);
    assert(image.tj().disk_view.wf_addrs());
    assert(image.tj().disk_view.pointer_is_upstream(
        image.tj().freshest_rec,
        image.snapshot.first(),
    ));
    assert(tight_entries.dom() <= journal_image_projection_domain_i(pre, durable_image)) by {
        assert forall |addr: Address| #[trigger] tight_entries.dom().contains(addr)
            implies journal_image_projection_domain_i(pre, durable_image).contains(addr) by {
            assert(tight_entries.contains_key(addr));
            assert(to_journal_records(image.persistent).contains_key(addr));
            assert(image.persistent.contains_key(addr));
            assert(image.persistent == pre.disk.content.restrict(
                journal_image_projection_domain_i(pre, durable_image),
            ));
        }
    }
    assert forall |au: AU| #[trigger] discovered_aus.contains(au)
        implies journal_projection_aus(pre).contains(au) by {
        assert(build_lsn_au_index_from_reads_au_walk_depth(
            disk_records,
            snapshot.boundary_lsn,
            snapshot.freshest_rec(),
            snapshot.first(),
            au_depth,
            page_depth,
        ).values().contains(au));
        build_lsn_au_index_from_reads_au_walk_values_in_sub_entries(
            disk_records,
            tight_entries,
            snapshot.boundary_lsn,
            snapshot.freshest_rec(),
            snapshot.first(),
            au_depth,
            page_depth,
            au,
        );
        assert(to_aus(tight_entries.dom()).contains(au));
        assert(tight_entries.dom() <= journal_image_projection_domain_i(pre, durable_image));
        assert(journal_image_projection_domain_i(pre, durable_image)
            <= addresses_in_aus(journal_projection_aus(pre)));
        assert(tight_entries.dom() <= addresses_in_aus(journal_projection_aus(pre)));
        to_aus_subset_of_aus_from_addr_subset(tight_entries.dom(), journal_projection_aus(pre));
    }
}

pub proof fn journal_load_index_matches_valid_persistent_subdisk(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    reads: Map<Address, RawPage>,
    discovered_aus: Set<AU>,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        AnotherAtomicState::journal_load_index(
            pre.program.state,
            post.program.state,
            reads,
            discovered_aus,
        ),
        post.disk == pre.disk,
    ensures
        post.program.state.journal.journal.status is Some,
        post.program.state.journal.journal.status.unwrap().lsn_au_index =~=
            persistent_journal_image_i(post).i().tj.disk_view.build_lsn_au_index_au_walk(
                post.program.state.journal.journal.snapshot.freshest_rec(),
                post.program.state.journal.journal.snapshot.first(),
            ),
{
    AnotherAtomicState::journal_load_index_effect(
        pre.program.state,
        post.program.state,
        reads,
        discovered_aus,
    );
    journal_load_index_reads_match_disk(pre, post, reads, discovered_aus);
    let cj_lbl = CachedJournal::Label::LoadIndex{
        reads: to_journal_records(reads),
        discovered_aus,
    };
    assert(CachedJournal::State::next(
        pre.program.state.journal.journal,
        post.program.state.journal.journal,
        cj_lbl,
    ));
    reveal(CachedJournal::State::next);
    reveal(CachedJournal::State::next_by);
    let step = choose |step| CachedJournal::State::next_by(
        pre.program.state.journal.journal,
        post.program.state.journal.journal,
        cj_lbl,
        step,
    );
    match step {
        CachedJournal::Step::load_index(au_depth, page_depth) => {
            let ptr = pre.program.state.journal.journal.snapshot.freshest_rec();
            let bdy = pre.program.state.journal.journal.snapshot.boundary_lsn;
            let first = pre.program.state.journal.journal.snapshot.first();
            let read_records = to_journal_records(reads);
            let disk_records = to_journal_records(pre.disk.content);
            let image = persistent_journal_image_i(pre);
            let sub_entries = image.i().tj.disk_view.entries;
            let sub_dv = DiskView{boundary_lsn: bdy, entries: sub_entries};
            assert(post.program.state.journal.journal.snapshot
                == pre.program.state.journal.journal.snapshot);
            assert(persistent_journal_image_i(post) == image);
            assert(image.snapshot == pre.program.state.journal.journal.snapshot);
            assert(image.wf());
            assert(image.i().valid_image());
            assert(image.i().tj.disk_view == sub_dv);
            assert(sub_dv.pointer_is_upstream(ptr, first));
            assert(sub_dv.wf_addrs());
            assert(sub_entries <= disk_records) by {
                assert_maps_equal!(
                    sub_entries,
                    sub_entries.restrict(sub_entries.dom()),
                    addr => {}
                );
                assert forall |addr: Address| #[trigger] sub_entries.contains_key(addr)
                    implies {
                        &&& disk_records.contains_key(addr)
                        &&& disk_records[addr] == sub_entries[addr]
                    } by {
                    assert(image.i().tj.disk_view.entries.contains_key(addr));
                    assert(image.i().tj.disk_view.entries <= to_journal_records(image.persistent));
                    assert(to_journal_records(image.persistent).contains_key(addr));
                    assert(to_journal_records(image.persistent)[addr] == sub_entries[addr]);
                    assert(image.persistent.contains_key(addr));
                    assert(image.persistent <= pre.disk.content);
                    assert(pre.disk.content.contains_key(addr));
                    assert(pre.disk.content[addr] == image.persistent[addr]);
                    assert(disk_records.contains_key(addr));
                    assert(disk_records[addr] == to_journal_records(image.persistent)[addr]);
                }
            }
            assert(au_walk_reads_cover(read_records, bdy, ptr, first, au_depth, page_depth));
            au_walk_reads_cover_supermap(
                read_records,
                disk_records,
                bdy,
                ptr,
                first,
                au_depth,
                page_depth,
            );
            assert(au_walk_reads_cover(disk_records, bdy, ptr, first, au_depth, page_depth));
            au_walk_reads_cover_sub_entries(
                disk_records,
                sub_entries,
                bdy,
                ptr,
                first,
                au_depth,
                page_depth,
            );
            assert(au_walk_reads_cover(sub_entries, bdy, ptr, first, au_depth, page_depth));
            build_lsn_au_index_from_reads_au_walk_depth_supermap(
                read_records,
                disk_records,
                bdy,
                ptr,
                first,
                au_depth,
                page_depth,
            );
            assert(build_lsn_au_index_from_reads_au_walk_depth(
                read_records,
                bdy,
                ptr,
                first,
                au_depth,
                page_depth,
            ) =~= build_lsn_au_index_from_reads_au_walk_depth(
                disk_records,
                bdy,
                ptr,
                first,
                au_depth,
                page_depth,
            ));
            au_walk_larger_disk_matches_valid_subdisk(
                sub_entries,
                disk_records,
                bdy,
                ptr,
                first,
                au_depth,
                page_depth,
            );
            assert(post.program.state.journal.journal.status.unwrap().lsn_au_index
                == build_lsn_au_index_from_reads_au_walk_depth(
                    read_records,
                    bdy,
                    ptr,
                    first,
                    au_depth,
                    page_depth,
                ));
            assert(post.program.state.journal.journal.status.unwrap().lsn_au_index
                =~= sub_dv.build_lsn_au_index_au_walk(ptr, first));
        },
        _ => { assert(false); },
    }
}

pub proof fn persistent_journal_image_projection_domain_materialized(
    model: SystemModel::State<AnotherProgramModel>,
)
    requires
        persistent_journal_image_i(model).valid_image(),
    ensures
        journal_image_projection_domain_i(model, durable_superblock_image_i(model))
            <= model.disk.content.dom(),
{
    let image = persistent_journal_image_i(model);
    let abstract_image = durable_superblock_image_i(model);
    let domain = journal_image_projection_domain_i(model, abstract_image);
    let full_records = to_journal_records(model.disk.content);
    assert(image == journal_image_i(model, abstract_image));
    assert(image.snapshot == abstract_image.journal_snapshot);
    assert(image.persistent == model.disk.content.restrict(domain));
    to_journal_records_restrict(model.disk.content, domain);
    assert(to_journal_records(image.persistent) =~= full_records.restrict(domain));
    snapshot_walk_domain_restrict_domain_same(
        full_records,
        abstract_image.journal_snapshot.boundary_lsn,
        abstract_image.journal_snapshot.freshest_rec(),
    );
    assert(image.stable_tj().disk_view.entries.dom() =~= domain) by {
        assert forall |addr: Address|
            #[trigger] image.stable_tj().disk_view.entries.dom().contains(addr)
                <==> domain.contains(addr)
        by {
            assert(to_journal_records(image.persistent) =~= full_records.restrict(domain));
        }
    }
    image.valid_image_stable_domain_materialized();
    assert forall |addr: Address| #[trigger] domain.contains(addr)
        implies model.disk.content.dom().contains(addr) by {
        assert(image.stable_tj().disk_view.entries.dom().contains(addr));
        assert(image.persistent.dom().contains(addr));
        assert(image.persistent.contains_key(addr));
        assert(model.disk.content.restrict(domain).contains_key(addr));
        assert(model.disk.content.contains_key(addr));
    }
}

pub proof fn journal_unique_index_aus_imply_no_impersonation(
    model: SystemModel::State<AnotherProgramModel>,
)
    requires
        model.program.state.journal_metadata_loaded(),
        persistent_journal_image_i(model).wf(),
        journal_loaded_index_matches_persistent_subdisk(model),
        journal_index_aus_have_unique_lsns(model),
    ensures
        journal_owned_disk_records_do_not_impersonate_index(model),
{
    let journal = model.program.state.journal;
    let snapshot = journal.journal.snapshot;
    let disk_view = DiskView{
        boundary_lsn: snapshot.boundary_lsn,
        entries: to_journal_records(model.disk.content),
    };
    let index = journal.journal.status.unwrap().lsn_au_index;
    let image = persistent_journal_image_i(model);
    let sub_tj = image.i().tj;
    let sub_dv = sub_tj.disk_view;
    let sub_index = sub_tj.build_lsn_au_index_from_first(snapshot.first());
    assert(image.snapshot == snapshot);
    assert(image.i().valid_image());
    assert(sub_tj.freshest_rec == snapshot.freshest_rec());
    assert(sub_tj.disk_view.boundary_lsn == snapshot.boundary_lsn);
    assert(sub_tj.disk_view.wf());
    assert(sub_tj.disk_view.wf_addrs());
    assert(sub_tj.disk_view.pointer_is_upstream(sub_tj.freshest_rec, snapshot.first()));
    sub_tj.build_lsn_au_index_from_first_ensures(snapshot.first());
    assert(sub_index == sub_dv.build_lsn_au_index_au_walk(
        snapshot.freshest_rec(),
        snapshot.first(),
    ));
    assert(index =~= sub_index);

    assert forall |addr: Address, lsn: LSN| {
        &&& #[trigger] disk_view.entries.contains_key(addr)
        &&& model.program.state.journal_owned_aus().contains(addr.au)
        &&& #[trigger] index.contains_key(lsn)
        &&& index[lsn] == addr.au
        &&& disk_view.entries[addr].contains_lsn(snapshot.boundary_lsn, lsn)
    } implies {
        ||| snapshot_walk_domain(
            disk_view.entries,
            snapshot.boundary_lsn,
            snapshot.freshest_rec(),
        ).contains(addr)
        ||| mini_allocator_allocated_addrs(journal.mini_allocator).contains(addr)
    } by {
        assert(sub_index.contains_key(lsn));
        assert(sub_index[lsn] == index[lsn]);
        let witness = sub_dv.instantiate_index_keys_exist_valid_entries(sub_index, lsn);
        assert(sub_dv.addr_supports_lsn(witness, lsn));
        assert(sub_dv.entries.contains_key(witness));
        assert(sub_dv.entries[witness].contains_lsn(snapshot.boundary_lsn, lsn));
        assert(disk_view.entries.contains_key(witness)) by {
            assert(image.i().tj.disk_view.entries.contains_key(witness));
            assert(image.i().tj.disk_view.entries <= to_journal_records(image.persistent));
            assert(to_journal_records(image.persistent).contains_key(witness));
            assert(to_journal_records(image.persistent)[witness] == sub_dv.entries[witness]);
            assert(image.persistent <= model.disk.content);
            assert(image.persistent.contains_key(witness));
            assert(model.disk.content.contains_key(witness));
            assert(model.disk.content[witness] == image.persistent[witness]);
        }
        assert(disk_view.entries[witness] == sub_dv.entries[witness]) by {
            assert(to_journal_records(image.persistent).contains_key(witness));
            assert(to_journal_records(image.persistent)[witness] == sub_dv.entries[witness]);
            assert(image.persistent.contains_key(witness));
            assert(model.disk.content[witness] == image.persistent[witness]);
        }
        assert(disk_view.entries[witness].contains_lsn(snapshot.boundary_lsn, lsn));
        assert(index.values().contains(addr.au)) by {
            assert(index.contains_key(lsn));
            assert(index[lsn] == addr.au);
        }
        assert(index.values().contains(witness.au)) by {
            assert(index.contains_key(lsn));
            assert(sub_index[lsn] == witness.au);
            assert(index[lsn] == sub_index[lsn]);
        }
        assert(addr == witness) by {
            assert(journal_index_aus_have_unique_lsns(model));
        }
        assert(snapshot_walk_domain(
            disk_view.entries,
            snapshot.boundary_lsn,
            snapshot.freshest_rec(),
        ).contains(witness)) by {
            assert(image.i().tj.disk_view.entries.contains_key(witness));
            assert(image.i().tj.disk_view.entries.dom().contains(witness));
            assert(image.i().tj.disk_view.entries.dom()
                <= journal_image_projection_domain_i(model, durable_superblock_image_i(model))) by {
                assert_maps_equal!(
                    image.i().tj.disk_view.entries,
                    image.i().tj.disk_view.entries.restrict(image.i().tj.disk_view.entries.dom()),
                    a => {}
                );
                assert forall |a: Address| #[trigger] image.i().tj.disk_view.entries.dom().contains(a)
                    implies journal_image_projection_domain_i(
                        model,
                        durable_superblock_image_i(model),
                    ).contains(a) by {
                    assert(image.i().tj.disk_view.entries.contains_key(a));
                    assert(image.i().tj.disk_view.entries <= to_journal_records(image.persistent));
                    assert(to_journal_records(image.persistent).contains_key(a));
                    assert(image.persistent.contains_key(a));
                    assert(image.persistent == model.disk.content.restrict(
                        journal_image_projection_domain_i(model, durable_superblock_image_i(model)),
                    ));
                }
            }
            assert(journal_image_projection_domain_i(model, durable_superblock_image_i(model))
                == snapshot_walk_domain(
                    disk_view.entries,
                    snapshot.boundary_lsn,
                    snapshot.freshest_rec(),
                ));
        }
    }
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
                    &&& atomic.client_ready()
                    &&& atomic.in_flight is Some
                    &&& atomic.in_flight.unwrap().req_id == id
                    &&& post_disk.requests[id]->data
                        == marshal_abstract_superblock(atomic.atomic_inflight_superblock_i())
                    &&& atomic.atomic_inflight_superblock_i().wf()
                    &&& AtomicJournalState::State::next(
                        atomic.journal,
                        atomic.journal,
                        AtomicJournalState::Label::CommitPrepared,
                    )
                    &&& AtomicBranchState::State::next(
                        atomic.branch,
                        atomic.branch,
                        AtomicBranchState::Label::CommitPrepared,
                    )
                }
            by {
                assert(post_disk.requests == pre_disk.requests.remove(processed_id));
                assert(pre_disk.requests.contains_key(id));
                assert(post_disk.requests[id] == pre_disk.requests[id]);
                assert(another_atomic_superblock_write_request_wf(atomic, pre_disk));
            }
        },
        AsyncDisk::Step::process_write(processed_id) => {
            assert forall |id: ID| #![trigger post_disk.requests.contains_key(id)]
                post_disk.requests.contains_key(id)
                && post_disk.requests[id] is WriteReq
                && post_disk.requests[id]->to == spec_superblock_addr()
                implies {
                    &&& atomic.client_ready()
                    &&& atomic.in_flight is Some
                    &&& atomic.in_flight.unwrap().req_id == id
                    &&& post_disk.requests[id]->data
                        == marshal_abstract_superblock(atomic.atomic_inflight_superblock_i())
                    &&& atomic.atomic_inflight_superblock_i().wf()
                    &&& AtomicJournalState::State::next(
                        atomic.journal,
                        atomic.journal,
                        AtomicJournalState::Label::CommitPrepared,
                    )
                    &&& AtomicBranchState::State::next(
                        atomic.branch,
                        atomic.branch,
                        AtomicBranchState::Label::CommitPrepared,
                    )
                }
            by {
                assert(post_disk.requests == pre_disk.requests.remove(processed_id));
                assert(pre_disk.requests.contains_key(id));
                assert(post_disk.requests[id] == pre_disk.requests[id]);
                assert(another_atomic_superblock_write_request_wf(atomic, pre_disk));
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
                            cache_evicted_addr_lookup_slot(
                                pre_atomic.cache,
                                evicted_slots,
                                req->to,
                            );
                            let evicted_slot = pre_slot;
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
        journal_image_projection_domain_i(post, image)
            =~= journal_image_projection_domain_i(pre, image),
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

pub proof fn journal_image_static_domain_unchanged_by_disk_content(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    image: AbstractSuperblockImage,
)
    requires
        post.disk.content == pre.disk.content,
    ensures
        journal_image_static_domain_i(post, image) =~= journal_image_static_domain_i(pre, image),
{
    assert forall |addr: Address|
        journal_image_static_domain_i(post, image).contains(addr)
            <==> journal_image_static_domain_i(pre, image).contains(addr)
    by {
    }
}

pub proof fn cache_internal_dirty_in_post_was_dirty_in_pre(
    pre_cache: Cache::State,
    post_cache: Cache::State,
    addr: Address,
)
    requires
        pre_cache.inv(),
        Cache::State::next(pre_cache, post_cache, Cache::Label::Internal{}),
        filled_cache_status(post_cache).contains_key(addr),
        filled_cache_status(post_cache)[addr] == CachingDiskPageStatus::Dirty,
    ensures
        filled_cache_status(pre_cache).contains_key(addr),
        filled_cache_status(pre_cache)[addr] == CachingDiskPageStatus::Dirty,
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
    assert(cache_filled_addr(post_cache, addr));
    let post_slot = post_cache.lookup_map[addr];
    match step {
        Cache::Step::reserve(new_slots_mapping) => {
            assert(Cache::State::reserve(pre_cache, post_cache, Cache::Label::Internal{}, new_slots_mapping)) by {
                reveal(Cache::State::reserve);
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
            assert(pre_cache.entries[post_slot] == post_cache.entries[post_slot]);
            assert(post_cache.entries[post_slot].get_addr() == addr);
            assert(pre_cache.entries[post_slot].get_addr() == addr);
            assert(pre_cache.lookup_map.contains_key(addr));
            assert(pre_cache.lookup_map[addr] == post_slot);
            assert(cache_filled_addr(pre_cache, addr));
            assert(pre_cache.status_map[post_slot] == post_cache.status_map[post_slot]);
        },
        Cache::Step::evict(evicted_slots) => {
            assert(Cache::State::evict(pre_cache, post_cache, Cache::Label::Internal{}, evicted_slots)) by {
                reveal(Cache::State::evict);
            }
            let evicted_addrs = Map::new(
                |slot: Slot| evicted_slots.contains(slot),
                |slot: Slot| pre_cache.entries[slot].get_addr(),
            ).values();
            assert(post_cache.lookup_map == pre_cache.lookup_map.remove_keys(evicted_addrs));
            assert(!evicted_addrs.contains(addr)) by {
                if evicted_addrs.contains(addr) {
                    assert(!post_cache.lookup_map.contains_key(addr));
                    assert(cache_filled_addr(post_cache, addr));
                    assert(false);
                }
            }
            assert(pre_cache.lookup_map.contains_key(addr));
            assert(pre_cache.lookup_map[addr] == post_slot);
            let updated_entries = Map::new(
                |slot| evicted_slots.contains(slot),
                |slot| Entry::Empty,
            );
            let updated_status_map = Map::new(
                |slot| evicted_slots.contains(slot),
                |slot| CacheStatus::NotFilled,
            );
            assert(post_cache.entries == pre_cache.entries.union_prefer_right(updated_entries));
            assert(post_cache.status_map == pre_cache.status_map.union_prefer_right(updated_status_map));
            assert(!evicted_slots.contains(post_slot)) by {
                if evicted_slots.contains(post_slot) {
                    assert(evicted_addrs.contains(addr));
                    assert(false);
                }
            }
            assert(!updated_entries.contains_key(post_slot));
            assert(!updated_status_map.contains_key(post_slot));
            assert(post_cache.entries[post_slot] == pre_cache.entries[post_slot]);
            assert(post_cache.status_map[post_slot] == pre_cache.status_map[post_slot]);
            assert(cache_filled_addr(pre_cache, addr));
        },
        Cache::Step::noop() => {
            assert(Cache::State::noop(pre_cache, post_cache, Cache::Label::Internal{})) by {
                reveal(Cache::State::noop);
            }
            assert(post_cache == pre_cache);
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn journal_image_writeback_disjoint_preserved_by_cache_internal(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
)
    requires
        pre.program.state.cache.inv(),
        journal_image_writeback_disjoint(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Internal{},
        ),
        post.disk == pre.disk,
        post.program.state.journal == pre.program.state.journal,
        post.program.state.in_flight == pre.program.state.in_flight,
        post.program.state.journal.in_flight == pre.program.state.journal.in_flight,
        post.program.state.branch.in_flight == pre.program.state.branch.in_flight,
    ensures
        journal_image_writeback_disjoint(post),
{
    let durable_image = durable_superblock_image_i(pre);
    assert(durable_superblock_image_i(post) == durable_image);
    journal_image_static_domain_unchanged_by_disk_content(pre, post, durable_image);
    if pre.program.state.in_flight is Some {
        assert(post.program.state.atomic_inflight_superblock_i()
            == pre.program.state.atomic_inflight_superblock_i());
        journal_image_static_domain_unchanged_by_disk_content(
            pre,
            post,
            pre.program.state.atomic_inflight_superblock_i(),
        );
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
        cache_internal_dirty_in_post_was_dirty_in_pre(
            pre.program.state.cache,
            post.program.state.cache,
            addr,
        );
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
        if filled_cache_status(post.program.state.cache)[addr] == CachingDiskPageStatus::Dirty {
            cache_internal_dirty_in_post_was_dirty_in_pre(
                pre.program.state.cache,
                post.program.state.cache,
                addr,
            );
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
                &&& !journal_image_static_domain_i(post, durable_superblock_image_i(post)).contains(addr)
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

pub proof fn journal_image_writeback_disjoint_preserved_by_unchanged_cache_disk_images(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
)
    requires
        journal_image_writeback_disjoint(pre),
        post.disk == pre.disk,
        post.program.state.cache == pre.program.state.cache,
        post.program.state.journal_metadata_loaded() == pre.program.state.journal_metadata_loaded(),
        forall |addr: Address| #[trigger] post.program.state.journal.mini_allocator.can_allocate(addr)
            ==> pre.program.state.journal.mini_allocator.can_allocate(addr),
        post.program.state.in_flight == pre.program.state.in_flight,
        post.program.state.journal.in_flight == pre.program.state.journal.in_flight,
        post.program.state.branch.in_flight == pre.program.state.branch.in_flight,
    ensures
        journal_image_writeback_disjoint(post),
{
    let durable_image = durable_superblock_image_i(pre);
    assert(durable_superblock_image_i(post) == durable_image);
    journal_image_static_domain_unchanged_by_disk_content(pre, post, durable_image);
    if pre.program.state.in_flight is Some {
        assert(post.program.state.atomic_inflight_superblock_i()
            == pre.program.state.atomic_inflight_superblock_i());
        journal_image_static_domain_unchanged_by_disk_content(
            pre,
            post,
            pre.program.state.atomic_inflight_superblock_i(),
        );
    }
    assert(filled_cache_status(post.program.state.cache)
        =~= filled_cache_status(pre.program.state.cache)) by {
        assert_maps_equal!(
            filled_cache_status(post.program.state.cache),
            filled_cache_status(pre.program.state.cache),
            addr => { }
        );
    }

    assert forall |id: ID| #[trigger] post.disk.requests.contains_key(id)
        && post.disk.requests[id] is WriteReq
        && post.disk.requests[id]->to != spec_superblock_addr()
        implies post.program.state.journal_metadata_loaded()
    by {
        assert(pre.disk.requests.contains_key(id));
        assert(pre.disk.requests[id] == post.disk.requests[id]);
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
        if filled_cache_status(post.program.state.cache)[addr] == CachingDiskPageStatus::Dirty {
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
                &&& !journal_image_static_domain_i(post, durable_superblock_image_i(post)).contains(addr)
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
        post.program.state.recovery_state == pre.program.state.recovery_state,
        pre.program.state.journal_metadata_loaded(),
        post.program.state.journal_metadata_loaded(),
        forall |addr: Address| #[trigger] post.program.state.journal.mini_allocator.can_allocate(addr)
            ==> pre.program.state.journal.mini_allocator.can_allocate(addr),
        post.program.state.in_flight == pre.program.state.in_flight,
        post.program.state.journal.in_flight == pre.program.state.journal.in_flight,
        post.program.state.branch.in_flight == pre.program.state.branch.in_flight,
        atomic_persistent_superblock_image_i(post) == atomic_persistent_superblock_image_i(pre),
        writes.dom().disjoint(journal_image_static_domain_i(
            pre,
            atomic_persistent_superblock_image_i(pre),
        )),
        pre.program.state.in_flight is Some ==>
            writes.dom().disjoint(journal_image_static_domain_i(
                pre,
                pre.program.state.atomic_inflight_superblock_i(),
            )),
    ensures
        journal_image_writeback_disjoint(post),
{
    let persistent_image = atomic_persistent_superblock_image_i(pre);
    pre.program.state.cache.build_lookup_map_ensures();
    assert(pre.program.state.cache.build_lookup_map_props(pre.program.state.cache.lookup_map));
    assert(atomic_persistent_superblock_image_i(post) == persistent_image);
    journal_image_static_domain_unchanged_by_loaded_index_preservation(pre, post, persistent_image);
    if pre.program.state.in_flight is Some {
        let frozen_image = pre.program.state.atomic_inflight_superblock_i();
        assert(post.program.state.in_flight is Some);
        assert(post.program.state.atomic_inflight_superblock_i() == frozen_image);
        journal_image_static_domain_unchanged_by_loaded_index_preservation(pre, post, frozen_image);
    }

    assert forall |id: ID| #[trigger] post.disk.requests.contains_key(id)
        && post.disk.requests[id] is WriteReq
        && post.disk.requests[id]->to != spec_superblock_addr()
        implies journal_projection_uses_live(post)
    by {
        assert(pre.disk.requests.contains_key(id));
        assert(pre.disk.requests[id] == post.disk.requests[id]);
        assert(journal_projection_uses_live(pre));
    }

    assert forall |addr: Address| #[trigger] filled_cache_status(post.program.state.cache).contains_key(addr)
        implies {
            &&& journal_image_dirty_cache_disjoint_at(post, persistent_image, addr)
            &&& post.program.state.in_flight is Some ==>
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
                assert(!journal_image_static_domain_i(pre, persistent_image).contains(addr));
                assert(!journal_image_static_domain_i(post, persistent_image).contains(addr));
                if post.program.state.in_flight is Some {
                    assert(pre.program.state.in_flight is Some);
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
                assert(journal_image_dirty_cache_disjoint_at(pre, persistent_image, addr));
                assert(!journal_image_static_domain_i(pre, persistent_image).contains(addr));
                assert(!journal_image_static_domain_i(post, persistent_image).contains(addr));
                if post.program.state.in_flight is Some {
                    assert(pre.program.state.in_flight is Some);
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
            &&& journal_image_request_writeback_disjoint_at(post, persistent_image, id)
            &&& post.program.state.in_flight is Some ==>
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
            assert(journal_image_request_writeback_disjoint_at(pre, persistent_image, id));
            assert(!journal_image_static_domain_i(pre, persistent_image).contains(post.disk.requests[id]->to));
            assert(!journal_image_static_domain_i(post, persistent_image).contains(post.disk.requests[id]->to));
            if post.program.state.in_flight is Some {
                assert(pre.program.state.in_flight is Some);
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
                &&& !journal_image_static_domain_i(post, persistent_image).contains(addr)
                &&& post.program.state.in_flight is Some ==>
                    !journal_image_static_domain_i(
                        post,
                        post.program.state.atomic_inflight_superblock_i(),
                    ).contains(addr)
            } by {
            assert(pre.program.state.journal.mini_allocator.can_allocate(addr));
            assert(journal_allocable_addrs_image_disjoint(pre));
            assert(!journal_image_static_domain_i(pre, persistent_image).contains(addr));
            assert(!journal_image_static_domain_i(post, persistent_image).contains(addr));
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
        journal_image_static_domain_i(model, image) <= addresses_in_aus(journal_projection_aus(model)),
    ensures
        journal_image_static_domain_i(model, image) <= addresses_in_aus(journal_projection_aus(model)),
{
}

pub proof fn branch_writes_disjoint_from_journal_static_domains(
    model: SystemModel::State<AnotherProgramModel>,
    writes: Map<Address, RawPage>,
)
    requires
        journal_component_refinement_inv(model),
        model.program.state.journal_metadata_loaded(),
        to_aus(writes.dom()) <= model.program.state.branch_owned_aus(),
    ensures
        writes.dom().disjoint(journal_projection_addrs(model)),
        writes.dom().disjoint(journal_image_static_domain_i(
            model,
            atomic_persistent_superblock_image_i(model),
        )),
        model.program.state.in_flight is Some ==>
            writes.dom().disjoint(journal_image_static_domain_i(
                model,
                model.program.state.atomic_inflight_superblock_i(),
            )),
{
    branch_writes_disjoint_from_journal_projection(model, writes);
    let persistent_image = atomic_persistent_superblock_image_i(model);
    journal_image_static_domain_subset_journal_projection(model, persistent_image);
    assert(writes.dom().disjoint(journal_image_static_domain_i(model, persistent_image))) by {
        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
            implies !journal_image_static_domain_i(model, persistent_image).contains(addr) by {
            if journal_image_static_domain_i(model, persistent_image).contains(addr) {
                assert(addresses_in_aus(journal_projection_aus(model)).contains(addr));
                assert(false);
            }
        }
    }
    if model.program.state.in_flight is Some {
        let frozen_image = model.program.state.atomic_inflight_superblock_i();
        journal_image_static_domain_subset_journal_projection(model, frozen_image);
        assert(writes.dom().disjoint(journal_image_static_domain_i(model, frozen_image))) by {
            assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                implies !journal_image_static_domain_i(model, frozen_image).contains(addr) by {
                if journal_image_static_domain_i(model, frozen_image).contains(addr) {
                    assert(addresses_in_aus(journal_projection_aus(model)).contains(addr));
                    assert(false);
                }
            }
        }
    }
}

pub proof fn superblock_write_request_wf_preserved_by_branch_seal(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    aux_ptr: Option<Address>,
    summary: Summary,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    branch: AtomicBranchState::State,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        AnotherAtomicState::branch_seal(
            pre.program.state,
            post.program.state,
            aux_ptr,
            summary,
            reads,
            writes,
            branch,
        ),
        post.disk == pre.disk,
    ensures
        another_atomic_superblock_write_request_wf(post.program.state, post.disk),
{
    branch_seal_write_projection_facts(pre, post, aux_ptr, summary, reads, writes, branch);
    assert forall |id: ID| #![trigger post.disk.requests.contains_key(id)]
        post.disk.requests.contains_key(id)
        && post.disk.requests[id] is WriteReq
        && post.disk.requests[id]->to == spec_superblock_addr()
        implies {
            &&& post.program.state.client_ready()
            &&& post.program.state.in_flight is Some
            &&& post.program.state.in_flight.unwrap().req_id == id
            &&& post.disk.requests[id]->data
                == marshal_abstract_superblock(post.program.state.atomic_inflight_superblock_i())
            &&& post.program.state.atomic_inflight_superblock_i().wf()
            &&& AtomicJournalState::State::next(
                post.program.state.journal,
                post.program.state.journal,
                AtomicJournalState::Label::CommitPrepared,
            )
            &&& AtomicBranchState::State::next(
                post.program.state.branch,
                post.program.state.branch,
                AtomicBranchState::Label::CommitPrepared,
            )
        }
    by {
        assert(pre.disk.requests.contains_key(id));
        assert(pre.disk.requests[id] == post.disk.requests[id]);
        assert(another_atomic_superblock_write_request_wf(pre.program.state, pre.disk));
        assert(pre.program.state.client_ready());
        assert(post.program.state.client_ready());
        assert(pre.program.state.in_flight is Some);
        assert(post.program.state.in_flight == pre.program.state.in_flight);
        assert(pre.program.state.journal.in_flight is Some);
        assert(post.program.state.journal == pre.program.state.journal);
        assert(post.program.state.journal.in_flight == pre.program.state.journal.in_flight);
        assert(post.program.state.atomic_inflight_superblock_i()
            == pre.program.state.atomic_inflight_superblock_i());
        assert(AtomicJournalState::State::next(
            pre.program.state.journal,
            pre.program.state.journal,
            AtomicJournalState::Label::CommitPrepared,
        ));
        assert(AtomicJournalState::State::next(
            post.program.state.journal,
            post.program.state.journal,
            AtomicJournalState::Label::CommitPrepared,
        ));

        assert(AtomicBranchState::State::next(
            pre.program.state.branch,
            pre.program.state.branch,
            AtomicBranchState::Label::CommitPrepared,
        ));
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let pre_step = choose |step: AtomicBranchState::Step|
            AtomicBranchState::State::next_by(
                pre.program.state.branch,
                pre.program.state.branch,
                AtomicBranchState::Label::CommitPrepared,
                step,
            );
        match pre_step {
            AtomicBranchState::Step::commit_prepared() => {
                assert(AtomicBranchState::State::commit_prepared(
                    pre.program.state.branch,
                    pre.program.state.branch,
                    AtomicBranchState::Label::CommitPrepared,
                )) by {
                    reveal(AtomicBranchState::State::commit_prepared);
                }
                let image = pre.program.state.branch.in_flight.unwrap();
                assert(post.program.state.branch.in_flight == pre.program.state.branch.in_flight);
                assert(post.program.state.branch.persisted_root_count
                    == pre.program.state.branch.persisted_root_count);
                assert(image.sealed_roots.len()
                    <= post.program.state.branch.persisted_root_count);
                assert(post.program.state.branch.wf());
                assert(post.program.state.branch.image.sealed_roots.take(
                    image.sealed_roots.len() as int,
                ) == image.sealed_roots);
                assert(AtomicBranchState::State::commit_prepared(
                    post.program.state.branch,
                    post.program.state.branch,
                    AtomicBranchState::Label::CommitPrepared,
                )) by {
                    reveal(AtomicBranchState::State::commit_prepared);
                }
                assert(AtomicBranchState::State::next_by(
                    post.program.state.branch,
                    post.program.state.branch,
                    AtomicBranchState::Label::CommitPrepared,
                    AtomicBranchState::Step::commit_prepared(),
                )) by {
                    reveal(AtomicBranchState::State::next_by);
                }
            },
            _ => {
                assert(false);
            },
        }
    }
}

pub proof fn cache_disk_coupling_preserved_by_cache_access(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre.program.state.cache.inv(),
        another_atomic_cache_disk_coupling(pre.program.state, pre.disk),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads, writes},
        ),
        post.disk == pre.disk,
        post.program.state.outstanding_cache_reqs == pre.program.state.outstanding_cache_reqs,
    ensures
        another_atomic_cache_disk_coupling(post.program.state, post.disk),
{
    assert forall |id: ID| #![trigger post.program.state.outstanding_cache_reqs.contains_key(id)]
        post.program.state.outstanding_cache_reqs.contains_key(id)
        implies disk_has_pending_id(post.disk, id)
    by {
        assert(pre.program.state.outstanding_cache_reqs.contains_key(id));
        assert(disk_has_pending_id(pre.disk, id));
    }

    assert forall |addr: Address| #[trigger] filled_cache_status(post.program.state.cache).contains_key(addr)
        && filled_cache_status(post.program.state.cache)[addr] == CachingDiskPageStatus::Clean
        && addr != spec_superblock_addr()
        implies {
            &&& post.disk.content.contains_key(addr)
            &&& post.disk.content[addr] == cache_filled_page(post.program.state.cache, addr)
        }
    by {
        if writes.contains_key(addr) {
            reveal(Cache::State::next);
            reveal(Cache::State::next_by);
            assert(Cache::State::next_by(
                pre.program.state.cache,
                post.program.state.cache,
                Cache::Label::Access{reads, writes},
                Cache::Step::access(),
            ));
            assert(Cache::State::access(
                pre.program.state.cache,
                post.program.state.cache,
                Cache::Label::Access{reads, writes},
            ));
            let slot = pre.program.state.cache.lookup_map[addr];
            assert(pre.program.state.cache.valid_write(addr));
            assert(pre.program.state.cache.lookup_map.contains_key(addr));
            let restricted = pre.program.state.cache.lookup_map.restrict(writes.dom());
            assert(restricted.contains_key(addr));
            assert(restricted[addr] == slot);
            assert(restricted.values().contains(slot));
            assert(pre.program.state.cache.write_updated_status(writes).contains_key(slot));
            assert(post.program.state.cache.status_map[slot] == CacheStatus::Dirty);
            post.program.state.cache.build_lookup_map_ensures();
            assert(filled_cache_status(post.program.state.cache)[addr]
                == CachingDiskPageStatus::Dirty);
            assert(false);
        } else {
            assert(cache_filled_addr(post.program.state.cache, addr));
            assert(post.program.state.cache.status_map.contains_key(
                post.program.state.cache.lookup_map[addr],
            ));
            Cache::State::access_unwritten_addr_unchanged(
                pre.program.state.cache,
                post.program.state.cache,
                reads,
                writes,
                addr,
            );
            assert(pre.program.state.cache.lookup_map.contains_key(addr));
            pre.program.state.cache.build_lookup_map_ensures();
            assert(pre.program.state.cache.entries.contains_key(
                pre.program.state.cache.lookup_map[addr],
            ));
            assert(post.program.state.cache.lookup_map[addr]
                == pre.program.state.cache.lookup_map[addr]);
            assert(post.program.state.cache.entries[post.program.state.cache.lookup_map[addr]]
                == pre.program.state.cache.entries[pre.program.state.cache.lookup_map[addr]]);
            assert(post.program.state.cache.status_map[post.program.state.cache.lookup_map[addr]]
                == pre.program.state.cache.status_map[pre.program.state.cache.lookup_map[addr]]);
            assert(cache_filled_addr(pre.program.state.cache, addr));
            assert(pre.program.state.cache.status_map.contains_key(
                pre.program.state.cache.lookup_map[addr],
            ));
            assert(filled_cache_status(pre.program.state.cache).contains_key(addr));
            assert(filled_cache_status(pre.program.state.cache)[addr] == CachingDiskPageStatus::Clean);
            assert(cache_filled_page(post.program.state.cache, addr)
                == cache_filled_page(pre.program.state.cache, addr));
            assert(pre.disk.content.contains_key(addr));
            assert(pre.disk.content[addr] == cache_filled_page(pre.program.state.cache, addr));
        }
    }
}

pub proof fn program_internal_cache_internal_preserves_bookkeeping(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        AnotherAtomicState::cache_internal(pre.program.state, post.program.state),
        post.disk == pre.disk,
    ensures
        post.program.state.wf(),
        another_atomic_model_refinement_invariants(post.program.state),
        another_atomic_cache_disk_coupling(post.program.state, post.disk),
        journal_component_refinement_inv(post),
        branch_component_refinement_inv(post),
        another_atomic_superblock_write_request_wf(post.program.state, post.disk),
        another_atomic_cache_disk_request_wf(post.program.state, post.disk),
        journal_image_writeback_disjoint(post),
        another_atomic_disk_refinement_invariants(post),
{
    assert(Cache::State::next(
        pre.program.state.cache,
        post.program.state.cache,
        Cache::Label::Internal{},
    ));
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
    journal_image_writeback_disjoint_preserved_by_cache_internal(pre, post);
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let cache_step = choose |step: Cache::Step| Cache::State::next_by(
        pre.program.state.cache,
        post.program.state.cache,
        Cache::Label::Internal{},
        step,
    );

    assert(another_atomic_cache_disk_coupling(post.program.state, post.disk)) by {
        assert forall |id: ID| #![trigger post.program.state.outstanding_cache_reqs.contains_key(id)]
            post.program.state.outstanding_cache_reqs.contains_key(id)
            implies disk_has_pending_id(post.disk, id)
        by {
            assert(pre.program.state.outstanding_cache_reqs.contains_key(id));
            assert(disk_has_pending_id(pre.disk, id));
        }
        assert forall |addr: Address| #[trigger] filled_cache_status(post.program.state.cache).contains_key(addr)
            && filled_cache_status(post.program.state.cache)[addr] == CachingDiskPageStatus::Clean
            implies {
                &&& post.disk.content.contains_key(addr)
                &&& post.disk.content[addr] == cache_filled_page(post.program.state.cache, addr)
            }
        by {
            assert(post.disk == pre.disk);
            assert(cache_filled_addr(post.program.state.cache, addr));
            let post_slot = post.program.state.cache.lookup_map[addr];
            match cache_step {
                Cache::Step::reserve(new_slots_mapping) => {
                    assert(Cache::State::reserve(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Internal{},
                        new_slots_mapping,
                    ));
                    let updated_entries = Map::new(
                        |slot| new_slots_mapping.contains_key(slot),
                        |slot| Entry::Reserved{addr: new_slots_mapping[slot]},
                    );
                    assert(post.program.state.cache.entries
                        == pre.program.state.cache.entries.union_prefer_right(updated_entries));
                    assert(post.program.state.cache.status_map == pre.program.state.cache.status_map);
                    assert(!updated_entries.contains_key(post_slot)) by {
                        if updated_entries.contains_key(post_slot) {
                            assert(post.program.state.cache.entries[post_slot]
                                == Entry::Reserved{addr: new_slots_mapping[post_slot]});
                            assert(post.program.state.cache.entries[post_slot] is Filled);
                            assert(false);
                        }
                    }
                    assert(pre.program.state.cache.entries[post_slot]
                        == post.program.state.cache.entries[post_slot]);
                    post.program.state.cache.build_lookup_map_ensures();
                    assert(post.program.state.cache.build_lookup_map_props(
                        post.program.state.cache.lookup_map,
                    ));
                    assert(post.program.state.cache.entries[post_slot].get_addr() == addr);
                    assert(pre.program.state.cache.entries[post_slot].get_addr() == addr);
                    pre.program.state.cache.build_lookup_map_ensures();
                    assert(pre.program.state.cache.build_lookup_map_props(
                        pre.program.state.cache.lookup_map,
                    ));
                    assert(pre.program.state.cache.lookup_map.contains_key(addr));
                    assert(pre.program.state.cache.lookup_map[addr] == post_slot) by {
                    }
                    assert(cache_filled_addr(pre.program.state.cache, addr));
                    assert(cache_filled_page(pre.program.state.cache, addr)
                        == cache_filled_page(post.program.state.cache, addr));
                    assert(filled_cache_status(pre.program.state.cache).contains_key(addr));
                    assert(filled_cache_status(pre.program.state.cache)[addr]
                        == CachingDiskPageStatus::Clean);
                },
                Cache::Step::evict(evicted_slots) => {
                    assert(Cache::State::evict(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Internal{},
                        evicted_slots,
                    ));
                    let evicted_addrs = Map::new(
                        |slot: Slot| evicted_slots.contains(slot),
                        |slot: Slot| pre.program.state.cache.entries[slot].get_addr(),
                    ).values();
                    assert(post.program.state.cache.lookup_map
                        == pre.program.state.cache.lookup_map.remove_keys(evicted_addrs));
                    assert(!evicted_addrs.contains(addr)) by {
                        if evicted_addrs.contains(addr) {
                            assert(!post.program.state.cache.lookup_map.contains_key(addr));
                            assert(cache_filled_addr(post.program.state.cache, addr));
                            assert(false);
                        }
                    }
                    assert(pre.program.state.cache.lookup_map.contains_key(addr));
                    assert(pre.program.state.cache.lookup_map[addr] == post_slot) by {
                        pre.program.state.cache.build_lookup_map_ensures();
                        post.program.state.cache.build_lookup_map_ensures();
                        assert(pre.program.state.cache.build_lookup_map_props(
                            pre.program.state.cache.lookup_map,
                        ));
                        assert(post.program.state.cache.build_lookup_map_props(
                            post.program.state.cache.lookup_map,
                        ));
                    }
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
                        |slot| CacheStatus::NotFilled,
                    );
                    assert(post.program.state.cache.entries
                        == pre.program.state.cache.entries.union_prefer_right(updated_entries));
                    assert(post.program.state.cache.status_map
                        == pre.program.state.cache.status_map.union_prefer_right(updated_status_map));
                    assert(!updated_entries.contains_key(post_slot));
                    assert(!updated_status_map.contains_key(post_slot));
                    assert(pre.program.state.cache.entries[post_slot]
                        == post.program.state.cache.entries[post_slot]);
                    assert(pre.program.state.cache.status_map[post_slot]
                        == post.program.state.cache.status_map[post_slot]);
                    assert(cache_filled_addr(pre.program.state.cache, addr));
                    assert(cache_filled_page(pre.program.state.cache, addr)
                        == cache_filled_page(post.program.state.cache, addr));
                    assert(filled_cache_status(pre.program.state.cache).contains_key(addr));
                    assert(filled_cache_status(pre.program.state.cache)[addr]
                        == CachingDiskPageStatus::Clean);
                },
                Cache::Step::noop() => {
                    assert(Cache::State::noop(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Internal{},
                    ));
                    assert(post.program.state.cache == pre.program.state.cache);
                    assert(filled_cache_status(pre.program.state.cache).contains_key(addr));
                    assert(filled_cache_status(pre.program.state.cache)[addr]
                        == CachingDiskPageStatus::Clean);
                },
                _ => {
                    assert(false);
                },
            }
            assert(pre.disk.content.contains_key(addr));
            assert(pre.disk.content[addr] == cache_filled_page(pre.program.state.cache, addr));
        }
    }
    assert(pre.disk.content.union_prefer_right(filled_cache_pages(pre.program.state.cache))
        =~= post.disk.content.union_prefer_right(filled_cache_pages(post.program.state.cache))) by {
        assert_maps_equal!(
            pre.disk.content.union_prefer_right(filled_cache_pages(pre.program.state.cache)),
            post.disk.content.union_prefer_right(filled_cache_pages(post.program.state.cache)),
            addr => {
                assert(post.disk == pre.disk);
                match cache_step {
                    Cache::Step::reserve(new_slots_mapping) => {
                        assert(Cache::State::reserve(
                            pre.program.state.cache,
                            post.program.state.cache,
                            Cache::Label::Internal{},
                            new_slots_mapping,
                        ));
                        let updated_entries = Map::new(
                            |slot| new_slots_mapping.contains_key(slot),
                            |slot| Entry::Reserved{addr: new_slots_mapping[slot]},
                        );
                        assert(post.program.state.cache.entries
                            == pre.program.state.cache.entries.union_prefer_right(updated_entries));
                        assert(post.program.state.cache.status_map == pre.program.state.cache.status_map);
                        if filled_cache_pages(post.program.state.cache).contains_key(addr) {
                            assert(cache_filled_addr(post.program.state.cache, addr));
                            let slot = post.program.state.cache.lookup_map[addr];
                            assert(!updated_entries.contains_key(slot)) by {
                                if updated_entries.contains_key(slot) {
                                    assert(post.program.state.cache.entries[slot]
                                        == Entry::Reserved{addr: new_slots_mapping[slot]});
                                    assert(post.program.state.cache.entries[slot] is Filled);
                                    assert(false);
                                }
                            }
                            assert(pre.program.state.cache.entries[slot]
                                == post.program.state.cache.entries[slot]);
                            post.program.state.cache.build_lookup_map_ensures();
                            pre.program.state.cache.build_lookup_map_ensures();
                            assert(post.program.state.cache.entries[slot].get_addr() == addr);
                            assert(pre.program.state.cache.entries[slot].get_addr() == addr);
                            assert(pre.program.state.cache.lookup_map.contains_key(addr));
                            assert(cache_filled_addr(pre.program.state.cache, addr));
                        }
                        if filled_cache_pages(pre.program.state.cache).contains_key(addr) {
                            assert(cache_filled_addr(pre.program.state.cache, addr));
                            let slot = pre.program.state.cache.lookup_map[addr];
                            assert(!new_slots_mapping.contains_key(slot)) by {
                                if new_slots_mapping.contains_key(slot) {
                                    assert(pre.program.state.cache.valid_new_slots_mapping(new_slots_mapping));
                                    assert(pre.program.state.cache.entries[slot] is Empty);
                                    assert(false);
                                }
                            }
                            assert(!updated_entries.contains_key(slot));
                            assert(post.program.state.cache.entries[slot]
                                == pre.program.state.cache.entries[slot]);
                            post.program.state.cache.build_lookup_map_ensures();
                            pre.program.state.cache.build_lookup_map_ensures();
                            assert(pre.program.state.cache.entries[slot].get_addr() == addr);
                            assert(post.program.state.cache.entries[slot].get_addr() == addr);
                            assert(post.program.state.cache.lookup_map.contains_key(addr));
                            assert(cache_filled_addr(post.program.state.cache, addr));
                        }
                    },
                    Cache::Step::evict(evicted_slots) => {
                        assert(Cache::State::evict(
                            pre.program.state.cache,
                            post.program.state.cache,
                            Cache::Label::Internal{},
                            evicted_slots,
                        ));
                        let evicted_addrs = Map::new(
                            |slot: Slot| evicted_slots.contains(slot),
                            |slot: Slot| pre.program.state.cache.entries[slot].get_addr(),
                        ).values();
                        assert(post.program.state.cache.lookup_map
                            == pre.program.state.cache.lookup_map.remove_keys(evicted_addrs));
                        if filled_cache_pages(post.program.state.cache).contains_key(addr) {
                            assert(!evicted_addrs.contains(addr)) by {
                                if evicted_addrs.contains(addr) {
                                    assert(!post.program.state.cache.lookup_map.contains_key(addr));
                                    assert(cache_filled_addr(post.program.state.cache, addr));
                                    assert(false);
                                }
                            }
                            assert(cache_filled_addr(post.program.state.cache, addr));
                            let slot = post.program.state.cache.lookup_map[addr];
                            post.program.state.cache.build_lookup_map_ensures();
                            pre.program.state.cache.build_lookup_map_ensures();
                            assert(pre.program.state.cache.lookup_map.contains_key(addr));
                            assert(pre.program.state.cache.lookup_map[addr] == slot);
                            assert(cache_filled_addr(pre.program.state.cache, addr));
                        }
                        if filled_cache_pages(pre.program.state.cache).contains_key(addr) {
                            if evicted_addrs.contains(addr) {
                                cache_evicted_addr_lookup_slot(
                                    pre.program.state.cache,
                                    evicted_slots,
                                    addr,
                                );
                                let evicted_slot = pre.program.state.cache.lookup_map[addr];
                                assert(evicted_slots.contains(evicted_slot));
                                assert(pre.program.state.cache.status_map[evicted_slot] is Clean);
                                pre.program.state.cache.build_lookup_map_ensures();
                                assert(pre.program.state.cache.build_lookup_map_props(
                                    pre.program.state.cache.lookup_map,
                                ));
                                assert(pre.program.state.cache.entries[evicted_slot].get_addr() == addr);
                                assert(pre.program.state.cache.lookup_map.contains_key(addr));
                                assert(pre.program.state.cache.lookup_map[addr] == evicted_slot);
                                assert(filled_cache_status(pre.program.state.cache).contains_key(addr));
                                assert(filled_cache_status(pre.program.state.cache)[addr]
                                    == CachingDiskPageStatus::Clean);
                                assert(pre.disk.content.contains_key(addr));
                                assert(pre.disk.content[addr]
                                    == cache_filled_page(pre.program.state.cache, addr));
                            } else {
                                assert(cache_filled_addr(pre.program.state.cache, addr));
                                let slot = pre.program.state.cache.lookup_map[addr];
                                post.program.state.cache.build_lookup_map_ensures();
                                pre.program.state.cache.build_lookup_map_ensures();
                                assert(post.program.state.cache.lookup_map.contains_key(addr));
                                assert(post.program.state.cache.lookup_map[addr] == slot);
                                assert(cache_filled_addr(post.program.state.cache, addr));
                            }
                        }
                    },
                    Cache::Step::noop() => {
                        assert(Cache::State::noop(
                            pre.program.state.cache,
                            post.program.state.cache,
                            Cache::Label::Internal{},
                        ));
                        assert(post.program.state.cache == pre.program.state.cache);
                    },
                    _ => {
                        assert(false);
                    },
                }
            }
        );
    }

    assert(post.program.state.journal == pre.program.state.journal);
    assert(post.program.state.branch == pre.program.state.branch);
    assert(post.program.state.recovery_state == pre.program.state.recovery_state);
    assert(post.program.state.free_aus == pre.program.state.free_aus);
    assert(post.program.state.persistent_image == pre.program.state.persistent_image);
    assert(post.program.state.in_flight == pre.program.state.in_flight);
    assert(post.program.state.sync_req_map == pre.program.state.sync_req_map);
    assert(post.program.state.outstanding_cache_reqs == pre.program.state.outstanding_cache_reqs);

    assert(post.program.state.journal.wf());
    assert(post.program.state.branch.wf());
    assert(post.program.state.allocation_wf());
    assert(post.program.state.recovery_metadata_wf());
    assert(post.program.state.in_flight_agrees());
    assert(post.program.state.wf());

    assert(another_atomic_persistent_image_wf(post.program.state));
    assert(another_atomic_in_flight_wf(post.program.state));
    assert(another_atomic_branch_summary_wf(post.program.state));
    assert(another_atomic_persisted_branch_prefix_metadata_wf(post.program.state));
    assert(another_atomic_replay_progress_wf(post.program.state));
    assert(another_atomic_journal_mini_allocator_stage_wf(post.program.state));
    assert(another_atomic_sync_request_wf(post.program.state));
    assert(another_atomic_model_refinement_invariants(post.program.state));

    assert(another_atomic_superblock_write_request_wf(post.program.state, post.disk)) by {
        assert forall |id: ID| #![trigger post.disk.requests.contains_key(id)]
            post.disk.requests.contains_key(id)
            && post.disk.requests[id] is WriteReq
            && post.disk.requests[id]->to == spec_superblock_addr()
            implies {
                &&& post.program.state.client_ready()
                &&& post.program.state.in_flight is Some
                &&& post.program.state.in_flight.unwrap().req_id == id
                &&& post.disk.requests[id]->data
                    == marshal_abstract_superblock(post.program.state.atomic_inflight_superblock_i())
                &&& post.program.state.atomic_inflight_superblock_i().wf()
                &&& AtomicJournalState::State::next(
                    post.program.state.journal,
                    post.program.state.journal,
                    AtomicJournalState::Label::CommitPrepared,
                )
                &&& AtomicBranchState::State::next(
                    post.program.state.branch,
                    post.program.state.branch,
                    AtomicBranchState::Label::CommitPrepared,
                )
            }
        by {
            assert(pre.disk.requests.contains_key(id));
            assert(pre.disk.requests[id] == post.disk.requests[id]);
            assert(pre.program.state.in_flight == post.program.state.in_flight);
            assert(pre.program.state.journal.in_flight == post.program.state.journal.in_flight);
            assert(pre.program.state.branch.in_flight == post.program.state.branch.in_flight);
            assert(pre.program.state.atomic_inflight_superblock_i()
                == post.program.state.atomic_inflight_superblock_i());
            assert(another_atomic_superblock_write_request_wf(pre.program.state, pre.disk));
        }
    }

    assert(branch_component_refinement_inv(post)) by {
        assert(post.program.state.wf());
        assert(post.disk.inv());
        assert(async_disk_superblock_page_wf(post.disk.content));
        if crash_aware_caching_disk_branch_i(pre).ephemeral is Unknown {
            assert(crash_aware_caching_disk_branch_i(post) == crash_aware_caching_disk_branch_i(pre));
        } else {
            assert(branch_projection_addrs(post) =~= branch_projection_addrs(pre)) by {
                assert(branch_interpreted_summary_i(post) == branch_interpreted_summary_i(pre)) by {
                    assert(branch_raw_visible_i(post) =~= branch_raw_visible_i(pre));
                    assert(crate::implementation::CachingDiskBranch_v::to_branch_nodes(
                        branch_raw_visible_i(post),
                    ) == crate::implementation::CachingDiskBranch_v::to_branch_nodes(
                        branch_raw_visible_i(pre),
                    ));
                }
            }
            assert(branch_persistent_projection_addrs(post) =~= branch_persistent_projection_addrs(pre)) by {
                assert(branch_projection_addrs(post) =~= branch_projection_addrs(pre));
            }
            cache_internal_refines_caching_disk_internal_by_domains(
                pre.program.state.cache,
                post.program.state.cache,
                pre.disk,
                branch_projection_addrs(pre),
                branch_persistent_projection_addrs(pre),
            );
            assert(branch_projection_aus(post) =~= branch_projection_aus(pre)) by {
                assert(branch_interpreted_summary_i(post) == branch_interpreted_summary_i(pre));
            }
            let src = crash_aware_caching_disk_branch_i(pre);
            let dst = crash_aware_caching_disk_branch_i(post);
            assert(src.ephemeral is Known);
            assert(dst.ephemeral is Known);
            assert(src.ephemeral->v.disk == branch_caching_disk_i(pre));
            assert(dst.ephemeral->v.disk == branch_caching_disk_i(post));
            assert(crate::implementation::CachingDiskBranch_v::CachingDiskBranch::State::disk_internal(
                src.ephemeral->v,
                dst.ephemeral->v,
                crate::implementation::CachingDiskBranch_v::CachingDiskBranch::Label::Internal,
                dst.ephemeral->v.disk,
            )) by {
                reveal(crate::implementation::CachingDiskBranch_v::CachingDiskBranch::State::disk_internal);
            }
            assert(crate::implementation::CachingDiskBranch_v::CachingDiskBranch::State::next_by(
                src.ephemeral->v,
                dst.ephemeral->v,
                crate::implementation::CachingDiskBranch_v::CachingDiskBranch::Label::Internal,
                crate::implementation::CachingDiskBranch_v::CachingDiskBranch::Step::disk_internal(
                    dst.ephemeral->v.disk,
                ),
            )) by {
                reveal(crate::implementation::CachingDiskBranch_v::CachingDiskBranch::State::next_by);
            }
            reveal(crate::implementation::CachingDiskBranch_v::CachingDiskBranch::State::next);
            assert(CrashAwareCachingDiskBranch::State::next_by(
                src,
                dst,
                CrashAwareCachingDiskBranch::Label::Internal,
                CrashAwareCachingDiskBranch::Step::internal(dst.ephemeral->v),
            )) by {
                reveal(CrashAwareCachingDiskBranch::State::next_by);
            }
            reveal(CrashAwareCachingDiskBranch::State::next);
            CrashAwareCachingDiskBranch::State::inv_next(
                src,
                dst,
                CrashAwareCachingDiskBranch::Label::Internal,
            );
            assert(branch_caching_disk_state_i(post) == dst.ephemeral->v);
            assert(dst.ephemeral->v.active_branch_i().inv());
        }
        if crash_aware_caching_disk_branch_i(post).ephemeral is Known {
            assert(branch_caching_disk_state_i(post).active_branch_i().inv());
        }
    }

    assert(journal_component_refinement_inv(post)) by {
        assert(post.program.state.wf());
        assert(post.disk.inv());
        assert(async_disk_superblock_page_wf(post.disk.content));
        pre.program.state.cache.build_lookup_map_ensures();
        post.program.state.cache.build_lookup_map_ensures();
        assert(post.program.state.journal == pre.program.state.journal);
        assert(post.program.state.recovery_state == pre.program.state.recovery_state);
        assert(post.program.state.in_flight == pre.program.state.in_flight);
        assert(post.program.state.journal.in_flight == pre.program.state.journal.in_flight);
        assert(post.program.state.branch.in_flight == pre.program.state.branch.in_flight);
        assert(journal_projection_uses_live(post) == journal_projection_uses_live(pre));
        assert(journal_projection_addrs(post) =~= journal_projection_addrs(pre));
        if crash_aware_caching_disk_journal_i(pre).ephemeral is Unknown {
            assert(crash_aware_caching_disk_journal_i(post) == crash_aware_caching_disk_journal_i(pre));
        } else {
            assert(journal_persistent_projection_addrs(post) =~= journal_persistent_projection_addrs(pre)) by {
                assert forall |addr: Address| #[trigger] journal_persistent_projection_addrs(post).contains(addr)
                    <==> journal_persistent_projection_addrs(pre).contains(addr) by {
                    assert(journal_projection_addrs(post).contains(addr)
                        <==> journal_projection_addrs(pre).contains(addr));
                    let cache_step = choose |step: Cache::Step| Cache::State::next_by(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Internal{},
                        step,
                    );
                    match cache_step {
                        Cache::Step::reserve(new_slots_mapping) => {
                            assert(Cache::State::reserve(
                                pre.program.state.cache,
                                post.program.state.cache,
                                Cache::Label::Internal{},
                                new_slots_mapping,
                            ));
                            let updated_entries = Map::new(
                                |slot: Slot| new_slots_mapping.contains_key(slot),
                                |slot: Slot| Entry::Reserved{addr: new_slots_mapping[slot]},
                            );
                            assert(post.program.state.cache.entries
                                == pre.program.state.cache.entries.union_prefer_right(updated_entries));
                            assert(post.program.state.cache.status_map
                                == pre.program.state.cache.status_map);
                            if filled_cache_pages(post.program.state.cache).contains_key(addr) {
                                assert(cache_filled_addr(post.program.state.cache, addr));
                                let slot = post.program.state.cache.lookup_map[addr];
                                assert(post.program.state.cache.entries[slot] is Filled);
                                assert(!updated_entries.contains_key(slot)) by {
                                    if updated_entries.contains_key(slot) {
                                        assert(post.program.state.cache.entries[slot]
                                            == Entry::Reserved{addr: new_slots_mapping[slot]});
                                        assert(false);
                                    }
                                }
                                assert(post.program.state.cache.entries[slot]
                                    == pre.program.state.cache.entries[slot]);
                                assert(pre.program.state.cache.entries[slot] is Filled);
                                assert(pre.program.state.cache.lookup_map.contains_key(addr));
                                assert(pre.program.state.cache.lookup_map[addr] == slot) by {
                                    assert(pre.program.state.cache.build_lookup_map_props(
                                        pre.program.state.cache.lookup_map,
                                    ));
                                }
                                assert(cache_filled_addr(pre.program.state.cache, addr));
                            }
                            if filled_cache_pages(pre.program.state.cache).contains_key(addr) {
                                assert(cache_filled_addr(pre.program.state.cache, addr));
                                let slot = pre.program.state.cache.lookup_map[addr];
                                assert(pre.program.state.cache.entries[slot] is Filled);
                                assert(!new_slots_mapping.contains_key(slot)) by {
                                    if new_slots_mapping.contains_key(slot) {
                                        assert(pre.program.state.cache.valid_new_slots_mapping(
                                            new_slots_mapping,
                                        ));
                                        assert(pre.program.state.cache.entries[slot] is Empty);
                                        assert(false);
                                    }
                                }
                                assert(!updated_entries.contains_key(slot));
                                assert(post.program.state.cache.entries[slot]
                                    == pre.program.state.cache.entries[slot]);
                                assert(post.program.state.cache.lookup_map.contains_key(addr));
                                assert(post.program.state.cache.lookup_map[addr] == slot) by {
                                    assert(post.program.state.cache.build_lookup_map_props(
                                        post.program.state.cache.lookup_map,
                                    ));
                                }
                                assert(cache_filled_addr(post.program.state.cache, addr));
                            }
                            assert(filled_cache_pages(post.program.state.cache).contains_key(addr)
                                <==> filled_cache_pages(pre.program.state.cache).contains_key(addr));
                            if filled_cache_status(post.program.state.cache).contains_key(addr) {
                                assert(cache_filled_addr(post.program.state.cache, addr));
                                assert(cache_filled_addr(pre.program.state.cache, addr));
                                let slot = post.program.state.cache.lookup_map[addr];
                                assert(pre.program.state.cache.lookup_map[addr] == slot);
                                assert(post.program.state.cache.status_map[slot]
                                    == pre.program.state.cache.status_map[slot]);
                            }
                            if filled_cache_status(pre.program.state.cache).contains_key(addr) {
                                assert(cache_filled_addr(pre.program.state.cache, addr));
                                assert(cache_filled_addr(post.program.state.cache, addr));
                                let slot = pre.program.state.cache.lookup_map[addr];
                                assert(post.program.state.cache.lookup_map[addr] == slot);
                                assert(post.program.state.cache.status_map[slot]
                                    == pre.program.state.cache.status_map[slot]);
                            }
                            assert(filled_cache_status(post.program.state.cache).contains_key(addr)
                                <==> filled_cache_status(pre.program.state.cache).contains_key(addr));
                        },
                        Cache::Step::evict(evicted_slots) => {
                            assert(Cache::State::evict(
                                pre.program.state.cache,
                                post.program.state.cache,
                                Cache::Label::Internal{},
                                evicted_slots,
                            ));
                            let evicted_map = Map::new(
                                |slot: Slot| evicted_slots.contains(slot),
                                |slot: Slot| pre.program.state.cache.entries[slot].get_addr(),
                            );
                            let evicted_addrs = evicted_map.values();
                            assert(post.program.state.cache.lookup_map
                                == pre.program.state.cache.lookup_map.remove_keys(evicted_addrs));
                            if filled_cache_status(pre.program.state.cache).contains_key(addr)
                                && !filled_cache_status(post.program.state.cache).contains_key(addr) {
                                assert(cache_filled_addr(pre.program.state.cache, addr));
                                assert(!post.program.state.cache.lookup_map.contains_key(addr)) by {
                                    if post.program.state.cache.lookup_map.contains_key(addr) {
                                        assert(cache_filled_addr(post.program.state.cache, addr));
                                        assert(filled_cache_status(post.program.state.cache).contains_key(addr));
                                        assert(false);
                                    }
                                }
                                assert(evicted_addrs.contains(addr)) by {
                                    if !evicted_addrs.contains(addr) {
                                        assert(pre.program.state.cache.lookup_map.contains_key(addr));
                                        assert(post.program.state.cache.lookup_map.contains_key(addr));
                                        assert(false);
                                    }
                                }
                                cache_evicted_addr_lookup_slot(
                                    pre.program.state.cache,
                                    evicted_slots,
                                    addr,
                                );
                                let slot = pre.program.state.cache.lookup_map[addr];
                                assert(evicted_slots.contains(slot));
                                assert(pre.program.state.cache.entries[slot] is Filled);
                                assert(pre.program.state.cache.status_map[slot] is Clean);
                                assert(pre.program.state.cache.lookup_map.contains_key(addr));
                                assert(pre.program.state.cache.lookup_map[addr] == slot) by {
                                    assert(pre.program.state.cache.build_lookup_map_props(
                                        pre.program.state.cache.lookup_map,
                                    ));
                                }
                                assert(cache_filled_addr(pre.program.state.cache, addr));
                                assert(filled_cache_status(pre.program.state.cache)[addr]
                                    == CachingDiskPageStatus::Clean);
                                assert(another_atomic_cache_disk_coupling(pre.program.state, pre.disk));
                                assert(pre.disk.content.contains_key(addr));
                                assert(pre.disk.content[addr]
                                    == cache_filled_page(pre.program.state.cache, addr));
                            }
                        },
                        Cache::Step::noop() => {
                            assert(Cache::State::noop(
                                pre.program.state.cache,
                                post.program.state.cache,
                                Cache::Label::Internal{},
                            ));
                            assert(post.program.state.cache == pre.program.state.cache);
                        },
                        _ => {
                            assert(false);
                        },
                    }
                }
            }
            cache_internal_refines_caching_disk_internal_by_domains(
                pre.program.state.cache,
                post.program.state.cache,
                pre.disk,
                journal_projection_addrs(pre),
                journal_persistent_projection_addrs(pre),
            );
            let src = crash_aware_caching_disk_journal_i(pre);
            let dst = crash_aware_caching_disk_journal_i(post);
            assert(src.ephemeral is Known);
            assert(dst.ephemeral is Known);
            assert(src.ephemeral->v.disk == journal_caching_disk_i(pre));
            assert(dst.ephemeral->v.disk == journal_caching_disk_i(post));
            assert(CachingDiskJournal::State::caching_disk_internal(
                src.ephemeral->v,
                dst.ephemeral->v,
                CachingDiskJournal::Label::Internal,
                dst.ephemeral->v.disk,
            )) by {
                reveal(CachingDiskJournal::State::caching_disk_internal);
            }
            assert(CachingDiskJournal::State::next_by(
                src.ephemeral->v,
                dst.ephemeral->v,
                CachingDiskJournal::Label::Internal,
                CachingDiskJournal::Step::caching_disk_internal(dst.ephemeral->v.disk),
            )) by {
                reveal(CachingDiskJournal::State::next_by);
            }
            reveal(CachingDiskJournal::State::next);
            assert(CrashAwareCachingDiskJournal::State::next_by(
                src,
                dst,
                CrashAwareCachingDiskJournal::Label::Internal,
                CrashAwareCachingDiskJournal::Step::internal(dst.ephemeral->v),
            )) by {
                reveal(CrashAwareCachingDiskJournal::State::next_by);
            }
            reveal(CrashAwareCachingDiskJournal::State::next);
            CrashAwareCachingDiskJournal::State::inv_next(
                src,
                dst,
                CrashAwareCachingDiskJournal::Label::Internal,
            );
        }
    }

    assert(another_atomic_disk_refinement_invariants(post));
}

pub proof fn program_internal_journal_load_index_preserves_journal_component(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    reads: Map<Address, RawPage>,
    discovered_aus: Set<AU>,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        AnotherAtomicState::journal_load_index(
            pre.program.state,
            post.program.state,
            reads,
            discovered_aus,
        ),
        post.disk == pre.disk,
    ensures
        journal_component_refinement_inv(post),
{
    AnotherAtomicState::journal_load_index_effect(
        pre.program.state,
        post.program.state,
        reads,
        discovered_aus,
    );
    journal_load_index_discovered_aus_subset_projection(pre, post, reads, discovered_aus);
    CachedJournal::State::load_index_effect(
        pre.program.state.journal.journal,
        post.program.state.journal.journal,
        to_journal_records(reads),
        discovered_aus,
    );
    assert(pre.program.state.recovery_state is SuperblockAvailable);
    assert(!pre.program.state.journal_metadata_loaded());
    assert(post.program.state.journal_metadata_loaded());
    assert(post.program.state.journal.loaded_index_aus() == discovered_aus);
    assert(post.program.state.journal.mini_allocator == pre.program.state.journal.mini_allocator);
    assert(pre.program.state.journal.mini_allocator
        == crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty());
    assert(post.program.state.journal.mini_allocator
        == crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty());
    AtomicJournalState::State::wf_next(
        pre.program.state.journal,
        post.program.state.journal,
        AtomicJournalState::Label::LoadIndex{
            reads: to_journal_records(reads),
            discovered_aus,
        },
    );
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
    assert(post.program.state.journal_owned_aus() == discovered_aus) by {
        assert(post.program.state.journal.owned_aus()
            == post.program.state.journal.loaded_index_aus()
                + post.program.state.journal.mini_allocator.all_aus());
        assert(post.program.state.journal.mini_allocator.all_aus() == Set::<AU>::empty());
    }
    assert(post.program.state.branch == pre.program.state.branch);
    assert(post.program.state.in_flight == pre.program.state.in_flight);
    assert(post.program.state.sync_req_map == pre.program.state.sync_req_map);
    assert(post.program.state.outstanding_cache_reqs
        == pre.program.state.outstanding_cache_reqs);
    assert(post.program.state.persistent_image == pre.program.state.persistent_image);
    assert(post.program.state.recovery_metadata_wf());
    assert(post.program.state.component_disjoint()) by {
        assert(journal_projected_aus_are_component_data(pre));
        assert(discovered_aus <= journal_projection_aus(pre));
        assert(AnotherAtomicState::reserved_aus().disjoint(journal_projection_aus(pre)));
        assert(pre.program.state.branch_owned_aus().disjoint(journal_projection_aus(pre)));
        assert(post.program.state.branch_owned_aus() == pre.program.state.branch_owned_aus());
    }
    assert(post.program.state.free_aus.disjoint(post.program.state.component_owned_aus())) by {
        assert(pre.program.state.allocation_wf());
        assert(post.program.state.free_aus == pre.program.state.free_aus - discovered_aus);
        assert(post.program.state.branch_owned_aus() == pre.program.state.branch_owned_aus());
        assert(post.program.state.component_owned_aus()
            == AnotherAtomicState::reserved_aus() + discovered_aus + pre.program.state.branch_owned_aus());
        assert forall |au: AU| #[trigger] post.program.state.free_aus.contains(au)
            implies !post.program.state.component_owned_aus().contains(au) by {
            assert(pre.program.state.free_aus.contains(au));
            assert(!discovered_aus.contains(au));
            if AnotherAtomicState::reserved_aus().contains(au) {
                assert(pre.program.state.component_owned_aus().contains(au));
                assert(false);
            }
            if pre.program.state.branch_owned_aus().contains(au) {
                assert(pre.program.state.component_owned_aus().contains(au));
                assert(false);
            }
        }
    }
    assert(post.program.state.allocation_wf());
    assert(post.program.state.wf());
    assert(journal_projection_aus(post) =~= journal_projection_aus(pre)) by {
        assert(post.program.state.recovery_state == pre.program.state.recovery_state);
        assert(post.program.state.persistent_image == pre.program.state.persistent_image);
        assert(post.program.state.journal.journal.snapshot
            == pre.program.state.journal.journal.snapshot);
        assert(post.disk == pre.disk);
    }
    filled_cache_read_only_access_unchanged(
        pre.program.state.cache,
        post.program.state.cache,
        reads,
    );
    assert(journal_projection_addrs(post) =~= journal_projection_addrs(pre)) by {
        assert forall |addr: Address| #[trigger] journal_projection_addrs(post).contains(addr)
            <==> journal_projection_addrs(pre).contains(addr) by {
        }
    }
    assert(journal_persistent_projection_addrs(post)
        =~= journal_persistent_projection_addrs(pre)) by {
        assert forall |addr: Address| #[trigger] journal_persistent_projection_addrs(post).contains(addr)
            <==> journal_persistent_projection_addrs(pre).contains(addr) by {
            assert(journal_projection_addrs(post).contains(addr)
                <==> journal_projection_addrs(pre).contains(addr));
            assert(filled_cache_pages(post.program.state.cache).contains_key(addr)
                <==> filled_cache_pages(pre.program.state.cache).contains_key(addr));
            assert(filled_cache_status(post.program.state.cache).contains_key(addr)
                <==> filled_cache_status(pre.program.state.cache).contains_key(addr));
        }
    }
    assert(journal_caching_disk_i(post) == journal_caching_disk_i(pre));
    {
        let src = crash_aware_caching_disk_journal_i(pre);
        let dst = crash_aware_caching_disk_journal_i(post);
        let cj_lbl = CachedJournal::Label::LoadIndex{
            reads: to_journal_records(reads),
            discovered_aus,
        };
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let step = choose |step: CachedJournal::Step| CachedJournal::State::next_by(
            pre.program.state.journal.journal,
            post.program.state.journal.journal,
            cj_lbl,
            step,
        );
        match step {
            CachedJournal::Step::load_index(au_depth, page_depth) => {
                let ptr = pre.program.state.journal.journal.snapshot.freshest_rec();
                let bdy = pre.program.state.journal.journal.snapshot.boundary_lsn;
                let first = pre.program.state.journal.journal.snapshot.first();
                let read_records = to_journal_records(reads);
                let visible_records = dst.ephemeral->v.journal_disk_view().entries;
                assert(dst.ephemeral is Known);
                assert(src.ephemeral is Known);
                assert(dst.ephemeral->v.disk == src.ephemeral->v.disk);
                assert(dst.ephemeral->v.journal.snapshot == src.ephemeral->v.journal.snapshot);
                assert(dst.ephemeral->v.journal_tj().disk_view == src.ephemeral->v.journal_tj().disk_view);
                assert(src.ephemeral->v.visible_journal_structure());
                assert(dst.ephemeral->v.visible_journal_structure());
                assert(au_walk_reads_cover(read_records, bdy, ptr, first, au_depth, page_depth));
                assert forall |addr: Address| #[trigger] read_records.contains_key(addr)
                    && visible_records.contains_key(addr) implies read_records[addr] == visible_records[addr] by {
                    assert(reads.contains_key(addr));
                    assert(Cache::State::next(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Access{reads, writes: Map::empty()},
                    ));
                    Cache::State::access_read_valid(
                        pre.program.state.cache,
                        post.program.state.cache,
                        reads,
                        Map::empty(),
                        addr,
                    );
                    assert(pre.program.state.cache.valid_read(addr, reads[addr]));
                    assert(pre.program.state.cache.inv());
                    pre.program.state.cache.build_lookup_map_ensures();
                    assert(cache_filled_addr(pre.program.state.cache, addr));
                    assert(filled_cache_pages(pre.program.state.cache).contains_key(addr));
                    assert(filled_cache_pages(pre.program.state.cache)[addr] == reads[addr]);
                    assert(journal_projection_addrs(pre).contains(addr)) by {
                        assert(visible_records.contains_key(addr));
                        assert(dst.ephemeral->v.disk.visible().contains_key(addr));
                        if !journal_projection_addrs(pre).contains(addr) {
                            assert(!journal_disk_cache_i(pre).contains_key(addr));
                            assert(!journal_disk_persistent_i(pre).contains_key(addr));
                            assert(!src.ephemeral->v.disk.cache.contains_key(addr));
                            assert(!src.ephemeral->v.disk.persistent.contains_key(addr));
                            assert(!src.ephemeral->v.disk.visible().contains_key(addr));
                            assert(false);
                        }
                    }
                    assert(journal_disk_cache_i(pre).contains_key(addr));
                    assert(src.ephemeral->v.disk.cache.contains_key(addr));
                    assert(src.ephemeral->v.disk.cache[addr] == reads[addr]);
                    assert(src.ephemeral->v.disk.visible()[addr] == reads[addr]);
                    assert(dst.ephemeral->v.disk.visible()[addr] == reads[addr]);
                }
                au_walk_reads_cover_build_matches_full_by_value(
                    read_records,
                    visible_records,
                    bdy,
                    ptr,
                    first,
                    au_depth,
                    page_depth,
                );
                assert(crate::implementation::CachingDiskJournal_v::cj_lsn_au_index(
                    dst.ephemeral->v.journal,
                ) == dst.ephemeral->v.journal_tj().build_lsn_au_index_from_first(first));
                if ptr is Some {
                    let root = ptr.unwrap();
                    assert(read_records.contains_key(root));
                    assert(visible_records.contains_key(root));
                    assert(read_records[root] == visible_records[root]);
                    assert(dst.ephemeral->v.journal_tj().seq_end()
                        == visible_records[root].message_seq.seq_end);
                } else {
                    assert(dst.ephemeral->v.journal_tj().seq_end() == bdy);
                }
                assert(dst.ephemeral->v.journal_tj().seq_end()
                    == crate::implementation::CachingDiskJournal_v::cj_unmarshalled_tail(
                        dst.ephemeral->v.journal,
                    ).seq_start);
                assert(dst.ephemeral->v.loaded_journal_structure());
            },
            _ => { assert(false); },
        }
    }
    assert(journal_projection_tight(post));
    assert(journal_projection_uses_shared_async_disk(post));
    assert(persistent_journal_image_i(post) == persistent_journal_image_i(pre));
    assert(persistent_journal_image_i(post).wf());
    assert(crash_aware_caching_disk_journal_i(post).inv());
}

pub proof fn metadata_load_complete_preserves_refinement_invariants(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        AnotherAtomicState::metadata_load_complete(pre.program.state, post.program.state),
        post.disk == pre.disk,
    ensures
        another_atomic_disk_refinement_invariants(post),
{
    assert(post.program.state.cache == pre.program.state.cache);
    assert(post.program.state.free_aus == pre.program.state.free_aus);
    assert(post.program.state.journal == pre.program.state.journal);
    assert(post.program.state.branch == pre.program.state.branch);
    assert(post.program.state.outstanding_cache_reqs
        == pre.program.state.outstanding_cache_reqs);
    assert(post.program.state.persistent_image == pre.program.state.persistent_image);
    assert(post.program.state.sync_req_map == pre.program.state.sync_req_map);
    AnotherAtomicState::cache_request_wf_preserved_by_unchanged(
        pre.program.state,
        post.program.state,
    );
    cache_disk_request_wf_preserved_by_unchanged(
        pre.program.state,
        post.program.state,
        post.disk,
    );
    assert(post.program.state.journal_metadata_loaded()
        == pre.program.state.journal_metadata_loaded());
    assert(post.program.state.in_flight == pre.program.state.in_flight);
    assert(post.program.state.journal.in_flight
        == pre.program.state.journal.in_flight);
    assert(post.program.state.branch.in_flight
        == pre.program.state.branch.in_flight);
    assert(post.program.state.journal_metadata_loaded());
    assert(post.program.state.branch_metadata_loaded());
    assert(post.program.state.branch.seq_end() <= post.program.state.journal.journal.seq_end()) by {
        assert(pre.program.state.recovery_metadata_wf());
        assert(another_atomic_recovery_image_seq_wf(pre.program.state));
        let image = pre.program.state.persistent_image.unwrap();
        assert(image.wf());
        assert(pre.program.state.branch.seq_end() == image.branch_seq_end);
        assert(pre.program.state.journal.journal.seq_end() == image.journal_seq_end);
        assert(image.branch_seq_end == image.journal_snapshot.boundary_lsn);
        assert(image.journal_snapshot.boundary_lsn <= image.journal_seq_end);
    }
    assert(post.program.state.recovery_metadata_wf());
    assert(post.program.state.allocation_wf());
    assert(post.program.state.in_flight_agrees());
    assert(post.program.state.wf());
    assert(another_atomic_persistent_image_wf(post.program.state));
    assert(another_atomic_in_flight_wf(post.program.state));
    assert(another_atomic_branch_summary_wf(post.program.state));
    assert(another_atomic_persisted_branch_prefix_metadata_wf(post.program.state));
    assert(another_atomic_replay_progress_wf(post.program.state));
    assert(another_atomic_recovery_image_seq_wf(post.program.state));
    assert(another_atomic_journal_mini_allocator_stage_wf(post.program.state));
    assert(another_atomic_sync_request_wf(post.program.state));
    assert(another_atomic_model_refinement_invariants(post.program.state));
    assert forall |addr: Address|
        #[trigger] post.program.state.journal.mini_allocator.can_allocate(addr)
        implies pre.program.state.journal.mini_allocator.can_allocate(addr) by {
        assert(post.program.state.journal.mini_allocator
            == pre.program.state.journal.mini_allocator);
    }
    journal_image_writeback_disjoint_preserved_by_unchanged_cache_disk_images(
        pre,
        post,
    );
    persistent_journal_image_projection_domain_materialized(post);
    let post_journal = crash_aware_caching_disk_journal_i(post).ephemeral->v;
    post_journal.journal_disk_aus_match_index_values();
    assert(post_journal.accessible_aus() == post.program.state.journal_owned_aus()) by {
        assert(post_journal.lsn_au_index_or_empty()
            == post.program.state.journal.journal.status.unwrap().lsn_au_index);
        assert(post_journal.mini_allocator == post.program.state.journal.mini_allocator);
    }
    assert(to_aus(journal_projection_addrs(post)) <= post.program.state.journal_owned_aus()) by {
        assert(post.program.state.journal.mini_allocator
            == crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty());
        assert(mini_allocator_allocated_addrs(post.program.state.journal.mini_allocator)
            =~= Set::<Address>::empty()) by {
            assert forall |addr: Address| #[trigger] mini_allocator_allocated_addrs(
                post.program.state.journal.mini_allocator,
            ).contains(addr) implies false by {
            }
        }
        assert(journal_projection_addrs(post)
            =~= post_journal.journal_disk_view().entries.dom()) by {
            assert forall |addr: Address| #[trigger] journal_projection_addrs(post).contains(addr)
                <==> post_journal.journal_disk_view().entries.dom().contains(addr) by {
                if journal_projection_addrs(post).contains(addr) {
                    assert(live_journal_projection_addrs(post).contains(addr));
                    assert(snapshot_walk_domain(
                        to_journal_records(post.disk.content),
                        post.program.state.journal.journal.snapshot.boundary_lsn,
                        post.program.state.journal.journal.snapshot.freshest_rec(),
                    ).contains(addr));
                    if filled_cache_pages(post.program.state.cache).contains_key(addr) {
                        assert(cache_filled_addr(post.program.state.cache, addr));
                        assert(journal_disk_cache_i(post).contains_key(addr));
                        assert(journal_caching_disk_i(post).cache.contains_key(addr));
                    } else {
                        assert(!filled_cache_status(post.program.state.cache).contains_key(addr));
                        assert(post.disk.content.contains_key(addr)) by {
                            assert(journal_image_projection_domain_i(
                                post,
                                durable_superblock_image_i(post),
                            ).contains(addr));
                        }
                        assert(journal_persistent_projection_addrs(post).contains(addr));
                        assert(journal_disk_persistent_i(post).contains_key(addr));
                        assert(journal_caching_disk_i(post).persistent.contains_key(addr));
                    }
                    assert(journal_caching_disk_i(post).visible().contains_key(addr));
                    assert(post_journal.journal_disk_view().entries.contains_key(addr));
                }
                if post_journal.journal_disk_view().entries.dom().contains(addr) {
                    assert(post_journal.journal_disk_view().entries.contains_key(addr));
                    assert(journal_caching_disk_i(post).visible().contains_key(addr));
                    assert(journal_projection_addrs(post).contains(addr));
                }
            }
        }
        assert(to_aus(journal_projection_addrs(post))
            =~= to_aus(post_journal.journal_disk_view().entries.dom()));
        assert(to_aus(post_journal.journal_disk_view().entries.dom())
            <= post_journal.accessible_aus());
    }
    assert(journal_projection_aus(post) <= post.program.state.journal_owned_aus()) by {
        assert(to_aus(journal_projection_addrs(post)) <= post.program.state.journal_owned_aus());
        assert forall |au: AU| #[trigger] to_aus(journal_projection_addrs(post)).contains(au)
            implies post.program.state.journal_owned_aus().contains(au) by {
        }
        assert(post.program.state.journal.loaded_index_aus()
            <= post.program.state.journal_owned_aus());
        assert(post.program.state.journal.mini_allocator.all_aus()
            <= post.program.state.journal_owned_aus());
    }
    assert(to_aus(journal_projection_addrs(post)) <= post.program.state.journal_owned_aus()) by {
        assert(journal_projection_aus(post) <= post.program.state.journal_owned_aus());
    }
    assert(journal_loaded_index_matches_persistent_subdisk(post)) by {
        assert(journal_loaded_index_matches_persistent_subdisk(pre));
        assert(persistent_journal_image_i(post) == persistent_journal_image_i(pre));
        assert(post.program.state.journal == pre.program.state.journal);
    }
    assert(journal_index_aus_have_unique_lsns(post)) by {
        assert(journal_index_aus_have_unique_lsns(pre));
        let journal = post.program.state.journal.journal;
        let snapshot = journal.snapshot;
        let disk_view = DiskView{
            boundary_lsn: snapshot.boundary_lsn,
            entries: to_journal_records(post.disk.content),
        };
        let index = journal.status.unwrap().lsn_au_index;
        assert forall |addr1: Address, addr2: Address, lsn: LSN|
            #![trigger
                disk_view.entries[addr1].contains_lsn(snapshot.boundary_lsn, lsn),
                disk_view.entries[addr2].contains_lsn(snapshot.boundary_lsn, lsn)
            ]
            {
                &&& disk_view.entries.contains_key(addr1)
                &&& disk_view.entries.contains_key(addr2)
                &&& index.values().contains(addr1.au)
                &&& index.values().contains(addr2.au)
                &&& disk_view.entries[addr1].contains_lsn(snapshot.boundary_lsn, lsn)
                &&& disk_view.entries[addr2].contains_lsn(snapshot.boundary_lsn, lsn)
            } implies addr1 == addr2 by {
            assert(post.program.state.journal == pre.program.state.journal);
            assert(post.disk == pre.disk);
            assert(post.program.state.journal_metadata_loaded()
                == pre.program.state.journal_metadata_loaded());
        }
    }
    journal_unique_index_aus_imply_no_impersonation(post);
    assert(journal_component_refinement_inv(post));
    atomic_branch_metadata_loaded_flag_from_metadata_loaded(pre.program.state.branch);
    atomic_branch_metadata_loaded_flag_from_metadata_loaded(post.program.state.branch);
    loaded_branch_projection_unchanged(pre, post);
    assert(crash_aware_caching_disk_branch_i(post)
        == crash_aware_caching_disk_branch_i(pre));
    assert(branch_component_refinement_inv(post));
    assert(another_atomic_cache_disk_coupling(post.program.state, post.disk));
    assert(another_atomic_superblock_disk_coupling(post.program.state, post.disk));
    assert(another_atomic_superblock_write_request_wf(post.program.state, post.disk));
    assert(another_atomic_cache_disk_request_wf(post.program.state, post.disk));
    assert(journal_image_writeback_disjoint(post));
    assert(another_atomic_disk_refinement_invariants(post));
}

pub proof fn branch_split_write_projection_facts(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    new_child_addr: Address,
    receipt: crate::implementation::CachedBranch_v::LoadedPathReceipt,
    split_arg: crate::betree::LinkedBranch_v::SplitArg,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    branch: AtomicBranchState::State,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        AnotherAtomicState::branch_split(
            pre.program.state,
            post.program.state,
            new_child_addr,
            receipt,
            split_arg,
            reads,
            writes,
            branch,
        ),
    ensures
        to_aus(writes.dom()) <= pre.program.state.branch_owned_aus(),
        writes.dom() <= addresses_in_aus(branch_projection_aus(pre)),
{
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
    assert(linked.disk_view.is_fresh(set![new_child_addr])) by {
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
    assert(write_nodes == loaded_split_write_nodes(
        receipt,
        read_nodes,
        split_arg,
        new_child_addr,
    ));
    assert(write_nodes.dom() =~= set![parent_addr, child_addr, new_child_addr]) by {
        assert_maps_equal!(
            write_nodes,
            map! {
                parent_addr => write_nodes[parent_addr],
                child_addr => write_nodes[child_addr],
                new_child_addr => write_nodes[new_child_addr],
            },
            a => { }
        );
    }
    assert(set![parent_addr.au, child_addr.au, new_child_addr.au]
        <= pre.program.state.branch_owned_aus()) by {
        assert(pre.program.state.branch.mini_allocator.can_allocate(new_child_addr));
        assert(pre.program.state.branch.mini_allocator.all_aus().contains(new_child_addr.au));
        assert(active_i.addrs_closed_under_mini_allocator());
        assert(active_i.mini_allocator.page_is_reserved(parent_addr));
        assert(active_i.mini_allocator.page_is_reserved(child_addr));
        assert(pre.program.state.branch.mini_allocator.all_aus().contains(parent_addr.au));
        assert(pre.program.state.branch.mini_allocator.all_aus().contains(child_addr.au));
    }
    assert(to_aus(writes.dom()) <= pre.program.state.branch_owned_aus()) by {
        assert(writes.dom() =~= write_nodes.dom());
        assert(writes.dom() =~= set![parent_addr, child_addr, new_child_addr]);
        let write_addrs = set![parent_addr] + set![child_addr] + set![new_child_addr];
        assert(writes.dom() =~= write_addrs);
        crate::disk::GenericDisk_v::to_aus_singleton(parent_addr);
        crate::disk::GenericDisk_v::to_aus_singleton(child_addr);
        crate::disk::GenericDisk_v::to_aus_singleton(new_child_addr);
        crate::disk::GenericDisk_v::to_aus_additive(set![parent_addr], set![child_addr]);
        crate::disk::GenericDisk_v::to_aus_additive(
            set![parent_addr] + set![child_addr],
            set![new_child_addr],
        );
        assert(to_aus(writes.dom())
            == set![parent_addr.au] + set![child_addr.au] + set![new_child_addr.au]);
        assert forall |au: AU| #[trigger] to_aus(writes.dom()).contains(au)
            implies pre.program.state.branch_owned_aus().contains(au) by {
            assert((set![parent_addr.au] + set![child_addr.au] + set![new_child_addr.au]).contains(au));
        }
    }
    client_ready_implies_atomic_branch_metadata_loaded_flag(pre.program.state);
    assert(branch_projection_aus(pre) == pre.program.state.branch_owned_aus());
    assert(writes.dom() <= addresses_in_aus(branch_projection_aus(pre))) by {
        to_aus_domain(writes.dom());
        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
            implies addresses_in_aus(branch_projection_aus(pre)).contains(addr) by {
            assert(to_aus(writes.dom()).contains(addr.au));
            assert(pre.program.state.branch_owned_aus().contains(addr.au));
            assert(branch_projection_aus(pre).contains(addr.au));
        }
    }
}

pub proof fn branch_grow_write_projection_facts(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    new_root_addr: Address,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    branch: AtomicBranchState::State,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        AnotherAtomicState::branch_grow(
            pre.program.state,
            post.program.state,
            new_root_addr,
            reads,
            writes,
            branch,
        ),
    ensures
        to_aus(writes.dom()) <= pre.program.state.branch_owned_aus(),
        post.program.state.branch == branch,
        post.program.state.journal == pre.program.state.journal,
        post.program.state.in_flight == pre.program.state.in_flight,
        post.program.state.journal.in_flight == pre.program.state.journal.in_flight,
        post.program.state.branch.in_flight == pre.program.state.branch.in_flight,
        post.program.state.branch.persisted_root_count
            == pre.program.state.branch.persisted_root_count,
        post.program.state.branch.wf(),
        post.program.state.branch_owned_aus() <= pre.program.state.branch_owned_aus(),
        post.program.state.branch_metadata_loaded(),
        post.program.state.recovery_metadata_wf(),
{
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
}

pub proof fn branch_seal_write_projection_facts(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    aux_ptr: Option<Address>,
    summary: Summary,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    branch: AtomicBranchState::State,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        AnotherAtomicState::branch_seal(
            pre.program.state,
            post.program.state,
            aux_ptr,
            summary,
            reads,
            writes,
            branch,
        ),
    ensures
        to_aus(writes.dom()) <= pre.program.state.branch_owned_aus(),
        post.program.state.branch == branch,
        post.program.state.journal == pre.program.state.journal,
        post.program.state.in_flight == pre.program.state.in_flight,
        post.program.state.journal.in_flight == pre.program.state.journal.in_flight,
        post.program.state.branch.in_flight == pre.program.state.branch.in_flight,
        post.program.state.branch.persisted_root_count
            == pre.program.state.branch.persisted_root_count,
        post.program.state.branch.wf(),
        post.program.state.branch_owned_aus() <= pre.program.state.branch_owned_aus(),
        post.program.state.branch_metadata_loaded(),
        post.program.state.recovery_metadata_wf(),
{
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
            assert(branch.persisted_root_count
                == pre.program.state.branch.persisted_root_count);
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
    AtomicBranchState::State::wf_next(
        pre.program.state.branch,
        branch,
        branch_lbl,
    );
    assert(post.program.state.branch == branch);
    assert(post.program.state.journal == pre.program.state.journal);
    assert(post.program.state.in_flight == pre.program.state.in_flight);
    assert(post.program.state.journal.in_flight == pre.program.state.journal.in_flight);
    assert(post.program.state.branch.in_flight == branch.in_flight);
    assert(branch.in_flight == pre.program.state.branch.in_flight);
    pre.program.state.branch.mini_allocator.prune_preserves_wf(summary);
    assert(branch.mini_allocator.all_aus()
        == pre.program.state.branch.mini_allocator.all_aus().difference(summary));
    assert(summary <= pre.program.state.branch.mini_allocator.all_aus()) by {
        assert(summary == pre.program.state.branch.mini_allocator.reserved_aus());
        assert forall |au: AU| #[trigger] summary.contains(au)
            implies pre.program.state.branch.mini_allocator.all_aus().contains(au) by {
            assert(pre.program.state.branch.mini_allocator.reserved_aus().contains(au));
            assert(pre.program.state.branch.mini_allocator.allocs.contains_key(au));
        }
    }
    assert(summary_aus(branch.branch_summary)
        <= summary_aus(pre.program.state.branch.branch_summary) + summary) by {
        assert(branch.branch_summary
            == pre.program.state.branch.branch_summary.insert(
                pre.program.state.branch.active_branch.root.unwrap().au,
                summary,
            ));
        lemma_values_finite(branch.branch_summary);
        assert forall |au: AU| #[trigger] summary_aus(branch.branch_summary).contains(au)
            implies (summary_aus(pre.program.state.branch.branch_summary) + summary).contains(au) by {
            let found_summary = lemma_union_set_of_sets_contains(branch.branch_summary.values(), au);
            assert(branch.branch_summary.values().contains(found_summary));
            let root_au = pre.program.state.branch.active_branch.root.unwrap().au;
            if found_summary == summary {
                assert(summary.contains(au));
            } else {
                assert(pre.program.state.branch.branch_summary.values().contains(found_summary)) by {
                    if !pre.program.state.branch.branch_summary.values().contains(found_summary) {
                        assert(branch.branch_summary == pre.program.state.branch.branch_summary.insert(root_au, summary));
                        assert(branch.branch_summary.contains_key(root_au));
                        assert(branch.branch_summary[root_au] == summary);
                        assert(found_summary == summary);
                        assert(false);
                    }
                }
                assert(pre.program.state.branch.branch_summary.values().contains(found_summary));
                assert(found_summary.contains(au));
                lemma_values_finite(pre.program.state.branch.branch_summary);
                lemma_union_set_of_sets_subset(
                    pre.program.state.branch.branch_summary.values(),
                    found_summary,
                );
                assert(union_set_of_sets(pre.program.state.branch.branch_summary.values()).contains(au));
                assert(summary_aus(pre.program.state.branch.branch_summary).contains(au));
            }
        }
    }
    assert(post.program.state.branch_owned_aus() <= pre.program.state.branch_owned_aus()) by {
        assert forall |au: AU| #[trigger] post.program.state.branch_owned_aus().contains(au)
            implies pre.program.state.branch_owned_aus().contains(au) by {
            if summary_aus(branch.branch_summary).contains(au) {
                if summary_aus(pre.program.state.branch.branch_summary).contains(au) {
                } else {
                    assert(summary.contains(au));
                    assert(pre.program.state.branch.mini_allocator.all_aus().contains(au));
                }
            } else {
                assert(branch.mini_allocator.all_aus().contains(au));
                assert(pre.program.state.branch.mini_allocator.all_aus().contains(au));
            }
        }
    }
    assert(post.program.state.branch_metadata_loaded()) by {
        assert(pre.program.state.client_ready());
        assert(pre.program.state.recovery_state is RecoveryComplete);
        assert(pre.program.state.recovery_metadata_wf());
        assert(pre.program.state.branch_metadata_loaded());
        let root = pre.program.state.branch.active_branch.root.unwrap();
        assert(branch.image.sealed_roots == pre.program.state.branch.image.sealed_roots.push(root));
        assert(branch.branch_summary == pre.program.state.branch.branch_summary.insert(root.au, summary));
        assert forall |i: int| #![trigger branch.image.sealed_roots[i]]
            0 <= i < branch.image.sealed_roots.len()
            implies branch.branch_summary.contains_key(branch.image.sealed_roots[i].au) by {
            if i == pre.program.state.branch.image.sealed_roots.len() {
                assert(branch.image.sealed_roots[i] == root);
                assert(branch.branch_summary.contains_key(root.au));
            } else {
                assert(0 <= i < pre.program.state.branch.image.sealed_roots.len());
                assert(branch.image.sealed_roots[i]
                    == pre.program.state.branch.image.sealed_roots[i]);
                assert(pre.program.state.branch.branch_summary.contains_key(
                    pre.program.state.branch.image.sealed_roots[i].au,
                ));
                assert(branch.branch_summary.contains_key(branch.image.sealed_roots[i].au));
            }
        }
    }
    assert(post.program.state.recovery_metadata_wf()) by {
        assert(post.program.state.recovery_state == pre.program.state.recovery_state);
        assert(pre.program.state.recovery_metadata_wf());
        assert(post.program.state.superblock_metadata_known());
        assert(post.program.state.journal_metadata_loaded());
        assert(post.program.state.branch_metadata_loaded());
        assert(post.program.state.journal.journal.seq_end()
            == pre.program.state.journal.journal.seq_end());
        assert(post.program.state.branch.seq_end() == pre.program.state.branch.seq_end());
        assert(pre.program.state.recovery_state is RecoveryComplete);
    }
    assert(writes.dom() =~= write_nodes.dom());
    assert(to_aus(writes.dom()) <= pre.program.state.branch_owned_aus());
}

pub proof fn branch_read_node_matches_visible_after_read_only_access(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    reads: Map<Address, RawPage>,
    addr: Address,
)
    requires
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads, writes: Map::empty()},
        ),
        post.disk == pre.disk,
        reads.contains_key(addr),
    ensures
        branch_visible_nodes_i(post).contains_key(addr),
        crate::implementation::AnotherAtomicState_v::to_branch_nodes(reads)[addr]
            == branch_visible_nodes_i(post)[addr],
{
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    assert(Cache::State::next_by(
        pre.program.state.cache,
        post.program.state.cache,
        Cache::Label::Access{reads, writes: Map::empty()},
        Cache::Step::access(),
    ));
    assert(Cache::State::access(
        pre.program.state.cache,
        post.program.state.cache,
        Cache::Label::Access{reads, writes: Map::empty()},
    )) by {
        reveal(Cache::State::access);
    }
    assert(pre.program.state.cache.valid_read(addr, reads[addr]));
    assert(cache_filled_addr(pre.program.state.cache, addr)) by {
        assert(pre.program.state.cache.lookup_map.contains_key(addr));
        assert(pre.program.state.cache.entries[
            pre.program.state.cache.lookup_map[addr]
        ] is Filled);
    }
    assert(filled_cache_pages(pre.program.state.cache).contains_key(addr));
    assert(filled_cache_pages(pre.program.state.cache)[addr] == reads[addr]);
    filled_cache_read_only_access_unchanged(
        pre.program.state.cache,
        post.program.state.cache,
        reads,
    );
    assert(filled_cache_pages(post.program.state.cache).contains_key(addr));
    assert(filled_cache_pages(post.program.state.cache)[addr] == reads[addr]);
    assert(branch_raw_visible_i(post).contains_key(addr));
    assert(branch_raw_visible_i(post)[addr] == reads[addr]);
    assert(branch_visible_nodes_i(post).contains_key(addr));
}

pub proof fn visible_root_summary_subset_branch_projection(
    model: SystemModel::State<AnotherProgramModel>,
    root: Address,
)
    requires
        branch_loaded_metadata_agrees_with_visible(model),
        model.program.state.superblock_metadata_known(),
        set_addrs_disjoint_aus(model.program.state.branch.image.sealed_roots.to_set()),
        model.program.state.branch.image.sealed_roots.to_set().contains(root),
    ensures
        root_summary_from_read(root, branch_visible_nodes_i(model)) <= branch_projection_aus(model),
{
    let roots = model.program.state.branch.image.sealed_roots;
    let nodes = branch_visible_nodes_i(model);
    let summary = root_summary_from_read(root, nodes);
    assert(CachingDiskBranchModule::branch_summary_reads_valid(roots, nodes));
    let idx = choose |i: int| 0 <= i < roots.len() && roots[i] == root;
    CachingDiskBranchModule::root_aus_up_to_contains(
        roots,
        roots.len() as nat,
        idx,
    );
    to_aus_finite(roots.to_set());
    CachingDiskBranchModule::root_aus_up_to_full(roots);
    if atomic_branch_metadata_loaded_flag(model.program.state.branch) {
        assert(model.program.state.branch.branch_summary.dom().contains(root.au));
        assert(CachingDiskBranchModule::loaded_branch_summary_agrees(
            roots,
            nodes,
            model.program.state.branch.branch_summary,
        ));
        assert(model.program.state.branch.branch_summary.dom()
            <= CachingDiskBranchModule::root_aus_up_to(roots, roots.len() as nat));
        assert(model.program.state.branch.branch_summary.dom().finite());
        assert(model.program.state.branch.branch_summary[root.au] == summary);
        assert(branch_projection_summary_i(model)
            == model.program.state.branch.branch_summary);
    } else {
        CachingDiskBranchModule::branch_summary_from_reads_up_to_self_ensures(
            roots,
            nodes,
            roots.len() as nat,
        );
        assert(CachingDiskBranchModule::completed_branch_summary_from_reads(roots, nodes)
            .contains_key(root.au));
        assert(CachingDiskBranchModule::completed_branch_summary_from_reads(roots, nodes).dom()
            =~= CachingDiskBranchModule::root_aus_up_to(roots, roots.len() as nat));
        assert(CachingDiskBranchModule::completed_branch_summary_from_reads(roots, nodes)
            .dom().finite());
        assert(CachingDiskBranchModule::completed_branch_summary_from_reads(roots, nodes)[root.au]
            == summary);
        assert(branch_interpreted_summary_i(model)
            == CachingDiskBranchModule::completed_branch_summary_from_reads(roots, nodes));
        assert(branch_projection_summary_i(model) == branch_interpreted_summary_i(model));
    }
    assert(branch_projection_summary_i(model).dom().finite());
    assert(branch_projection_summary_i(model).contains_key(root.au));
    assert(branch_projection_summary_i(model)[root.au] == summary);
    assert(branch_projection_summary_i(model).values().contains(summary));
    lemma_values_finite(branch_projection_summary_i(model));
    lemma_union_set_of_sets_subset(branch_projection_summary_i(model).values(), summary);
    assert(summary <= summary_aus(branch_projection_summary_i(model))) by {
        assert forall |au: AU| #[trigger] summary.contains(au)
            implies summary_aus(branch_projection_summary_i(model)).contains(au)
        by {
            assert(union_set_of_sets(branch_projection_summary_i(model).values()).contains(au));
        }
    }
}

pub proof fn branch_projection_summary_equals_interpreted_when_agrees(
    model: SystemModel::State<AnotherProgramModel>,
)
    requires
        branch_loaded_metadata_agrees_with_visible(model),
        model.program.state.superblock_metadata_known(),
        set_addrs_disjoint_aus(model.program.state.branch.image.sealed_roots.to_set()),
    ensures
        branch_projection_summary_i(model) == branch_interpreted_summary_i(model),
{
    let roots = model.program.state.branch.image.sealed_roots;
    let nodes = branch_visible_nodes_i(model);
    assert(CachingDiskBranchModule::branch_summary_reads_valid(roots, nodes));
    if atomic_branch_metadata_loaded_flag(model.program.state.branch) {
        assert(branch_projection_summary_i(model)
            == model.program.state.branch.branch_summary);
        assert(branch_interpreted_summary_i(model)
            == CachingDiskBranchModule::completed_branch_summary_from_reads(roots, nodes));
        CachingDiskBranchModule::branch_summary_from_reads_up_to_self_ensures(
            roots,
            nodes,
            roots.len() as nat,
        );
        assert(CachingDiskBranchModule::loaded_branch_summary_agrees(
            roots,
            nodes,
            model.program.state.branch.branch_summary,
        ));
        assert(model.program.state.branch.branch_summary.dom()
            <= CachingDiskBranchModule::root_aus_up_to(roots, roots.len() as nat));
        assert(CachingDiskBranchModule::root_aus_up_to(roots, roots.len() as nat)
            <= model.program.state.branch.branch_summary.dom());
        assert(model.program.state.branch.branch_summary.dom()
            =~= CachingDiskBranchModule::completed_branch_summary_from_reads(roots, nodes).dom()) by {
            assert(CachingDiskBranchModule::completed_branch_summary_from_reads(roots, nodes).dom()
                =~= CachingDiskBranchModule::root_aus_up_to(roots, roots.len() as nat));
        }
        assert(model.program.state.branch.branch_summary
            == CachingDiskBranchModule::completed_branch_summary_from_reads(roots, nodes)) by {
            assert_maps_equal!(
                model.program.state.branch.branch_summary,
                CachingDiskBranchModule::completed_branch_summary_from_reads(roots, nodes),
                au => {
                    if model.program.state.branch.branch_summary.contains_key(au) {
                        assert(CachingDiskBranchModule::root_aus_up_to(
                            roots,
                            roots.len() as nat,
                        ).contains(au));
                        let idx = CachingDiskBranchModule::root_aus_up_to_member_has_index(
                            roots,
                            roots.len() as nat,
                            au,
                        );
                        assert(roots[idx].au == au);
                        assert(model.program.state.branch.branch_summary[au]
                            == root_summary_from_read(roots[idx], nodes));
                        assert(CachingDiskBranchModule::completed_branch_summary_from_reads(
                            roots,
                            nodes,
                        )[au] == root_summary_from_read(roots[idx], nodes));
                    }
                    if CachingDiskBranchModule::completed_branch_summary_from_reads(
                        roots,
                        nodes,
                    ).contains_key(au) {
                        assert(CachingDiskBranchModule::completed_branch_summary_from_reads(
                            roots,
                            nodes,
                        ).dom().contains(au));
                        assert(CachingDiskBranchModule::root_aus_up_to(
                            roots,
                            roots.len() as nat,
                        ).contains(au));
                        let idx = CachingDiskBranchModule::root_aus_up_to_member_has_index(
                            roots,
                            roots.len() as nat,
                            au,
                        );
                        assert(roots[idx].au == au);
                        assert(model.program.state.branch.branch_summary.contains_key(au));
                        assert(model.program.state.branch.branch_summary[au]
                            == root_summary_from_read(roots[idx], nodes));
                        assert(CachingDiskBranchModule::completed_branch_summary_from_reads(
                            roots,
                            nodes,
                        )[au] == root_summary_from_read(roots[idx], nodes));
                    }
                }
            );
        }
    } else {
        assert(branch_projection_summary_i(model) == branch_interpreted_summary_i(model));
    }
}

pub proof fn branch_load_metadata_preserves_allocation_projection_wf(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    root: Address,
    reads: Map<Address, RawPage>,
    discovered_aus: Set<AU>,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        AnotherAtomicState::branch_load_metadata(
            pre.program.state,
            post.program.state,
            root,
            reads,
            discovered_aus,
        ),
        post.disk == pre.disk,
    ensures
        post.program.state.allocation_wf(),
        branch_projected_aus_are_owned_data(post),
        branch_loaded_metadata_agrees_with_visible(post),
        branch_projection_aus(post) =~= branch_projection_aus(pre),
{
    assert(AnotherAtomicState::branch_load_metadata(
        pre.program.state,
        post.program.state,
        root,
        reads,
        discovered_aus,
    ));
    let read_nodes = crate::implementation::AnotherAtomicState_v::to_branch_nodes(reads);
    let branch_lbl = AtomicBranchState::Label::LoadMetadata{root, discovered_aus, read_nodes};
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
    AtomicBranchState::State::wf_next(
        pre.program.state.branch,
        post.program.state.branch,
        branch_lbl,
    );
    filled_cache_read_only_access_unchanged(
        pre.program.state.cache,
        post.program.state.cache,
        reads,
    );
    assert(branch_raw_visible_i(post) =~= branch_raw_visible_i(pre)) by {
        assert_maps_equal!(branch_raw_visible_i(post), branch_raw_visible_i(pre), addr => {
            assert(filled_cache_pages(post.program.state.cache).contains_key(addr)
                <==> filled_cache_pages(pre.program.state.cache).contains_key(addr));
            if branch_raw_visible_i(post).contains_key(addr) {
                if filled_cache_pages(post.program.state.cache).contains_key(addr) {
                    assert(filled_cache_pages(pre.program.state.cache).contains_key(addr));
                    assert(filled_cache_pages(post.program.state.cache)[addr]
                        == filled_cache_pages(pre.program.state.cache)[addr]);
                } else {
                    assert(post.disk.content.contains_key(addr));
                    assert(pre.disk.content.contains_key(addr));
                }
            }
            if branch_raw_visible_i(pre).contains_key(addr) {
                if filled_cache_pages(pre.program.state.cache).contains_key(addr) {
                    assert(filled_cache_pages(post.program.state.cache).contains_key(addr));
                    assert(filled_cache_pages(post.program.state.cache)[addr]
                        == filled_cache_pages(pre.program.state.cache)[addr]);
                } else {
                    assert(pre.disk.content.contains_key(addr));
                    assert(post.disk.content.contains_key(addr));
                }
            }
        });
    }
    assert(branch_visible_nodes_i(post) =~= branch_visible_nodes_i(pre)) by {
        assert_maps_equal!(branch_visible_nodes_i(post), branch_visible_nodes_i(pre), addr => {
            assert(branch_raw_visible_i(post).contains_key(addr)
                <==> branch_raw_visible_i(pre).contains_key(addr));
            if branch_visible_nodes_i(post).contains_key(addr) {
                assert(branch_raw_visible_i(post).contains_key(addr));
                assert(branch_raw_visible_i(pre).contains_key(addr));
                assert(branch_raw_visible_i(post)[addr] == branch_raw_visible_i(pre)[addr]);
            }
            if branch_visible_nodes_i(pre).contains_key(addr) {
                assert(branch_raw_visible_i(post).contains_key(addr));
                assert(branch_raw_visible_i(pre).contains_key(addr));
                assert(branch_raw_visible_i(post)[addr] == branch_raw_visible_i(pre)[addr]);
            }
        });
    }
    assert(branch_loaded_metadata_agrees_with_visible(post)) by {
        assert(branch_loaded_metadata_agrees_with_visible(pre));
        assert(post.program.state.superblock_metadata_known());
        assert(CachingDiskBranchModule::branch_summary_reads_valid(
            post.program.state.branch.image.sealed_roots,
            branch_visible_nodes_i(post),
        ));
        assert(CachingDiskBranchModule::loaded_branch_summary_agrees(
            post.program.state.branch.image.sealed_roots,
            branch_visible_nodes_i(post),
            post.program.state.branch.branch_summary,
        )) by {
            let roots = post.program.state.branch.image.sealed_roots;
            assert(post.program.state.branch.branch_summary
                == pre.program.state.branch.branch_summary.insert(root.au, discovered_aus));
            assert(roots == pre.program.state.branch.image.sealed_roots);
            assert(set_addrs_disjoint_aus(roots.to_set())) by {
                assert(branch_component_refinement_inv(pre));
                assert(pre.program.state.superblock_metadata_known());
                assert(crash_aware_caching_disk_branch_i(pre).ephemeral is Known);
                assert(branch_caching_disk_state_i(pre).inv());
                assert(branch_caching_disk_state_i(pre).sealed_stack_i().wf());
            }
            assert(post.program.state.branch.branch_summary.dom()
                <= CachingDiskBranchModule::root_aus_up_to(
                    post.program.state.branch.image.sealed_roots,
                    post.program.state.branch.image.sealed_roots.len() as nat,
                )) by {
                assert forall |au: AU|
                    #[trigger] post.program.state.branch.branch_summary.dom().contains(au)
                    implies CachingDiskBranchModule::root_aus_up_to(
                        post.program.state.branch.image.sealed_roots,
                        post.program.state.branch.image.sealed_roots.len() as nat,
                    ).contains(au)
                by {
                    if pre.program.state.branch.branch_summary.dom().contains(au) {
                        assert(CachingDiskBranchModule::loaded_branch_summary_agrees(
                            pre.program.state.branch.image.sealed_roots,
                            branch_visible_nodes_i(pre),
                            pre.program.state.branch.branch_summary,
                        ));
                    } else {
                        assert(au == root.au);
                        let idx = choose |i: int|
                            0 <= i < pre.program.state.branch.image.sealed_roots.len()
                                && pre.program.state.branch.image.sealed_roots[i] == root;
                        CachingDiskBranchModule::root_aus_up_to_contains(
                            pre.program.state.branch.image.sealed_roots,
                            pre.program.state.branch.image.sealed_roots.len() as nat,
                            idx,
                        );
                    }
                }
            }
            assert forall |i: int| #![trigger post.program.state.branch.image.sealed_roots[i]]
                0 <= i < post.program.state.branch.image.sealed_roots.len()
                    && post.program.state.branch.branch_summary.contains_key(
                        post.program.state.branch.image.sealed_roots[i].au,
                    )
                implies {
                    &&& root_summary_read_valid(
                        post.program.state.branch.image.sealed_roots[i],
                        branch_visible_nodes_i(post),
                    )
                    &&& post.program.state.branch.branch_summary[
                        post.program.state.branch.image.sealed_roots[i].au
                    ] == root_summary_from_read(
                        post.program.state.branch.image.sealed_roots[i],
                        branch_visible_nodes_i(post),
                    )
                } by {
                let item = post.program.state.branch.image.sealed_roots[i];
                assert(root_summary_read_valid(
                    item,
                    branch_visible_nodes_i(post),
                ));
                if item.au == root.au {
                    assert(post.program.state.branch.image.sealed_roots.to_set().contains(item));
                    assert(pre.program.state.branch.image.sealed_roots.to_set().contains(root));
                    if item != root {
                        assert(set_addrs_disjoint_aus(roots.to_set()));
                        assert(false);
                    }
                    branch_read_node_matches_visible_after_read_only_access(pre, post, reads, root);
                    assert(read_nodes[root] == branch_visible_nodes_i(post)[root]);
                    if read_nodes[root] is Index {
                        let aux = read_nodes[root]->aux_ptr.unwrap();
                        branch_read_node_matches_visible_after_read_only_access(pre, post, reads, aux);
                        assert(read_nodes[aux] == branch_visible_nodes_i(post)[aux]);
                        assert(root_summary_from_read(root, read_nodes) == read_nodes[aux]->0);
                        assert(root_summary_from_read(root, branch_visible_nodes_i(post))
                            == branch_visible_nodes_i(post)[aux]->0);
                    } else {
                        assert(root_summary_from_read(root, read_nodes) == set![root.au]);
                        assert(root_summary_from_read(root, branch_visible_nodes_i(post))
                            == set![root.au]);
                    }
                    assert(root_summary_from_read(root, read_nodes)
                        == root_summary_from_read(
                            root,
                            branch_visible_nodes_i(post),
                        ));
                    assert(post.program.state.branch.branch_summary[root.au] == discovered_aus);
                    assert(discovered_aus == root_summary_from_read(root, read_nodes));
                } else {
                    assert(pre.program.state.branch.branch_summary.contains_key(item.au));
                    assert(CachingDiskBranchModule::loaded_branch_summary_agrees(
                        pre.program.state.branch.image.sealed_roots,
                        branch_visible_nodes_i(pre),
                        pre.program.state.branch.branch_summary,
                    ));
                    assert(pre.program.state.branch.branch_summary[item.au]
                        == root_summary_from_read(
                            item,
                            branch_visible_nodes_i(pre),
                        ));
                    assert(branch_visible_nodes_i(post) =~= branch_visible_nodes_i(pre));
                    assert(post.program.state.branch.branch_summary[item.au]
                        == pre.program.state.branch.branch_summary[item.au]);
                    assert(root_summary_from_read(item, branch_visible_nodes_i(post))
                        == root_summary_from_read(item, branch_visible_nodes_i(pre)));
                }
            }
        }
    }
    assert(post.program.state.journal == pre.program.state.journal);
    assert(post.program.state.free_aus == pre.program.state.free_aus - discovered_aus);
    assert(discovered_aus <= branch_projection_aus(pre)) by {
        assert(set_addrs_disjoint_aus(
            pre.program.state.branch.image.sealed_roots.to_set(),
        )) by {
            assert(branch_component_refinement_inv(pre));
            assert(pre.program.state.superblock_metadata_known());
            assert(crash_aware_caching_disk_branch_i(pre).ephemeral is Known);
            assert(branch_caching_disk_state_i(pre).inv());
            assert(branch_caching_disk_state_i(pre).sealed_stack_i().wf());
        }
        branch_read_node_matches_visible_after_read_only_access(pre, post, reads, root);
        assert(read_nodes[root] == branch_visible_nodes_i(post)[root]);
        if read_nodes[root] is Index {
            let aux = read_nodes[root]->aux_ptr.unwrap();
            branch_read_node_matches_visible_after_read_only_access(pre, post, reads, aux);
            assert(read_nodes[aux] == branch_visible_nodes_i(post)[aux]);
            assert(root_summary_from_read(root, read_nodes) == read_nodes[aux]->0);
            assert(root_summary_from_read(root, branch_visible_nodes_i(post))
                == branch_visible_nodes_i(post)[aux]->0);
        } else {
            assert(root_summary_from_read(root, read_nodes) == set![root.au]);
            assert(root_summary_from_read(root, branch_visible_nodes_i(post)) == set![root.au]);
        }
        assert(root_summary_from_read(root, read_nodes)
            == root_summary_from_read(root, branch_visible_nodes_i(post)));
        assert(branch_visible_nodes_i(post) =~= branch_visible_nodes_i(pre));
        assert(root_summary_from_read(root, branch_visible_nodes_i(post))
            == root_summary_from_read(root, branch_visible_nodes_i(pre)));
        assert(discovered_aus == root_summary_from_read(root, branch_visible_nodes_i(pre)));
        visible_root_summary_subset_branch_projection(pre, root);
    }
    assert(post.program.state.branch_owned_aus()
        <= pre.program.state.branch_owned_aus() + discovered_aus) by {
        assert(post.program.state.branch.mini_allocator
            == pre.program.state.branch.mini_allocator);
        assert(summary_aus(post.program.state.branch.branch_summary)
            <= summary_aus(pre.program.state.branch.branch_summary) + discovered_aus) by {
            lemma_values_finite(post.program.state.branch.branch_summary);
            assert forall |au: AU|
                #[trigger] summary_aus(post.program.state.branch.branch_summary).contains(au)
                implies (summary_aus(pre.program.state.branch.branch_summary) + discovered_aus).contains(au)
            by {
                let summary = lemma_union_set_of_sets_contains(
                    post.program.state.branch.branch_summary.values(),
                    au,
                );
                if summary == discovered_aus {
                } else {
                    assert(pre.program.state.branch.branch_summary.values().contains(summary));
                    lemma_union_set_of_sets_subset(
                        pre.program.state.branch.branch_summary.values(),
                        summary,
                    );
                }
            }
        }
    }
    assert(post.program.state.component_disjoint()) by {
        assert(pre.program.state.component_disjoint());
        assert(branch_projected_aus_are_owned_data(pre));
        assert forall |au: AU|
            #[trigger] post.program.state.branch_owned_aus().contains(au)
            implies {
                &&& !AnotherAtomicState::reserved_aus().contains(au)
                &&& !post.program.state.journal_owned_aus().contains(au)
            } by {
            if pre.program.state.branch_owned_aus().contains(au) {
            } else {
                assert(discovered_aus.contains(au));
                assert(branch_projection_aus(pre).contains(au));
            }
        }
    }
    assert(post.program.state.free_aus.disjoint(post.program.state.component_owned_aus())) by {
        assert(pre.program.state.allocation_wf());
        assert(branch_projected_aus_are_owned_data(pre));
        assert forall |au: AU|
            #[trigger] post.program.state.free_aus.contains(au)
            implies !post.program.state.component_owned_aus().contains(au) by {
            assert(pre.program.state.free_aus.contains(au));
            assert(!discovered_aus.contains(au));
            if post.program.state.component_owned_aus().contains(au) {
                if post.program.state.branch_owned_aus().contains(au) {
                    if pre.program.state.branch_owned_aus().contains(au) {
                    } else {
                        assert(discovered_aus.contains(au));
                    }
                }
            }
        }
    }
    assert(post.program.state.allocation_wf());
    assert(branch_projection_aus(post) =~= branch_projection_aus(pre)) by {
        assert(set_addrs_disjoint_aus(
            pre.program.state.branch.image.sealed_roots.to_set(),
        )) by {
            assert(branch_component_refinement_inv(pre));
            assert(pre.program.state.superblock_metadata_known());
            assert(crash_aware_caching_disk_branch_i(pre).ephemeral is Known);
            assert(branch_caching_disk_state_i(pre).inv());
            assert(branch_caching_disk_state_i(pre).sealed_stack_i().wf());
        }
        assert(set_addrs_disjoint_aus(
            post.program.state.branch.image.sealed_roots.to_set(),
        )) by {
            assert(post.program.state.branch.image.sealed_roots
                == pre.program.state.branch.image.sealed_roots);
        }
        branch_projection_summary_equals_interpreted_when_agrees(pre);
        branch_projection_summary_equals_interpreted_when_agrees(post);
        assert(branch_visible_nodes_i(post) =~= branch_visible_nodes_i(pre));
        assert(branch_visible_nodes_i(post) == branch_visible_nodes_i(pre));
        assert(post.program.state.branch.image.sealed_roots
            == pre.program.state.branch.image.sealed_roots);
        assert(branch_interpreted_summary_i(post) == branch_interpreted_summary_i(pre));
        assert(branch_projection_summary_i(post) == branch_projection_summary_i(pre));
        assert(post.program.state.branch.mini_allocator
            == pre.program.state.branch.mini_allocator);
        assert(summary_aus(branch_projection_summary_i(post))
            == summary_aus(branch_projection_summary_i(pre)));
        assert forall |au: AU| #[trigger] branch_projection_aus(post).contains(au)
            implies branch_projection_aus(pre).contains(au) by {
        }
        assert forall |au: AU| #[trigger] branch_projection_aus(pre).contains(au)
            implies branch_projection_aus(post).contains(au) by {
        }
    }
    assert(branch_projected_aus_are_owned_data(post)) by {
        assert(post.program.state.journal_owned_aus() == pre.program.state.journal_owned_aus());
        assert forall |au: AU| #[trigger] branch_projection_aus(post).contains(au)
            implies {
                &&& !AnotherAtomicState::reserved_aus().contains(au)
                &&& !post.program.state.journal_owned_aus().contains(au)
                &&& !post.program.state.free_aus.contains(au)
            } by {
            assert(branch_projection_aus(pre).contains(au));
            assert(branch_projected_aus_are_owned_data(pre));
            if post.program.state.free_aus.contains(au) {
                assert(pre.program.state.free_aus.contains(au));
            }
        }
    }
}

pub proof fn disk_internal_preserves_refinement_invariants(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        post.program == pre.program,
        AsyncDisk::State::next(pre.disk, post.disk, DiskLabel::Internal{}),
    ensures
        another_atomic_disk_refinement_invariants(post),
{
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
            disk_internal_process_read_preserves_refinement_invariants(pre, post, id);
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
                assert(another_atomic_superblock_write_request_wf(pre.program.state, pre.disk));
                assert(pre.disk.requests.contains_key(id));
                assert(pre.disk.requests[id] is WriteReq);
                assert(pre.disk.requests[id]->to == spec_superblock_addr());
                assert(pre.program.state.client_ready());
                assert(post.program.state.client_ready());
                assert(pre.program.state.in_flight is Some);
                assert(req->data == marshal_abstract_superblock(
                    pre.program.state.atomic_inflight_superblock_i(),
                ));
                assert(pre.program.state.atomic_inflight_superblock_i().wf());
                marshalled_abstract_superblock_raw_wf(
                    pre.program.state.atomic_inflight_superblock_i(),
                );
                assert(pre.program.state.persistent_image is Some);
                assert(post.program.state.persistent_image == pre.program.state.persistent_image);
                assert(atomic_persistent_superblock_image_i(post)
                    == atomic_persistent_superblock_image_i(pre));
                let persistent_image = atomic_persistent_superblock_image_i(pre);
                assert(!journal_image_static_domain_i(pre, persistent_image).contains(
                    spec_superblock_addr(),
                )) by {
                    assert(journal_component_refinement_inv(pre));
                    assert(journal_image_static_domain_i(pre, persistent_image)
                        <= addresses_in_aus(journal_projection_aus(pre)));
                    if journal_image_static_domain_i(pre, persistent_image).contains(
                        spec_superblock_addr(),
                    ) {
                        assert(addresses_in_aus(journal_projection_aus(pre)).contains(
                            spec_superblock_addr(),
                        ));
                        assert(journal_projected_aus_are_component_data(pre));
                        assert(AnotherAtomicState::reserved_aus().contains(spec_superblock_addr().au));
                        assert(false);
                    }
                }
                journal_image_persistent_preserved_by_disjoint_write(
                    pre,
                    post,
                    persistent_image,
                    spec_superblock_addr(),
                    req->data,
                );
                assert(persistent_journal_image_i(post) == persistent_journal_image_i(pre));
                let frozen_image = pre.program.state.atomic_inflight_superblock_i();
                assert(!journal_image_static_domain_i(pre, frozen_image).contains(
                    spec_superblock_addr(),
                )) by {
                    assert(journal_component_refinement_inv(pre));
                    assert(journal_image_static_domain_i(pre, frozen_image)
                        <= addresses_in_aus(journal_projection_aus(pre)));
                    if journal_image_static_domain_i(pre, frozen_image).contains(
                        spec_superblock_addr(),
                    ) {
                        assert(addresses_in_aus(journal_projection_aus(pre)).contains(
                            spec_superblock_addr(),
                        ));
                        assert(journal_projected_aus_are_component_data(pre));
                        assert(AnotherAtomicState::reserved_aus().contains(spec_superblock_addr().au));
                        assert(false);
                    }
                }
                journal_image_persistent_preserved_by_disjoint_write(
                    pre,
                    post,
                    frozen_image,
                    spec_superblock_addr(),
                    req->data,
                );
                assert(frozen_journal_image_i(post) == frozen_journal_image_i(pre));
                assert(journal_projection_uses_live(pre));
                assert(journal_projection_uses_live(post));
                assert(journal_projection_addrs(post) =~= journal_projection_addrs(pre)) by {
                    assert(post.program.state == pre.program.state);
                }
                assert(journal_persistent_projection_addrs(post)
                    =~= journal_persistent_projection_addrs(pre)) by {
                    assert forall |addr: Address|
                        #[trigger] journal_persistent_projection_addrs(post).contains(addr)
                            <==> journal_persistent_projection_addrs(pre).contains(addr)
                    by {
                        assert(journal_projection_addrs(post).contains(addr)
                            <==> journal_projection_addrs(pre).contains(addr));
                        if addr == spec_superblock_addr() {
                            assert(AnotherAtomicState::reserved_aus().contains(addr.au));
                            assert(addresses_in_aus(AnotherAtomicState::reserved_aus()).contains(addr));
                            assert(!journal_projection_addrs(post).contains(addr));
                            assert(!journal_projection_addrs(pre).contains(addr));
                        } else {
                            assert(post.disk.content.contains_key(addr)
                                == pre.disk.content.contains_key(addr));
                            if post.disk.content.contains_key(addr) {
                                assert(post.disk.content[addr] == pre.disk.content[addr]);
                            }
                        }
                    }
                }
                assert(journal_disk_persistent_i(post) == journal_disk_persistent_i(pre)) by {
                    assert_maps_equal!(
                        journal_disk_persistent_i(post),
                        journal_disk_persistent_i(pre),
                        addr => {
                            assert(journal_persistent_projection_addrs(post).contains(addr)
                                <==> journal_persistent_projection_addrs(pre).contains(addr));
                            if addr != spec_superblock_addr() {
                                assert(post.disk.content[addr] == pre.disk.content[addr]);
                            } else {
                                assert(!journal_persistent_projection_addrs(post).contains(addr));
                                assert(!journal_persistent_projection_addrs(pre).contains(addr));
                            }
                        }
                    );
                }
                assert(journal_disk_cache_i(post) == journal_disk_cache_i(pre)) by {
                    assert(post.program.state.cache == pre.program.state.cache);
                    assert(journal_projection_addrs(post) =~= journal_projection_addrs(pre));
                }
                assert(journal_disk_status_i(post) == journal_disk_status_i(pre)) by {
                    assert(post.program.state.cache == pre.program.state.cache);
                    assert(journal_projection_addrs(post) =~= journal_projection_addrs(pre));
                }
                assert(journal_caching_disk_i(post) == journal_caching_disk_i(pre));
                assert(journal_caching_disk_state_i(post) == journal_caching_disk_state_i(pre));
                client_ready_implies_atomic_branch_metadata_loaded_flag(pre.program.state);
                client_ready_implies_atomic_branch_metadata_loaded_flag(post.program.state);
                assert(branch_projection_summary_i(post) == branch_projection_summary_i(pre));
                assert(branch_projection_addrs(post) =~= branch_projection_addrs(pre)) by {
                    assert(post.program.state == pre.program.state);
                    assert(atomic_branch_metadata_loaded_flag(pre.program.state.branch));
                    assert(atomic_branch_metadata_loaded_flag(post.program.state.branch));
                }
                assert(!branch_projection_addrs(pre).contains(spec_superblock_addr())) by {
                    if branch_projection_addrs(pre).contains(spec_superblock_addr()) {
                        assert(branch_projection_aus(pre).contains(spec_superblock_addr().au)) by {
                            if addresses_in_aus(summary_aus(branch_projection_summary_i(pre))).contains(
                                spec_superblock_addr(),
                            ) {
                                assert(summary_aus(branch_projection_summary_i(pre)).contains(
                                    spec_superblock_addr().au,
                                ));
                            } else {
                                assert(branch_mini_allocator_allocated_addrs(
                                    pre.program.state.branch.mini_allocator,
                                ).contains(spec_superblock_addr()));
                                assert(pre.program.state.branch.mini_allocator.all_aus().contains(
                                    spec_superblock_addr().au,
                                ));
                            }
                        }
                        assert(branch_projected_aus_are_owned_data(pre));
                        assert(AnotherAtomicState::reserved_aus().contains(spec_superblock_addr().au));
                        assert(false);
                    }
                }
                assert(!branch_projection_addrs(post).contains(spec_superblock_addr())) by {
                    assert(branch_projection_addrs(post) =~= branch_projection_addrs(pre));
                }
                assert(branch_persistent_projection_addrs(post)
                    =~= branch_persistent_projection_addrs(pre)) by {
                    assert forall |addr: Address|
                        #[trigger] branch_persistent_projection_addrs(post).contains(addr)
                            <==> branch_persistent_projection_addrs(pre).contains(addr)
                    by {
                        assert(branch_projection_addrs(post).contains(addr)
                            <==> branch_projection_addrs(pre).contains(addr));
                        if addr == spec_superblock_addr() {
                            assert(!branch_projection_addrs(post).contains(addr));
                            assert(!branch_projection_addrs(pre).contains(addr));
                        } else {
                            assert(post.disk.content.contains_key(addr)
                                == pre.disk.content.contains_key(addr));
                            if post.disk.content.contains_key(addr) {
                                assert(post.disk.content[addr] == pre.disk.content[addr]);
                            }
                        }
                    }
                }
                assert(branch_disk_persistent_i(post) == branch_disk_persistent_i(pre)) by {
                    assert_maps_equal!(
                        branch_disk_persistent_i(post),
                        branch_disk_persistent_i(pre),
                        addr => {
                            assert(branch_persistent_projection_addrs(post).contains(addr)
                                <==> branch_persistent_projection_addrs(pre).contains(addr));
                            if addr != spec_superblock_addr() {
                                assert(post.disk.content[addr] == pre.disk.content[addr]);
                            } else {
                                assert(!branch_persistent_projection_addrs(post).contains(addr));
                                assert(!branch_persistent_projection_addrs(pre).contains(addr));
                            }
                        }
                    );
                }
                assert(branch_disk_cache_i(post) == branch_disk_cache_i(pre)) by {
                    assert(post.program.state.cache == pre.program.state.cache);
                    assert(branch_projection_addrs(post) =~= branch_projection_addrs(pre));
                }
                assert(branch_disk_status_i(post) == branch_disk_status_i(pre)) by {
                    assert(post.program.state.cache == pre.program.state.cache);
                    assert(branch_projection_addrs(post) =~= branch_projection_addrs(pre));
                }
                assert(branch_caching_disk_i(post) == branch_caching_disk_i(pre));
                assert(branch_caching_disk_state_i(post) == branch_caching_disk_state_i(pre));
            } else {
                disk_internal_process_data_write_preserves_refinement_invariants(
                    pre,
                    post,
                    id,
                );
                assert(another_atomic_disk_refinement_invariants(post));
            }
        },
        _ => {
            assert(false);
        },
    }
    assert(persistent_journal_image_i(post).wf());
    assert(journal_projection_tight(post));
    assert(journal_projection_uses_shared_async_disk(post));
    if post.program.state.client_ready() {
        assert(journal_owned_disk_records_do_not_impersonate_index(post)) by {
            assert(post.program.state.client_ready());
        }
    }
    assert(journal_component_refinement_inv(post));
    assert(another_atomic_disk_refinement_invariants(post));
}

pub proof fn disk_internal_process_read_preserves_refinement_invariants(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    id: ID,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        post.program == pre.program,
        AsyncDisk::State::next_by(
            pre.disk,
            post.disk,
            DiskLabel::Internal{},
            AsyncDisk::Step::process_read(id),
        ),
    ensures
        another_atomic_disk_refinement_invariants(post),
{
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    assert(AsyncDisk::State::next(pre.disk, post.disk, DiskLabel::Internal{}));
    assert(post.program.state == pre.program.state);
    assert(post.program.state.wf());
    assert(another_atomic_model_refinement_invariants(post.program.state));
    async_disk_inv_next(pre.disk, post.disk, DiskLabel::Internal{});
    assert(post.disk.inv());
    assert(post.disk.content == pre.disk.content);
    async_disk_superblock_page_wf_preserved_by_internal(
        pre.program.state,
        pre.disk,
        post.disk,
    );
    assert(async_disk_superblock_page_wf(post.disk.content));
    assert(another_atomic_cache_disk_coupling(post.program.state, post.disk)) by {
        assert forall |pending_id: ID| #[trigger] post.program.state.outstanding_cache_reqs.contains_key(pending_id)
            implies disk_has_pending_id(post.disk, pending_id) by {
            assert(pre.program.state.outstanding_cache_reqs.contains_key(pending_id));
            assert(disk_has_pending_id(pre.disk, pending_id));
            disk_has_pending_id_preserved_by_internal(pre.disk, post.disk, pending_id);
        }
        assert forall |addr: Address| #[trigger] filled_cache_status(post.program.state.cache).contains_key(addr)
            && filled_cache_status(post.program.state.cache)[addr] == CachingDiskPageStatus::Clean
            && addr != spec_superblock_addr()
            implies {
                &&& post.disk.content.contains_key(addr)
                &&& post.disk.content[addr] == cache_filled_page(post.program.state.cache, addr)
            } by {
            assert(filled_cache_status(pre.program.state.cache).contains_key(addr));
            assert(filled_cache_status(pre.program.state.cache)[addr] == CachingDiskPageStatus::Clean);
            assert(another_atomic_cache_disk_coupling(pre.program.state, pre.disk));
            assert(pre.disk.content.contains_key(addr));
            assert(pre.disk.content[addr] == cache_filled_page(pre.program.state.cache, addr));
        }
    }
    assert(another_atomic_superblock_disk_coupling(post.program.state, post.disk));
    superblock_write_request_wf_preserved_by_internal(
        post.program.state,
        pre.disk,
        post.disk,
    );
    cache_disk_request_wf_preserved_by_internal(
        post.program.state,
        pre.disk,
        post.disk,
    );
    assert(another_atomic_superblock_write_request_wf(post.program.state, post.disk));
    assert(another_atomic_cache_disk_request_wf(post.program.state, post.disk));
    assert(persistent_journal_image_i(post) == persistent_journal_image_i(pre));
    assert(journal_projection_aus(post) == journal_projection_aus(pre));
    assert(journal_disk_persistent_i(post) == journal_disk_persistent_i(pre));
    assert(journal_disk_cache_i(post) == journal_disk_cache_i(pre));
    assert(journal_disk_status_i(post) == journal_disk_status_i(pre));
    assert(frozen_journal_image_i(post) == frozen_journal_image_i(pre));
    assert(branch_caching_disk_i(post) == branch_caching_disk_i(pre));
    assert(branch_caching_disk_state_i(post) == branch_caching_disk_state_i(pre));
    assert(crash_aware_caching_disk_branch_i(post) == crash_aware_caching_disk_branch_i(pre));
    assert(branch_component_refinement_inv(post));
    assert(journal_projection_tight(post));
    assert(journal_projection_uses_shared_async_disk(post));
    assert(persistent_journal_image_i(post).wf());
    assert(journal_component_refinement_inv(post));
    assert(journal_projected_aus_are_component_data(post));
    assert(branch_projected_aus_are_owned_data(post));
    assert(branch_loaded_metadata_agrees_with_visible(post));
    assert(journal_loaded_index_matches_persistent_subdisk(post));
    assert(journal_index_aus_have_unique_lsns(post));
    assert(journal_inflight_projection_wf(post)) by {
        if post.program.state.in_flight is Some {
            assert(pre.program.state.in_flight is Some);
            assert(journal_inflight_projection_wf(pre));
            assert(journal_projection_uses_live(post) == journal_projection_uses_live(pre));
            assert(frozen_journal_image_i(post) == frozen_journal_image_i(pre));
            assert(post.program.state.journal.loaded_index_aus()
                == pre.program.state.journal.loaded_index_aus());
        }
    }
    assert(another_atomic_recovery_image_matches_disk(post));
    assert(journal_image_writeback_disjoint(post)) by {
        assert(journal_image_writeback_disjoint(pre));
        assert(durable_superblock_image_i(post) == durable_superblock_image_i(pre));
        let durable_image = durable_superblock_image_i(pre);
        journal_image_static_domain_unchanged_by_disk_content(pre, post, durable_image);
        if pre.program.state.in_flight is Some {
            journal_image_static_domain_unchanged_by_disk_content(
                pre,
                post,
                pre.program.state.atomic_inflight_superblock_i(),
            );
        }
        assert(post.disk.requests == pre.disk.requests.remove(id));
        assert(filled_cache_status(post.program.state.cache)
            =~= filled_cache_status(pre.program.state.cache)) by {
            assert_maps_equal!(
                filled_cache_status(post.program.state.cache),
                filled_cache_status(pre.program.state.cache),
                addr => { }
            );
        }
        assert forall |req_id: ID| #[trigger] post.disk.requests.contains_key(req_id)
            && post.disk.requests[req_id] is WriteReq
            && post.disk.requests[req_id]->to != spec_superblock_addr()
            implies post.program.state.journal_metadata_loaded()
        by {
            assert(pre.disk.requests.contains_key(req_id));
            assert(post.disk.requests[req_id] == pre.disk.requests[req_id]);
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
            && filled_cache_status(post.program.state.cache)[addr] == CachingDiskPageStatus::Writeback
            implies post.program.state.journal_metadata_loaded()
        by {
            assert(filled_cache_status(pre.program.state.cache).contains_key(addr));
            assert(filled_cache_status(pre.program.state.cache)[addr] == CachingDiskPageStatus::Writeback);
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
            if filled_cache_status(post.program.state.cache)[addr] == CachingDiskPageStatus::Dirty {
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
        assert forall |req_id: ID| #[trigger] post.disk.requests.contains_key(req_id)
            implies {
                &&& journal_image_request_writeback_disjoint_at(post, durable_superblock_image_i(post), req_id)
                &&& another_atomic_superblock_write_pending(post) ==>
                    journal_image_request_writeback_disjoint_at(
                        post,
                        post.program.state.atomic_inflight_superblock_i(),
                        req_id,
                    )
            }
        by {
            assert(pre.disk.requests.contains_key(req_id));
            assert(post.disk.requests[req_id] == pre.disk.requests[req_id]);
            if post.disk.requests[req_id] is WriteReq
                && post.disk.requests[req_id]->to != spec_superblock_addr() {
                assert(journal_image_request_writeback_disjoint_at(pre, durable_image, req_id));
                assert(!journal_image_static_domain_i(pre, durable_image).contains(
                    post.disk.requests[req_id]->to,
                ));
                assert(!journal_image_static_domain_i(post, durable_image).contains(
                    post.disk.requests[req_id]->to,
                ));
                if another_atomic_superblock_write_pending(post) {
                    assert(pre.program.state.in_flight is Some);
                    assert(another_atomic_superblock_write_pending(pre));
                    let frozen_image = pre.program.state.atomic_inflight_superblock_i();
                    assert(post.program.state.atomic_inflight_superblock_i() == frozen_image);
                    assert(journal_image_request_writeback_disjoint_at(pre, frozen_image, req_id));
                    assert(!journal_image_static_domain_i(pre, frozen_image).contains(
                        post.disk.requests[req_id]->to,
                    ));
                    assert(!journal_image_static_domain_i(post, frozen_image).contains(
                        post.disk.requests[req_id]->to,
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
    assert(another_atomic_disk_refinement_invariants(post));
}

pub proof fn disk_internal_process_data_write_preserves_refinement_invariants(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    id: ID,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        post.program == pre.program,
        AsyncDisk::State::next_by(
            pre.disk,
            post.disk,
            DiskLabel::Internal{},
            AsyncDisk::Step::process_write(id),
        ),
        pre.disk.requests[id]->to != spec_superblock_addr(),
    ensures
        another_atomic_disk_refinement_invariants(post),
{
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    assert(AsyncDisk::State::next(pre.disk, post.disk, DiskLabel::Internal{}));
    assert(post.program.state == pre.program.state);
    assert(post.program.state.wf());
    assert(another_atomic_model_refinement_invariants(post.program.state));
    async_disk_inv_next(pre.disk, post.disk, DiskLabel::Internal{});
    async_disk_superblock_page_wf_preserved_by_internal(
        pre.program.state,
        pre.disk,
        post.disk,
    );
    assert(post.disk.inv());
    assert(async_disk_superblock_page_wf(post.disk.content));

    let req = pre.disk.requests[id];
    assert(pre.disk.requests.contains_key(id));
    assert(req is WriteReq);
    assert(req->to != spec_superblock_addr());
    assert(post.disk.content == pre.disk.content.insert(req->to, req->data));
    assert(post.disk.content[spec_superblock_addr()]
        == pre.disk.content[spec_superblock_addr()]);
    assert(durable_superblock_image_i(post) == durable_superblock_image_i(pre));

    assert(another_atomic_cache_disk_coupling(post.program.state, post.disk)) by {
        assert forall |pending_id: ID| #[trigger] post.program.state.outstanding_cache_reqs.contains_key(pending_id)
            implies disk_has_pending_id(post.disk, pending_id) by {
            assert(pre.program.state.outstanding_cache_reqs.contains_key(pending_id));
            assert(disk_has_pending_id(pre.disk, pending_id));
            disk_has_pending_id_preserved_by_internal(pre.disk, post.disk, pending_id);
        }
        assert forall |addr: Address| #[trigger] filled_cache_status(post.program.state.cache).contains_key(addr)
            && filled_cache_status(post.program.state.cache)[addr] == CachingDiskPageStatus::Clean
            && addr != spec_superblock_addr()
            implies {
                &&& post.disk.content.contains_key(addr)
                &&& post.disk.content[addr] == cache_filled_page(post.program.state.cache, addr)
            } by {
            assert(filled_cache_status(pre.program.state.cache).contains_key(addr));
            assert(filled_cache_status(pre.program.state.cache)[addr] == CachingDiskPageStatus::Clean);
            if addr == req->to {
                assert(another_atomic_cache_disk_request_wf(pre.program.state, pre.disk));
                assert(pre.program.state.outstanding_cache_reqs.contains_key(id));
                assert(pre.program.state.outstanding_cache_reqs[id] == req->to);
                assert(filled_cache_status(pre.program.state.cache)[req->to]
                    == CachingDiskPageStatus::Writeback);
                assert(false);
            } else {
                assert(post.disk.content[addr] == pre.disk.content[addr]);
                assert(another_atomic_cache_disk_coupling(pre.program.state, pre.disk));
                assert(pre.disk.content.contains_key(addr));
                assert(pre.disk.content[addr] == cache_filled_page(pre.program.state.cache, addr));
            }
        }
    }
    assert(another_atomic_superblock_disk_coupling(post.program.state, post.disk));
    superblock_write_request_wf_preserved_by_internal(
        post.program.state,
        pre.disk,
        post.disk,
    );
    cache_disk_request_wf_preserved_by_internal(
        post.program.state,
        pre.disk,
        post.disk,
    );
    assert(another_atomic_superblock_write_request_wf(post.program.state, post.disk));
    assert(another_atomic_cache_disk_request_wf(post.program.state, post.disk));
    assert(journal_image_writeback_disjoint(pre));
    assert(journal_dirty_writeback_pages_tracked(pre));
    assert(journal_projection_uses_live(pre));
    assert(journal_projection_uses_live(post));
    assert(pre.program.state.journal_metadata_loaded());
    assert(pre.program.state.outstanding_cache_reqs.contains_key(id));
    assert(pre.program.state.outstanding_cache_reqs[id] == req->to);
    assert(cache_filled_addr(pre.program.state.cache, req->to));
    assert(cache_filled_page(pre.program.state.cache, req->to) == req->data);
    assert(filled_cache_status(pre.program.state.cache).contains_key(req->to));
    assert(filled_cache_status(pre.program.state.cache)[req->to]
        == CachingDiskPageStatus::Writeback);
    let image = atomic_persistent_superblock_image_i(pre);
    assert(journal_image_request_writeback_disjoint_at(pre, image, id));
    journal_image_persistent_preserved_by_disjoint_write(
        pre,
        post,
        image,
        req->to,
        req->data,
    );
    assert(persistent_journal_image_i(post) == persistent_journal_image_i(pre));
    if pre.program.state.in_flight is Some {
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
    assert(persistent_journal_image_i(post).wf());
    assert(to_aus(journal_projection_addrs(post)) <= journal_projection_aus(post)) by {
        assert forall |au: AU| #[trigger] to_aus(journal_projection_addrs(post)).contains(au)
            implies journal_projection_aus(post).contains(au) by {
            if journal_projection_uses_live(post) {
                assert((to_aus(journal_projection_addrs(post))
                    + post.program.state.journal.loaded_index_aus()
                    + post.program.state.journal.mini_allocator.all_aus()).contains(au));
            } else if post.program.state.superblock_metadata_known() {
                assert(journal_projection_aus(post) == to_aus(journal_projection_addrs(post)));
            } else {
                assert(journal_projection_aus(post) == to_aus(journal_projection_addrs(post)));
            }
        }
    }
    assert(journal_disk_persistent_i(post).dom() <= addresses_in_aus(journal_projection_aus(post))) by {
        to_aus_domain(journal_projection_addrs(post));
        assert forall |addr: Address| #[trigger] journal_disk_persistent_i(post).dom().contains(addr)
            implies addresses_in_aus(journal_projection_aus(post)).contains(addr) by {
            assert(journal_disk_persistent_i(post).contains_key(addr));
            assert(project_persistent_by_addrs(post.disk, journal_persistent_projection_addrs(post))
                .contains_key(addr));
            assert(journal_persistent_projection_addrs(post).contains(addr));
            assert(journal_projection_addrs(post).contains(addr));
            assert(to_aus(journal_projection_addrs(post)).contains(addr.au));
            assert(journal_projection_aus(post).contains(addr.au));
        }
    }
    assert(journal_disk_cache_i(post).dom() <= addresses_in_aus(journal_projection_aus(post))) by {
        to_aus_domain(journal_projection_addrs(post));
        assert forall |addr: Address| #[trigger] journal_disk_cache_i(post).dom().contains(addr)
            implies addresses_in_aus(journal_projection_aus(post)).contains(addr) by {
            assert(journal_disk_cache_i(post).contains_key(addr));
            assert(project_cache_pages_by_addrs(post.program.state.cache, journal_projection_addrs(post))
                .contains_key(addr));
            assert(journal_projection_addrs(post).contains(addr));
            assert(to_aus(journal_projection_addrs(post)).contains(addr.au));
            assert(journal_projection_aus(post).contains(addr.au));
        }
    }
    assert(journal_disk_status_i(post).dom() <= addresses_in_aus(journal_projection_aus(post))) by {
        to_aus_domain(journal_projection_addrs(post));
        assert forall |addr: Address| #[trigger] journal_disk_status_i(post).dom().contains(addr)
            implies addresses_in_aus(journal_projection_aus(post)).contains(addr) by {
            assert(journal_disk_status_i(post).contains_key(addr));
            assert(project_cache_status_by_addrs(post.program.state.cache, journal_projection_addrs(post))
                .contains_key(addr));
            assert(journal_projection_addrs(post).contains(addr));
            assert(to_aus(journal_projection_addrs(post)).contains(addr.au));
            assert(journal_projection_aus(post).contains(addr.au));
        }
    }
    assert(persistent_journal_image_i(post).persistent.dom()
        <= addresses_in_aus(journal_projection_aus(post)));
    if frozen_journal_image_i(post) is Some {
        assert(post.program.state.in_flight is Some);
        assert(pre.program.state.in_flight is Some);
        assert(journal_inflight_projection_wf(pre));
        assert(post.program.state.journal.loaded_index_aus()
            == pre.program.state.journal.loaded_index_aus());
        assert(journal_projection_uses_live(pre));
        assert(journal_projection_uses_live(post));
        assert(frozen_journal_image_i(post) == frozen_journal_image_i(pre));
        assert(frozen_journal_image_i(pre).unwrap().persistent.dom()
            <= addresses_in_aus(pre.program.state.journal.loaded_index_aus()));
        assert(frozen_journal_image_i(post).unwrap().persistent.dom()
            <= addresses_in_aus(journal_projection_aus(post)));
    }
    assert(journal_projection_tight(post));
    assert(journal_projection_uses_shared_async_disk(post));
    assert(journal_inflight_projection_wf(post)) by {
        if post.program.state.in_flight is Some {
            assert(pre.program.state.in_flight is Some);
            assert(journal_inflight_projection_wf(pre));
            assert(journal_projection_uses_live(pre));
            assert(journal_projection_uses_live(post));
            assert(frozen_journal_image_i(post) == frozen_journal_image_i(pre));
            assert(post.program.state.journal.loaded_index_aus()
                == pre.program.state.journal.loaded_index_aus());
        }
    }
    assert(journal_dirty_writeback_pages_tracked(post)) by {
        assert forall |addr: Address| #[trigger] filled_cache_status(post.program.state.cache).contains_key(addr)
            && (filled_cache_status(post.program.state.cache)[addr] == CachingDiskPageStatus::Dirty
                || filled_cache_status(post.program.state.cache)[addr] == CachingDiskPageStatus::Writeback)
            && post.program.state.journal_owned_aus().contains(addr.au)
            implies mini_allocator_allocated_addrs(post.program.state.journal.mini_allocator).contains(addr) by {
            assert(filled_cache_status(pre.program.state.cache).contains_key(addr));
            assert(filled_cache_status(pre.program.state.cache)[addr]
                == filled_cache_status(post.program.state.cache)[addr]);
            assert(pre.program.state.journal_owned_aus().contains(addr.au));
            assert(journal_dirty_writeback_pages_tracked(pre));
            assert(post.program.state.journal.mini_allocator
                == pre.program.state.journal.mini_allocator);
        }
    }
    assert(journal_projection_addrs(post) =~= journal_projection_addrs(pre)) by {
        assert(post.program.state == pre.program.state);
        assert(journal_projection_uses_live(pre));
        assert(journal_projection_uses_live(post));
    }
    assert(journal_projection_aus(post) =~= journal_projection_aus(pre)) by {
        assert(post.program.state == pre.program.state);
        assert(journal_projection_addrs(post) =~= journal_projection_addrs(pre));
        assert(journal_projection_uses_live(pre));
        assert(journal_projection_uses_live(post));
    }
    assert(journal_image_projection_domain_i(post, atomic_persistent_superblock_image_i(post))
        <= addresses_in_aus(journal_projection_aus(post))) by {
        assert(atomic_persistent_superblock_image_i(post)
            == atomic_persistent_superblock_image_i(pre));
        assert(journal_image_projection_domain_i(
            post,
            atomic_persistent_superblock_image_i(post),
        ) =~= journal_image_projection_domain_i(
            pre,
            atomic_persistent_superblock_image_i(pre),
        ));
        assert(journal_component_refinement_inv(pre));
        assert(journal_image_projection_domain_i(
            pre,
            atomic_persistent_superblock_image_i(pre),
        ) <= addresses_in_aus(journal_projection_aus(pre)));
        assert(journal_projection_aus(post) =~= journal_projection_aus(pre));
    }
    if post.program.state.in_flight is Some {
        assert(pre.program.state.in_flight is Some);
        assert(post.program.state.atomic_inflight_superblock_i()
            == pre.program.state.atomic_inflight_superblock_i());
        assert(journal_image_projection_domain_i(
            post,
            post.program.state.atomic_inflight_superblock_i(),
        ) =~= journal_image_projection_domain_i(
            pre,
            pre.program.state.atomic_inflight_superblock_i(),
        ));
        assert(journal_image_projection_domain_i(
            post,
            post.program.state.atomic_inflight_superblock_i(),
        ) <= addresses_in_aus(journal_projection_aus(post))) by {
            assert(journal_component_refinement_inv(pre));
            assert(journal_image_projection_domain_i(
                pre,
                pre.program.state.atomic_inflight_superblock_i(),
            ) <= addresses_in_aus(journal_projection_aus(pre)));
            assert(journal_projection_aus(post) =~= journal_projection_aus(pre));
        }
    }
    assert(journal_caching_disk_i(post).inv()) by {
        let cd = journal_caching_disk_i(post);
        assert(cd.status.dom() =~= cd.cache.dom()) by {
            assert forall |addr: Address| #[trigger] cd.status.dom().contains(addr)
                implies cd.cache.dom().contains(addr) by {
                assert(journal_disk_status_i(post).contains_key(addr));
                assert(project_cache_status_by_addrs(
                    post.program.state.cache,
                    journal_projection_addrs(post),
                ).contains_key(addr));
                assert(journal_projection_addrs(post).contains(addr));
                assert(filled_cache_status(post.program.state.cache).contains_key(addr));
                assert(cache_filled_addr(post.program.state.cache, addr));
                assert(filled_cache_pages(post.program.state.cache).contains_key(addr));
                assert(project_cache_pages_by_addrs(
                    post.program.state.cache,
                    journal_projection_addrs(post),
                ).contains_key(addr));
            }
            assert forall |addr: Address| #[trigger] cd.cache.dom().contains(addr)
                implies cd.status.dom().contains(addr) by {
                assert(journal_disk_cache_i(post).contains_key(addr));
                assert(project_cache_pages_by_addrs(
                    post.program.state.cache,
                    journal_projection_addrs(post),
                ).contains_key(addr));
                assert(journal_projection_addrs(post).contains(addr));
                assert(filled_cache_pages(post.program.state.cache).contains_key(addr));
                assert(cache_filled_addr(post.program.state.cache, addr));
                assert(filled_cache_status(post.program.state.cache).contains_key(addr));
                assert(project_cache_status_by_addrs(
                    post.program.state.cache,
                    journal_projection_addrs(post),
                ).contains_key(addr));
            }
        }
        assert forall |addr: Address| #[trigger] cd.status.contains_key(addr)
            && cd.status[addr] == CachingDiskPageStatus::Clean implies {
                &&& cd.persistent.contains_key(addr)
                &&& cd.persistent[addr] == cd.cache[addr]
            } by {
            assert(project_cache_status_by_addrs(
                post.program.state.cache,
                journal_projection_addrs(post),
            ).contains_key(addr));
            assert(project_cache_status_by_addrs(
                post.program.state.cache,
                journal_projection_addrs(post),
            )[addr] == CachingDiskPageStatus::Clean);
            assert(journal_projection_addrs(post).contains(addr));
            assert(filled_cache_status(post.program.state.cache).contains_key(addr));
            assert(filled_cache_status(post.program.state.cache)[addr]
                == CachingDiskPageStatus::Clean);
            if addr == req->to {
                assert(filled_cache_status(pre.program.state.cache).contains_key(req->to));
                assert(filled_cache_status(pre.program.state.cache)[req->to]
                    == CachingDiskPageStatus::Writeback);
                assert(filled_cache_status(post.program.state.cache)[addr]
                    == CachingDiskPageStatus::Writeback);
                assert(false);
            }
            assert(addr != spec_superblock_addr()) by {
                if addr == spec_superblock_addr() {
                    assert(AnotherAtomicState::reserved_aus().contains(addr.au));
                    assert(addresses_in_aus(AnotherAtomicState::reserved_aus()).contains(addr));
                    assert(!journal_projection_addrs(post).contains(addr));
                    assert(false);
                }
            }
            assert(journal_persistent_projection_addrs(post).contains(addr));
            assert(project_persistent_by_addrs(
                post.disk,
                journal_persistent_projection_addrs(post),
            ).contains_key(addr));
            assert(cd.persistent.contains_key(addr));
            assert(another_atomic_cache_disk_coupling(post.program.state, post.disk));
            assert(post.disk.content.contains_key(addr));
            assert(post.disk.content[addr] == cache_filled_page(post.program.state.cache, addr));
            assert(cd.persistent[addr] == post.disk.content[addr]);
            assert(cd.cache[addr] == cache_filled_page(post.program.state.cache, addr));
        }
    }
    assert(journal_caching_disk_i(post).visible() =~= journal_caching_disk_i(pre).visible()) by {
        assert_maps_equal!(
            journal_caching_disk_i(post).visible(),
            journal_caching_disk_i(pre).visible(),
            addr => {
                if addr == req->to {
                    if journal_caching_disk_i(post).visible().contains_key(addr) {
                        assert(cache_filled_addr(pre.program.state.cache, addr));
                        assert(filled_cache_pages(pre.program.state.cache).contains_key(addr));
                        assert(filled_cache_pages(pre.program.state.cache)[addr] == req->data);
                        assert(filled_cache_pages(post.program.state.cache).contains_key(addr));
                        assert(filled_cache_pages(post.program.state.cache)[addr] == req->data);
                    }
                    if journal_caching_disk_i(pre).visible().contains_key(addr) {
                        assert(cache_filled_addr(pre.program.state.cache, addr));
                        assert(filled_cache_pages(pre.program.state.cache).contains_key(addr));
                        assert(filled_cache_pages(pre.program.state.cache)[addr] == req->data);
                        assert(filled_cache_pages(post.program.state.cache).contains_key(addr));
                        assert(filled_cache_pages(post.program.state.cache)[addr] == req->data);
                    }
                } else {
                    assert(post.disk.content[addr] == pre.disk.content[addr]);
                }
            }
        );
    }
    assert(journal_index_aus_have_unique_lsns(post)) by {
        if !post.program.state.client_ready() && journal_projection_uses_live(post) {
            assert(post.program.state.journal.mini_allocator
                == crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty());
            assert(!post.program.state.journal_owned_aus().contains(req->to.au)) by {
                if post.program.state.journal_owned_aus().contains(req->to.au) {
                    assert(pre.program.state.journal_owned_aus().contains(req->to.au));
                    assert(journal_dirty_writeback_pages_tracked(pre));
                    assert(mini_allocator_allocated_addrs(
                        pre.program.state.journal.mini_allocator,
                    ).contains(req->to));
                    assert(pre.program.state.journal.mini_allocator
                        == crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty());
                    assert(!pre.program.state.journal.mini_allocator.allocs.contains_key(req->to.au));
                    assert(!mini_allocator_allocated_addrs(
                        pre.program.state.journal.mini_allocator,
                    ).contains(req->to));
                    assert(false);
                }
            }
            assert(journal_index_aus_have_unique_lsns(pre));
            let journal = post.program.state.journal.journal;
            let snapshot = journal.snapshot;
            let post_dv = DiskView{
                boundary_lsn: snapshot.boundary_lsn,
                entries: to_journal_records(post.disk.content),
            };
            let pre_dv = DiskView{
                boundary_lsn: snapshot.boundary_lsn,
                entries: to_journal_records(pre.disk.content),
            };
            let index = journal.status.unwrap().lsn_au_index;
            assert(index.values() == post.program.state.journal.loaded_index_aus());
            assert(index.values() <= post.program.state.journal_owned_aus()) by {
                assert(post.program.state.journal.loaded_index_aus()
                    <= post.program.state.journal.owned_aus());
                assert(post.program.state.journal.owned_aus()
                    == post.program.state.journal_owned_aus());
            }
            assert forall |addr1: Address, addr2: Address, lsn: LSN|
                #![trigger
                    post_dv.entries[addr1].contains_lsn(snapshot.boundary_lsn, lsn),
                    post_dv.entries[addr2].contains_lsn(snapshot.boundary_lsn, lsn)
                ]
                {
                    &&& post_dv.entries.contains_key(addr1)
                    &&& post_dv.entries.contains_key(addr2)
                    &&& index.values().contains(addr1.au)
                    &&& index.values().contains(addr2.au)
                    &&& post_dv.entries[addr1].contains_lsn(snapshot.boundary_lsn, lsn)
                    &&& post_dv.entries[addr2].contains_lsn(snapshot.boundary_lsn, lsn)
                } implies addr1 == addr2 by {
                assert(addr1 != req->to) by {
                    if addr1 == req->to {
                        assert(post.program.state.journal_owned_aus().contains(addr1.au));
                        assert(false);
                    }
                }
                assert(addr2 != req->to) by {
                    if addr2 == req->to {
                        assert(post.program.state.journal_owned_aus().contains(addr2.au));
                        assert(false);
                    }
                }
                assert(post.disk.content[addr1] == pre.disk.content[addr1]);
                assert(post.disk.content[addr2] == pre.disk.content[addr2]);
                assert(pre_dv.entries.contains_key(addr1));
                assert(pre_dv.entries.contains_key(addr2));
                assert(pre_dv.entries[addr1] == post_dv.entries[addr1]);
                assert(pre_dv.entries[addr2] == post_dv.entries[addr2]);
                assert(pre_dv.entries[addr1].contains_lsn(snapshot.boundary_lsn, lsn));
                assert(pre_dv.entries[addr2].contains_lsn(snapshot.boundary_lsn, lsn));
                assert(journal_index_aus_have_unique_lsns(pre));
            }
        }
    }
    assert(journal_owned_disk_records_do_not_impersonate_index(post)) by {
        if !post.program.state.client_ready() && journal_projection_uses_live(post) {
            assert(post.program.state.journal_metadata_loaded());
            assert(post.program.state.journal.mini_allocator
                == crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty());
            assert(!post.program.state.journal_owned_aus().contains(req->to.au)) by {
                if post.program.state.journal_owned_aus().contains(req->to.au) {
                    assert(pre.program.state.journal_owned_aus().contains(req->to.au));
                    assert(journal_dirty_writeback_pages_tracked(pre));
                    assert(mini_allocator_allocated_addrs(
                        pre.program.state.journal.mini_allocator,
                    ).contains(req->to));
                    assert(pre.program.state.journal.mini_allocator
                        == crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty());
                    assert(!pre.program.state.journal.mini_allocator.allocs.contains_key(req->to.au));
                    assert(!mini_allocator_allocated_addrs(
                        pre.program.state.journal.mini_allocator,
                    ).contains(req->to));
                    assert(false);
                }
            }
            assert(journal_loaded_index_matches_persistent_subdisk(post)) by {
                assert(journal_loaded_index_matches_persistent_subdisk(pre));
                assert(persistent_journal_image_i(post) == persistent_journal_image_i(pre));
                assert(post.program.state.journal == pre.program.state.journal);
            }
            assert(journal_index_aus_have_unique_lsns(post));
            journal_unique_index_aus_imply_no_impersonation(post);
        }
    }
    assert(branch_raw_visible_i(post) =~= branch_raw_visible_i(pre)) by {
        assert_maps_equal!(branch_raw_visible_i(post), branch_raw_visible_i(pre), addr => {
            assert(filled_cache_pages(post.program.state.cache)
                == filled_cache_pages(pre.program.state.cache));
            if addr == req->to {
                assert(cache_filled_addr(pre.program.state.cache, req->to));
                assert(filled_cache_pages(pre.program.state.cache).contains_key(req->to));
                assert(filled_cache_pages(post.program.state.cache).contains_key(req->to));
                assert(filled_cache_pages(pre.program.state.cache)[req->to] == req->data);
                assert(filled_cache_pages(post.program.state.cache)[req->to] == req->data);
            } else {
                assert(post.disk.content[addr] == pre.disk.content[addr]);
            }
        });
    }
    assert(branch_visible_nodes_i(post) == branch_visible_nodes_i(pre));
    assert(branch_interpreted_summary_i(post) == branch_interpreted_summary_i(pre));
    assert(branch_projection_summary_i(post) == branch_projection_summary_i(pre));
    assert(branch_projection_addrs(post) == branch_projection_addrs(pre));
    assert(branch_disk_cache_i(post) == branch_disk_cache_i(pre));
    assert(branch_disk_status_i(post) == branch_disk_status_i(pre));
    assert(branch_caching_disk_i(post).cache == branch_caching_disk_i(pre).cache);
    assert(branch_caching_disk_i(post).status == branch_caching_disk_i(pre).status);
    assert(branch_caching_disk_i(post).visible() == branch_caching_disk_i(pre).visible()) by {
        assert_maps_equal!(
            branch_caching_disk_i(post).visible(),
            branch_caching_disk_i(pre).visible(),
            addr => {
                if addr == req->to {
                    if branch_caching_disk_i(post).cache.contains_key(addr) {
                        assert(branch_caching_disk_i(pre).cache.contains_key(addr));
                        assert(branch_caching_disk_i(post).cache[addr]
                            == branch_caching_disk_i(pre).cache[addr]);
                    }
                } else {
                    if branch_caching_disk_i(post).persistent.contains_key(addr) {
                        assert(post.disk.content[addr] == pre.disk.content[addr]);
                    }
                    if branch_caching_disk_i(pre).persistent.contains_key(addr) {
                        assert(post.disk.content[addr] == pre.disk.content[addr]);
                    }
                }
            }
        );
    }
    assert(branch_image_writeback_disjoint(pre));
    let durable_branch_image = atomic_persistent_superblock_image_i(pre);
    assert(branch_image_request_writeback_disjoint_at(pre, durable_branch_image, id));
    if pre.program.state.superblock_metadata_known()
        && atomic_branch_metadata_loaded_flag(pre.program.state.branch)
    {
        assert(atomic_persistent_superblock_image_i(post)
            == atomic_persistent_superblock_image_i(pre));
        assert(atomic_branch_metadata_loaded_flag(post.program.state.branch));
        assert(persistent_branch_image_i(post) == persistent_branch_image_i(pre)) by {
            let frozen = CachingDiskBranchModule::CachingDiskBranchFrozenImage{
                sealed_roots: durable_branch_image.branch_roots,
                seq_end: durable_branch_image.branch_seq_end,
            };
            assert(branch_caching_disk_state_i(post).visible_image_for_metadata(frozen)
                == branch_caching_disk_state_i(pre).visible_image_for_metadata(frozen)) by {
                assert(branch_caching_disk_i(post).visible() == branch_caching_disk_i(pre).visible());
                assert(post.program.state == pre.program.state);
            }
        }
        assert(branch_image_static_domain_i(post, durable_branch_image)
            == branch_image_static_domain_i(pre, durable_branch_image)) by {
            let frozen = CachingDiskBranchModule::CachingDiskBranchFrozenImage{
                sealed_roots: durable_branch_image.branch_roots,
                seq_end: durable_branch_image.branch_seq_end,
            };
            assert(branch_caching_disk_state_i(post).visible_image_for_metadata(frozen)
                == branch_caching_disk_state_i(pre).visible_image_for_metadata(frozen)) by {
                assert(branch_caching_disk_i(post).visible() == branch_caching_disk_i(pre).visible());
                assert(post.program.state == pre.program.state);
            }
        }
    }
    if pre.program.state.in_flight is Some {
        let inflight_branch_image = pre.program.state.atomic_inflight_superblock_i();
        assert(branch_image_request_writeback_disjoint_at(pre, inflight_branch_image, id));
        if pre.program.state.superblock_metadata_known()
            && atomic_branch_metadata_loaded_flag(pre.program.state.branch)
        {
            assert(branch_image_static_domain_i(post, inflight_branch_image)
                == branch_image_static_domain_i(pre, inflight_branch_image)) by {
                let frozen = CachingDiskBranchModule::CachingDiskBranchFrozenImage{
                    sealed_roots: inflight_branch_image.branch_roots,
                    seq_end: inflight_branch_image.branch_seq_end,
                };
                assert(branch_caching_disk_state_i(post).visible_image_for_metadata(frozen)
                    == branch_caching_disk_state_i(pre).visible_image_for_metadata(frozen)) by {
                    assert(branch_caching_disk_i(post).visible() == branch_caching_disk_i(pre).visible());
                    assert(post.program.state == pre.program.state);
                }
            }
        }
    }
    if pre.program.state.superblock_metadata_known()
        && atomic_branch_metadata_loaded_flag(pre.program.state.branch)
    {
        assert(branch_image_writeback_disjoint(post)) by {
            assert forall |req_id: ID| #[trigger] post.disk.requests.contains_key(req_id)
                implies {
                    &&& branch_image_request_writeback_disjoint_at(
                        post,
                        atomic_persistent_superblock_image_i(post),
                        req_id,
                    )
                    &&& post.program.state.in_flight is Some ==>
                        branch_image_request_writeback_disjoint_at(
                            post,
                            post.program.state.atomic_inflight_superblock_i(),
                            req_id,
                        )
                } by {
                assert(pre.disk.requests.contains_key(req_id));
                assert(post.disk.requests[req_id] == pre.disk.requests[req_id]);
                if post.disk.requests[req_id] is WriteReq
                    && post.disk.requests[req_id]->to != spec_superblock_addr() {
                    assert(branch_image_request_writeback_disjoint_at(
                        pre,
                        atomic_persistent_superblock_image_i(pre),
                        req_id,
                    ));
                    assert(atomic_persistent_superblock_image_i(post)
                        == atomic_persistent_superblock_image_i(pre));
                    assert(branch_image_static_domain_i(
                        post,
                        atomic_persistent_superblock_image_i(post),
                    ) == branch_image_static_domain_i(
                        pre,
                        atomic_persistent_superblock_image_i(pre),
                    ));
                    if post.program.state.in_flight is Some {
                        assert(pre.program.state.in_flight is Some);
                        assert(post.program.state.atomic_inflight_superblock_i()
                            == pre.program.state.atomic_inflight_superblock_i());
                        assert(branch_image_request_writeback_disjoint_at(
                            pre,
                            pre.program.state.atomic_inflight_superblock_i(),
                            req_id,
                        ));
                        assert(branch_image_static_domain_i(
                            post,
                            post.program.state.atomic_inflight_superblock_i(),
                        ) == branch_image_static_domain_i(
                            pre,
                            pre.program.state.atomic_inflight_superblock_i(),
                        ));
                    }
                }
            }
        }
    }
    if pre.program.state.superblock_metadata_known() {
        assert(branch_caching_disk_i(post).inv()) by {
            assert(branch_component_refinement_inv(pre));
            assert(crash_aware_caching_disk_branch_i(pre).ephemeral is Known);
            assert(crash_aware_caching_disk_branch_i(pre).ephemeral->v
                == branch_caching_disk_state_i(pre));
            assert(branch_caching_disk_state_i(pre).disk == branch_caching_disk_i(pre));
            assert(branch_caching_disk_state_i(pre).inv());
            assert(branch_caching_disk_i(pre).inv());
            assert(branch_caching_disk_i(post).status.dom() =~= branch_caching_disk_i(post).cache.dom());
            assert forall |addr: Address| #[trigger] branch_caching_disk_i(post).status.contains_key(addr)
                && branch_caching_disk_i(post).status[addr] == CachingDiskPageStatus::Clean
                implies {
                    &&& branch_caching_disk_i(post).persistent.contains_key(addr)
                    &&& branch_caching_disk_i(post).persistent[addr] == branch_caching_disk_i(post).cache[addr]
                } by {
                if addr == req->to {
                    assert(filled_cache_status(pre.program.state.cache).contains_key(req->to));
                    assert(filled_cache_status(pre.program.state.cache)[req->to]
                        == CachingDiskPageStatus::Writeback);
                    assert(branch_caching_disk_i(post).status[addr]
                        == branch_caching_disk_i(pre).status[addr]);
                    assert(branch_caching_disk_i(pre).status[addr]
                        == CachingDiskPageStatus::Writeback);
                    assert(false);
                } else {
                    assert(branch_caching_disk_i(pre).status.contains_key(addr));
                    assert(branch_caching_disk_i(pre).status[addr] == CachingDiskPageStatus::Clean);
                    assert(branch_caching_disk_i(pre).persistent.contains_key(addr));
                    assert(branch_caching_disk_i(pre).persistent[addr]
                        == branch_caching_disk_i(pre).cache[addr]);
                    assert(branch_caching_disk_i(post).persistent[addr]
                        == branch_caching_disk_i(pre).persistent[addr]);
                    assert(branch_caching_disk_i(post).cache[addr]
                        == branch_caching_disk_i(pre).cache[addr]);
                }
            }
        }
    }
    assert(atomic_superblock_prepared_i(post) == atomic_superblock_prepared_i(pre)) by {
        if pre.program.state.in_flight is Some {
            let super_id = pre.program.state.in_flight.unwrap().req_id;
            assert(super_id != id) by {
                if super_id == id {
                    assert(another_atomic_inflight_cache_id_disjoint(pre.program.state));
                    assert(pre.program.state.outstanding_cache_reqs.contains_key(id));
                    assert(false);
                }
            }
            if pre.disk.requests.contains_key(super_id) {
                assert(post.disk.requests.contains_key(super_id));
                assert(post.disk.requests[super_id] == pre.disk.requests[super_id]);
            }
            if pre.disk.responses.contains_key(super_id) {
                assert(post.disk.responses.contains_key(super_id));
                assert(post.disk.responses[super_id] == pre.disk.responses[super_id]);
            }
            if post.disk.requests.contains_key(super_id) {
                assert(pre.disk.requests.contains_key(super_id));
                assert(post.disk.requests[super_id] == pre.disk.requests[super_id]);
            }
            if post.disk.responses.contains_key(super_id) {
                assert(pre.disk.responses.contains_key(super_id));
                assert(post.disk.responses[super_id] == pre.disk.responses[super_id]);
            }
            assert(post.disk.content[spec_superblock_addr()]
                == pre.disk.content[spec_superblock_addr()]);
        }
    }
    if pre.program.state.superblock_metadata_known() {
        if atomic_branch_metadata_loaded_flag(pre.program.state.branch) {
            assert(crash_aware_caching_disk_branch_i(post).persistent
                == crash_aware_caching_disk_branch_i(pre).persistent) by {
                assert(persistent_branch_image_i(post) == persistent_branch_image_i(pre));
            }
        } else {
            assert(!atomic_branch_metadata_loaded_flag(post.program.state.branch));
            let pre_p = crash_aware_caching_disk_branch_i(pre).persistent;
            let post_p = crash_aware_caching_disk_branch_i(post).persistent;
            let image = atomic_persistent_superblock_image_i(pre);
            assert(atomic_persistent_superblock_image_i(post) == image);
            assert(pre_p == branch_image_i(pre, image));
            assert(post_p == branch_image_i(post, image));
            assert(!branch_image_projection_addrs_i(pre.disk.content, image.branch_roots).contains(req->to)) by {
                assert(branch_image_request_writeback_disjoint_at(pre, image, id));
                assert(branch_image_static_domain_i(pre, image)
                    == branch_image_projection_addrs_i(pre.disk.content, image.branch_roots));
            }
            sealed_roots_pointer_domain_preserved_by_write_outside(
                pre.disk.content,
                image.branch_roots,
                req->to,
                req->data,
            );
            assert(branch_image_projection_addrs_i(post.disk.content, image.branch_roots)
                == branch_image_projection_addrs_i(pre.disk.content, image.branch_roots));
            assert(post_p.persistent == pre_p.persistent) by {
                assert_maps_equal!(
                    post_p.persistent,
                    pre_p.persistent,
                    addr => {
                        if branch_image_projection_addrs_i(pre.disk.content, image.branch_roots).contains(addr) {
                            assert(addr != req->to);
                            assert(post.disk.content[addr] == pre.disk.content[addr]);
                        }
                    }
                );
            }
            assert(post_p == pre_p);
        }
        assert(crash_aware_caching_disk_branch_i(post).frozen
            == crash_aware_caching_disk_branch_i(pre).frozen);
        assert(crash_aware_caching_disk_branch_i(post).prepared
            == crash_aware_caching_disk_branch_i(pre).prepared);
        if crash_aware_caching_disk_branch_i(post).ephemeral is Known {
            assert(crash_aware_caching_disk_branch_i(pre).ephemeral is Known);
            assert(branch_caching_disk_i(post).visible() == branch_caching_disk_i(pre).visible());
            let persistent_frozen = CachingDiskBranchModule::CachingDiskBranchFrozenImage{
                sealed_roots: crash_aware_caching_disk_branch_i(post).persistent.sealed_roots,
                seq_end: crash_aware_caching_disk_branch_i(post).persistent.seq_end,
            };
            assert(persistent_frozen == CachingDiskBranchModule::CachingDiskBranchFrozenImage{
                sealed_roots: crash_aware_caching_disk_branch_i(pre).persistent.sealed_roots,
                seq_end: crash_aware_caching_disk_branch_i(pre).persistent.seq_end,
            });
            assert(crash_aware_caching_disk_branch_i(post).ephemeral->v
                .visible_image_for_metadata(persistent_frozen)
                == crash_aware_caching_disk_branch_i(pre).ephemeral->v
                .visible_image_for_metadata(persistent_frozen)) by {
                assert(crash_aware_caching_disk_branch_i(post).ephemeral->v.disk.visible()
                    == crash_aware_caching_disk_branch_i(pre).ephemeral->v.disk.visible());
                assert(crash_aware_caching_disk_branch_i(post).ephemeral->v.sealed_roots
                    == crash_aware_caching_disk_branch_i(pre).ephemeral->v.sealed_roots);
                assert(crash_aware_caching_disk_branch_i(post).ephemeral->v.seq_end
                    == crash_aware_caching_disk_branch_i(pre).ephemeral->v.seq_end);
            }
            assert(crash_aware_caching_disk_branch_i(post).ephemeral->v
                .visible_image_for_metadata(persistent_frozen).sealed_stack_i()
                == crash_aware_caching_disk_branch_i(pre).ephemeral->v
                .visible_image_for_metadata(persistent_frozen).sealed_stack_i());
            assert(crash_aware_caching_disk_branch_i(post).persistent_matches_ephemeral()) by {
                assert(crash_aware_caching_disk_branch_i(pre).persistent_matches_ephemeral());
            }
        }
    }
    assert(branch_component_refinement_inv(post));
    assert(journal_component_refinement_inv(post));
    assert(another_atomic_disk_refinement_invariants(post));
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn program_internal_read_for_recovery_preserves_refinement(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    addr: Address,
    keys: Seq<Key>,
    msgs: Seq<Message>,
    receipt: LoadedPathReceipt,
    init_root: Option<Address>,
    journal_reads: Map<Address, RawPage>,
    branch_reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    branch: AtomicBranchState::State,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        AnotherAtomicState::read_for_recovery(
            pre.program.state,
            post.program.state,
            addr,
            keys,
            msgs,
            receipt,
            init_root,
            journal_reads,
            branch_reads,
            writes,
            branch,
        ),
        post.disk == pre.disk,
    ensures
        another_atomic_disk_refinement_invariants(post),
{
    let reads = journal_reads.union_prefer_right(branch_reads);
    let branch_lbl = AtomicBranchState::Label::Append{
        keys,
        msgs,
        receipt,
        init_root,
        read_nodes: crate::implementation::AnotherAtomicState_v::to_branch_nodes(branch_reads),
        write_nodes: crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes),
    };
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
    cache_disk_coupling_preserved_by_cache_access(pre, post, reads, writes);

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
        journal_reads,
        branch_reads,
        writes,
        branch,
    );
    AtomicBranchState::State::append_effect(
        pre.program.state.branch,
        branch,
        branch_lbl,
    );
    AtomicBranchState::State::append_support_effect(
        pre.program.state.branch,
        branch,
        branch_lbl,
    );
    AtomicBranchState::State::wf_next(
        pre.program.state.branch,
        branch,
        branch_lbl,
    );
    AtomicBranchState::State::append_preserves_owned_aus(
        pre.program.state.branch,
        branch,
        branch_lbl,
    );
    assert(pre.program.state.recovery_metadata_wf());
    assert(pre.program.state.branch_metadata_loaded());
    atomic_branch_metadata_loaded_flag_from_metadata_loaded(pre.program.state.branch);
    assert(atomic_branch_metadata_loaded_flag(pre.program.state.branch));
    assert(atomic_branch_metadata_loaded_flag(branch)) by {
        assert(branch.image == pre.program.state.branch.image);
        assert(branch.branch_summary == pre.program.state.branch.branch_summary);
    }
    cache_access_reads_available_in_branch_projection_from_support(
        pre,
        post,
        branch_reads,
        reads,
        writes,
    );
    assert(branch_reads <= branch_disk_cache_i(pre));
    branch_projection_addrs_eq_atomic_support_addrs(pre);
    branch_projection_addrs_eq_atomic_support_addrs(post);
    assert(writes.dom() =~= crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes).dom());
    assert(branch_projection_addrs(pre) <= branch_projection_addrs(post)) by {
        assert(atomic_branch_support_addrs(pre.program.state.branch)
            <= atomic_branch_support_addrs(branch));
    }
    assert(writes.dom() <= branch_projection_addrs(post)) by {
        assert(crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes).dom()
            <= atomic_branch_support_addrs(branch));
    }
    assert(branch_projection_addrs(post) <= branch_projection_addrs(pre) + writes.dom()) by {
        assert(atomic_branch_support_addrs(branch)
            <= atomic_branch_support_addrs(pre.program.state.branch)
                + crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes).dom());
    }
    assert(branch_projection_aus(post) =~= branch_projection_aus(pre));
    assert(writes.dom() <= addresses_in_aus(branch_projection_aus(pre))) by {
        to_aus_domain(writes.dom());
        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
            implies addresses_in_aus(branch_projection_aus(pre)).contains(addr) by {
            assert(to_aus(writes.dom()).contains(addr.au));
            assert(pre.program.state.branch_owned_aus().contains(addr.au));
            assert(branch_projection_aus(pre).contains(addr.au));
        }
    }
    branch_append_refines(
        pre,
        post,
        keys,
        msgs,
        receipt,
        init_root,
        reads,
        branch_reads,
        writes,
        branch,
    );
    CrashAwareCachingDiskBranch::State::inv_next(
        crash_aware_caching_disk_branch_i(pre),
        crash_aware_caching_disk_branch_i(post),
        CrashAwareCachingDiskBranch::Label::Append{keys, msgs},
    );
    assert(persistent_branch_image_i(post) == persistent_branch_image_i(pre));
    assert(persistent_branch_image_i(post).wf());
    assert(branch_component_refinement_inv(post));

    branch_writes_disjoint_from_journal_static_domains(pre, writes);
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
    assert(post.program.state.journal == pre.program.state.journal);
    assert(post.program.state.branch == branch);
    assert(post.program.state.branch.wf());
    assert(post.program.state.branch.owned_aus()
        == pre.program.state.branch.owned_aus());
    assert(post.program.state.journal.owned_aus()
        == pre.program.state.journal.owned_aus());
    assert(post.program.state.component_owned_aus()
        == pre.program.state.component_owned_aus());
    assert(post.program.state.allocation_wf());
    assert(post.program.state.recovery_metadata_wf());
    assert(post.program.state.in_flight_agrees());
    assert(post.program.state.wf());
    branch_cache_access_preserves_journal_component_refinement(
        pre,
        post,
        reads,
        writes,
    );
    assert(journal_component_refinement_inv(post));
    assert(another_atomic_superblock_disk_coupling(post.program.state, post.disk));
    superblock_write_request_wf_preserved_by_unchanged_commit_components(
        pre.program.state,
        post.program.state,
        post.disk,
    );
    assert(another_atomic_superblock_write_request_wf(post.program.state, post.disk));
    assert(post.disk.inv());
    assert(async_disk_superblock_page_wf(post.disk.content));
    assert(another_atomic_model_refinement_invariants(post.program.state));
    assert(another_atomic_cache_disk_coupling(post.program.state, post.disk));
    assert(another_atomic_cache_disk_request_wf(post.program.state, post.disk));
    assert(journal_image_writeback_disjoint(post));
    assert(another_atomic_disk_refinement_invariants(post));
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
                    branch_writes_disjoint_from_journal_static_domains(pre, writes);
                    assert(pre.program.state.recovery_state is MetadataLoadComplete);
                    assert(pre.program.state.recovery_metadata_wf());
                    assert(pre.program.state.branch_metadata_loaded());
                    atomic_branch_metadata_loaded_flag_from_metadata_loaded(pre.program.state.branch);
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
                    client_ready_implies_atomic_branch_metadata_loaded_flag(pre.program.state);
                    assert(post.program.state.branch == pre.program.state.branch);
                    assert(atomic_branch_metadata_loaded_flag(post.program.state.branch));
                    loaded_branch_projection_unchanged(pre, post);
                    assert(atomic_branch_metadata_loaded_flag(pre.program.state.branch));
                    assert(branch_projection_aus(post) =~= branch_projection_aus(pre));
                    assert(branch_projection_addrs(post) =~= branch_projection_addrs(pre));
                    assert(branch_persistent_projection_addrs(post) =~= branch_persistent_projection_addrs(pre));
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
                        assert(post.program.state.branch.branch_summary
                            == Map::<AU, Set<AU>>::empty());
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
                    program_internal_cache_internal_preserves_bookkeeping(pre, post);
                    assert(another_atomic_disk_refinement_invariants(post));
                },
                InternalEvent::JournalLoadIndex{reads, discovered_aus} => {
                    assert(AnotherAtomicState::journal_load_index(
                        pre.program.state,
                        post.program.state,
                        reads,
                        discovered_aus,
                    ));
                    let journal_lbl = AtomicJournalState::Label::LoadIndex{
                        reads: to_journal_records(reads),
                        discovered_aus,
                    };
                    AtomicJournalState::State::wf_next(
                        pre.program.state.journal,
                        post.program.state.journal,
                        journal_lbl,
                    );
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
                            && filled_cache_status(post.program.state.cache)[addr] == CachingDiskPageStatus::Writeback
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
                    assert(post.program.state.branch == pre.program.state.branch);
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.program.state.persistent_image == pre.program.state.persistent_image);
                    assert(post.program.state.recovery_state == pre.program.state.recovery_state);
                    assert(!pre.program.state.client_ready()) by {
                        assert(pre.program.state.recovery_metadata_wf());
                        if pre.program.state.client_ready() {
                            assert(pre.program.state.recovery_state is RecoveryComplete);
                            assert(pre.program.state.journal_metadata_loaded());
                            assert(false);
                        }
                    }
                    assert(!post.program.state.client_ready()) by {
                        assert(post.program.state.recovery_state == pre.program.state.recovery_state);
                    }
                    superblock_write_request_wf_when_not_client_ready(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                    branch_component_refinement_inv_preserved_by_unchanged_branch_projection(
                        pre,
                        post,
                    );
                    assert(another_atomic_superblock_write_request_wf(
                        post.program.state,
                        post.disk,
                    ));
                    assert(branch_component_refinement_inv(post));
                },
                InternalEvent::ReadForRecovery{
                    addr,
                    keys,
                    msgs,
                    receipt,
                    init_root,
                    journal_reads,
                    branch_reads,
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
                        journal_reads,
                        branch_reads,
                        writes,
                        branch,
                    ));
                    program_internal_read_for_recovery_preserves_refinement(
                        pre,
                        post,
                        addr,
                        keys,
                        msgs,
                        receipt,
                        init_root,
                        journal_reads,
                        branch_reads,
                        writes,
                        branch,
                    );
                    assert(another_atomic_disk_refinement_invariants(post));
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
                    AtomicJournalState::State::wf_next(
                        pre.program.state.journal,
                        post.program.state.journal,
                        journal_lbl,
                    );
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
                            assert(pre.program.state.journal_metadata_loaded());
                            assert(pre.program.state.journal.journal.status is Some);
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
                    assert(post.program.state.branch == pre.program.state.branch);
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.program.state.journal.in_flight
                        == pre.program.state.journal.in_flight);
                    assert(post.program.state.branch.in_flight
                        == pre.program.state.branch.in_flight);
                    assert(post.program.state.persistent_image == pre.program.state.persistent_image);
                    assert(post.program.state.recovery_state == pre.program.state.recovery_state);
                    atomic_inflight_superblock_unchanged(pre.program.state, post.program.state);
                    assert(post.program.state.journal.journal.clean_watermark()
                        == pre.program.state.journal.journal.clean_watermark()) by {
                        assert(post.program.state.journal.journal.status.unwrap().clean_watermark_lsn
                            == pre.program.state.journal.journal.status.unwrap().clean_watermark_lsn);
                    }
                    if post.program.state.in_flight is Some
                        && post.disk.requests.contains_key(post.program.state.in_flight.unwrap().req_id)
                        && post.disk.requests[post.program.state.in_flight.unwrap().req_id] is WriteReq
                        && post.disk.requests[post.program.state.in_flight.unwrap().req_id]->to
                            == spec_superblock_addr() {
                        assert(another_atomic_superblock_write_request_wf(
                            pre.program.state,
                            pre.disk,
                        ));
                        assert(post.disk == pre.disk);
                        assert(AtomicJournalState::State::next(
                            pre.program.state.journal,
                            pre.program.state.journal,
                            AtomicJournalState::Label::CommitPrepared,
                        ));
                        assert(AtomicBranchState::State::next(
                            pre.program.state.branch,
                            pre.program.state.branch,
                            AtomicBranchState::Label::CommitPrepared,
                        ));
                        atomic_journal_commit_prepared_preserved(
                            pre.program.state.journal,
                            post.program.state.journal,
                        );
                        atomic_branch_commit_prepared_preserved(
                            pre.program.state.branch,
                            post.program.state.branch,
                        );
                    }
                    superblock_write_request_wf_preserved_by_prepared_components(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                    branch_component_refinement_inv_preserved_by_unchanged_branch_projection(
                        pre,
                        post,
                    );
                    assert(another_atomic_superblock_write_request_wf(
                        post.program.state,
                        post.disk,
                    ));
                    assert(branch_component_refinement_inv(post));
                },
                InternalEvent::ObserveCleanJournalAUs{aus} => {
                    assert(AnotherAtomicState::acknowledge_flushed_journal_aus(
                        pre.program.state,
                        post.program.state,
                        aus,
                    ));
                    let journal_lbl = AtomicJournalState::Label::ObserveCleanAUs{aus};
                    AtomicJournalState::State::wf_next(
                        pre.program.state.journal,
                        post.program.state.journal,
                        journal_lbl,
                    );
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
                        AtomicJournalState::Step::observe_clean_aus(new_journal) => {
                            assert(AtomicJournalState::State::observe_clean_aus(
                                pre.program.state.journal,
                                post.program.state.journal,
                                journal_lbl,
                                new_journal,
                            )) by {
                                reveal(AtomicJournalState::State::observe_clean_aus);
                            }
                            CachedJournal::State::observe_clean_aus_effect(
                                pre.program.state.journal.journal,
                                new_journal,
                                aus,
                            );
                            assert(post.program.state.journal.journal == new_journal);
                        },
                        _ => {
                            assert(false);
                        },
                    }
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
                    assert(post.program.state.journal_metadata_loaded()
                        == pre.program.state.journal_metadata_loaded());
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.program.state.journal.in_flight
                        == pre.program.state.journal.in_flight);
                    assert(post.program.state.branch.in_flight
                        == pre.program.state.branch.in_flight);
                    assert forall |addr: Address|
                        #[trigger] post.program.state.journal.mini_allocator.can_allocate(addr)
                        implies pre.program.state.journal.mini_allocator.can_allocate(addr) by {
                        assert(post.program.state.journal.mini_allocator
                            == pre.program.state.journal.mini_allocator);
                    }
                    journal_image_writeback_disjoint_preserved_by_unchanged_cache_disk_images(
                        pre,
                        post,
                    );
                    assert(journal_projection_aus(post) =~= journal_projection_aus(pre));
                    journal_observe_clean_aus_refines(pre, post, aus);
                    CrashAwareCachingDiskJournal::State::inv_next(
                        crash_aware_caching_disk_journal_i(pre),
                        crash_aware_caching_disk_journal_i(post),
                        CrashAwareCachingDiskJournal::Label::ObserveCleanAUs{aus},
                    );
                    assert(journal_component_refinement_inv(post));
                    assert(post.program.state.branch == pre.program.state.branch);
                    assert(post.program.state.persistent_image == pre.program.state.persistent_image);
                    assert(post.program.state.recovery_state == pre.program.state.recovery_state);
                    atomic_inflight_superblock_unchanged(pre.program.state, post.program.state);
                    if post.program.state.in_flight is Some
                        && post.disk.requests.contains_key(post.program.state.in_flight.unwrap().req_id)
                        && post.disk.requests[post.program.state.in_flight.unwrap().req_id] is WriteReq
                        && post.disk.requests[post.program.state.in_flight.unwrap().req_id]->to
                            == spec_superblock_addr() {
                        assert(another_atomic_superblock_write_request_wf(
                            pre.program.state,
                            pre.disk,
                        ));
                        assert(post.disk == pre.disk);
                        assert(AtomicJournalState::State::next(
                            pre.program.state.journal,
                            pre.program.state.journal,
                            AtomicJournalState::Label::CommitPrepared,
                        ));
                        assert(AtomicBranchState::State::next(
                            pre.program.state.branch,
                            pre.program.state.branch,
                            AtomicBranchState::Label::CommitPrepared,
                        ));
                        atomic_journal_commit_prepared_preserved(
                            pre.program.state.journal,
                            post.program.state.journal,
                        );
                        atomic_branch_commit_prepared_preserved(
                            pre.program.state.branch,
                            post.program.state.branch,
                        );
                    }
                    superblock_write_request_wf_preserved_by_prepared_components(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                    branch_component_refinement_inv_preserved_by_unchanged_branch_projection(
                        pre,
                        post,
                    );
                    assert(another_atomic_superblock_write_request_wf(
                        post.program.state,
                        post.disk,
                    ));
                    assert(branch_component_refinement_inv(post));
                },
                InternalEvent::JournalFillAUs{aus} => {
                    assert(AnotherAtomicState::journal_fill_aus(pre.program.state, post.program.state, aus));
                    let journal_lbl = AtomicJournalState::Label::FillAUs{aus};
                    AtomicJournalState::State::wf_next(
                        pre.program.state.journal,
                        post.program.state.journal,
                        journal_lbl,
                    );
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
                        AtomicJournalState::Step::fill_aus() => {
                            assert(AtomicJournalState::State::fill_aus(
                                pre.program.state.journal,
                                post.program.state.journal,
                                journal_lbl,
                            )) by {
                                reveal(AtomicJournalState::State::fill_aus);
                            }
                        },
                        _ => {
                            assert(false);
                        },
                    }
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
                    assert(post.program.state.journal.wf());
                    assert(post.program.state.journal.journal == pre.program.state.journal.journal);
                    assert(post.program.state.journal.persistent_seq_end
                        == pre.program.state.journal.persistent_seq_end);
                    assert(post.program.state.journal.in_flight
                        == pre.program.state.journal.in_flight);
                    assert(post.program.state.branch == pre.program.state.branch);
                    assert(post.program.state.branch.wf());
                    assert(post.program.state.recovery_state == pre.program.state.recovery_state);
                    assert(post.program.state.persistent_image == pre.program.state.persistent_image);
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.program.state.branch.in_flight
                        == pre.program.state.branch.in_flight);
                    assert(post.program.state.journal_metadata_loaded()
                        == pre.program.state.journal_metadata_loaded());
                    assert(post.program.state.branch_metadata_loaded()
                        == pre.program.state.branch_metadata_loaded());
                    assert(post.program.state.superblock_metadata_known()
                        == pre.program.state.superblock_metadata_known());
                    assert(post.program.state.recovery_metadata_wf()) by {
                        assert(pre.program.state.recovery_metadata_wf());
                    }
                    assert(post.program.state.in_flight_agrees()) by {
                        assert(pre.program.state.in_flight_agrees());
                        if pre.program.state.in_flight is Some {
                            assert(post.program.state.atomic_inflight_superblock_i()
                                == pre.program.state.atomic_inflight_superblock_i());
                        }
                    }
                    assert(pre.program.state.allocation_wf());
                    assert(post.program.state.free_aus == pre.program.state.free_aus - aus);
                    assert(aus <= pre.program.state.free_aus);
                    assert(post.program.state.journal.loaded_index_aus()
                        == pre.program.state.journal.loaded_index_aus());
                    assert(post.program.state.journal.mini_allocator.all_aus()
                        == pre.program.state.journal.mini_allocator.all_aus() + aus) by {
                        assert(post.program.state.journal.mini_allocator
                            == pre.program.state.journal.mini_allocator.add_aus(aus));
                        assert forall |au: AU| #[trigger] post.program.state.journal.mini_allocator.all_aus().contains(au)
                            implies (pre.program.state.journal.mini_allocator.all_aus() + aus).contains(au) by {
                            if pre.program.state.journal.mini_allocator.all_aus().contains(au) {
                                assert(pre.program.state.journal.mini_allocator.all_aus().contains(au));
                            } else {
                                assert(aus.contains(au));
                            }
                        }
                        assert forall |au: AU| #[trigger] (pre.program.state.journal.mini_allocator.all_aus() + aus).contains(au)
                            implies post.program.state.journal.mini_allocator.all_aus().contains(au) by {
                        }
                    }
                    assert(post.program.state.journal.owned_aus()
                        == pre.program.state.journal.owned_aus() + aus) by {
                        assert(post.program.state.journal.loaded_index_aus()
                            == pre.program.state.journal.loaded_index_aus());
                    }
                    assert(post.program.state.branch.owned_aus()
                        == pre.program.state.branch.owned_aus());
                    assert(post.program.state.allocation_wf()) by {
                        assert(post.program.state.component_disjoint()) by {
                            assert(pre.program.state.component_disjoint());
                            assert(pre.program.state.free_aus.disjoint(pre.program.state.component_owned_aus()));
                            assert(aus.disjoint(pre.program.state.component_owned_aus()));
                        }
                        assert(post.program.state.free_aus.disjoint(post.program.state.component_owned_aus()));
                    }
                    assert(post.program.state.wf());
                    journal_fill_aus_refines(pre, post, aus);
                    CrashAwareCachingDiskJournal::State::inv_next(
                        crash_aware_caching_disk_journal_i(pre),
                        crash_aware_caching_disk_journal_i(post),
                        CrashAwareCachingDiskJournal::Label::InternalAlloc{
                            allocs: aus,
                            deallocs: Set::empty(),
                            prune_aus: Set::empty(),
                        },
                    );
                    assert(journal_component_refinement_inv(post));
                    atomic_inflight_superblock_unchanged(pre.program.state, post.program.state);
                    if post.program.state.in_flight is Some
                        && post.disk.requests.contains_key(post.program.state.in_flight.unwrap().req_id)
                        && post.disk.requests[post.program.state.in_flight.unwrap().req_id] is WriteReq
                        && post.disk.requests[post.program.state.in_flight.unwrap().req_id]->to
                            == spec_superblock_addr() {
                        assert(another_atomic_superblock_write_request_wf(
                            pre.program.state,
                            pre.disk,
                        ));
                        assert(post.disk == pre.disk);
                        assert(AtomicJournalState::State::next(
                            pre.program.state.journal,
                            pre.program.state.journal,
                            AtomicJournalState::Label::CommitPrepared,
                        ));
                        assert(AtomicBranchState::State::next(
                            pre.program.state.branch,
                            pre.program.state.branch,
                            AtomicBranchState::Label::CommitPrepared,
                        ));
                        assert(pre.program.state.journal.journal.clean_watermark()
                            == post.program.state.journal.journal.clean_watermark());
                        assert(pre.program.state.branch.in_flight is Some) by {
                            reveal(AtomicBranchState::State::next);
                            reveal(AtomicBranchState::State::next_by);
                            let step = choose |step: AtomicBranchState::Step|
                                AtomicBranchState::State::next_by(
                                    pre.program.state.branch,
                                    pre.program.state.branch,
                                    AtomicBranchState::Label::CommitPrepared,
                                    step,
                                );
                            match step {
                                AtomicBranchState::Step::commit_prepared() => {},
                                _ => { assert(false); },
                            }
                        }
                        assert(pre.program.state.branch.in_flight.unwrap().sealed_roots.len()
                            <= pre.program.state.branch.persisted_root_count) by {
                            assert(AtomicBranchState::State::commit_prepared(
                                pre.program.state.branch,
                                pre.program.state.branch,
                                AtomicBranchState::Label::CommitPrepared,
                            ));
                        }
                        assert(post.program.state.branch.persisted_root_count
                            == pre.program.state.branch.persisted_root_count);
                        assert(pre.program.state.branch.in_flight.unwrap().sealed_roots.len()
                            <= post.program.state.branch.persisted_root_count);
                        atomic_journal_commit_prepared_preserved(
                            pre.program.state.journal,
                            post.program.state.journal,
                        );
                        atomic_branch_commit_prepared_preserved(
                            pre.program.state.branch,
                            post.program.state.branch,
                        );
                    }
                    superblock_write_request_wf_preserved_by_prepared_components(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                    branch_component_refinement_inv_preserved_by_unchanged_branch_projection(
                        pre,
                        post,
                    );
                    assert(another_atomic_superblock_write_request_wf(
                        post.program.state,
                        post.disk,
                    ));
                    assert(branch_component_refinement_inv(post));
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
                    AtomicBranchState::State::wf_next(
                        pre.program.state.branch,
                        post.program.state.branch,
                        branch_lbl,
                    );
                    assert(post.disk == pre.disk);
                    branch_load_metadata_preserves_allocation_projection_wf(
                        pre,
                        post,
                        root,
                        reads,
                        discovered_aus,
                    );
                    assert(post.program.state.branch.in_flight == pre.program.state.branch.in_flight);
                    assert(post.program.state.recovery_metadata_wf());
                    assert(post.program.state.in_flight_agrees());
                    assert(post.program.state.allocation_wf());
                    journal_image_writeback_disjoint_preserved_by_read_only_cache_access(
                        pre,
                        post,
                        reads,
                    );
                    assert(post.program.state.wf());
                    branch_cache_access_preserves_journal_component_refinement(
                        pre,
                        post,
                        reads,
                        Map::empty(),
                    );
                    assert(journal_component_refinement_inv(post));
                    assert(branch_projection_aus(post) =~= branch_projection_aus(pre));
                    assert(reads <= branch_disk_cache_i(pre));
                    branch_load_metadata_refines(pre, post, root, reads, discovered_aus);
                    CrashAwareCachingDiskBranch::State::inv_next(
                        crash_aware_caching_disk_branch_i(pre),
                        crash_aware_caching_disk_branch_i(post),
                        CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus},
                    );
                    assert(branch_component_refinement_inv(post));
                    assert(!pre.program.state.client_ready()) by {
                        assert(pre.program.state.recovery_state is SuperblockAvailable);
                    }
                    assert(!post.program.state.client_ready()) by {
                        assert(post.program.state.recovery_state == pre.program.state.recovery_state);
                    }
                    superblock_write_request_wf_when_not_client_ready(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                    assert(another_atomic_superblock_write_request_wf(
                        post.program.state,
                        post.disk,
                    ));
                },
                InternalEvent::MetadataLoadComplete{} => {
                    assert(AnotherAtomicState::metadata_load_complete(pre.program.state, post.program.state));
                    metadata_load_complete_preserves_refinement_invariants(pre, post);
                    assert(post.program.state.cache == pre.program.state.cache);
                    assert(post.program.state.free_aus == pre.program.state.free_aus);
                    assert(post.program.state.journal == pre.program.state.journal);
                    assert(post.program.state.branch == pre.program.state.branch);
                    assert(post.program.state.outstanding_cache_reqs
                        == pre.program.state.outstanding_cache_reqs);
                    assert(post.program.state.persistent_image == pre.program.state.persistent_image);
                    assert(post.program.state.sync_req_map == pre.program.state.sync_req_map);
                    AnotherAtomicState::cache_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                    );
                    cache_disk_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                    assert(post.program.state.journal_metadata_loaded()
                        == pre.program.state.journal_metadata_loaded());
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.program.state.journal.in_flight
                        == pre.program.state.journal.in_flight);
                    assert(post.program.state.branch.in_flight
                        == pre.program.state.branch.in_flight);
                    assert(post.program.state.journal_metadata_loaded());
                    assert(post.program.state.branch_metadata_loaded());
                    assert(post.program.state.branch.seq_end() <= post.program.state.journal.journal.seq_end()) by {
                        assert(pre.program.state.recovery_metadata_wf());
                        assert(another_atomic_recovery_image_seq_wf(pre.program.state));
                        let image = pre.program.state.persistent_image.unwrap();
                        assert(image.wf());
                        assert(pre.program.state.branch.seq_end() == image.branch_seq_end);
                        assert(pre.program.state.journal.journal.seq_end() == image.journal_seq_end);
                        assert(image.branch_seq_end == image.journal_snapshot.boundary_lsn);
                        assert(image.journal_snapshot.boundary_lsn <= image.journal_seq_end);
                    }
                    assert(post.program.state.recovery_metadata_wf());
                    assert(post.program.state.allocation_wf());
                    assert(post.program.state.in_flight_agrees());
                    assert(post.program.state.wf());
                    assert(another_atomic_persistent_image_wf(post.program.state));
                    assert(another_atomic_in_flight_wf(post.program.state));
                    assert(another_atomic_branch_summary_wf(post.program.state));
                    assert(another_atomic_persisted_branch_prefix_metadata_wf(post.program.state));
                    assert(another_atomic_replay_progress_wf(post.program.state));
                    assert(another_atomic_recovery_image_seq_wf(post.program.state));
                    assert(another_atomic_journal_mini_allocator_stage_wf(post.program.state));
                    assert(another_atomic_sync_request_wf(post.program.state));
                    assert(another_atomic_model_refinement_invariants(post.program.state));
                    assert forall |addr: Address|
                        #[trigger] post.program.state.journal.mini_allocator.can_allocate(addr)
                        implies pre.program.state.journal.mini_allocator.can_allocate(addr) by {
                        assert(post.program.state.journal.mini_allocator
                            == pre.program.state.journal.mini_allocator);
                    }
                    journal_image_writeback_disjoint_preserved_by_unchanged_cache_disk_images(
                        pre,
                        post,
                    );
                    assert(journal_component_refinement_inv(post));
                    atomic_branch_metadata_loaded_flag_from_metadata_loaded(pre.program.state.branch);
                    atomic_branch_metadata_loaded_flag_from_metadata_loaded(post.program.state.branch);
                    loaded_branch_projection_unchanged(pre, post);
                    assert(crash_aware_caching_disk_branch_i(post)
                        == crash_aware_caching_disk_branch_i(pre));
                    assert(branch_component_refinement_inv(post));
                    assert(another_atomic_cache_disk_coupling(post.program.state, post.disk));
                    assert(another_atomic_superblock_disk_coupling(post.program.state, post.disk));
                    assert(another_atomic_superblock_write_request_wf(post.program.state, post.disk));
                    assert(another_atomic_cache_disk_request_wf(post.program.state, post.disk));
                    assert(journal_image_writeback_disjoint(post));
                    assert(another_atomic_disk_refinement_invariants(post));
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
                    branch_grow_write_projection_facts(
                        pre,
                        post,
                        new_root_addr,
                        reads,
                        writes,
                        branch,
                    );
                    /*
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
                    */
                    branch_writes_disjoint_from_journal_static_domains(pre, writes);
                    assert(post.program.state.journal == pre.program.state.journal);
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.program.state.journal.in_flight == pre.program.state.journal.in_flight);
                    assert(post.program.state.branch.in_flight == pre.program.state.branch.in_flight);
                    assert(post.program.state.branch_owned_aus()
                        <= pre.program.state.branch_owned_aus());
                    assert(post.program.state.journal_owned_aus()
                        == pre.program.state.journal_owned_aus());
                    assert(post.program.state.free_aus == pre.program.state.free_aus);
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
                    assert(post.program.state.allocation_wf()) by {
                        assert(pre.program.state.allocation_wf());
                        assert(pre.program.state.free_aus.disjoint(pre.program.state.component_owned_aus()));
                        assert(post.program.state.component_owned_aus()
                            <= pre.program.state.component_owned_aus());
                    }
                    assert(post.program.state.recovery_metadata_wf());
                    assert(post.program.state.in_flight_agrees());
                    assert(post.program.state.journal.journal.status.unwrap().lsn_au_index
                        == pre.program.state.journal.journal.status.unwrap().lsn_au_index);
                    journal_image_writeback_disjoint_preserved_by_cache_access(
                        pre,
                        post,
                        reads,
                        writes,
                    );
                    assert(journal_image_writeback_disjoint(post));
                    assert(post.program.state.wf());
                    branch_cache_access_preserves_journal_component_refinement(
                        pre,
                        post,
                        reads,
                        writes,
                    );
                    assert(journal_component_refinement_inv(post));
                    client_ready_implies_atomic_branch_metadata_loaded_flag(pre.program.state);
                    assert(atomic_branch_metadata_loaded_flag(pre.program.state.branch));
                    assert(reads <= branch_disk_cache_i(pre));
                    branch_grow_refines(pre, post, new_root_addr, reads, writes, branch);
                    CrashAwareCachingDiskBranch::State::inv_next(
                        crash_aware_caching_disk_branch_i(pre),
                        crash_aware_caching_disk_branch_i(post),
                        CrashAwareCachingDiskBranch::Label::Internal,
                    );
                    assert(branch_component_refinement_inv(post));
                    atomic_inflight_superblock_unchanged(pre.program.state, post.program.state);
                    if post.program.state.in_flight is Some
                        && post.disk.requests.contains_key(post.program.state.in_flight.unwrap().req_id)
                        && post.disk.requests[post.program.state.in_flight.unwrap().req_id] is WriteReq
                        && post.disk.requests[post.program.state.in_flight.unwrap().req_id]->to
                            == spec_superblock_addr() {
                        assert(another_atomic_superblock_write_request_wf(
                            pre.program.state,
                            pre.disk,
                        ));
                        assert(post.disk == pre.disk);
                        assert(AtomicJournalState::State::next(
                            pre.program.state.journal,
                            pre.program.state.journal,
                            AtomicJournalState::Label::CommitPrepared,
                        ));
                        assert(AtomicBranchState::State::next(
                            pre.program.state.branch,
                            pre.program.state.branch,
                            AtomicBranchState::Label::CommitPrepared,
                        ));
                        assert(pre.program.state.journal.journal.clean_watermark()
                            == post.program.state.journal.journal.clean_watermark());
                        atomic_journal_commit_prepared_preserved(
                            pre.program.state.journal,
                            post.program.state.journal,
                        );
                        atomic_branch_commit_prepared_preserved(
                            pre.program.state.branch,
                            post.program.state.branch,
                        );
                    }
                    superblock_write_request_wf_preserved_by_prepared_components(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                    assert(another_atomic_superblock_write_request_wf(
                        post.program.state,
                        post.disk,
                    ));
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
                    branch_split_write_projection_facts(
                        pre,
                        post,
                        new_child_addr,
                        receipt,
                        split_arg,
                        reads,
                        writes,
                        branch,
                    );
                    /*
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
                    assert(write_nodes == loaded_split_write_nodes(
                        receipt,
                        read_nodes,
                        split_arg,
                        new_child_addr,
                    ));
                    assert(write_nodes.dom() =~= set![parent_addr, child_addr, new_child_addr]) by {
                        assert_maps_equal!(
                            write_nodes,
                            map! {
                                parent_addr => write_nodes[parent_addr],
                                child_addr => write_nodes[child_addr],
                                new_child_addr => write_nodes[new_child_addr],
                            },
                            a => { }
                        );
                    }
                    assert(set![parent_addr.au, child_addr.au, new_child_addr.au]
                        <= pre.program.state.branch_owned_aus()) by {
                        assert(pre.program.state.branch.mini_allocator.can_allocate(new_child_addr));
                        assert(pre.program.state.branch.mini_allocator.all_aus().contains(new_child_addr.au));
                        assert(active_i.addrs_closed_under_mini_allocator());
                        assert(active_i.mini_allocator.page_is_reserved(parent_addr));
                        assert(active_i.mini_allocator.page_is_reserved(child_addr));
                        assert(pre.program.state.branch.mini_allocator.all_aus().contains(parent_addr.au));
                        assert(pre.program.state.branch.mini_allocator.all_aus().contains(child_addr.au));
                    }
                    assert(to_aus(writes.dom()) <= pre.program.state.branch_owned_aus()) by {
                        assert(writes.dom() =~= write_nodes.dom());
                        assert(writes.dom() =~= set![parent_addr, child_addr, new_child_addr]);
                        let write_addrs = set![parent_addr] + set![child_addr] + set![new_child_addr];
                        assert(writes.dom() =~= write_addrs);
                        crate::disk::GenericDisk_v::to_aus_singleton(parent_addr);
                        crate::disk::GenericDisk_v::to_aus_singleton(child_addr);
                        crate::disk::GenericDisk_v::to_aus_singleton(new_child_addr);
                        crate::disk::GenericDisk_v::to_aus_additive(
                            set![parent_addr],
                            set![child_addr],
                        );
                        crate::disk::GenericDisk_v::to_aus_additive(
                            set![parent_addr] + set![child_addr],
                            set![new_child_addr],
                        );
                        assert(to_aus(writes.dom())
                            == set![parent_addr.au] + set![child_addr.au] + set![new_child_addr.au]);
                        assert forall |au: AU| #[trigger] to_aus(writes.dom()).contains(au)
                            implies pre.program.state.branch_owned_aus().contains(au) by {
                            assert((set![parent_addr.au] + set![child_addr.au] + set![new_child_addr.au]).contains(au));
                        }
                    }
                    */
                    branch_writes_disjoint_from_journal_static_domains(pre, writes);
                    assert(post.program.state.journal == pre.program.state.journal);
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.program.state.journal.in_flight == pre.program.state.journal.in_flight);
                    assert(post.program.state.branch.in_flight == pre.program.state.branch.in_flight);
                    assert(post.program.state.branch_owned_aus()
                        <= pre.program.state.branch_owned_aus());
                    assert(post.program.state.journal_owned_aus()
                        == pre.program.state.journal_owned_aus());
                    assert(post.program.state.free_aus == pre.program.state.free_aus);
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
                    assert(post.program.state.allocation_wf()) by {
                        assert(pre.program.state.allocation_wf());
                        assert(pre.program.state.free_aus.disjoint(pre.program.state.component_owned_aus()));
                        assert(post.program.state.component_owned_aus()
                            <= pre.program.state.component_owned_aus());
                    }
                    assert(post.program.state.recovery_metadata_wf());
                    assert(post.program.state.in_flight_agrees());
                    assert(post.program.state.journal.journal.status.unwrap().lsn_au_index
                        == pre.program.state.journal.journal.status.unwrap().lsn_au_index);
                    journal_image_writeback_disjoint_preserved_by_cache_access(
                        pre,
                        post,
                        reads,
                        writes,
                    );
                    assert(journal_image_writeback_disjoint(post));
                    assert(post.program.state.wf());
                    branch_cache_access_preserves_journal_component_refinement(
                        pre,
                        post,
                        reads,
                        writes,
                    );
                    assert(journal_component_refinement_inv(post));
                    client_ready_implies_atomic_branch_metadata_loaded_flag(pre.program.state);
                    assert(atomic_branch_metadata_loaded_flag(pre.program.state.branch));
                    assert(reads <= branch_disk_cache_i(pre));
                    branch_split_refines(
                        pre,
                        post,
                        new_child_addr,
                        receipt,
                        split_arg,
                        reads,
                        writes,
                        branch,
                    );
                    CrashAwareCachingDiskBranch::State::inv_next(
                        crash_aware_caching_disk_branch_i(pre),
                        crash_aware_caching_disk_branch_i(post),
                        CrashAwareCachingDiskBranch::Label::Internal,
                    );
                    assert(branch_component_refinement_inv(post));
                    atomic_inflight_superblock_unchanged(pre.program.state, post.program.state);
                    if post.program.state.in_flight is Some
                        && post.disk.requests.contains_key(post.program.state.in_flight.unwrap().req_id)
                        && post.disk.requests[post.program.state.in_flight.unwrap().req_id] is WriteReq
                        && post.disk.requests[post.program.state.in_flight.unwrap().req_id]->to
                            == spec_superblock_addr() {
                        assert(another_atomic_superblock_write_request_wf(
                            pre.program.state,
                            pre.disk,
                        ));
                        assert(post.disk == pre.disk);
                        assert(AtomicJournalState::State::next(
                            pre.program.state.journal,
                            pre.program.state.journal,
                            AtomicJournalState::Label::CommitPrepared,
                        ));
                        assert(AtomicBranchState::State::next(
                            pre.program.state.branch,
                            pre.program.state.branch,
                            AtomicBranchState::Label::CommitPrepared,
                        ));
                        assert(pre.program.state.journal.journal.clean_watermark()
                            == post.program.state.journal.journal.clean_watermark());
                        atomic_journal_commit_prepared_preserved(
                            pre.program.state.journal,
                            post.program.state.journal,
                        );
                        atomic_branch_commit_prepared_preserved(
                            pre.program.state.branch,
                            post.program.state.branch,
                        );
                    }
                    superblock_write_request_wf_preserved_by_prepared_components(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                    assert(another_atomic_superblock_write_request_wf(
                        post.program.state,
                        post.disk,
                    ));
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
                    cache_disk_coupling_preserved_by_cache_access(
                        pre,
                        post,
                        reads,
                        writes,
                    );
                    assert(another_atomic_cache_disk_coupling(
                        post.program.state,
                        post.disk,
                    ));
                    branch_seal_write_projection_facts(
                        pre,
                        post,
                        aux_ptr,
                        summary,
                        reads,
                        writes,
                        branch,
                    );
                    assert(post.program.state.branch == branch);
                    assert(post.program.state.journal == pre.program.state.journal);
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.program.state.journal.in_flight == pre.program.state.journal.in_flight);
                    assert(post.program.state.branch.in_flight == pre.program.state.branch.in_flight);
                    assert(post.program.state.branch.wf());
                    assert(post.program.state.branch_owned_aus()
                        <= pre.program.state.branch_owned_aus());
                    assert(post.program.state.journal_owned_aus()
                        == pre.program.state.journal_owned_aus());
                    assert(post.program.state.free_aus == pre.program.state.free_aus);
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
                    assert(post.program.state.allocation_wf()) by {
                        assert(pre.program.state.allocation_wf());
                        assert(pre.program.state.free_aus.disjoint(pre.program.state.component_owned_aus()));
                        assert(post.program.state.component_owned_aus()
                            <= pre.program.state.component_owned_aus());
                    }
                    assert(post.program.state.recovery_metadata_wf());
                    assert(post.program.state.in_flight_agrees());
                    /*
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
            assert(branch.persisted_root_count
                == pre.program.state.branch.persisted_root_count);
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
                    */
                    branch_writes_disjoint_from_journal_static_domains(pre, writes);
                    assert(post.program.state.journal == pre.program.state.journal);
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.program.state.journal.in_flight == pre.program.state.journal.in_flight);
                    assert(post.program.state.branch.in_flight == pre.program.state.branch.in_flight);
                    assert(post.program.state.branch_owned_aus()
                        <= pre.program.state.branch_owned_aus());
                    assert(post.program.state.journal_owned_aus()
                        == pre.program.state.journal_owned_aus());
                    assert(post.program.state.free_aus == pre.program.state.free_aus);
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
                    assert(post.program.state.allocation_wf()) by {
                        assert(pre.program.state.allocation_wf());
                        assert(pre.program.state.free_aus.disjoint(pre.program.state.component_owned_aus()));
                        assert(post.program.state.component_owned_aus()
                            <= pre.program.state.component_owned_aus());
                    }
                    assert(post.program.state.recovery_metadata_wf());
                    assert(post.program.state.in_flight_agrees());
                    assert(post.program.state.journal.journal.status.unwrap().lsn_au_index
                        == pre.program.state.journal.journal.status.unwrap().lsn_au_index);
                    journal_image_writeback_disjoint_preserved_by_cache_access(
                        pre,
                        post,
                        reads,
                        writes,
                    );
                    assert(journal_image_writeback_disjoint(post));
                    superblock_write_request_wf_preserved_by_branch_seal(
                        pre,
                        post,
                        aux_ptr,
                        summary,
                        reads,
                        writes,
                        branch,
                    );
                    assert(another_atomic_superblock_write_request_wf(
                        post.program.state,
                        post.disk,
                    ));
                    assert(post.program.state.wf());
                    branch_cache_access_preserves_journal_component_refinement(
                        pre,
                        post,
                        reads,
                        writes,
                    );
                    assert(journal_component_refinement_inv(post));
                    atomic_inflight_superblock_unchanged(pre.program.state, post.program.state);
                    if post.program.state.in_flight is Some
                        && post.disk.requests.contains_key(post.program.state.in_flight.unwrap().req_id)
                        && post.disk.requests[post.program.state.in_flight.unwrap().req_id] is WriteReq
                        && post.disk.requests[post.program.state.in_flight.unwrap().req_id]->to
                            == spec_superblock_addr() {
                        assert(another_atomic_superblock_write_request_wf(
                            pre.program.state,
                            pre.disk,
                        ));
                        assert(post.disk == pre.disk);
                        assert(AtomicJournalState::State::next(
                            pre.program.state.journal,
                            pre.program.state.journal,
                            AtomicJournalState::Label::CommitPrepared,
                        ));
                        assert(AtomicBranchState::State::next(
                            pre.program.state.branch,
                            pre.program.state.branch,
                            AtomicBranchState::Label::CommitPrepared,
                        ));
                        assert(pre.program.state.journal.journal.clean_watermark()
                            == post.program.state.journal.journal.clean_watermark());
                        assert(pre.program.state.branch.in_flight is Some) by {
                            reveal(AtomicBranchState::State::next);
                            reveal(AtomicBranchState::State::next_by);
                            let step = choose |step: AtomicBranchState::Step|
                                AtomicBranchState::State::next_by(
                                    pre.program.state.branch,
                                    pre.program.state.branch,
                                    AtomicBranchState::Label::CommitPrepared,
                                    step,
                                );
                            match step {
                                AtomicBranchState::Step::commit_prepared() => {},
                                _ => { assert(false); },
                            }
                        }
                        assert(pre.program.state.branch.in_flight.unwrap().sealed_roots.len()
                            <= pre.program.state.branch.persisted_root_count) by {
                            assert(AtomicBranchState::State::commit_prepared(
                                pre.program.state.branch,
                                pre.program.state.branch,
                                AtomicBranchState::Label::CommitPrepared,
                            ));
                        }
                        assert(post.program.state.branch.persisted_root_count
                            == pre.program.state.branch.persisted_root_count);
                        assert(pre.program.state.branch.in_flight.unwrap().sealed_roots.len()
                            <= post.program.state.branch.persisted_root_count);
                        atomic_journal_commit_prepared_preserved(
                            pre.program.state.journal,
                            post.program.state.journal,
                        );
                        atomic_branch_commit_prepared_preserved(
                            pre.program.state.branch,
                            post.program.state.branch,
                        );
                    }
                    superblock_write_request_wf_preserved_by_prepared_components(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                    assert(another_atomic_superblock_write_request_wf(
                        post.program.state,
                        post.disk,
                    ));
                },
                InternalEvent::BranchFillAUs{aus} => {
                    assert(AnotherAtomicState::branch_fill_aus(pre.program.state, post.program.state, aus));
                    let branch_lbl = AtomicBranchState::Label::FillAUs{aus};
                    AtomicBranchState::State::wf_next(
                        pre.program.state.branch,
                        post.program.state.branch,
                        branch_lbl,
                    );
                    AtomicBranchState::State::fill_aus_effect(
                        pre.program.state.branch,
                        post.program.state.branch,
                        branch_lbl,
                    );
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
                    assert(post.program.state.journal_metadata_loaded()
                        == pre.program.state.journal_metadata_loaded());
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.program.state.journal.in_flight
                        == pre.program.state.journal.in_flight);
                    assert(post.program.state.branch.in_flight
                        == pre.program.state.branch.in_flight);
                    assert forall |addr: Address|
                        #[trigger] post.program.state.journal.mini_allocator.can_allocate(addr)
                        implies pre.program.state.journal.mini_allocator.can_allocate(addr) by {
                        assert(post.program.state.journal.mini_allocator
                            == pre.program.state.journal.mini_allocator);
                    }
                    journal_image_writeback_disjoint_preserved_by_unchanged_cache_disk_images(
                        pre,
                        post,
                    );
                    assert(post.program.state.branch.in_flight
                        == pre.program.state.branch.in_flight);
                    assert(post.program.state.branch.branch_summary
                        == pre.program.state.branch.branch_summary);
                    assert(post.program.state.branch.image == pre.program.state.branch.image);
                    assert(post.program.state.branch.active_branch
                        == pre.program.state.branch.active_branch);
                    assert(post.program.state.branch.seq_end == pre.program.state.branch.seq_end);
                    assert(branch_caching_disk_i(post) == branch_caching_disk_i(pre));
                    branch_fill_aus_refines(pre, post, aus);
                    CrashAwareCachingDiskBranch::State::inv_next(
                        crash_aware_caching_disk_branch_i(pre),
                        crash_aware_caching_disk_branch_i(post),
                        CrashAwareCachingDiskBranch::Label::InternalAlloc{
                            allocs: aus,
                            deallocs: Set::<AU>::empty(),
                        },
                    );
                    assert(branch_component_refinement_inv(post));
                    atomic_inflight_superblock_unchanged(pre.program.state, post.program.state);
                    if post.program.state.in_flight is Some
                        && post.disk.requests.contains_key(post.program.state.in_flight.unwrap().req_id)
                        && post.disk.requests[post.program.state.in_flight.unwrap().req_id] is WriteReq
                        && post.disk.requests[post.program.state.in_flight.unwrap().req_id]->to
                            == spec_superblock_addr() {
                        assert(another_atomic_superblock_write_request_wf(
                            pre.program.state,
                            pre.disk,
                        ));
                        assert(post.disk == pre.disk);
                        assert(AtomicJournalState::State::next(
                            pre.program.state.journal,
                            pre.program.state.journal,
                            AtomicJournalState::Label::CommitPrepared,
                        ));
                        assert(AtomicBranchState::State::next(
                            pre.program.state.branch,
                            pre.program.state.branch,
                            AtomicBranchState::Label::CommitPrepared,
                        ));
                        assert(pre.program.state.journal.journal.clean_watermark()
                            == post.program.state.journal.journal.clean_watermark());
                        atomic_journal_commit_prepared_preserved(
                            pre.program.state.journal,
                            post.program.state.journal,
                        );
                        atomic_branch_commit_prepared_preserved(
                            pre.program.state.branch,
                            post.program.state.branch,
                        );
                    }
                    superblock_write_request_wf_preserved_by_prepared_components(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                    assert(another_atomic_superblock_write_request_wf(
                        post.program.state,
                        post.disk,
                    ));
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
                    let branch_lbl = AtomicBranchState::Label::ObservePersistedRoots{target_count};
                    AtomicBranchState::State::wf_next(
                        pre.program.state.branch,
                        post.program.state.branch,
                        branch_lbl,
                    );
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
                        AtomicBranchState::Step::observe_persisted_roots() => {
                            assert(AtomicBranchState::State::observe_persisted_roots(
                                pre.program.state.branch,
                                post.program.state.branch,
                                branch_lbl,
                            )) by {
                                reveal(AtomicBranchState::State::observe_persisted_roots);
                            }
                        },
                        _ => {
                            assert(false);
                        },
                    }
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
                    assert(post.program.state.journal_metadata_loaded()
                        == pre.program.state.journal_metadata_loaded());
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.program.state.journal.in_flight
                        == pre.program.state.journal.in_flight);
                    assert(post.program.state.branch.in_flight
                        == pre.program.state.branch.in_flight);
                    assert forall |addr: Address|
                        #[trigger] post.program.state.journal.mini_allocator.can_allocate(addr)
                        implies pre.program.state.journal.mini_allocator.can_allocate(addr) by {
                        assert(post.program.state.journal.mini_allocator
                            == pre.program.state.journal.mini_allocator);
                    }
                    journal_image_writeback_disjoint_preserved_by_unchanged_cache_disk_images(
                        pre,
                        post,
                    );
                    client_ready_implies_atomic_branch_metadata_loaded_flag(pre.program.state);
                    assert(post.program.state.branch.branch_summary
                        == pre.program.state.branch.branch_summary);
                    assert(post.program.state.branch.mini_allocator
                        == pre.program.state.branch.mini_allocator);
                    assert(atomic_branch_metadata_loaded_flag(post.program.state.branch));
                    loaded_branch_projection_unchanged(pre, post);
                    assert(branch_projection_aus(post) =~= branch_projection_aus(pre));
                    assert(atomic_branch_metadata_loaded_flag(pre.program.state.branch));
                    observe_persisted_branch_roots_refines(pre, post, target_count, aus);
                    CrashAwareCachingDiskBranch::State::inv_next(
                        crash_aware_caching_disk_branch_i(pre),
                        crash_aware_caching_disk_branch_i(post),
                        CrashAwareCachingDiskBranch::Label::Internal,
                    );
                    assert(branch_component_refinement_inv(post));
                    atomic_inflight_superblock_unchanged(pre.program.state, post.program.state);
                    if post.program.state.in_flight is Some
                        && post.disk.requests.contains_key(post.program.state.in_flight.unwrap().req_id)
                        && post.disk.requests[post.program.state.in_flight.unwrap().req_id] is WriteReq
                        && post.disk.requests[post.program.state.in_flight.unwrap().req_id]->to
                            == spec_superblock_addr() {
                        assert(another_atomic_superblock_write_request_wf(
                            pre.program.state,
                            pre.disk,
                        ));
                        assert(post.disk == pre.disk);
                        assert(AtomicJournalState::State::next(
                            pre.program.state.journal,
                            pre.program.state.journal,
                            AtomicJournalState::Label::CommitPrepared,
                        ));
                        assert(AtomicBranchState::State::next(
                            pre.program.state.branch,
                            pre.program.state.branch,
                            AtomicBranchState::Label::CommitPrepared,
                        ));
                        assert(pre.program.state.journal.journal.clean_watermark()
                            == post.program.state.journal.journal.clean_watermark());
                        atomic_journal_commit_prepared_preserved(
                            pre.program.state.journal,
                            post.program.state.journal,
                        );
                        atomic_branch_commit_prepared_preserved(
                            pre.program.state.branch,
                            post.program.state.branch,
                        );
                    }
                    superblock_write_request_wf_preserved_by_prepared_components(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                    assert(another_atomic_superblock_write_request_wf(
                        post.program.state,
                        post.disk,
                    ));
                },
                InternalEvent::RecoveryComplete{} => {
                    assert(AnotherAtomicState::recovery_complete(pre.program.state, post.program.state));
                    AnotherAtomicState::recovery_complete_effect(
                        pre.program.state,
                        post.program.state,
                    );
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
                    recovery_complete_preserves_journal_component_refinement(pre, post);
                    assert(!pre.program.state.client_ready()) by {
                        assert(pre.program.state.recovery_state is MetadataLoadComplete);
                    }
                    superblock_write_request_wf_when_not_client_ready(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                    branch_component_refinement_inv_preserved_by_unchanged_branch_projection(
                        pre,
                        post,
                    );
                    assert(another_atomic_superblock_write_request_wf(
                        post.program.state,
                        post.disk,
                    ));
                    assert(branch_component_refinement_inv(post));
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
                    assert(post.program.state.journal_metadata_loaded()
                        == pre.program.state.journal_metadata_loaded());
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.program.state.journal.in_flight
                        == pre.program.state.journal.in_flight);
                    assert(post.program.state.branch.in_flight
                        == pre.program.state.branch.in_flight);
                    assert forall |addr: Address|
                        #[trigger] post.program.state.journal.mini_allocator.can_allocate(addr)
                        implies pre.program.state.journal.mini_allocator.can_allocate(addr) by {
                        assert(post.program.state.journal.mini_allocator
                            == pre.program.state.journal.mini_allocator);
                    }
                    journal_image_writeback_disjoint_preserved_by_unchanged_cache_disk_images(
                        pre,
                        post,
                    );
                    superblock_write_request_wf_preserved_by_unchanged_commit_components(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                    branch_component_refinement_inv_preserved_by_unchanged_branch_projection(
                        pre,
                        post,
                    );
                    assert(another_atomic_superblock_write_request_wf(
                        post.program.state,
                        post.disk,
                    ));
                    assert(branch_component_refinement_inv(post));
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
                    assert(post.program.state.journal_metadata_loaded()
                        == pre.program.state.journal_metadata_loaded());
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.program.state.journal.in_flight
                        == pre.program.state.journal.in_flight);
                    assert(post.program.state.branch.in_flight
                        == pre.program.state.branch.in_flight);
                    assert forall |addr: Address|
                        #[trigger] post.program.state.journal.mini_allocator.can_allocate(addr)
                        implies pre.program.state.journal.mini_allocator.can_allocate(addr) by {
                        assert(post.program.state.journal.mini_allocator
                            == pre.program.state.journal.mini_allocator);
                    }
                    journal_image_writeback_disjoint_preserved_by_unchanged_cache_disk_images(
                        pre,
                        post,
                    );
                    superblock_write_request_wf_preserved_by_unchanged_commit_components(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                    branch_component_refinement_inv_preserved_by_unchanged_branch_projection(
                        pre,
                        post,
                    );
                    assert(another_atomic_superblock_write_request_wf(
                        post.program.state,
                        post.disk,
                    ));
                    assert(branch_component_refinement_inv(post));
                },
            }
            assert(post.disk == pre.disk);
            assert(post.disk.inv());
            assert(async_disk_superblock_page_wf(post.disk.content));
            assert(another_atomic_cache_disk_coupling(post.program.state, post.disk));
            assert(another_atomic_superblock_disk_coupling(post.program.state, post.disk));
            assert(another_atomic_superblock_write_request_wf(post.program.state, post.disk));
            assert(another_atomic_cache_disk_request_wf(post.program.state, post.disk));
            assert(journal_component_refinement_inv(post));
            assert(branch_component_refinement_inv(post));
            assert(journal_image_writeback_disjoint(post));
            assert(another_atomic_disk_refinement_invariants(post));
        },
        SystemModel::Step::disk_internal(new_disk) => {
            assert(post.program == pre.program);
            disk_internal_preserves_refinement_invariants(pre, post);
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
