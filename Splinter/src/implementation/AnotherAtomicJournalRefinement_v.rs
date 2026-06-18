// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Draft component refinement from SystemModel<AnotherProgramModel> to the
// crash-aware caching-disk journal.  This is intentionally local to the journal
// component: the source of persistent raw pages is the shared AsyncDisk in the
// trusted SystemModel, while journal metadata comes from AnotherAtomicState.

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::map::*;
use vstd::assert_maps_equal;

use crate::abstract_system::MsgHistory_v::{KeyedMessage, MsgHistory};
use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::{Address, AU, Pointer, to_aus, to_aus_domain};
use crate::implementation::AbstractSuperblock_v::{
    AbstractSuperblockImage, abstract_superblock_raw_wf, marshal_abstract_superblock,
    parse_abstract_superblock,
};
use crate::implementation::AnotherAtomicState_v::{
    AnotherAtomicState, AtomicBranchState, AtomicJournalState,
};
use crate::implementation::AnotherProgramModel_v::AnotherProgramModel;
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedBranch_v::LoadedPathReceipt;
use crate::implementation::CachingDiskAdapterRefinement_v::{
    cache_access_refines_caching_disk_access, cache_evictable_refines_observe_clean_aus,
    cache_filled_addr, filled_cache_pages,
    caching_disk_i as adapter_caching_disk_i, caching_disk_i_by_domains,
    project_cache_pages, project_cache_pages_by_addrs, project_cache_status,
    project_cache_status_by_addrs, project_persistent, project_persistent_by_addrs,
    filled_cache_access_effect, filled_cache_read_only_access_unchanged,
    projected_cache_access_effect, projected_cache_read_only_access_unchanged,
    projected_cache_read_only_access_unchanged_by_addrs,
    projected_cache_access_outside_aus_unchanged,
    projected_cache_access_outside_addrs_unchanged, ownership_projection_forget_refines,
};
use crate::implementation::CachedJournal_v::{CachedJournal, JournalSnapshot};
use crate::implementation::CachingDisk_v::{
    addresses_in_aus, CachingDisk, PageStatus as CachingDiskPageStatus,
};
use crate::implementation::CachingDiskJournal_v::CachingDiskJournal;
use crate::implementation::CrashAwareCachingDiskJournal_v::{
    caching_disk_journal_accessible_aus, CachingDiskJournalFrozenImage, CachingDiskJournalImage,
    snapshot_walk_domain, snapshot_walk_ptr, CrashAwareCachingDiskJournal, EphemeralCachingDiskJournal,
};
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::JournalTypes_v::to_journal_records;
use crate::journal::LinkedJournal_v::*;
use crate::spec::AsyncDisk_t::{AsyncDisk, DiskResponse, RawPage};
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::{Request, Reply};
use crate::spec::Messages_t::Message;
use crate::trusted::SystemModel_t::SystemModel;

verus! {

pub open spec fn async_disk_superblock_raw_i(
    disk_content: Map<Address, RawPage>,
) -> RawPage
{
    if disk_content.contains_key(spec_superblock_addr()) {
        disk_content[spec_superblock_addr()]
    } else {
        arbitrary()
    }
}

pub open spec fn async_disk_superblock_image_i(
    disk_content: Map<Address, RawPage>,
) -> AbstractSuperblockImage
{
    parse_abstract_superblock(async_disk_superblock_raw_i(disk_content))
}

pub open spec fn async_disk_superblock_page_wf(
    disk_content: Map<Address, RawPage>,
) -> bool
{
    &&& disk_content.contains_key(spec_superblock_addr())
    &&& abstract_superblock_raw_wf(disk_content[spec_superblock_addr()])
}

pub open spec fn on_disk_journal_tj_i(
    disk_content: Map<Address, RawPage>,
) -> TruncatedJournal
{
    let image = async_disk_superblock_image_i(disk_content);
    TruncatedJournal{
        freshest_rec: image.journal_snapshot.freshest_rec(),
        disk_view: DiskView{
            boundary_lsn: image.journal_snapshot.boundary_lsn,
            entries: to_journal_records(disk_content),
        },
    }
}

pub open spec fn on_disk_journal_aus_i(
    disk_content: Map<Address, RawPage>,
) -> Set<AU>
{
    let image = async_disk_superblock_image_i(disk_content);
    on_disk_journal_tj_i(disk_content)
        .build_lsn_au_index_from_first(image.journal_snapshot.first())
        .values()
}

pub open spec fn on_disk_journal_addrs_i(
    disk_content: Map<Address, RawPage>,
) -> Set<Address>
{
    let image = async_disk_superblock_image_i(disk_content);
    snapshot_walk_domain(
        to_journal_records(disk_content),
        image.journal_snapshot.boundary_lsn,
        image.journal_snapshot.freshest_rec(),
    )
}

pub proof fn snapshot_walk_ptr_none(
    records: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    depth: nat,
)
    ensures
        snapshot_walk_ptr(records, boundary_lsn, None, depth) is None,
    decreases depth
{
    if depth > 0 {
        snapshot_walk_ptr_none(records, boundary_lsn, (depth - 1) as nat);
    }
}

pub proof fn snapshot_walk_domain_none_empty(
    records: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
)
    ensures
        snapshot_walk_domain(records, boundary_lsn, None) =~= Set::<Address>::empty(),
{
    assert forall |addr: Address| #[trigger] snapshot_walk_domain(records, boundary_lsn, None).contains(addr)
        implies false by {
        let depth = choose |depth: nat|
            snapshot_walk_ptr(records, boundary_lsn, None, depth) == Some(addr);
        snapshot_walk_ptr_none(records, boundary_lsn, depth);
    }
}

pub open spec fn mini_allocator_allocated_addrs(
    mini_allocator: crate::allocation_layer::MiniAllocator_v::MiniAllocator,
) -> Set<Address>
{
    Set::new(|addr: Address| {
        &&& mini_allocator.allocs.contains_key(addr.au)
        &&& (mini_allocator.allocs[addr.au].reserved
            + mini_allocator.allocs[addr.au].observed).contains(addr)
    })
}

pub open spec fn live_journal_projection_addrs(
    model: SystemModel::State<AnotherProgramModel>,
) -> Set<Address>
{
    let journal = model.program.state.journal;
    addresses_in_aus(journal.loaded_index_aus().difference(journal.mini_allocator.all_aus()))
        + mini_allocator_allocated_addrs(journal.mini_allocator)
}

pub open spec fn snapshot_tight_journal_projection_addrs(
    model: SystemModel::State<AnotherProgramModel>,
) -> Set<Address>
{
    let journal = model.program.state.journal;
    let snapshot = journal.journal.snapshot;
    let overlay_records = to_journal_records(model.disk.content);
    snapshot_walk_domain(
        overlay_records,
        snapshot.boundary_lsn,
        snapshot.freshest_rec(),
    )
        + mini_allocator_allocated_addrs(journal.mini_allocator)
}

pub open spec fn journal_projection_addrs(
    model: SystemModel::State<AnotherProgramModel>,
) -> Set<Address>
{
    let raw_addrs = if journal_projection_uses_live(model) {
        live_journal_projection_addrs(model)
    } else if model.program.state.superblock_metadata_known() {
        snapshot_tight_journal_projection_addrs(model)
    } else {
        on_disk_journal_addrs_i(model.disk.content)
    };
    raw_addrs.difference(addresses_in_aus(AnotherAtomicState::reserved_aus()))
}

pub open spec fn journal_projection_uses_live(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    ||| model.program.state.recovery_state is MetadataLoadComplete
    ||| model.program.state.recovery_state is RecoveryComplete
}

pub open spec fn journal_projection_aus(
    model: SystemModel::State<AnotherProgramModel>,
) -> Set<AU>
{
    // AU-level over-approximation used for disjointness proofs.  Actual journal
    // cache/disk projection is address-precise through journal_projection_addrs.
    if journal_projection_uses_live(model) {
        to_aus(journal_projection_addrs(model))
            + model.program.state.journal.loaded_index_aus()
            + model.program.state.journal.mini_allocator.all_aus()
    } else {
        to_aus(journal_projection_addrs(model))
    }
}

pub open spec fn journal_persistent_projection_addrs(
    model: SystemModel::State<AnotherProgramModel>,
) -> Set<Address>
{
    let support = journal_projection_addrs(model);
    let cache_status = crate::implementation::CachingDiskAdapterRefinement_v::filled_cache_status(
        model.program.state.cache,
    );
    let cache_pages = filled_cache_pages(model.program.state.cache);
    Set::new(|addr: Address| {
        &&& support.contains(addr)
        &&& model.disk.content.contains_key(addr)
        &&& if cache_status.contains_key(addr) {
            ||| cache_status[addr] == CachingDiskPageStatus::Clean
            ||| (cache_status[addr] == CachingDiskPageStatus::Writeback
                && cache_pages.contains_key(addr)
                && model.disk.content[addr] == cache_pages[addr])
        } else {
            true
        }
    })
}

pub open spec fn journal_disk_persistent_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> Map<Address, RawPage>
{
    project_persistent_by_addrs(model.disk, journal_persistent_projection_addrs(model))
}

pub open spec fn journal_disk_cache_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> Map<Address, RawPage>
{
    project_cache_pages_by_addrs(model.program.state.cache, journal_projection_addrs(model))
}

pub open spec fn journal_disk_status_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> Map<Address, CachingDiskPageStatus>
{
    project_cache_status_by_addrs(model.program.state.cache, journal_projection_addrs(model))
}

pub open spec fn journal_caching_disk_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> CachingDisk::State
{
    caching_disk_i_by_domains(
        model.program.state.cache,
        model.disk,
        journal_projection_addrs(model),
        journal_persistent_projection_addrs(model),
    )
}

pub open spec fn journal_caching_disk_state_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> CachingDiskJournal::State
{
    CachingDiskJournal::State{
        journal: model.program.state.journal.journal,
        disk: journal_caching_disk_i(model),
        mini_allocator: model.program.state.journal.mini_allocator,
    }
}

pub open spec fn durable_superblock_image_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> AbstractSuperblockImage
{
    // AnotherAtomicState::persistent_image is only cached ephemeral knowledge.
    // The durable image for this refinement comes from the shared AsyncDisk
    // superblock page.
    async_disk_superblock_image_i(model.disk.content)
}

pub open spec fn atomic_persistent_superblock_image_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> AbstractSuperblockImage
{
    if model.program.state.persistent_image is Some {
        model.program.state.persistent_image.unwrap()
    } else {
        durable_superblock_image_i(model)
    }
}

pub open spec fn journal_image_i(
    model: SystemModel::State<AnotherProgramModel>,
    image: AbstractSuperblockImage,
) -> CachingDiskJournalImage
{
    CachingDiskJournalImage{
        persistent: journal_image_persistent_i(model, image),
        snapshot: image.journal_snapshot,
        seq_end: image.journal_seq_end,
    }
}

pub open spec fn journal_image_tj_i(
    disk_content: Map<Address, RawPage>,
    image: AbstractSuperblockImage,
) -> TruncatedJournal
{
    TruncatedJournal{
        freshest_rec: image.journal_snapshot.freshest_rec(),
        disk_view: DiskView{
            boundary_lsn: image.journal_snapshot.boundary_lsn,
            entries: to_journal_records(disk_content),
        },
    }
}

pub open spec fn journal_image_projection_aus(
    disk_content: Map<Address, RawPage>,
    image: AbstractSuperblockImage,
) -> Set<AU>
{
    journal_image_tj_i(disk_content, image)
        .build_lsn_au_index_from_first(image.journal_snapshot.first())
        .values()
}

pub open spec fn journal_image_loaded_index_aus(
    model: SystemModel::State<AnotherProgramModel>,
    image: AbstractSuperblockImage,
) -> Set<AU>
{
    let index = model.program.state.journal.journal.status.unwrap().lsn_au_index;
    let image_lsns = Set::new(|lsn: LSN|
        image.journal_snapshot.boundary_lsn <= lsn && lsn < image.journal_seq_end);
    index.restrict(image_lsns).values()
}

pub open spec fn journal_image_projection_aus_i(
    model: SystemModel::State<AnotherProgramModel>,
    image: AbstractSuperblockImage,
) -> Set<AU>
{
    if model.program.state.journal_metadata_loaded() {
        journal_image_loaded_index_aus(model, image)
    } else {
        journal_image_projection_aus(model.disk.content, image)
    }
}

pub open spec fn journal_image_projection_domain_i(
    model: SystemModel::State<AnotherProgramModel>,
    image: AbstractSuperblockImage,
) -> Set<Address>
{
    snapshot_walk_domain(
        to_journal_records(model.disk.content),
        image.journal_snapshot.boundary_lsn,
        image.journal_snapshot.freshest_rec(),
    )
}

pub proof fn snapshot_walk_ptr_union_outside_domain_same(
    records: Map<Address, JournalRecord>,
    updates: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
)
    requires
        updates.dom().disjoint(snapshot_walk_domain(records, boundary_lsn, root)),
    ensures
        snapshot_walk_ptr(records.union_prefer_right(updates), boundary_lsn, root, depth)
            == snapshot_walk_ptr(records, boundary_lsn, root, depth),
    decreases depth,
{
    if depth == 0 {
    } else {
        snapshot_walk_ptr_union_outside_domain_same(
            records,
            updates,
            boundary_lsn,
            root,
            (depth - 1) as nat,
        );
        let prev = snapshot_walk_ptr(records, boundary_lsn, root, (depth - 1) as nat);
        if prev is Some {
            let prev_addr = prev.unwrap();
            assert(snapshot_walk_domain(records, boundary_lsn, root).contains(prev_addr)) by {
                assert(snapshot_walk_ptr(records, boundary_lsn, root, (depth - 1) as nat)
                    == Some(prev_addr));
            }
            assert(!updates.contains_key(prev_addr)) by {
                if updates.contains_key(prev_addr) {
                    assert(updates.dom().contains(prev_addr));
                    assert(false);
                }
            }
            assert(records.union_prefer_right(updates).contains_key(prev_addr)
                == records.contains_key(prev_addr));
            if records.contains_key(prev_addr) {
                assert(records.union_prefer_right(updates)[prev_addr] == records[prev_addr]);
            }
        }
    }
}

pub proof fn snapshot_walk_domain_union_outside_same(
    records: Map<Address, JournalRecord>,
    updates: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
)
    requires
        updates.dom().disjoint(snapshot_walk_domain(records, boundary_lsn, root)),
    ensures
        snapshot_walk_domain(records.union_prefer_right(updates), boundary_lsn, root)
            =~= snapshot_walk_domain(records, boundary_lsn, root),
{
    assert forall |addr: Address| #[trigger] snapshot_walk_domain(
        records.union_prefer_right(updates),
        boundary_lsn,
        root,
    ).contains(addr) <==> snapshot_walk_domain(records, boundary_lsn, root).contains(addr) by {
        if snapshot_walk_domain(records.union_prefer_right(updates), boundary_lsn, root).contains(addr) {
            let depth = choose |depth: nat|
                snapshot_walk_ptr(records.union_prefer_right(updates), boundary_lsn, root, depth)
                    == Some(addr);
            snapshot_walk_ptr_union_outside_domain_same(records, updates, boundary_lsn, root, depth);
            assert(snapshot_walk_ptr(records, boundary_lsn, root, depth) == Some(addr));
        }
        if snapshot_walk_domain(records, boundary_lsn, root).contains(addr) {
            let depth = choose |depth: nat|
                snapshot_walk_ptr(records, boundary_lsn, root, depth) == Some(addr);
            snapshot_walk_ptr_union_outside_domain_same(records, updates, boundary_lsn, root, depth);
            assert(snapshot_walk_ptr(records.union_prefer_right(updates), boundary_lsn, root, depth)
                == Some(addr));
        }
    }
}

pub open spec fn journal_image_projection_domain_from_disk(
    disk_content: Map<Address, RawPage>,
    image: AbstractSuperblockImage,
) -> Set<Address>
{
    let tj = journal_image_tj_i(disk_content, image);
    let index = tj.build_lsn_au_index_from_first(image.journal_snapshot.first());
    tj.disk_view.tight_domain(index, tj.freshest_rec)
}

pub open spec fn journal_image_persistent_i(
    model: SystemModel::State<AnotherProgramModel>,
    image: AbstractSuperblockImage,
) -> Map<Address, RawPage>
{
    model.disk.content.restrict(journal_image_projection_domain_i(model, image))
}

pub open spec fn persistent_journal_image_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> CachingDiskJournalImage
{
    journal_image_i(model, atomic_persistent_superblock_image_i(model))
}

pub open spec fn frozen_journal_image_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> Option<CachingDiskJournalImage>
{
    if model.program.state.in_flight is Some {
        Option::Some(journal_image_i(model, model.program.state.atomic_inflight_superblock_i()))
    } else {
        Option::None
    }
}

pub open spec fn frozen_journal_metadata_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> Option<CachingDiskJournalFrozenImage>
{
    if model.program.state.in_flight is Some {
        let image = model.program.state.atomic_inflight_superblock_i();
        Option::Some(CachingDiskJournalFrozenImage{
            snapshot: image.journal_snapshot,
            seq_end: image.journal_seq_end,
        })
    } else {
        Option::None
    }
}

pub proof fn journal_image_persistent_unchanged_for_same_projection(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    image: AbstractSuperblockImage,
)
    requires
        post.disk.content == pre.disk.content,
        journal_image_projection_aus_i(post, image) =~= journal_image_projection_aus_i(pre, image),
    ensures
        journal_image_persistent_i(post, image) == journal_image_persistent_i(pre, image),
{
    assert(journal_image_projection_domain_i(post, image)
        =~= journal_image_projection_domain_i(pre, image)) by {
        assert forall |addr: Address|
            journal_image_projection_domain_i(post, image).contains(addr)
                <==> journal_image_projection_domain_i(pre, image).contains(addr)
        by {
            assert(journal_image_projection_aus_i(post, image).contains(addr.au)
                <==> journal_image_projection_aus_i(pre, image).contains(addr.au));
        }
    }
    assert_maps_equal!(
        journal_image_persistent_i(post, image),
        journal_image_persistent_i(pre, image),
        addr => {
            assert(journal_image_projection_domain_i(post, image).contains(addr)
                <==> journal_image_projection_domain_i(pre, image).contains(addr));
        }
    );
}

pub proof fn journal_image_projection_aus_loaded_index_unchanged(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    image: AbstractSuperblockImage,
)
    requires
        pre.program.state.journal_metadata_loaded(),
        post.program.state.journal_metadata_loaded(),
        post.program.state.journal.journal.status.unwrap().lsn_au_index
            == pre.program.state.journal.journal.status.unwrap().lsn_au_index,
    ensures
        journal_image_projection_aus_i(post, image) =~= journal_image_projection_aus_i(pre, image),
{
    assert(journal_image_loaded_index_aus(post, image)
        == journal_image_loaded_index_aus(pre, image));
}

pub proof fn journal_images_unchanged_by_loaded_index_preservation(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
)
    requires
        post.disk == pre.disk,
        pre.program.state.journal_metadata_loaded(),
        post.program.state.journal_metadata_loaded(),
        post.program.state.journal.journal.status.unwrap().lsn_au_index
            == pre.program.state.journal.journal.status.unwrap().lsn_au_index,
        post.program.state.in_flight == pre.program.state.in_flight,
        post.program.state.journal.in_flight == pre.program.state.journal.in_flight,
        post.program.state.branch.in_flight == pre.program.state.branch.in_flight,
    ensures
        persistent_journal_image_i(post) == persistent_journal_image_i(pre),
        frozen_journal_image_i(post) == frozen_journal_image_i(pre),
{
    let persistent_image = durable_superblock_image_i(pre);
    assert(durable_superblock_image_i(post) == persistent_image);
    journal_image_projection_aus_loaded_index_unchanged(pre, post, persistent_image);
    journal_image_persistent_unchanged_for_same_projection(pre, post, persistent_image);
    assert(persistent_journal_image_i(post) == persistent_journal_image_i(pre));

    if pre.program.state.in_flight is Some {
        assert(post.program.state.in_flight is Some);
        assert(post.program.state.atomic_inflight_superblock_i()
            == pre.program.state.atomic_inflight_superblock_i());
        let frozen_image = pre.program.state.atomic_inflight_superblock_i();
        journal_image_projection_aus_loaded_index_unchanged(pre, post, frozen_image);
        journal_image_persistent_unchanged_for_same_projection(pre, post, frozen_image);
        assert(frozen_journal_image_i(post) == frozen_journal_image_i(pre));
    } else {
        assert(post.program.state.in_flight is None);
        assert(frozen_journal_image_i(post) == frozen_journal_image_i(pre));
    }
}

pub open spec fn ephemeral_journal_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> EphemeralCachingDiskJournal
{
    if model.program.state.superblock_metadata_known() {
        EphemeralCachingDiskJournal::Known{v: journal_caching_disk_state_i(model)}
    } else {
        EphemeralCachingDiskJournal::Unknown
    }
}

pub open spec fn atomic_superblock_prepared_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    if model.program.state.in_flight is Some {
        let id = model.program.state.in_flight.unwrap().req_id;
        let raw = marshal_abstract_superblock(model.program.state.atomic_inflight_superblock_i());
        ||| {
            &&& model.disk.requests.contains_key(id)
            &&& model.disk.requests[id] is WriteReq
            &&& model.disk.requests[id]->to == spec_superblock_addr()
            &&& model.disk.requests[id]->data == raw
        }
        ||| {
            &&& model.disk.responses.contains_key(id)
            &&& model.disk.responses[id] == DiskResponse::WriteResp{}
            &&& model.disk.content.contains_key(spec_superblock_addr())
            &&& model.disk.content[spec_superblock_addr()] == raw
        }
    } else {
        false
    }
}

pub open spec fn crash_aware_caching_disk_journal_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> CrashAwareCachingDiskJournal::State
{
    CrashAwareCachingDiskJournal::State{
        persistent: persistent_journal_image_i(model),
        ephemeral: ephemeral_journal_i(model),
        frozen: frozen_journal_metadata_i(model),
        prepared: atomic_superblock_prepared_i(model),
    }
}

pub open spec fn journal_projection_tight(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    let aus = journal_projection_aus(model);
    &&& journal_disk_persistent_i(model).dom() <= addresses_in_aus(aus)
    &&& journal_disk_cache_i(model).dom() <= addresses_in_aus(aus)
    &&& journal_disk_status_i(model).dom() <= addresses_in_aus(aus)
    &&& persistent_journal_image_i(model).persistent.dom() <= addresses_in_aus(aus)
    &&& frozen_journal_image_i(model) is Some ==>
        frozen_journal_image_i(model).unwrap().persistent.dom() <= addresses_in_aus(aus)
}

pub open spec fn journal_projection_uses_shared_async_disk(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    &&& journal_disk_persistent_i(model) <= model.disk.content
    &&& persistent_journal_image_i(model).persistent <= model.disk.content
    &&& frozen_journal_image_i(model) is Some ==>
        frozen_journal_image_i(model).unwrap().persistent <= model.disk.content
}

pub open spec fn journal_owned_disk_records_do_not_impersonate_index(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    !model.program.state.client_ready() && journal_projection_uses_live(model) ==> {
        let journal = model.program.state.journal;
        let snapshot = journal.journal.snapshot;
        let disk_view = DiskView{
            boundary_lsn: snapshot.boundary_lsn,
            entries: to_journal_records(model.disk.content),
        };
        let index = journal.journal.status.unwrap().lsn_au_index;
        forall |addr: Address, lsn: LSN| {
            &&& #[trigger] disk_view.entries.contains_key(addr)
            &&& model.program.state.journal_owned_aus().contains(addr.au)
            &&& #[trigger] index.contains_key(lsn)
            &&& index[lsn] == addr.au
            &&& disk_view.entries[addr].contains_lsn(snapshot.boundary_lsn, lsn)
        } ==> {
            ||| snapshot_walk_domain(
                disk_view.entries,
                snapshot.boundary_lsn,
                snapshot.freshest_rec(),
            ).contains(addr)
            ||| mini_allocator_allocated_addrs(journal.mini_allocator).contains(addr)
        }
    }
}

pub open spec fn journal_owned_cache_matches_disk_unless_allocated(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    model.program.state.journal_metadata_loaded() && !model.program.state.client_ready() ==> {
        let journal = model.program.state.journal;
        let cache_pages = filled_cache_pages(model.program.state.cache);
        forall |addr: Address| {
            &&& #[trigger] cache_pages.contains_key(addr)
            &&& model.program.state.journal_owned_aus().contains(addr.au)
            &&& !mini_allocator_allocated_addrs(journal.mini_allocator).contains(addr)
        } ==> {
            &&& model.disk.content.contains_key(addr)
            &&& model.disk.content[addr] == cache_pages[addr]
        }
    }
}

pub open spec fn journal_component_refinement_inv(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    &&& model.program.state.wf()
    &&& model.disk.inv()
    &&& async_disk_superblock_page_wf(model.disk.content)
    &&& crash_aware_caching_disk_journal_i(model).inv()
    &&& !model.program.state.journal_metadata_loaded() ==>
        model.program.state.journal.mini_allocator == crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty()
    &&& !model.program.state.client_ready() ==>
        model.program.state.journal.mini_allocator == crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty()
    &&& persistent_journal_image_i(model).wf()
    &&& journal_projection_tight(model)
    &&& journal_projection_uses_shared_async_disk(model)
    &&& journal_owned_disk_records_do_not_impersonate_index(model)
    &&& journal_image_projection_domain_i(model, atomic_persistent_superblock_image_i(model))
        <= addresses_in_aus(journal_projection_aus(model))
    &&& model.program.state.in_flight is Some ==>
        journal_image_projection_domain_i(
            model,
            model.program.state.atomic_inflight_superblock_i(),
        ) <= addresses_in_aus(journal_projection_aus(model))
    &&& journal_projection_uses_live(model) ==>
        to_aus(journal_projection_addrs(model)) <= model.program.state.journal_owned_aus()
    &&& journal_projection_uses_live(model) ==>
        journal_projection_aus(model) <= model.program.state.journal_owned_aus()
}

pub proof fn branch_writes_disjoint_from_journal_projection(
    model: SystemModel::State<AnotherProgramModel>,
    writes: Map<Address, RawPage>,
)
    requires
        journal_component_refinement_inv(model),
        model.program.state.journal_metadata_loaded(),
        to_aus(writes.dom()) <= model.program.state.branch_owned_aus(),
    ensures
        writes.dom().disjoint(addresses_in_aus(journal_projection_aus(model))),
        writes.dom().disjoint(journal_projection_addrs(model)),
{
    assert(model.program.state.allocation_wf());
    assert(model.program.state.component_disjoint());
    assert(model.program.state.journal_owned_aus().disjoint(model.program.state.branch_owned_aus()));
    to_aus_domain(writes.dom());
    assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
        implies !addresses_in_aus(journal_projection_aus(model)).contains(addr) by {
        assert(to_aus(writes.dom()).contains(addr.au));
        assert(model.program.state.branch_owned_aus().contains(addr.au));
        if addresses_in_aus(journal_projection_aus(model)).contains(addr) {
            assert(journal_projection_aus(model).contains(addr.au));
            assert(model.program.state.journal_owned_aus().contains(addr.au));
            assert(false);
        }
    }
    assert(writes.dom().disjoint(journal_projection_addrs(model))) by {
        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
            implies !journal_projection_addrs(model).contains(addr) by {
            assert(!addresses_in_aus(journal_projection_aus(model)).contains(addr));
            if journal_projection_addrs(model).contains(addr) {
                to_aus_domain(journal_projection_addrs(model));
                assert(to_aus(journal_projection_addrs(model)).contains(addr.au));
                assert(model.program.state.journal_owned_aus().contains(addr.au));
                assert(model.program.state.branch_owned_aus().contains(addr.au));
                assert(false);
            }
        }
    }
}

pub proof fn cache_access_reads_restricted_to_journal_projection_available(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        journal_component_refinement_inv(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads, writes},
        ),
    ensures
        reads.restrict(journal_projection_addrs(pre)) <= journal_disk_cache_i(pre),
{
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let lbl = Cache::Label::Access{reads, writes};
    assert(Cache::State::next_by(
        pre.program.state.cache,
        post.program.state.cache,
        lbl,
        Cache::Step::access(),
    ));
    assert(Cache::State::access(pre.program.state.cache, post.program.state.cache, lbl)) by {
        reveal(Cache::State::access);
    }
    reveal(Cache::State::access);
    assert(lbl is Access);
    assert(lbl->reads == reads);
    assert forall |addr: Address| #[trigger] reads.contains_key(addr)
        implies pre.program.state.cache.valid_read(addr, reads[addr]) by {
        assert(lbl->reads.contains_key(addr));
        assert(lbl->reads[addr] == reads[addr]);
    }
    assert forall |addr: Address| #[trigger] reads.restrict(journal_projection_addrs(pre)).contains_key(addr)
        implies journal_disk_cache_i(pre).contains_key(addr)
            && journal_disk_cache_i(pre)[addr]
                == reads.restrict(journal_projection_addrs(pre))[addr] by {
        assert(reads.contains_key(addr));
        assert(journal_projection_addrs(pre).contains(addr));
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
        assert(project_cache_pages_by_addrs(
            pre.program.state.cache,
            journal_projection_addrs(pre),
        ).contains_key(addr));
        assert(project_cache_pages_by_addrs(
            pre.program.state.cache,
            journal_projection_addrs(pre),
        )[addr] == reads[addr]);
    }
}

pub proof fn projected_caching_disk_read_only_access(
    model: SystemModel::State<AnotherProgramModel>,
    reads: Map<Address, RawPage>,
)
    requires
        reads <= journal_disk_cache_i(model),
    ensures
        CachingDisk::State::next(
            journal_caching_disk_i(model),
            journal_caching_disk_i(model),
            CachingDisk::Label::Access{reads, writes: Map::empty()},
        ),
{
    let disk = journal_caching_disk_i(model);
    assert(disk.cache.union_prefer_right(Map::<Address, RawPage>::empty()) == disk.cache);
    assert(disk.status.union_prefer_right(
        crate::implementation::CachingDisk_v::status_map(
            Set::<Address>::empty(),
            CachingDiskPageStatus::Dirty,
        ),
    ) == disk.status) by {
        assert_maps_equal!(
            disk.status.union_prefer_right(
                crate::implementation::CachingDisk_v::status_map(
                    Set::<Address>::empty(),
                    CachingDiskPageStatus::Dirty,
                ),
            ),
            disk.status,
            addr => {}
        );
    }
    assert(CachingDisk::State::next_by(
        disk,
        disk,
        CachingDisk::Label::Access{reads, writes: Map::empty()},
        CachingDisk::Step::access(),
    )) by {
        reveal(CachingDisk::State::next_by);
    }
    reveal(CachingDisk::State::next);
}

pub proof fn cache_read_only_access_projection_unchanged(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    reads: Map<Address, RawPage>,
)
    requires
        pre.program.state.cache.inv(),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads, writes: Map::empty()},
        ),
        pre.disk.content == post.disk.content,
        journal_projection_addrs(pre) =~= journal_projection_addrs(post),
        journal_persistent_projection_addrs(pre) =~= journal_persistent_projection_addrs(post),
    ensures
        journal_disk_cache_i(post) =~= journal_disk_cache_i(pre),
        journal_disk_status_i(post) =~= journal_disk_status_i(pre),
        journal_caching_disk_i(post) == journal_caching_disk_i(pre),
{
    projected_cache_read_only_access_unchanged_by_addrs(
        pre.program.state.cache,
        post.program.state.cache,
        journal_projection_addrs(pre),
        reads,
    );
    assert(project_persistent_by_addrs(post.disk, journal_persistent_projection_addrs(post))
        =~= project_persistent_by_addrs(pre.disk, journal_persistent_projection_addrs(pre))) by {
        assert_maps_equal!(
            project_persistent_by_addrs(post.disk, journal_persistent_projection_addrs(post)),
            project_persistent_by_addrs(pre.disk, journal_persistent_projection_addrs(pre)),
            addr => {
                assert(journal_persistent_projection_addrs(post).contains(addr)
                    <==> journal_persistent_projection_addrs(pre).contains(addr));
            }
        );
    }
    assert(project_cache_pages_by_addrs(post.program.state.cache, journal_projection_addrs(pre))
        =~= project_cache_pages_by_addrs(pre.program.state.cache, journal_projection_addrs(pre)));
    assert(project_cache_status_by_addrs(post.program.state.cache, journal_projection_addrs(pre))
        =~= project_cache_status_by_addrs(pre.program.state.cache, journal_projection_addrs(pre)));
    assert(project_cache_pages_by_addrs(post.program.state.cache, journal_projection_addrs(post))
        =~= project_cache_pages_by_addrs(post.program.state.cache, journal_projection_addrs(pre))) by {
        assert_maps_equal!(
            project_cache_pages_by_addrs(post.program.state.cache, journal_projection_addrs(post)),
            project_cache_pages_by_addrs(post.program.state.cache, journal_projection_addrs(pre)),
            addr => {
                assert(journal_projection_addrs(post).contains(addr)
                    <==> journal_projection_addrs(pre).contains(addr));
            }
        );
    }
    assert(project_cache_status_by_addrs(post.program.state.cache, journal_projection_addrs(post))
        =~= project_cache_status_by_addrs(post.program.state.cache, journal_projection_addrs(pre))) by {
        assert_maps_equal!(
            project_cache_status_by_addrs(post.program.state.cache, journal_projection_addrs(post)),
            project_cache_status_by_addrs(post.program.state.cache, journal_projection_addrs(pre)),
            addr => {
                assert(journal_projection_addrs(post).contains(addr)
                    <==> journal_projection_addrs(pre).contains(addr));
            }
        );
    }
    assert_maps_equal!(journal_disk_cache_i(post), journal_disk_cache_i(pre), addr => {
        assert(journal_projection_addrs(post).contains(addr)
            <==> journal_projection_addrs(pre).contains(addr));
    });
    assert_maps_equal!(journal_disk_status_i(post), journal_disk_status_i(pre), addr => {
        assert(journal_projection_addrs(post).contains(addr)
            <==> journal_projection_addrs(pre).contains(addr));
    });
}

pub proof fn cache_access_outside_journal_projection_unchanged(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
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
        pre.disk.content == post.disk.content,
        journal_projection_addrs(pre) =~= journal_projection_addrs(post),
        journal_persistent_projection_addrs(pre) =~= journal_persistent_projection_addrs(post),
        writes.dom().disjoint(journal_projection_addrs(pre)),
    ensures
        journal_disk_cache_i(post) =~= journal_disk_cache_i(pre),
        journal_disk_status_i(post) =~= journal_disk_status_i(pre),
        journal_caching_disk_i(post) == journal_caching_disk_i(pre),
{
    projected_cache_access_outside_addrs_unchanged(
        pre.program.state.cache,
        post.program.state.cache,
        journal_projection_addrs(pre),
        reads,
        writes,
    );
    assert(project_persistent_by_addrs(post.disk, journal_persistent_projection_addrs(post))
        =~= project_persistent_by_addrs(pre.disk, journal_persistent_projection_addrs(pre))) by {
        assert_maps_equal!(
            project_persistent_by_addrs(post.disk, journal_persistent_projection_addrs(post)),
            project_persistent_by_addrs(pre.disk, journal_persistent_projection_addrs(pre)),
            addr => {
                assert(journal_persistent_projection_addrs(post).contains(addr)
                    <==> journal_persistent_projection_addrs(pre).contains(addr));
            }
        );
    }
    assert(project_cache_pages_by_addrs(post.program.state.cache, journal_projection_addrs(pre))
        =~= project_cache_pages_by_addrs(pre.program.state.cache, journal_projection_addrs(pre)));
    assert(project_cache_status_by_addrs(post.program.state.cache, journal_projection_addrs(pre))
        =~= project_cache_status_by_addrs(pre.program.state.cache, journal_projection_addrs(pre)));
    assert(project_cache_pages_by_addrs(post.program.state.cache, journal_projection_addrs(post))
        =~= project_cache_pages_by_addrs(post.program.state.cache, journal_projection_addrs(pre))) by {
        assert_maps_equal!(
            project_cache_pages_by_addrs(post.program.state.cache, journal_projection_addrs(post)),
            project_cache_pages_by_addrs(post.program.state.cache, journal_projection_addrs(pre)),
            addr => {
                assert(journal_projection_addrs(post).contains(addr)
                    <==> journal_projection_addrs(pre).contains(addr));
            }
        );
    }
    assert(project_cache_status_by_addrs(post.program.state.cache, journal_projection_addrs(post))
        =~= project_cache_status_by_addrs(post.program.state.cache, journal_projection_addrs(pre))) by {
        assert_maps_equal!(
            project_cache_status_by_addrs(post.program.state.cache, journal_projection_addrs(post)),
            project_cache_status_by_addrs(post.program.state.cache, journal_projection_addrs(pre)),
            addr => {
                assert(journal_projection_addrs(post).contains(addr)
                    <==> journal_projection_addrs(pre).contains(addr));
            }
        );
    }
    assert_maps_equal!(journal_disk_cache_i(post), journal_disk_cache_i(pre), addr => {
        assert(journal_projection_addrs(post).contains(addr)
            <==> journal_projection_addrs(pre).contains(addr));
    });
    assert_maps_equal!(journal_disk_status_i(post), journal_disk_status_i(pre), addr => {
        assert(journal_projection_addrs(post).contains(addr)
            <==> journal_projection_addrs(pre).contains(addr));
    });
}

pub proof fn journal_projection_domains_unchanged_by_cache_access_outside(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        journal_component_refinement_inv(pre),
        pre.program.state.cache.inv(),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads, writes},
        ),
        post.disk.content == pre.disk.content,
        pre.program.state.superblock_metadata_known(),
        post.program.state.superblock_metadata_known(),
        journal_projection_uses_live(post) == journal_projection_uses_live(pre),
        post.program.state.journal_metadata_loaded() == pre.program.state.journal_metadata_loaded(),
        post.program.state.journal.journal.snapshot == pre.program.state.journal.journal.snapshot,
        post.program.state.journal.mini_allocator == pre.program.state.journal.mini_allocator,
        post.program.state.journal.journal.status.unwrap().lsn_au_index
            == pre.program.state.journal.journal.status.unwrap().lsn_au_index,
        post.program.state.journal.loaded_index_aus()
            =~= pre.program.state.journal.loaded_index_aus(),
        writes.dom().disjoint(journal_projection_addrs(pre)),
    ensures
        journal_projection_addrs(post) =~= journal_projection_addrs(pre),
        journal_persistent_projection_addrs(post) =~= journal_persistent_projection_addrs(pre),
        journal_projection_aus(post) =~= journal_projection_aus(pre),
{
    filled_cache_access_effect(pre.program.state.cache, post.program.state.cache, reads, writes);
    projected_cache_access_outside_addrs_unchanged(
        pre.program.state.cache,
        post.program.state.cache,
        journal_projection_addrs(pre),
        reads,
        writes,
    );

    let snapshot = pre.program.state.journal.journal.snapshot;
    let pre_pages = filled_cache_pages(pre.program.state.cache);
    let post_pages = filled_cache_pages(post.program.state.cache);
    let pre_overlay = pre.disk.content.union_prefer_right(pre_pages);
    let post_overlay = post.disk.content.union_prefer_right(post_pages);
    let raw_updates = writes;
    let pre_records = to_journal_records(pre_overlay);
    let post_records = to_journal_records(post_overlay);
    let updates = to_journal_records(raw_updates);
    let pre_disk_records = to_journal_records(pre.disk.content);
    let post_disk_records = to_journal_records(post.disk.content);
    assert(post_pages =~= pre_pages.union_prefer_right(writes));
    assert(post_overlay =~= pre_overlay.union_prefer_right(writes)) by {
        assert_maps_equal!(post_overlay, pre_overlay.union_prefer_right(writes), addr => {
            if writes.contains_key(addr) {
                assert(post_pages.contains_key(addr));
                assert(post_pages[addr] == writes[addr]);
            } else {
                if post_overlay.contains_key(addr) {
                    if post_pages.contains_key(addr) {
                        assert(pre_pages.contains_key(addr));
                        assert(post_pages[addr] == pre_pages[addr]);
                    } else {
                        assert(pre.disk.content.contains_key(addr));
                    }
                }
                if pre_overlay.union_prefer_right(writes).contains_key(addr) {
                    if pre_overlay.contains_key(addr) {
                        if pre_pages.contains_key(addr) {
                            assert(post_pages.contains_key(addr));
                            assert(post_pages[addr] == pre_pages[addr]);
                        } else {
                            assert(pre.disk.content.contains_key(addr));
                        }
                    }
                }
            }
        });
    }
    assert(post_records =~= pre_records.union_prefer_right(updates)) by {
        assert_maps_equal!(post_records, pre_records.union_prefer_right(updates), addr => {
            if updates.contains_key(addr) {
                assert(writes.contains_key(addr));
                assert(post_overlay.contains_key(addr));
                assert(post_overlay[addr] == writes[addr]);
            } else {
                if post_records.contains_key(addr) {
                    assert(post_overlay.contains_key(addr));
                    assert(pre_overlay.contains_key(addr));
                    assert(post_overlay[addr] == pre_overlay[addr]);
                }
                if pre_records.union_prefer_right(updates).contains_key(addr) {
                    assert(pre_records.contains_key(addr));
                    assert(pre_overlay.contains_key(addr));
                    assert(post_overlay.contains_key(addr));
                    assert(post_overlay[addr] == pre_overlay[addr]);
                }
            }
        });
    }
    if !journal_projection_uses_live(pre) {
        assert(post_disk_records == pre_disk_records);
        assert(snapshot_walk_domain(post_disk_records, snapshot.boundary_lsn, snapshot.freshest_rec())
            =~= snapshot_walk_domain(pre_disk_records, snapshot.boundary_lsn, snapshot.freshest_rec()));
    }

    assert(journal_projection_addrs(post) =~= journal_projection_addrs(pre)) by {
        if journal_projection_uses_live(pre) {
            assert(journal_projection_uses_live(post));
            assert(post.program.state.journal.mini_allocator.all_aus()
                == pre.program.state.journal.mini_allocator.all_aus());
            assert(post.program.state.journal.journal.status.unwrap().lsn_au_index
                == pre.program.state.journal.journal.status.unwrap().lsn_au_index);
            assert(mini_allocator_allocated_addrs(post.program.state.journal.mini_allocator)
                =~= mini_allocator_allocated_addrs(pre.program.state.journal.mini_allocator));
        } else {
            assert forall |addr: Address| #[trigger] journal_projection_addrs(post).contains(addr)
                <==> journal_projection_addrs(pre).contains(addr) by {
                if journal_projection_addrs(post).contains(addr) {
                    if mini_allocator_allocated_addrs(post.program.state.journal.mini_allocator).contains(addr) {
                        assert(mini_allocator_allocated_addrs(pre.program.state.journal.mini_allocator).contains(addr));
                    } else {
                        assert(snapshot_walk_domain(post_disk_records, snapshot.boundary_lsn, snapshot.freshest_rec()).contains(addr));
                        assert(snapshot_walk_domain(pre_disk_records, snapshot.boundary_lsn, snapshot.freshest_rec()).contains(addr));
                    }
                }
                if journal_projection_addrs(pre).contains(addr) {
                    if mini_allocator_allocated_addrs(pre.program.state.journal.mini_allocator).contains(addr) {
                        assert(mini_allocator_allocated_addrs(post.program.state.journal.mini_allocator).contains(addr));
                    } else {
                        assert(snapshot_walk_domain(pre_disk_records, snapshot.boundary_lsn, snapshot.freshest_rec()).contains(addr));
                        assert(snapshot_walk_domain(post_disk_records, snapshot.boundary_lsn, snapshot.freshest_rec()).contains(addr));
                    }
                }
            }
        }
    }
    assert(journal_persistent_projection_addrs(post) =~= journal_persistent_projection_addrs(pre)) by {
        assert forall |addr: Address| #[trigger] journal_persistent_projection_addrs(post).contains(addr)
            <==> journal_persistent_projection_addrs(pre).contains(addr) by {
            assert(journal_projection_addrs(post).contains(addr)
                <==> journal_projection_addrs(pre).contains(addr));
            let support = journal_projection_addrs(pre);
            let post_pages = filled_cache_pages(post.program.state.cache);
            let pre_pages = filled_cache_pages(pre.program.state.cache);
            let post_status =
                crate::implementation::CachingDiskAdapterRefinement_v::filled_cache_status(
                    post.program.state.cache,
                );
            let pre_status =
                crate::implementation::CachingDiskAdapterRefinement_v::filled_cache_status(
                    pre.program.state.cache,
                );
            assert(project_cache_pages_by_addrs(post.program.state.cache, support)
                =~= project_cache_pages_by_addrs(pre.program.state.cache, support));
            assert(project_cache_status_by_addrs(post.program.state.cache, support)
                =~= project_cache_status_by_addrs(pre.program.state.cache, support));
            if support.contains(addr) {
                assert(project_cache_pages_by_addrs(
                    post.program.state.cache,
                    support,
                ).contains_key(addr) <==> post_pages.contains_key(addr));
                assert(project_cache_pages_by_addrs(
                    pre.program.state.cache,
                    support,
                ).contains_key(addr) <==> pre_pages.contains_key(addr));
                assert(project_cache_status_by_addrs(
                    post.program.state.cache,
                    support,
                ).contains_key(addr) <==> post_status.contains_key(addr));
                assert(project_cache_status_by_addrs(
                    pre.program.state.cache,
                    support,
                ).contains_key(addr) <==> pre_status.contains_key(addr));
                assert(post_pages.contains_key(addr) <==> pre_pages.contains_key(addr));
                assert(post_status.contains_key(addr) <==> pre_status.contains_key(addr));
                if post_pages.contains_key(addr) {
                    assert(project_cache_pages_by_addrs(
                        post.program.state.cache,
                        support,
                    )[addr] == post_pages[addr]);
                    assert(project_cache_pages_by_addrs(
                        pre.program.state.cache,
                        support,
                    )[addr] == pre_pages[addr]);
                    assert(post_pages[addr] == pre_pages[addr]);
                }
                if post_status.contains_key(addr) {
                    assert(project_cache_status_by_addrs(
                        post.program.state.cache,
                        support,
                    )[addr] == post_status[addr]);
                    assert(project_cache_status_by_addrs(
                        pre.program.state.cache,
                        support,
                    )[addr] == pre_status[addr]);
                    assert(post_status[addr] == pre_status[addr]);
                }
            }
        }
    }
    assert(journal_projection_aus(post) =~= journal_projection_aus(pre)) by {
        to_aus_domain(journal_projection_addrs(post));
        to_aus_domain(journal_projection_addrs(pre));
        assert(to_aus(journal_projection_addrs(post)) =~= to_aus(journal_projection_addrs(pre))) by {
            assert forall |au: AU| #[trigger] to_aus(journal_projection_addrs(post)).contains(au)
                <==> to_aus(journal_projection_addrs(pre)).contains(au) by {
                if to_aus(journal_projection_addrs(post)).contains(au) {
                    let addr = choose |addr: Address|
                        journal_projection_addrs(post).contains(addr) && addr.au == au;
                    assert(journal_projection_addrs(pre).contains(addr));
                    assert(to_aus(journal_projection_addrs(pre)).contains(au));
                }
                if to_aus(journal_projection_addrs(pre)).contains(au) {
                    let addr = choose |addr: Address|
                        journal_projection_addrs(pre).contains(addr) && addr.au == au;
                    assert(journal_projection_addrs(post).contains(addr));
                    assert(to_aus(journal_projection_addrs(post)).contains(au));
                }
            }
        }
    }
}

pub proof fn journal_load_index_refines(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    reads: Map<Address, RawPage>,
    discovered_aus: Set<AU>,
)
    requires
        journal_component_refinement_inv(pre),
        AnotherAtomicState::journal_load_index(
            pre.program.state,
            post.program.state,
            reads,
            discovered_aus,
        ),
        post.disk == pre.disk,
        journal_projection_aus(post) =~= journal_projection_aus(pre),
        reads <= journal_disk_cache_i(pre),
        journal_image_projection_aus_i(post, durable_superblock_image_i(pre))
            =~= journal_image_projection_aus_i(pre, durable_superblock_image_i(pre)),
        pre.program.state.in_flight is None,
        post.program.state.in_flight is None,
    ensures
        CrashAwareCachingDiskJournal::State::next(
            crash_aware_caching_disk_journal_i(pre),
            crash_aware_caching_disk_journal_i(post),
            CrashAwareCachingDiskJournal::Label::LoadIndex{discovered_aus},
        ),
{
    let atomic_pre = pre.program.state;
    let atomic_post = post.program.state;
    let raw_lbl = Cache::Label::Access{reads, writes: Map::empty()};
    let journal_reads = to_journal_records(reads);
    let atomic_journal_lbl = AtomicJournalState::Label::LoadIndex{
        reads: journal_reads,
        discovered_aus,
    };

    AnotherAtomicState::journal_load_index_effect(
        pre.program.state,
        post.program.state,
        reads,
        discovered_aus,
    );
    assert(AnotherAtomicState::journal_load_index_cached_next(
        pre.program.state,
        post.program.state,
        reads,
        discovered_aus,
    ));
    assert(atomic_pre.recovery_state is SuperblockAvailable);
    assert(atomic_pre.superblock_metadata_known());
    assert(atomic_post.superblock_metadata_known());
    assert(CachedJournal::State::next(
        pre.program.state.journal.journal,
        post.program.state.journal.journal,
        CachedJournal::Label::LoadIndex{
            reads: to_journal_records(reads),
            discovered_aus,
        },
    )) by {
        assert(AnotherAtomicState::journal_load_index_cached_next(
            pre.program.state,
            post.program.state,
            reads,
            discovered_aus,
        ));
    }
    CachedJournal::State::load_index_effect(
        pre.program.state.journal.journal,
        post.program.state.journal.journal,
        to_journal_records(reads),
        discovered_aus,
    );
    assert(atomic_post.journal.journal.snapshot == atomic_pre.journal.journal.snapshot);
    assert(atomic_post.journal.mini_allocator == atomic_pre.journal.mini_allocator);
    filled_cache_read_only_access_unchanged(
        pre.program.state.cache,
        post.program.state.cache,
        reads,
    );
    assert(filled_cache_pages(post.program.state.cache)
        =~= filled_cache_pages(pre.program.state.cache));
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
            assert(crate::implementation::CachingDiskAdapterRefinement_v::filled_cache_status(
                post.program.state.cache,
            ).contains_key(addr)
                <==> crate::implementation::CachingDiskAdapterRefinement_v::filled_cache_status(
                    pre.program.state.cache,
                ).contains_key(addr));
        }
    }

    cache_read_only_access_projection_unchanged(pre, post, reads);
    assert(journal_caching_disk_i(post) == journal_caching_disk_i(pre));
    projected_caching_disk_read_only_access(pre, reads);
    assert(journal_caching_disk_state_i(post).disk == journal_caching_disk_state_i(pre).disk);
    assert(journal_caching_disk_state_i(post).mini_allocator
        == journal_caching_disk_state_i(pre).mini_allocator);

    let src = crash_aware_caching_disk_journal_i(pre);
    let dst = crash_aware_caching_disk_journal_i(post);
    let lbl = CrashAwareCachingDiskJournal::Label::LoadIndex{discovered_aus};
    let inner_lbl = CachingDiskJournal::Label::LoadIndex{discovered_aus};

    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(src.ephemeral->v == journal_caching_disk_state_i(pre));
    assert(dst.ephemeral->v == journal_caching_disk_state_i(post));
    assert(src.ephemeral->v.journal == pre.program.state.journal.journal);
    assert(dst.ephemeral->v.journal == post.program.state.journal.journal);
    assert(atomic_post.journal.journal == post.program.state.journal.journal);
    reveal(CachedJournal::State::next);
    let cj_lbl = CachedJournal::Label::LoadIndex{
        reads: to_journal_records(reads),
        discovered_aus,
    };
    assert(exists |step: CachedJournal::Step| CachedJournal::State::next_by(
        pre.program.state.journal.journal,
        post.program.state.journal.journal,
        cj_lbl,
        step,
    )) by {
        assert(AnotherAtomicState::journal_load_index_cached_next(
            pre.program.state,
            post.program.state,
            reads,
            discovered_aus,
        ));
    }
    let cj_step = choose |step: CachedJournal::Step|
        CachedJournal::State::next_by(
            pre.program.state.journal.journal,
            post.program.state.journal.journal,
            cj_lbl,
            step,
        );
    assert(CachedJournal::State::next_by(
        pre.program.state.journal.journal,
        post.program.state.journal.journal,
        cj_lbl,
        cj_step,
    ));
    assert(CachedJournal::State::next(
        pre.program.state.journal.journal,
        post.program.state.journal.journal,
        cj_lbl,
    ));
    assert(CachedJournal::State::next(
        src.ephemeral->v.journal,
        atomic_post.journal.journal,
        CachedJournal::Label::LoadIndex{
            reads: to_journal_records(reads),
            discovered_aus,
        },
    ));

    assert(CachingDiskJournal::State::next_by(
        src.ephemeral->v,
        dst.ephemeral->v,
        inner_lbl,
        CachingDiskJournal::Step::load_index(atomic_post.journal.journal, reads),
    )) by {
        reveal(CachingDiskJournal::State::next_by);
    }
    reveal(CachingDiskJournal::State::next);
    let persistent_image = durable_superblock_image_i(pre);
    assert(durable_superblock_image_i(post) == persistent_image);
    assert(journal_image_projection_aus_i(post, persistent_image)
        =~= journal_image_projection_aus_i(pre, persistent_image));
    journal_image_persistent_unchanged_for_same_projection(pre, post, persistent_image);
    assert(dst.persistent == src.persistent);
    assert(post.program.state.in_flight == pre.program.state.in_flight);
    assert(post.program.state.in_flight is None);
    assert(dst.frozen == src.frozen);

    assert(CrashAwareCachingDiskJournal::State::next_by(
        src,
        dst,
        lbl,
        CrashAwareCachingDiskJournal::Step::load_index(dst.ephemeral->v),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next_by);
    }
    reveal(CrashAwareCachingDiskJournal::State::next);
}

pub proof fn journal_execute_put_refines(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    req: Request,
    reply: Reply,
    receipt: LoadedPathReceipt,
    init_root: Option<Address>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    branch: crate::implementation::AnotherAtomicState_v::AtomicBranchState::State,
)
    requires
        journal_component_refinement_inv(pre),
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
        to_aus(writes.dom()) <= pre.program.state.branch_owned_aus(),
        journal_owned_cache_matches_disk_unless_allocated(pre),
    ensures
        CrashAwareCachingDiskJournal::State::next(
            crash_aware_caching_disk_journal_i(pre),
            crash_aware_caching_disk_journal_i(post),
            CrashAwareCachingDiskJournal::Label::Put{
                records: MsgHistory::singleton_at(
                    pre.program.state.branch.seq_end(),
                    KeyedMessage{
                        key: req.input.arrow_PutInput_key(),
                        message: Message::Define{value: req.input.arrow_PutInput_value()},
                    },
                ),
            },
        ),
{
    let key = req.input.arrow_PutInput_key();
    let value = req.input.arrow_PutInput_value();
    let msg = Message::Define{value};
    let keyed_message = KeyedMessage{key, message: msg};
    let records = MsgHistory::singleton_at(pre.program.state.branch.seq_end(), keyed_message);
    let atomic_lbl = AtomicJournalState::Label::Put{messages: records};

    AnotherAtomicState::execute_put_journal_effect(
        pre.program.state,
        post.program.state,
        req,
        reply,
        receipt,
        init_root,
        reads,
        writes,
        branch,
    );
    assert(pre.program.state.client_ready());
    assert(pre.program.state.recovery_state is RecoveryComplete);
    assert(pre.program.state.journal_metadata_loaded());
    assert(post.program.state.journal_metadata_loaded());
    assert(CachedJournal::State::next(
        pre.program.state.journal.journal,
        post.program.state.journal.journal,
        CachedJournal::Label::Put{messages: records},
    ));
    CachedJournal::State::put_effect(
        pre.program.state.journal.journal,
        post.program.state.journal.journal,
        records,
    );
    let branch_lbl = AtomicBranchState::Label::Append{
        keys: seq![key],
        msgs: seq![msg],
        receipt,
        init_root,
        read_nodes: crate::implementation::AnotherAtomicState_v::to_branch_nodes(reads),
        write_nodes: crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes),
    };
    AtomicBranchState::State::append_effect(pre.program.state.branch, branch, branch_lbl);
    assert(post.program.state.branch == branch);

    branch_writes_disjoint_from_journal_projection(pre, writes);
    journal_projection_domains_unchanged_by_cache_access_outside(pre, post, reads, writes);
    assert(journal_projection_aus(post) =~= journal_projection_aus(pre));
    cache_access_outside_journal_projection_unchanged(pre, post, reads, writes);
    assert(journal_caching_disk_state_i(post).disk == journal_caching_disk_state_i(pre).disk);
    assert(journal_caching_disk_state_i(post).mini_allocator
        == journal_caching_disk_state_i(pre).mini_allocator);

    let src = crash_aware_caching_disk_journal_i(pre);
    let dst = crash_aware_caching_disk_journal_i(post);
    let lbl = CrashAwareCachingDiskJournal::Label::Put{records};
    let inner_lbl = CachingDiskJournal::Label::Put{messages: records};

    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(src.ephemeral->v == journal_caching_disk_state_i(pre));
    assert(dst.ephemeral->v == journal_caching_disk_state_i(post));
    assert(CachedJournal::State::next(
        src.ephemeral->v.journal,
        dst.ephemeral->v.journal,
        CachedJournal::Label::Put{messages: records},
    ));
    assert(dst.ephemeral->v.journal.status.unwrap().lsn_au_index
        == src.ephemeral->v.journal.status.unwrap().lsn_au_index);
    assert(post.program.state.in_flight == pre.program.state.in_flight);
    assert(post.program.state.journal.in_flight == pre.program.state.journal.in_flight);
    assert(post.program.state.branch.in_flight == pre.program.state.branch.in_flight);
    journal_images_unchanged_by_loaded_index_preservation(pre, post);
    assert(CachingDiskJournal::State::next_by(
        src.ephemeral->v,
        dst.ephemeral->v,
        inner_lbl,
        CachingDiskJournal::Step::put(dst.ephemeral->v.journal),
    )) by {
        reveal(CachingDiskJournal::State::next_by);
    }
    reveal(CachingDiskJournal::State::next);
    assert(dst.persistent == src.persistent);
    assert(dst.frozen == src.frozen);

    assert(CrashAwareCachingDiskJournal::State::next_by(
        src,
        dst,
        lbl,
        CrashAwareCachingDiskJournal::Step::put(dst.ephemeral->v),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next_by);
    }
    reveal(CrashAwareCachingDiskJournal::State::next);
}

pub proof fn journal_read_for_recovery_refines(
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
    branch: crate::implementation::AnotherAtomicState_v::AtomicBranchState::State,
)
    requires
        journal_component_refinement_inv(pre),
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
        to_aus(writes.dom()) <= pre.program.state.branch_owned_aus(),
        journal_owned_cache_matches_disk_unless_allocated(pre),
    ensures
        CrashAwareCachingDiskJournal::State::next(
            crash_aware_caching_disk_journal_i(pre),
            crash_aware_caching_disk_journal_i(post),
            CrashAwareCachingDiskJournal::Label::ReadForRecovery{
                records: to_journal_records(journal_reads)[addr].message_seq.maybe_discard_old(
                    pre.program.state.journal.journal.snapshot.boundary_lsn,
                ),
            },
        ),
{
    let reads = journal_reads.union_prefer_right(branch_reads);
    let full_journal_reads = to_journal_records(journal_reads);
    let records = full_journal_reads[addr].message_seq.maybe_discard_old(
        pre.program.state.journal.journal.snapshot.boundary_lsn,
    );
    let raw_journal_reads = journal_reads.restrict(journal_projection_addrs(pre));
    let restricted_journal_reads = to_journal_records(raw_journal_reads);

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
    assert(pre.program.state.recovery_state is MetadataLoadComplete);
    assert(pre.program.state.journal_metadata_loaded());
    assert(post.program.state.journal_metadata_loaded());

    branch_writes_disjoint_from_journal_projection(pre, writes);
    journal_projection_domains_unchanged_by_cache_access_outside(pre, post, reads, writes);
    assert(journal_projection_aus(post) =~= journal_projection_aus(pre));
    cache_access_outside_journal_projection_unchanged(pre, post, reads, writes);
    cache_access_reads_restricted_to_journal_projection_available(pre, post, reads, writes);
    projected_caching_disk_read_only_access(pre, raw_journal_reads);

    let full_lbl = CachedJournal::Label::ReadForRecovery{
        messages: records,
        reads: full_journal_reads,
    };
    let restricted_lbl = CachedJournal::Label::ReadForRecovery{
        messages: records,
        reads: restricted_journal_reads,
    };
    reveal(CachedJournal::State::next);
    reveal(CachedJournal::State::next_by);
    let cj_step = choose |step: CachedJournal::Step|
        CachedJournal::State::next_by(
            pre.program.state.journal.journal,
            pre.program.state.journal.journal,
            full_lbl,
            step,
        );
    assert(CachedJournal::State::next_by(
        pre.program.state.journal.journal,
        pre.program.state.journal.journal,
        full_lbl,
        cj_step,
    ));
    match cj_step {
        CachedJournal::Step::read_for_recovery(start_lsn, read_addr) => {
            assert(CachedJournal::State::read_for_recovery(
                pre.program.state.journal.journal,
                pre.program.state.journal.journal,
                full_lbl,
                start_lsn,
                read_addr,
            )) by {
                reveal(CachedJournal::State::read_for_recovery);
            }
            reveal(CachedJournal::State::read_for_recovery);
            assert(pre.program.state.journal.journal.status is Some);
            let index = pre.program.state.journal.journal.status.unwrap().lsn_au_index;
            assert(index.contains_key(start_lsn));
            assert(index[start_lsn] == read_addr.au);
            assert(index.values().contains(read_addr.au));
            assert(journal_projection_aus(pre).contains(read_addr.au)) by {
                assert(pre.program.state.journal.loaded_index_aus().contains(read_addr.au));
            }
            assert(addresses_in_aus(journal_projection_aus(pre)).contains(read_addr));
            assert(!pre.program.state.client_ready());
            assert(pre.program.state.journal.mini_allocator
                == crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty());
            assert(pre.program.state.journal.mini_allocator.all_aus() =~= Set::<AU>::empty());
            assert(pre.program.state.journal.loaded_index_aus().contains(read_addr.au));
            assert(journal_projection_uses_live(pre));
            assert(full_journal_reads.contains_key(read_addr));
            assert(reads.contains_key(read_addr));
            assert(pre.program.state.cache.valid_read(read_addr, reads[read_addr])) by {
                let cache_lbl = Cache::Label::Access{reads, writes};
                assert(Cache::State::next(
                    pre.program.state.cache,
                    post.program.state.cache,
                    cache_lbl,
                ));
                reveal(Cache::State::next);
                reveal(Cache::State::next_by);
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
                reveal(Cache::State::access);
                assert(cache_lbl is Access);
                assert(cache_lbl->reads == reads);
                assert(cache_lbl->reads.contains_key(read_addr));
                assert(cache_lbl->reads[read_addr] == reads[read_addr]);
            }
            pre.program.state.cache.build_lookup_map_ensures();
            assert(cache_filled_addr(pre.program.state.cache, read_addr)) by {
                assert(pre.program.state.cache.lookup_map.contains_key(read_addr));
                assert(pre.program.state.cache.entries[
                    pre.program.state.cache.lookup_map[read_addr]
                ] is Filled);
                assert(pre.program.state.cache.entries.contains_key(
                    pre.program.state.cache.lookup_map[read_addr],
                ));
            }
            let cache_pages = filled_cache_pages(pre.program.state.cache);
            assert(cache_pages.contains_key(read_addr));
            assert(cache_pages[read_addr] == reads[read_addr]);
            assert(pre.program.state.journal_owned_aus().contains(read_addr.au)) by {
                assert(pre.program.state.journal.owned_aus().contains(read_addr.au));
            }
            assert(!mini_allocator_allocated_addrs(
                pre.program.state.journal.mini_allocator,
            ).contains(read_addr)) by {
                assert(pre.program.state.journal.mini_allocator
                    == crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty());
            }
            assert(journal_owned_cache_matches_disk_unless_allocated(pre));
            assert(pre.disk.content.contains_key(read_addr));
            assert(pre.disk.content[read_addr] == reads[read_addr]);
            let disk_view = DiskView{
                boundary_lsn: pre.program.state.journal.journal.snapshot.boundary_lsn,
                entries: to_journal_records(pre.disk.content),
            };
            assert(disk_view.entries.contains_key(read_addr));
            assert(disk_view.entries[read_addr] == full_journal_reads[read_addr]);
            let record = full_journal_reads[read_addr];
            let cropped = record.message_seq.maybe_discard_old(
                pre.program.state.journal.journal.snapshot.boundary_lsn,
            );
            assert(start_lsn == cropped.seq_start);
            assert(start_lsn < record.message_seq.seq_end);
            assert(disk_view.entries[read_addr].contains_lsn(
                pre.program.state.journal.journal.snapshot.boundary_lsn,
                start_lsn,
            )) by {
                if record.message_seq.seq_start
                    <= pre.program.state.journal.journal.snapshot.boundary_lsn {
                    assert(cropped.seq_start
                        == pre.program.state.journal.journal.snapshot.boundary_lsn);
                } else {
                    assert(cropped.seq_start == record.message_seq.seq_start);
                }
            }
            assert(snapshot_walk_domain(
                disk_view.entries,
                pre.program.state.journal.journal.snapshot.boundary_lsn,
                pre.program.state.journal.journal.snapshot.freshest_rec(),
            ).contains(read_addr)
                || mini_allocator_allocated_addrs(
                    pre.program.state.journal.mini_allocator,
                ).contains(read_addr)) by {
                assert(journal_owned_disk_records_do_not_impersonate_index(pre));
            }
            assert(snapshot_walk_domain(
                disk_view.entries,
                pre.program.state.journal.journal.snapshot.boundary_lsn,
                pre.program.state.journal.journal.snapshot.freshest_rec(),
            ).contains(read_addr));
            assert(live_journal_projection_addrs(pre).contains(read_addr));
            assert(journal_projection_addrs(pre).contains(read_addr));
            assert(raw_journal_reads.contains_key(read_addr));
            assert(raw_journal_reads[read_addr] == reads[read_addr]);
            assert(restricted_journal_reads.contains_key(read_addr));
            assert(restricted_journal_reads[read_addr] == full_journal_reads[read_addr]);
            assert(CachedJournal::State::read_for_recovery(
                pre.program.state.journal.journal,
                pre.program.state.journal.journal,
                restricted_lbl,
                start_lsn,
                read_addr,
            ));
            assert(CachedJournal::State::next_by(
                pre.program.state.journal.journal,
                pre.program.state.journal.journal,
                restricted_lbl,
                CachedJournal::Step::read_for_recovery(start_lsn, read_addr),
            )) by {
                reveal(CachedJournal::State::next_by);
            }
        },
        _ => {
            assert(false);
        },
    }
    assert(exists |step: CachedJournal::Step| CachedJournal::State::next_by(
        pre.program.state.journal.journal,
        pre.program.state.journal.journal,
        restricted_lbl,
        step,
    ));
    assert(CachedJournal::State::next(
        pre.program.state.journal.journal,
        pre.program.state.journal.journal,
        restricted_lbl,
    )) by {
        reveal(CachedJournal::State::next);
    }

    let src = crash_aware_caching_disk_journal_i(pre);
    let dst = crash_aware_caching_disk_journal_i(post);
    let lbl = CrashAwareCachingDiskJournal::Label::ReadForRecovery{records};
    let inner_lbl = CachingDiskJournal::Label::ReadForRecovery{messages: records};

    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(journal_caching_disk_state_i(post) == journal_caching_disk_state_i(pre)) by {
        assert(post.program.state.journal == pre.program.state.journal);
        assert(journal_caching_disk_i(post) == journal_caching_disk_i(pre));
    }
    assert(CachingDiskJournal::State::next_by(
        src.ephemeral->v,
        src.ephemeral->v,
        inner_lbl,
        CachingDiskJournal::Step::read_for_recovery(raw_journal_reads),
    )) by {
        reveal(CachingDiskJournal::State::next_by);
    }
    reveal(CachingDiskJournal::State::next);

    assert(CrashAwareCachingDiskJournal::State::next_by(
        src,
        dst,
        lbl,
        CrashAwareCachingDiskJournal::Step::read_for_recovery(),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next_by);
    }
    reveal(CrashAwareCachingDiskJournal::State::next);
}

pub proof fn journal_query_end_lsn_refines(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
)
    requires
        journal_component_refinement_inv(pre),
        AnotherAtomicState::recovery_complete(pre.program.state, post.program.state),
        post.disk == pre.disk,
    ensures
        CrashAwareCachingDiskJournal::State::next(
            crash_aware_caching_disk_journal_i(pre),
            crash_aware_caching_disk_journal_i(post),
            CrashAwareCachingDiskJournal::Label::QueryEndLsn{
                end_lsn: pre.program.state.branch.seq_end(),
            },
        ),
{
    let end_lsn = pre.program.state.branch.seq_end();
    let atomic_lbl = AtomicJournalState::Label::QueryEndLsn{end_lsn};
    reveal(AtomicJournalState::State::next);
    reveal(AtomicJournalState::State::next_by);
    let atomic_step = choose |step: AtomicJournalState::Step|
        AtomicJournalState::State::next_by(pre.program.state.journal, post.program.state.journal, atomic_lbl, step);
    match atomic_step {
        AtomicJournalState::Step::query_end_lsn(new_journal) => {
            assert(AtomicJournalState::State::query_end_lsn(
                pre.program.state.journal,
                post.program.state.journal,
                atomic_lbl,
                new_journal,
            )) by {
                reveal(AtomicJournalState::State::query_end_lsn);
            }
            assert(new_journal == post.program.state.journal.journal);
            let cj_lbl = CachedJournal::Label::QueryEndLsn{end_lsn};
            assert(CachedJournal::State::next(
                pre.program.state.journal.journal,
                new_journal,
                cj_lbl,
            ));
            reveal(CachedJournal::State::next);
            reveal(CachedJournal::State::next_by);
            let cj_step = choose |step: CachedJournal::Step|
                CachedJournal::State::next_by(pre.program.state.journal.journal, new_journal, cj_lbl, step);
            match cj_step {
                CachedJournal::Step::query_end_lsn() => {
                    assert(CachedJournal::State::query_end_lsn(
                        pre.program.state.journal.journal,
                        new_journal,
                        cj_lbl,
                    )) by {
                        reveal(CachedJournal::State::query_end_lsn);
                    }
                },
                _ => {
                    assert(false);
                },
            }
            assert(new_journal == pre.program.state.journal.journal);
        },
        _ => {
            assert(false);
        },
    }
    assert(post.program.state.in_flight == pre.program.state.in_flight);
    assert(post.program.state.journal.in_flight == pre.program.state.journal.in_flight);
    assert(post.program.state.branch.in_flight == pre.program.state.branch.in_flight);
    journal_images_unchanged_by_loaded_index_preservation(pre, post);

    let src = crash_aware_caching_disk_journal_i(pre);
    let dst = crash_aware_caching_disk_journal_i(post);
    let lbl = CrashAwareCachingDiskJournal::Label::QueryEndLsn{end_lsn};
    assert(pre.program.state.recovery_state is MetadataLoadComplete);
    assert(pre.program.state.superblock_metadata_known());
    assert(post.program.state.superblock_metadata_known());
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(dst.ephemeral->v == src.ephemeral->v) by {
        assert(post.program.state.journal.journal == pre.program.state.journal.journal);
        assert(post.program.state.journal.mini_allocator == pre.program.state.journal.mini_allocator);
        assert(journal_caching_disk_i(post) == journal_caching_disk_i(pre));
    }

    let cj_lbl = CachingDiskJournal::Label::QueryEndLsn{end_lsn};
    assert(CachingDiskJournal::State::next_by(
        src.ephemeral->v,
        src.ephemeral->v,
        cj_lbl,
        CachingDiskJournal::Step::query_end_lsn(),
    )) by {
        reveal(CachingDiskJournal::State::next_by);
    }
    reveal(CachingDiskJournal::State::next);
    assert(CrashAwareCachingDiskJournal::State::next_by(
        src,
        dst,
        lbl,
        CrashAwareCachingDiskJournal::Step::query_end_lsn(),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next_by);
    }
    reveal(CrashAwareCachingDiskJournal::State::next);
}

pub proof fn journal_observe_clean_aus_refines(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    aus: Set<AU>,
)
    requires
        journal_component_refinement_inv(pre),
        AnotherAtomicState::acknowledge_flushed_journal_aus(pre.program.state, post.program.state, aus),
        post.disk == pre.disk,
        journal_projection_aus(post) =~= journal_projection_aus(pre),
    ensures
        CrashAwareCachingDiskJournal::State::next(
            crash_aware_caching_disk_journal_i(pre),
            crash_aware_caching_disk_journal_i(post),
            CrashAwareCachingDiskJournal::Label::ObserveCleanAUs{aus},
        ),
{
    let src = crash_aware_caching_disk_journal_i(pre);
    let dst = crash_aware_caching_disk_journal_i(post);
    let raw_lbl = Cache::Label::EvictableCheck{aus};
    assert(pre.program.state.client_ready());
    assert(pre.program.state.superblock_metadata_known());
    assert(post.program.state.superblock_metadata_known());
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let cache_step = choose |step: Cache::Step|
        Cache::State::next_by(pre.program.state.cache, post.program.state.cache, raw_lbl, step);
    match cache_step {
        Cache::Step::evictable() => {
            assert(Cache::State::evictable(pre.program.state.cache, post.program.state.cache, raw_lbl)) by {
                reveal(Cache::State::evictable);
            }
        },
        _ => {
            assert(false);
        },
    }
    assert(post.program.state.cache == pre.program.state.cache);

    assert(src.ephemeral->v.disk.aus_clean_or_evictable(aus)) by {
        assert forall |addr: Address| #[trigger] src.ephemeral->v.disk.cache.contains_key(addr)
            && aus.contains(addr.au) implies {
                &&& src.ephemeral->v.disk.status.contains_key(addr)
                &&& src.ephemeral->v.disk.status[addr] == CachingDiskPageStatus::Clean
            } by {
            assert(journal_disk_cache_i(pre).contains_key(addr));
            assert(project_cache_pages_by_addrs(
                pre.program.state.cache,
                journal_projection_addrs(pre),
            ).contains_key(addr));
            assert(cache_filled_addr(pre.program.state.cache, addr));
            reveal(Cache::State::evictable);
            assert(pre.program.state.cache.status_map[
                pre.program.state.cache.lookup_map[addr]
            ] is Clean);
            assert(crate::implementation::CachingDiskAdapterRefinement_v::filled_cache_status(
                pre.program.state.cache,
            ).contains_key(addr));
            assert(journal_disk_status_i(pre).contains_key(addr));
            assert(journal_disk_status_i(pre)[addr] == CachingDiskPageStatus::Clean);
        }
    }
    assert(CachingDisk::State::next_by(
        src.ephemeral->v.disk,
        src.ephemeral->v.disk,
        CachingDisk::Label::ObserveCleanAUs{aus},
        CachingDisk::Step::observe_clean_aus(),
    )) by {
        reveal(CachingDisk::State::next_by);
    }
    reveal(CachingDisk::State::next);

    let atomic_lbl = AtomicJournalState::Label::ObserveCleanAUs{aus};
    reveal(AtomicJournalState::State::next);
    reveal(AtomicJournalState::State::next_by);
    let atomic_step = choose |step: AtomicJournalState::Step|
        AtomicJournalState::State::next_by(pre.program.state.journal, post.program.state.journal, atomic_lbl, step);
    match atomic_step {
        AtomicJournalState::Step::observe_clean_aus(new_journal) => {
            assert(AtomicJournalState::State::observe_clean_aus(
                pre.program.state.journal,
                post.program.state.journal,
                atomic_lbl,
                new_journal,
            )) by {
                reveal(AtomicJournalState::State::observe_clean_aus);
            }
            assert(new_journal == post.program.state.journal.journal);
            CachedJournal::State::observe_clean_aus_effect(
                pre.program.state.journal.journal,
                post.program.state.journal.journal,
                aus,
            );
            assert(post.program.state.journal.journal.status.unwrap().lsn_au_index
                == pre.program.state.journal.journal.status.unwrap().lsn_au_index);
        },
        _ => {
            assert(false);
        },
    }
    assert(post.program.state.in_flight == pre.program.state.in_flight);
    assert(post.program.state.journal.in_flight == pre.program.state.journal.in_flight);
    assert(post.program.state.branch.in_flight == pre.program.state.branch.in_flight);
    journal_images_unchanged_by_loaded_index_preservation(pre, post);
    assert(journal_caching_disk_i(post) == journal_caching_disk_i(pre)) by {
        assert(post.disk == pre.disk);
        assert(post.program.state.cache == pre.program.state.cache);
    }
    assert(dst.ephemeral->v.disk == src.ephemeral->v.disk);
    assert(dst.ephemeral->v.mini_allocator == src.ephemeral->v.mini_allocator);
    let cj_lbl = CachingDiskJournal::Label::ObserveCleanAUs{aus};
    assert(CachingDiskJournal::State::next_by(
        src.ephemeral->v,
        dst.ephemeral->v,
        cj_lbl,
        CachingDiskJournal::Step::observe_clean_aus(post.program.state.journal.journal),
    )) by {
        reveal(CachingDiskJournal::State::next_by);
    }
    reveal(CachingDiskJournal::State::next);
    assert(dst.persistent == src.persistent);
    assert(dst.frozen == src.frozen);
    assert(CrashAwareCachingDiskJournal::State::next_by(
        src,
        dst,
        CrashAwareCachingDiskJournal::Label::ObserveCleanAUs{aus},
        CrashAwareCachingDiskJournal::Step::observe_clean_aus(dst.ephemeral->v),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next_by);
    }
    reveal(CrashAwareCachingDiskJournal::State::next);
}

pub proof fn journal_fill_aus_refines(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    aus: Set<AU>,
)
    requires
        journal_component_refinement_inv(pre),
        AnotherAtomicState::journal_fill_aus(pre.program.state, post.program.state, aus),
        post.disk == pre.disk,
    ensures
        CrashAwareCachingDiskJournal::State::next(
            crash_aware_caching_disk_journal_i(pre),
            crash_aware_caching_disk_journal_i(post),
            CrashAwareCachingDiskJournal::Label::InternalAlloc{
                allocs: aus,
                deallocs: Set::empty(),
                prune_aus: Set::empty(),
            },
        ),
{
    let src = crash_aware_caching_disk_journal_i(pre);
    let dst = crash_aware_caching_disk_journal_i(post);
    let lbl = CrashAwareCachingDiskJournal::Label::InternalAlloc{
        allocs: aus,
        deallocs: Set::empty(),
        prune_aus: Set::empty(),
    };
    let cj_lbl = CachingDiskJournal::Label::InternalAlloc{
        allocs: aus,
        deallocs: Set::empty(),
        prune_aus: Set::empty(),
    };
    let atomic_lbl = AtomicJournalState::Label::FillAUs{aus};
    assert(pre.program.state.client_ready());
    assert(pre.program.state.journal_metadata_loaded());
    assert(pre.program.state.superblock_metadata_known());
    assert(post.program.state.superblock_metadata_known());
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);

    reveal(AtomicJournalState::State::next);
    reveal(AtomicJournalState::State::next_by);
    let atomic_step = choose |step: AtomicJournalState::Step|
        AtomicJournalState::State::next_by(pre.program.state.journal, post.program.state.journal, atomic_lbl, step);
    match atomic_step {
        AtomicJournalState::Step::fill_aus() => {
            assert(AtomicJournalState::State::fill_aus(
                pre.program.state.journal,
                post.program.state.journal,
                atomic_lbl,
            )) by {
                reveal(AtomicJournalState::State::fill_aus);
            }
        },
        _ => {
            assert(false);
        },
    }

    assert(post.program.state.journal.journal == pre.program.state.journal.journal);
    assert(post.program.state.journal.persistent_seq_end == pre.program.state.journal.persistent_seq_end);
    assert(post.program.state.journal.mini_allocator
        == pre.program.state.journal.mini_allocator.add_aus(aus));
    assert(journal_caching_disk_i(post) == journal_caching_disk_i(pre)) by {
        assert(post.program.state.cache == pre.program.state.cache);
        assert(post.disk == pre.disk);
    }
    assert(dst.ephemeral->v.journal == src.ephemeral->v.journal);
    assert(dst.ephemeral->v.disk == src.ephemeral->v.disk);
    assert(dst.ephemeral->v.mini_allocator == src.ephemeral->v.mini_allocator.add_aus(aus));

    assert(aus.disjoint(caching_disk_journal_accessible_aus(src.ephemeral->v))) by {
        assert(aus <= pre.program.state.free_aus);
        assert(pre.program.state.allocation_wf());
        assert(pre.program.state.free_aus.disjoint(pre.program.state.journal_owned_aus()));
        assert forall |au: AU| #[trigger] aus.contains(au)
            implies !caching_disk_journal_accessible_aus(src.ephemeral->v).contains(au) by {
            assert(pre.program.state.free_aus.contains(au));
            if caching_disk_journal_accessible_aus(src.ephemeral->v).contains(au) {
                assert(src.ephemeral->v.journal.status is Some);
                if src.ephemeral->v.mini_allocator.all_aus().contains(au) {
                    assert(pre.program.state.journal.mini_allocator.all_aus().contains(au));
                    assert(pre.program.state.journal_owned_aus().contains(au));
                } else {
                    assert(src.ephemeral->v.lsn_au_index_or_empty().values().contains(au));
                    assert(pre.program.state.journal.loaded_index_aus().contains(au));
                    assert(pre.program.state.journal_owned_aus().contains(au));
                }
                assert(false);
            }
        }
    }

    assert(CachingDiskJournal::State::next_by(
        src.ephemeral->v,
        dst.ephemeral->v,
        cj_lbl,
        CachingDiskJournal::Step::mini_allocator_fill(src.ephemeral->v.disk),
    )) by {
        reveal(CachingDiskJournal::State::next_by);
    }
    reveal(CachingDiskJournal::State::next);

    assert(CrashAwareCachingDiskJournal::State::next_by(
        src,
        dst,
        lbl,
        CrashAwareCachingDiskJournal::Step::internal_alloc(dst.ephemeral->v),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next_by);
    }
    reveal(CrashAwareCachingDiskJournal::State::next);
}

} // verus!
