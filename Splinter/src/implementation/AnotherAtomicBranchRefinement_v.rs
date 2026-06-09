// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Draft component refinement from SystemModel<AnotherProgramModel> to the
// crash-aware caching-disk branch.  This mirrors the journal-side adapter:
// the branch-local metadata lives in AnotherAtomicState, while branch raw
// pages are projected from the shared Cache + AsyncDisk pair.

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::map::*;
use vstd::assert_maps_equal;
use vstd::assert_sets_equal;

use crate::allocation_layer::AllocationBranch_v::{BranchNode, Summary};
use crate::allocation_layer::AllocationBranchBetree_v::summary_aus;
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::LinkedBranch_v::SplitArg;
use crate::disk::GenericDisk_v::{Address, AU, Pointer, to_aus, to_aus_domain};
use crate::implementation::AbstractSuperblock_v::{
    AbstractSuperblockImage, abstract_superblock_raw_wf, parse_abstract_superblock,
};
use crate::implementation::AnotherAtomicJournalRefinement_v::{
    async_disk_superblock_image_i, async_disk_superblock_page_wf,
    atomic_persistent_superblock_image_i, atomic_superblock_prepared_i,
};
use crate::implementation::AnotherAtomicState_v::{
    AnotherAtomicState, AtomicBranchImage, AtomicBranchState,
};
use crate::implementation::AnotherProgramModel_v::AnotherProgramModel;
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedBranch_v::{
    CachedBranch, LoadedBranch, LoadedPathReceipt, loaded_grow_write_nodes,
};
use crate::implementation::CachingDiskAdapterRefinement_v::{
    cache_access_refines_caching_disk_access_by_domains,
    cache_access_refines_caching_disk_access_by_growing_domains,
    cache_access_refines_caching_disk_access_by_growing_domains_with_component_reads,
    cache_evictable_refines_observe_clean_aus_by_domains,
    cache_evictable_refines_observe_clean_aus_by_tight_domains,
    cache_filled_addr, filled_cache_pages, filled_cache_status,
    filled_cache_read_only_access_unchanged,
    caching_disk_i_by_domains as adapter_caching_disk_i_by_domains,
    project_cache_pages_by_addrs, project_cache_status_by_addrs,
    project_persistent_by_addrs,
    projected_cache_read_only_access_unchanged_by_addrs,
};
use crate::implementation::CachingDisk_v::{
    addresses_in_aus, CachingDisk, PageStatus as CachingDiskPageStatus,
};
use crate::implementation::CachingDiskBranch_v::{
    self as CachingDiskBranchModule, CachingDiskBranch, CachingDiskBranchFrozenImage,
    CachingDiskBranchImage,
    root_aus_up_to, root_aus_up_to_contains, root_aus_up_to_full,
    root_aus_up_to_member_has_index, sealed_summary_aus_between,
    sealed_summary_aus_up_to, sealed_summary_aus_up_to_split,
    sealed_summary_aus_up_to_subset_summary_aus,
    empty_caching_disk_branch_image, split_read_addrs, to_branch_nodes,
};
use crate::implementation::AllocationBranchStack_v::{
    mini_allocator_allocate_preserves_all_aus,
};
use crate::implementation::CrashAwareCachingDiskBranch_v::{
    CrashAwareCachingDiskBranch, EphemeralCachingDiskBranch,
};
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::marshalling::IBranchNodeFormat_v::raw_page_to_branch_node;
use crate::spec::AsyncDisk_t::{AsyncDisk, RawPage};
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::{Input, Reply, Request};
use crate::spec::Messages_t::{Message, Value};
use crate::trusted::SystemModel_t::SystemModel;

verus! {

pub open spec fn branch_projection_aus(
    model: SystemModel::State<AnotherProgramModel>,
) -> Set<AU>
{
    summary_aus(branch_projection_summary_i(model))
        + model.program.state.branch.mini_allocator.all_aus()
}

pub open spec fn branch_mini_allocator_allocated_addrs(
    mini_allocator: MiniAllocator,
) -> Set<Address>
{
    Set::new(|addr: Address| {
        &&& mini_allocator.allocs.contains_key(addr.au)
        &&& (mini_allocator.allocs[addr.au].reserved
            + mini_allocator.allocs[addr.au].observed).contains(addr)
    })
}

pub open spec fn branch_child_path_valid(
    nodes: LoadedBranch,
    root: Address,
    path: Seq<int>,
) -> bool
    decreases path.len()
{
    if path.len() == 0 {
        true
    } else {
        let idx = path[0];
        &&& nodes.contains_key(root)
        &&& nodes[root] is Index
        &&& nodes[root].valid_child_index(idx)
        &&& branch_child_path_valid(
            nodes,
            nodes[root]->children[idx],
            path.skip(1),
        )
    }
}

pub open spec fn branch_child_path_target(
    nodes: LoadedBranch,
    root: Address,
    path: Seq<int>,
) -> Address
    recommends branch_child_path_valid(nodes, root, path)
    decreases path.len()
{
    if path.len() == 0 {
        root
    } else {
        let idx = path[0];
        branch_child_path_target(
            nodes,
            nodes[root]->children[idx],
            path.skip(1),
        )
    }
}

pub open spec fn sealed_roots_pointer_domain(
    raw_pages: Map<Address, RawPage>,
    roots: Seq<Address>,
) -> Set<Address>
{
    let nodes = to_branch_nodes(raw_pages);
    Set::new(|addr: Address| {
        ||| exists |root: Address, path: Seq<int>| {
            &&& roots.contains(root)
            &&& #[trigger] branch_child_path_valid(nodes, root, path)
            &&& branch_child_path_target(nodes, root, path) == addr
        }
        ||| exists |root: Address| {
            &&& roots.contains(root)
            &&& nodes.contains_key(root)
            &&& nodes[root] is Index
            &&& nodes[root]->aux_ptr is Some
            &&& #[trigger] nodes[root]->aux_ptr.unwrap() == addr
        }
    })
}

pub open spec fn branch_projection_addrs(
    model: SystemModel::State<AnotherProgramModel>,
) -> Set<Address>
{
    addresses_in_aus(summary_aus(branch_projection_summary_i(model)))
        + branch_mini_allocator_allocated_addrs(model.program.state.branch.mini_allocator)
}

pub open spec fn branch_persistent_projection_addrs(
    model: SystemModel::State<AnotherProgramModel>,
) -> Set<Address>
{
    let support = branch_projection_addrs(model);
    Set::new(|addr: Address| {
        &&& support.contains(addr)
        &&& model.disk.content.contains_key(addr)
    })
}

pub open spec fn branch_raw_visible_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> Map<Address, RawPage>
{
    model.disk.content.union_prefer_right(filled_cache_pages(model.program.state.cache))
}

pub open spec fn branch_visible_nodes_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> LoadedBranch
{
    to_branch_nodes(branch_raw_visible_i(model))
}

pub open spec fn branch_interpreted_summary_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> Map<AU, crate::allocation_layer::AllocationBranch_v::Summary>
{
    if CachingDiskBranchModule::branch_summary_reads_valid(
        model.program.state.branch.image.sealed_roots,
        branch_visible_nodes_i(model),
    ) {
        CachingDiskBranchModule::completed_branch_summary_from_reads(
            model.program.state.branch.image.sealed_roots,
            branch_visible_nodes_i(model),
        )
    } else {
        model.program.state.branch.branch_summary
    }
}

pub open spec fn branch_projection_summary_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> Map<AU, crate::allocation_layer::AllocationBranch_v::Summary>
{
    if atomic_branch_metadata_loaded_flag(model.program.state.branch) {
        model.program.state.branch.branch_summary
    } else {
        branch_interpreted_summary_i(model)
    }
}

pub open spec fn branch_disk_persistent_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> Map<Address, RawPage>
{
    project_persistent_by_addrs(model.disk, branch_persistent_projection_addrs(model))
}

pub open spec fn branch_disk_cache_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> Map<Address, RawPage>
{
    project_cache_pages_by_addrs(model.program.state.cache, branch_projection_addrs(model))
}

pub open spec fn branch_disk_status_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> Map<Address, CachingDiskPageStatus>
{
    project_cache_status_by_addrs(model.program.state.cache, branch_projection_addrs(model))
}

pub open spec fn branch_caching_disk_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> CachingDisk::State
{
    adapter_caching_disk_i_by_domains(
        model.program.state.cache,
        model.disk,
        branch_projection_addrs(model),
        branch_persistent_projection_addrs(model),
    )
}

pub open spec fn atomic_branch_metadata_loaded_flag(
    branch: AtomicBranchState::State,
) -> bool
{
    root_aus_up_to(branch.image.sealed_roots, branch.image.sealed_roots.len() as nat)
        <= branch.branch_summary.dom()
}

pub open spec fn branch_caching_disk_state_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> CachingDiskBranch::State
{
    CachingDiskBranch::State{
        sealed_roots: model.program.state.branch.image.sealed_roots,
        branch_summary: model.program.state.branch.branch_summary,
        metadata_loaded: atomic_branch_metadata_loaded_flag(model.program.state.branch),
        persisted_root_count: model.program.state.branch.persisted_root_count,
        active_branch: model.program.state.branch.active_branch,
        mini_allocator: model.program.state.branch.mini_allocator,
        disk: branch_caching_disk_i(model),
        seq_end: model.program.state.branch.seq_end,
    }
}

pub open spec fn branch_image_i(
    model: SystemModel::State<AnotherProgramModel>,
    image: AbstractSuperblockImage,
) -> CachingDiskBranchImage
{
    CachingDiskBranchImage{
        persistent: branch_image_persistent_i(model, image),
        sealed_roots: image.branch_roots,
        seq_end: image.branch_seq_end,
    }
}

pub open spec fn branch_image_summary_i(
    disk_content: Map<Address, RawPage>,
    roots: Seq<Address>,
) -> Map<AU, Summary>
{
    let nodes = to_branch_nodes(disk_content);
    if CachingDiskBranchModule::branch_summary_reads_valid(roots, nodes) {
        CachingDiskBranchModule::completed_branch_summary_from_reads(roots, nodes)
    } else {
        Map::<AU, Summary>::empty()
    }
}

pub open spec fn branch_image_projection_addrs_i(
    disk_content: Map<Address, RawPage>,
    roots: Seq<Address>,
) -> Set<Address>
{
    sealed_roots_pointer_domain(disk_content, roots)
}

pub open spec fn branch_image_persistent_i(
    model: SystemModel::State<AnotherProgramModel>,
    image: AbstractSuperblockImage,
) -> Map<Address, RawPage>
{
    model.disk.content.restrict(branch_image_projection_addrs_i(model.disk.content, image.branch_roots))
}

pub open spec fn branch_visible_tight_image_i(
    model: SystemModel::State<AnotherProgramModel>,
    image: AbstractSuperblockImage,
) -> CachingDiskBranchImage
{
    let raw = branch_caching_disk_i(model).visible();
    let nodes = to_branch_nodes(raw);
    if CachingDiskBranchModule::branch_summary_reads_valid(image.branch_roots, nodes) {
        let summary = CachingDiskBranchModule::completed_branch_summary_from_reads(
            image.branch_roots,
            nodes,
        );
        CachingDiskBranchImage{
            persistent: raw.restrict(addresses_in_aus(summary_aus(summary))),
            sealed_roots: image.branch_roots,
            seq_end: image.branch_seq_end,
        }
    } else {
        CachingDiskBranchImage{
            persistent: raw,
            sealed_roots: image.branch_roots,
            seq_end: image.branch_seq_end,
        }
    }
}

pub proof fn branch_child_path_push_ensures(
    nodes: LoadedBranch,
    root: Address,
    path: Seq<int>,
    idx: int,
)
    requires
        branch_child_path_valid(nodes, root, path),
        nodes.contains_key(branch_child_path_target(nodes, root, path)),
        nodes[branch_child_path_target(nodes, root, path)] is Index,
        nodes[branch_child_path_target(nodes, root, path)].valid_child_index(idx),
    ensures
        branch_child_path_valid(nodes, root, path.push(idx)),
        branch_child_path_target(nodes, root, path.push(idx))
            == nodes[branch_child_path_target(nodes, root, path)]->children[idx],
    decreases path.len()
{
    if path.len() == 0 {
        assert(path.push(idx).len() == 1);
        assert(path.push(idx)[0] == idx);
        assert(path.push(idx).skip(1).len() == 0);
    } else {
        let first = path[0];
        let child = nodes[root]->children[first];
        assert(path.push(idx).len() == path.len() + 1);
        assert(path.push(idx)[0] == first);
        assert(path.push(idx).skip(1) == path.skip(1).push(idx));
        branch_child_path_push_ensures(nodes, child, path.skip(1), idx);
    }
}

pub proof fn branch_child_path_pre_write_preserves_rec(
    pre_raw: Map<Address, RawPage>,
    roots: Seq<Address>,
    origin: Address,
    prefix: Seq<int>,
    current: Address,
    suffix: Seq<int>,
    write_addr: Address,
    data: RawPage,
)
    requires
        roots.contains(origin),
        branch_child_path_valid(to_branch_nodes(pre_raw), origin, prefix),
        branch_child_path_target(to_branch_nodes(pre_raw), origin, prefix) == current,
        branch_child_path_valid(to_branch_nodes(pre_raw), current, suffix),
        !sealed_roots_pointer_domain(pre_raw, roots).contains(write_addr),
    ensures
        branch_child_path_valid(to_branch_nodes(pre_raw.insert(write_addr, data)), current, suffix),
        branch_child_path_target(to_branch_nodes(pre_raw.insert(write_addr, data)), current, suffix)
            == branch_child_path_target(to_branch_nodes(pre_raw), current, suffix),
    decreases suffix.len()
{
    let pre_nodes = to_branch_nodes(pre_raw);
    let post_raw = pre_raw.insert(write_addr, data);
    let post_nodes = to_branch_nodes(post_raw);
    assert(sealed_roots_pointer_domain(pre_raw, roots).contains(current)) by {
        assert(exists |root: Address, path: Seq<int>| {
            &&& roots.contains(root)
            &&& #[trigger] branch_child_path_valid(pre_nodes, root, path)
            &&& branch_child_path_target(pre_nodes, root, path) == current
        });
    }
    assert(current != write_addr);
    if suffix.len() == 0 {
    } else {
        let idx = suffix[0];
        let child = pre_nodes[current]->children[idx];
        assert(pre_raw.contains_key(current));
        assert(post_raw.contains_key(current));
        assert(post_raw[current] == pre_raw[current]);
        assert(post_nodes[current] == pre_nodes[current]);
        branch_child_path_push_ensures(pre_nodes, origin, prefix, idx);
        let next_prefix = prefix.push(idx);
        assert(branch_child_path_target(pre_nodes, origin, next_prefix) == child);
        branch_child_path_pre_write_preserves_rec(
            pre_raw,
            roots,
            origin,
            next_prefix,
            child,
            suffix.skip(1),
            write_addr,
            data,
        );
    }
}

pub proof fn branch_child_path_post_write_preserves_rec(
    pre_raw: Map<Address, RawPage>,
    roots: Seq<Address>,
    origin: Address,
    prefix: Seq<int>,
    current: Address,
    suffix: Seq<int>,
    write_addr: Address,
    data: RawPage,
)
    requires
        roots.contains(origin),
        branch_child_path_valid(to_branch_nodes(pre_raw), origin, prefix),
        branch_child_path_target(to_branch_nodes(pre_raw), origin, prefix) == current,
        branch_child_path_valid(to_branch_nodes(pre_raw.insert(write_addr, data)), current, suffix),
        !sealed_roots_pointer_domain(pre_raw, roots).contains(write_addr),
    ensures
        branch_child_path_valid(to_branch_nodes(pre_raw), current, suffix),
        branch_child_path_target(to_branch_nodes(pre_raw), current, suffix)
            == branch_child_path_target(to_branch_nodes(pre_raw.insert(write_addr, data)), current, suffix),
    decreases suffix.len()
{
    let pre_nodes = to_branch_nodes(pre_raw);
    let post_raw = pre_raw.insert(write_addr, data);
    let post_nodes = to_branch_nodes(post_raw);
    assert(sealed_roots_pointer_domain(pre_raw, roots).contains(current)) by {
        assert(exists |root: Address, path: Seq<int>| {
            &&& roots.contains(root)
            &&& #[trigger] branch_child_path_valid(pre_nodes, root, path)
            &&& branch_child_path_target(pre_nodes, root, path) == current
        });
    }
    assert(current != write_addr);
    if suffix.len() == 0 {
    } else {
        let idx = suffix[0];
        assert(post_raw.contains_key(current));
        assert(pre_raw.contains_key(current));
        assert(post_raw[current] == pre_raw[current]);
        assert(post_nodes[current] == pre_nodes[current]);
        let child = pre_nodes[current]->children[idx];
        assert(child == post_nodes[current]->children[idx]);
        branch_child_path_push_ensures(pre_nodes, origin, prefix, idx);
        let next_prefix = prefix.push(idx);
        assert(branch_child_path_target(pre_nodes, origin, next_prefix) == child);
        branch_child_path_post_write_preserves_rec(
            pre_raw,
            roots,
            origin,
            next_prefix,
            child,
            suffix.skip(1),
            write_addr,
            data,
        );
    }
}

pub proof fn sealed_roots_pointer_domain_preserved_by_write_outside(
    pre_raw: Map<Address, RawPage>,
    roots: Seq<Address>,
    write_addr: Address,
    data: RawPage,
)
    requires
        !sealed_roots_pointer_domain(pre_raw, roots).contains(write_addr),
    ensures
        sealed_roots_pointer_domain(pre_raw.insert(write_addr, data), roots)
            == sealed_roots_pointer_domain(pre_raw, roots),
{
    let pre_nodes = to_branch_nodes(pre_raw);
    let post_raw = pre_raw.insert(write_addr, data);
    let post_nodes = to_branch_nodes(post_raw);
    assert_sets_equal!(
        sealed_roots_pointer_domain(post_raw, roots),
        sealed_roots_pointer_domain(pre_raw, roots),
        addr => {
            if sealed_roots_pointer_domain(pre_raw, roots).contains(addr) {
                if exists |root: Address, path: Seq<int>| {
                    &&& roots.contains(root)
                    &&& #[trigger] branch_child_path_valid(pre_nodes, root, path)
                    &&& branch_child_path_target(pre_nodes, root, path) == addr
                } {
                    let (root, path) = choose |root: Address, path: Seq<int>| {
                        &&& roots.contains(root)
                        &&& #[trigger] branch_child_path_valid(pre_nodes, root, path)
                        &&& branch_child_path_target(pre_nodes, root, path) == addr
                    };
                    branch_child_path_pre_write_preserves_rec(
                        pre_raw,
                        roots,
                        root,
                        Seq::<int>::empty(),
                        root,
                        path,
                        write_addr,
                        data,
                    );
                    assert(branch_child_path_target(post_nodes, root, path) == addr);
                } else {
                    let root = choose |root: Address| {
                        &&& roots.contains(root)
                        &&& pre_nodes.contains_key(root)
                        &&& pre_nodes[root] is Index
                        &&& pre_nodes[root]->aux_ptr is Some
                        &&& #[trigger] pre_nodes[root]->aux_ptr.unwrap() == addr
                    };
                    assert(sealed_roots_pointer_domain(pre_raw, roots).contains(root)) by {
                        let empty = Seq::<int>::empty();
                        assert(branch_child_path_valid(pre_nodes, root, empty));
                        assert(branch_child_path_target(pre_nodes, root, empty) == root);
                        assert(exists |path: Seq<int>| {
                            &&& roots.contains(root)
                            &&& #[trigger] branch_child_path_valid(pre_nodes, root, path)
                            &&& branch_child_path_target(pre_nodes, root, path) == root
                        });
                    }
                    assert(root != write_addr);
                    assert(post_raw[root] == pre_raw[root]);
                    assert(post_nodes[root] == pre_nodes[root]);
                }
            }
            if sealed_roots_pointer_domain(post_raw, roots).contains(addr) {
                if exists |root: Address, path: Seq<int>| {
                    &&& roots.contains(root)
                    &&& #[trigger] branch_child_path_valid(post_nodes, root, path)
                    &&& branch_child_path_target(post_nodes, root, path) == addr
                } {
                    let (root, path) = choose |root: Address, path: Seq<int>| {
                        &&& roots.contains(root)
                        &&& #[trigger] branch_child_path_valid(post_nodes, root, path)
                        &&& branch_child_path_target(post_nodes, root, path) == addr
                    };
                    assert(sealed_roots_pointer_domain(pre_raw, roots).contains(root)) by {
                        let empty = Seq::<int>::empty();
                        assert(branch_child_path_valid(pre_nodes, root, empty));
                        assert(branch_child_path_target(pre_nodes, root, empty) == root);
                        assert(exists |prefix: Seq<int>| {
                            &&& roots.contains(root)
                            &&& #[trigger] branch_child_path_valid(pre_nodes, root, prefix)
                            &&& branch_child_path_target(pre_nodes, root, prefix) == root
                        });
                    }
                    assert(root != write_addr);
                    branch_child_path_post_write_preserves_rec(
                        pre_raw,
                        roots,
                        root,
                        Seq::<int>::empty(),
                        root,
                        path,
                        write_addr,
                        data,
                    );
                    assert(branch_child_path_target(pre_nodes, root, path) == addr);
                } else {
                    let root = choose |root: Address| {
                        &&& roots.contains(root)
                        &&& post_nodes.contains_key(root)
                        &&& post_nodes[root] is Index
                        &&& post_nodes[root]->aux_ptr is Some
                        &&& #[trigger] post_nodes[root]->aux_ptr.unwrap() == addr
                    };
                    assert(sealed_roots_pointer_domain(pre_raw, roots).contains(root)) by {
                        let empty = Seq::<int>::empty();
                        assert(branch_child_path_valid(pre_nodes, root, empty));
                        assert(branch_child_path_target(pre_nodes, root, empty) == root);
                        assert(exists |path: Seq<int>| {
                            &&& roots.contains(root)
                            &&& #[trigger] branch_child_path_valid(pre_nodes, root, path)
                            &&& branch_child_path_target(pre_nodes, root, path) == root
                        });
                    }
                    assert(root != write_addr);
                    assert(post_raw[root] == pre_raw[root]);
                    assert(post_nodes[root] == pre_nodes[root]);
                }
            }
        }
    );
}

pub open spec fn persistent_branch_image_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> CachingDiskBranchImage
{
    let image = atomic_persistent_superblock_image_i(model);
    if model.program.state.superblock_metadata_known()
        && atomic_branch_metadata_loaded_flag(model.program.state.branch)
    {
        branch_visible_tight_image_i(model, image)
    } else {
        branch_image_i(model, image)
    }
}

pub open spec fn frozen_branch_image_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> Option<CachingDiskBranchFrozenImage>
{
    if model.program.state.in_flight is Some {
        let image = model.program.state.atomic_inflight_superblock_i();
        Option::Some(CachingDiskBranchFrozenImage{
            sealed_roots: image.branch_roots,
            seq_end: image.branch_seq_end,
        })
    } else {
        Option::None
    }
}

pub open spec fn ephemeral_branch_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> EphemeralCachingDiskBranch
{
    if model.program.state.superblock_metadata_known() {
        EphemeralCachingDiskBranch::Known{v: branch_caching_disk_state_i(model)}
    } else {
        EphemeralCachingDiskBranch::Unknown
    }
}

pub open spec fn crash_aware_caching_disk_branch_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> CrashAwareCachingDiskBranch::State
{
    CrashAwareCachingDiskBranch::State{
        persistent: persistent_branch_image_i(model),
        ephemeral: ephemeral_branch_i(model),
        frozen: frozen_branch_image_i(model),
        prepared: atomic_superblock_prepared_i(model),
    }
}

pub open spec fn branch_component_refinement_inv(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    &&& model.program.state.wf()
    &&& model.disk.inv()
    &&& async_disk_superblock_page_wf(model.disk.content)
    &&& persistent_branch_image_i(model).wf()
    &&& crash_aware_caching_disk_branch_i(model).inv()
    &&& (crash_aware_caching_disk_branch_i(model).ephemeral is Known ==>
        branch_caching_disk_state_i(model).active_branch_i().inv())
}

pub proof fn atomic_branch_metadata_loaded_flag_from_metadata_loaded(
    branch: AtomicBranchState::State,
)
    requires
        branch.metadata_loaded(),
    ensures
        atomic_branch_metadata_loaded_flag(branch),
{
    assert forall |au: AU|
        #[trigger] root_aus_up_to(
            branch.image.sealed_roots,
            branch.image.sealed_roots.len() as nat,
        ).contains(au)
        implies branch.branch_summary.dom().contains(au)
    by {
        let idx = root_aus_up_to_member_has_index(
            branch.image.sealed_roots,
            branch.image.sealed_roots.len() as nat,
            au,
        );
        assert(0 <= idx < branch.image.sealed_roots.len());
        assert(branch.image.sealed_roots[idx].au == au);
        assert(branch.branch_summary.contains_key(branch.image.sealed_roots[idx].au));
    }
}

pub proof fn branch_caching_disk_visible_addrs_subset_projection(
    model: SystemModel::State<AnotherProgramModel>,
)
    ensures
        branch_caching_disk_i(model).visible().dom() <= branch_projection_addrs(model),
{
    let disk = branch_caching_disk_i(model);
    assert forall |addr: Address| #[trigger] disk.visible().dom().contains(addr)
        implies branch_projection_addrs(model).contains(addr)
    by {
        assert(disk.visible().contains_key(addr));
        assert(disk.visible() == disk.persistent.union_prefer_right(disk.cache));
        if disk.cache.contains_key(addr) {
            assert(project_cache_pages_by_addrs(
                model.program.state.cache,
                branch_projection_addrs(model),
            ).contains_key(addr));
            assert(branch_projection_addrs(model).contains(addr));
        } else {
            assert(disk.persistent.contains_key(addr));
            assert(project_persistent_by_addrs(
                model.disk,
                branch_persistent_projection_addrs(model),
            ).contains_key(addr));
            assert(branch_persistent_projection_addrs(model).contains(addr));
            assert(branch_projection_addrs(model).contains(addr));
        }
    }
}

pub proof fn branch_projected_visible_aus_subset_owned(
    model: SystemModel::State<AnotherProgramModel>,
)
    requires
        branch_component_refinement_inv(model),
        model.program.state.superblock_metadata_known(),
        atomic_branch_metadata_loaded_flag(model.program.state.branch),
    ensures
        to_aus(branch_caching_disk_i(model).visible().dom())
            <= model.program.state.branch_owned_aus(),
{
    branch_caching_disk_visible_addrs_subset_projection(model);
    assert forall |au: AU| #[trigger] to_aus(branch_caching_disk_i(model).visible().dom()).contains(au)
        implies model.program.state.branch_owned_aus().contains(au)
    by {
        let addr = choose |addr: Address|
            branch_caching_disk_i(model).visible().dom().contains(addr) && addr.au == au;
        assert(branch_projection_addrs(model).contains(addr));
        assert(branch_projection_summary_i(model)
            == model.program.state.branch.branch_summary);
        if addresses_in_aus(summary_aus(model.program.state.branch.branch_summary)).contains(addr) {
            assert(summary_aus(model.program.state.branch.branch_summary).contains(au));
        } else {
            assert(branch_mini_allocator_allocated_addrs(
                model.program.state.branch.mini_allocator,
            ).contains(addr));
            assert(model.program.state.branch.mini_allocator.allocs.contains_key(addr.au));
            assert(model.program.state.branch.mini_allocator.all_aus().contains(au));
        }
    }
}

pub proof fn loaded_branch_projection_unchanged(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
)
    requires
        atomic_branch_metadata_loaded_flag(pre.program.state.branch),
        atomic_branch_metadata_loaded_flag(post.program.state.branch),
        post.program.state.branch.branch_summary == pre.program.state.branch.branch_summary,
        post.program.state.branch.mini_allocator == pre.program.state.branch.mini_allocator,
        post.disk == pre.disk,
    ensures
        branch_projection_addrs(post) =~= branch_projection_addrs(pre),
        branch_projection_aus(post) =~= branch_projection_aus(pre),
        branch_persistent_projection_addrs(post) =~= branch_persistent_projection_addrs(pre),
{
    assert(branch_projection_summary_i(post) == post.program.state.branch.branch_summary);
    assert(branch_projection_summary_i(pre) == pre.program.state.branch.branch_summary);
    assert(branch_projection_summary_i(post) == branch_projection_summary_i(pre));
    assert(branch_projection_addrs(post) =~= branch_projection_addrs(pre)) by {
        assert forall |addr: Address| #[trigger] branch_projection_addrs(post).contains(addr)
            implies branch_projection_addrs(pre).contains(addr) by {
        }
        assert forall |addr: Address| #[trigger] branch_projection_addrs(pre).contains(addr)
            implies branch_projection_addrs(post).contains(addr) by {
        }
    }
    assert(branch_projection_aus(post) =~= branch_projection_aus(pre)) by {
        assert forall |au: AU| #[trigger] branch_projection_aus(post).contains(au)
            implies branch_projection_aus(pre).contains(au) by {
        }
        assert forall |au: AU| #[trigger] branch_projection_aus(pre).contains(au)
            implies branch_projection_aus(post).contains(au) by {
        }
    }
    assert(branch_persistent_projection_addrs(post) =~= branch_persistent_projection_addrs(pre)) by {
        assert forall |addr: Address| #[trigger] branch_persistent_projection_addrs(post).contains(addr)
            implies branch_persistent_projection_addrs(pre).contains(addr) by {
            assert(branch_projection_addrs(pre).contains(addr));
        }
        assert forall |addr: Address| #[trigger] branch_persistent_projection_addrs(pre).contains(addr)
            implies branch_persistent_projection_addrs(post).contains(addr) by {
            assert(branch_projection_addrs(post).contains(addr));
        }
    }
}

pub proof fn query_from_receipts_up_to_equiv(
    receipts: Seq<LoadedPathReceipt>,
    end: nat,
)
    requires
        end <= receipts.len(),
    ensures
        crate::implementation::AnotherAtomicState_v::query_from_receipts_up_to(receipts, end)
            == crate::implementation::CachingDiskBranch_v::query_from_receipts_up_to(receipts, end),
    decreases end
{
    if end > 0 {
        query_from_receipts_up_to_equiv(receipts, (end - 1) as nat);
    }
}

pub proof fn query_receipts_valid_equiv(
    roots: Seq<Address>,
    receipts: Seq<LoadedPathReceipt>,
    read_nodes: LoadedBranch,
    key: Key,
)
    requires
        crate::implementation::AnotherAtomicState_v::query_receipts_valid(
            roots,
            receipts,
            read_nodes,
            key,
        ),
    ensures
        crate::implementation::CachingDiskBranch_v::query_receipts_valid(
            roots,
            receipts,
            read_nodes,
            key,
        ),
{
    if receipts.len() < roots.len() {
        query_from_receipts_up_to_equiv(receipts, receipts.len() as nat);
    }
}

pub proof fn cache_access_reads_available_in_branch_projection(
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
        reads <= branch_disk_cache_i(pre),
    ensures
        reads <= branch_disk_cache_i(pre),
{
}

pub proof fn cache_read_only_branch_projection_unchanged(
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
        post.disk == pre.disk,
        branch_projection_addrs(post) =~= branch_projection_addrs(pre),
        branch_persistent_projection_addrs(post) =~= branch_persistent_projection_addrs(pre),
    ensures
        branch_caching_disk_i(post) == branch_caching_disk_i(pre),
{
    projected_cache_read_only_access_unchanged_by_addrs(
        pre.program.state.cache,
        post.program.state.cache,
        branch_projection_addrs(pre),
        reads,
    );
    filled_cache_read_only_access_unchanged(
        pre.program.state.cache,
        post.program.state.cache,
        reads,
    );
    assert_maps_equal!(branch_disk_cache_i(post), branch_disk_cache_i(pre), addr => {
        assert(branch_projection_addrs(post).contains(addr)
            <==> branch_projection_addrs(pre).contains(addr));
    });
    assert_maps_equal!(branch_disk_status_i(post), branch_disk_status_i(pre), addr => {
        assert(branch_projection_addrs(post).contains(addr)
            <==> branch_projection_addrs(pre).contains(addr));
    });
    assert_maps_equal!(branch_disk_persistent_i(post), branch_disk_persistent_i(pre), addr => {
        assert(branch_persistent_projection_addrs(post).contains(addr)
            <==> branch_persistent_projection_addrs(pre).contains(addr)) by {
            assert(branch_projection_addrs(post).contains(addr)
                <==> branch_projection_addrs(pre).contains(addr));
            assert(filled_cache_pages(post.program.state.cache).contains_key(addr)
                <==> filled_cache_pages(pre.program.state.cache).contains_key(addr));
            assert(filled_cache_status(post.program.state.cache).contains_key(addr)
                <==> filled_cache_status(pre.program.state.cache).contains_key(addr));
        }
    });
}

pub proof fn cache_access_refines_branch_caching_disk_access(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        branch_component_refinement_inv(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads, writes},
        ),
        post.disk == pre.disk,
        branch_projection_addrs(pre) <= branch_projection_addrs(post),
        branch_projection_addrs(post) <= branch_projection_addrs(pre) + writes.dom(),
        branch_disk_persistent_i(post) == branch_disk_persistent_i(pre),
        writes.dom() <= branch_projection_addrs(post),
        reads <= branch_disk_cache_i(pre),
    ensures
        CachingDisk::State::next(
            branch_caching_disk_i(pre),
            branch_caching_disk_i(post),
            CachingDisk::Label::Access{reads, writes},
        ),
{
    cache_access_reads_available_in_branch_projection(pre, post, reads, writes);
    cache_access_refines_caching_disk_access_by_growing_domains(
        pre.program.state.cache,
        post.program.state.cache,
        pre.disk,
        branch_projection_addrs(pre),
        branch_projection_addrs(post),
        branch_persistent_projection_addrs(pre),
        branch_persistent_projection_addrs(post),
        reads,
        writes,
    );
}

pub proof fn cache_access_refines_branch_caching_disk_access_with_component_reads(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    cache_reads: Map<Address, RawPage>,
    component_reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        branch_component_refinement_inv(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads: cache_reads, writes},
        ),
        post.disk == pre.disk,
        branch_projection_addrs(pre) <= branch_projection_addrs(post),
        branch_projection_addrs(post) <= branch_projection_addrs(pre) + writes.dom(),
        branch_disk_persistent_i(post) == branch_disk_persistent_i(pre),
        writes.dom() <= branch_projection_addrs(post),
        component_reads <= branch_disk_cache_i(pre),
    ensures
        CachingDisk::State::next(
            branch_caching_disk_i(pre),
            branch_caching_disk_i(post),
            CachingDisk::Label::Access{reads: component_reads, writes},
        ),
{
    cache_access_refines_caching_disk_access_by_growing_domains_with_component_reads(
        pre.program.state.cache,
        post.program.state.cache,
        pre.disk,
        branch_projection_addrs(pre),
        branch_projection_addrs(post),
        branch_persistent_projection_addrs(pre),
        branch_persistent_projection_addrs(post),
        cache_reads,
        component_reads,
        writes,
    );
}

pub proof fn branch_disk_persistent_eq_from_projection_eq(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
)
    requires
        post.disk == pre.disk,
        branch_persistent_projection_addrs(post) =~= branch_persistent_projection_addrs(pre),
    ensures
        branch_disk_persistent_i(post) == branch_disk_persistent_i(pre),
{
    assert_maps_equal!(
        branch_disk_persistent_i(post),
        branch_disk_persistent_i(pre),
        addr => {
            assert(post.disk == pre.disk);
            assert(branch_persistent_projection_addrs(post).contains(addr)
                <==> branch_persistent_projection_addrs(pre).contains(addr)) by {
                assert(branch_persistent_projection_addrs(post)
                    =~= branch_persistent_projection_addrs(pre));
            }
        }
    );
}

pub proof fn cache_access_refines_branch_caching_disk_access_same_domain(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        branch_component_refinement_inv(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads, writes},
        ),
        post.disk == pre.disk,
        branch_projection_addrs(post) =~= branch_projection_addrs(pre),
        branch_persistent_projection_addrs(post) =~= branch_persistent_projection_addrs(pre),
        writes.dom() <= branch_projection_addrs(pre),
        reads <= branch_disk_cache_i(pre),
    ensures
        CachingDisk::State::next(
            branch_caching_disk_i(pre),
            branch_caching_disk_i(post),
            CachingDisk::Label::Access{reads, writes},
        ),
{
    cache_access_reads_available_in_branch_projection(pre, post, reads, writes);
    cache_access_refines_caching_disk_access_by_domains(
        pre.program.state.cache,
        post.program.state.cache,
        pre.disk,
        branch_projection_addrs(pre),
        branch_persistent_projection_addrs(pre),
        reads,
        writes,
    );
    assert(branch_caching_disk_i(post) == adapter_caching_disk_i_by_domains(
        post.program.state.cache,
        pre.disk,
        branch_projection_addrs(pre),
        branch_persistent_projection_addrs(pre),
    )) by {
        assert_maps_equal!(
            project_cache_pages_by_addrs(post.program.state.cache, branch_projection_addrs(post)),
            project_cache_pages_by_addrs(post.program.state.cache, branch_projection_addrs(pre)),
            addr => {
                assert(branch_projection_addrs(post).contains(addr)
                    <==> branch_projection_addrs(pre).contains(addr));
            }
        );
        assert_maps_equal!(
            project_cache_status_by_addrs(post.program.state.cache, branch_projection_addrs(post)),
            project_cache_status_by_addrs(post.program.state.cache, branch_projection_addrs(pre)),
            addr => {
                assert(branch_projection_addrs(post).contains(addr)
                    <==> branch_projection_addrs(pre).contains(addr));
            }
        );
        assert_maps_equal!(
            project_persistent_by_addrs(post.disk, branch_persistent_projection_addrs(post)),
            project_persistent_by_addrs(pre.disk, branch_persistent_projection_addrs(pre)),
            addr => {
                assert(post.disk == pre.disk);
                assert(branch_persistent_projection_addrs(post).contains(addr)
                    <==> branch_persistent_projection_addrs(pre).contains(addr)) by {
                    assert(branch_persistent_projection_addrs(post)
                        =~= branch_persistent_projection_addrs(pre));
                }
            }
        );
    }
}

pub proof fn branch_load_metadata_refines(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    root: Address,
    reads: Map<Address, RawPage>,
    discovered_aus: Set<AU>,
)
    requires
        branch_component_refinement_inv(pre),
        AnotherAtomicState::branch_load_metadata(
            pre.program.state,
            post.program.state,
            root,
            reads,
            discovered_aus,
        ),
        post.disk == pre.disk,
        branch_projection_addrs(post) =~= branch_projection_addrs(pre),
        branch_persistent_projection_addrs(post) =~= branch_persistent_projection_addrs(pre),
        reads <= branch_disk_cache_i(pre),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            crash_aware_caching_disk_branch_i(pre),
            crash_aware_caching_disk_branch_i(post),
            CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus},
        ),
{
    let cache_lbl = Cache::Label::Access{reads, writes: Map::<Address, RawPage>::empty()};
    let read_nodes = crate::implementation::AnotherAtomicState_v::to_branch_nodes(reads);
    let atomic_lbl = AtomicBranchState::Label::LoadMetadata{root, discovered_aus, read_nodes};
    cache_access_refines_branch_caching_disk_access_same_domain(pre, post, reads, Map::empty());
    cache_read_only_branch_projection_unchanged(pre, post, reads);

    reveal(AtomicBranchState::State::next);
    reveal(AtomicBranchState::State::next_by);
    let atomic_step = choose |step: AtomicBranchState::Step|
        AtomicBranchState::State::next_by(pre.program.state.branch, post.program.state.branch, atomic_lbl, step);
    match atomic_step {
        AtomicBranchState::Step::load_metadata() => {
            assert(AtomicBranchState::State::load_metadata(
                pre.program.state.branch,
                post.program.state.branch,
                atomic_lbl,
            )) by {
                reveal(AtomicBranchState::State::load_metadata);
            }
        },
        _ => { assert(false); }
    }
    let src = crash_aware_caching_disk_branch_i(pre);
    let dst = crash_aware_caching_disk_branch_i(post);
    let lbl = CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus};
    let inner_lbl = CachingDiskBranch::Label::LoadMetadata{root, discovered_aus};
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(CachingDiskBranch::State::next_by(
        src.ephemeral->v,
        dst.ephemeral->v,
        inner_lbl,
        CachingDiskBranch::Step::load_metadata(reads),
    )) by {
        reveal(CachingDiskBranch::State::next_by);
    }
    reveal(CachingDiskBranch::State::next);
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        lbl,
        CrashAwareCachingDiskBranch::Step::load_metadata(dst.ephemeral->v),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);
}

pub proof fn branch_query_refines(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    req: Request,
    reply: Reply,
    end_lsn: nat,
    key: Key,
    value: Value,
    msg: Message,
    receipts: Seq<LoadedPathReceipt>,
    reads: Map<Address, RawPage>,
)
    requires
        branch_component_refinement_inv(pre),
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
        branch_projection_addrs(post) =~= branch_projection_addrs(pre),
        branch_persistent_projection_addrs(post) =~= branch_persistent_projection_addrs(pre),
        reads <= branch_disk_cache_i(pre),
        atomic_branch_metadata_loaded_flag(pre.program.state.branch),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            crash_aware_caching_disk_branch_i(pre),
            crash_aware_caching_disk_branch_i(post),
            CrashAwareCachingDiskBranch::Label::Query{key, value},
        ),
{
    cache_access_refines_branch_caching_disk_access_same_domain(pre, post, reads, Map::empty());
    cache_read_only_branch_projection_unchanged(pre, post, reads);
    let src = crash_aware_caching_disk_branch_i(pre);
    let dst = crash_aware_caching_disk_branch_i(post);
    let read_nodes = crate::implementation::AnotherAtomicState_v::to_branch_nodes(reads);
    let atomic_lbl = AtomicBranchState::Label::Query{key, msg, receipts, read_nodes};
    reveal(AtomicBranchState::State::next);
    reveal(AtomicBranchState::State::next_by);
    let atomic_step = choose |step: AtomicBranchState::Step|
        AtomicBranchState::State::next_by(pre.program.state.branch, pre.program.state.branch, atomic_lbl, step);
    match atomic_step {
        AtomicBranchState::Step::query() => {
            assert(AtomicBranchState::State::query(pre.program.state.branch, pre.program.state.branch, atomic_lbl)) by {
                reveal(AtomicBranchState::State::query);
            }
        },
        _ => { assert(false); }
    }
    assert(read_nodes == to_branch_nodes(reads));
    assert(crate::implementation::AnotherAtomicState_v::query_roots(
        pre.program.state.branch.image.sealed_roots,
        pre.program.state.branch.active_branch,
    ) == crate::implementation::CachingDiskBranch_v::query_roots(
        src.ephemeral->v.sealed_roots,
        src.ephemeral->v.active_branch,
    ));
    let roots = crate::implementation::CachingDiskBranch_v::query_roots(
        src.ephemeral->v.sealed_roots,
        src.ephemeral->v.active_branch,
    );
    query_receipts_valid_equiv(roots, receipts, read_nodes, key);
    query_from_receipts_up_to_equiv(receipts, receipts.len() as nat);

    let lbl = CrashAwareCachingDiskBranch::Label::Query{key, value};
    let inner_lbl = CachingDiskBranch::Label::QueryLabel{key, msg};
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(dst.ephemeral->v == src.ephemeral->v);
    assert(CachingDiskBranch::State::next_by(
        src.ephemeral->v,
        src.ephemeral->v,
        inner_lbl,
        CachingDiskBranch::Step::query(receipts, reads),
    )) by {
        reveal(CachingDiskBranch::State::next_by);
    }
    reveal(CachingDiskBranch::State::next);
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        lbl,
        CrashAwareCachingDiskBranch::Step::query(msg),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
pub proof fn branch_append_refines(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    keys: Seq<Key>,
    msgs: Seq<Message>,
    receipt: LoadedPathReceipt,
    init_root: Option<Address>,
    cache_reads: Map<Address, RawPage>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    branch: AtomicBranchState::State,
)
    requires
        branch_component_refinement_inv(pre),
        AtomicBranchState::State::next(
            pre.program.state.branch,
            branch,
            AtomicBranchState::Label::Append{
                keys,
                msgs,
                receipt,
                init_root,
                read_nodes: crate::implementation::AnotherAtomicState_v::to_branch_nodes(reads),
                write_nodes: crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes),
            },
        ),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads: cache_reads, writes},
        ),
        post.program.state.branch == branch,
        post.disk == pre.disk,
        pre.program.state.superblock_metadata_known(),
        post.program.state.superblock_metadata_known(),
        branch_projection_addrs(pre) <= branch_projection_addrs(post),
        branch_projection_addrs(post) <= branch_projection_addrs(pre) + writes.dom(),
        branch_disk_persistent_i(post) == branch_disk_persistent_i(pre),
        reads <= branch_disk_cache_i(pre),
        writes.dom() <= branch_projection_addrs(post),
        atomic_branch_metadata_loaded_flag(pre.program.state.branch),
        persistent_branch_image_i(post) == persistent_branch_image_i(pre),
        frozen_branch_image_i(post) == frozen_branch_image_i(pre),
        atomic_superblock_prepared_i(post) == atomic_superblock_prepared_i(pre),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            crash_aware_caching_disk_branch_i(pre),
            crash_aware_caching_disk_branch_i(post),
            CrashAwareCachingDiskBranch::Label::Append{keys, msgs},
        ),
{
    let read_nodes = crate::implementation::AnotherAtomicState_v::to_branch_nodes(reads);
    let write_nodes = crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes);
    let atomic_lbl = AtomicBranchState::Label::Append{
        keys,
        msgs,
        receipt,
        init_root,
        read_nodes,
        write_nodes,
    };
    cache_access_refines_branch_caching_disk_access_with_component_reads(
        pre,
        post,
        cache_reads,
        reads,
        writes,
    );

    reveal(AtomicBranchState::State::next);
    reveal(AtomicBranchState::State::next_by);
    let atomic_step = choose |step: AtomicBranchState::Step|
        AtomicBranchState::State::next_by(pre.program.state.branch, branch, atomic_lbl, step);
    match atomic_step {
        AtomicBranchState::Step::append(new_active_branch) => {
            assert(AtomicBranchState::State::append(
                pre.program.state.branch,
                branch,
                atomic_lbl,
                new_active_branch,
            )) by {
                reveal(AtomicBranchState::State::append);
            }
            assert(branch == post.program.state.branch);
        },
        _ => { assert(false); }
    }

    let src = crash_aware_caching_disk_branch_i(pre);
    let dst = crash_aware_caching_disk_branch_i(post);
    let lbl = CrashAwareCachingDiskBranch::Label::Append{keys, msgs};
    let inner_lbl = CachingDiskBranch::Label::AppendLabel{keys, msgs};
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(read_nodes == to_branch_nodes(reads));
    assert(write_nodes == to_branch_nodes(writes));
    assert(CachingDiskBranch::State::next_by(
        src.ephemeral->v,
        dst.ephemeral->v,
        inner_lbl,
        CachingDiskBranch::Step::append(
            dst.ephemeral->v.disk,
            post.program.state.branch.active_branch,
            receipt,
            init_root,
            reads,
            writes,
        ),
    )) by {
        reveal(CachingDiskBranch::State::next_by);
    }
    reveal(CachingDiskBranch::State::next);
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        lbl,
        CrashAwareCachingDiskBranch::Step::append(dst.ephemeral->v),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);
}

pub proof fn branch_append_from_execute_put_refines(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    req: Request,
    reply: Reply,
    receipt: LoadedPathReceipt,
    init_root: Option<Address>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    branch: AtomicBranchState::State,
)
    requires
        branch_component_refinement_inv(pre),
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
        pre.program.state.superblock_metadata_known(),
        post.program.state.superblock_metadata_known(),
        branch_projection_addrs(pre) <= branch_projection_addrs(post),
        branch_projection_addrs(post) <= branch_projection_addrs(pre) + writes.dom(),
        branch_disk_persistent_i(post) == branch_disk_persistent_i(pre),
        reads <= branch_disk_cache_i(pre),
        writes.dom() <= branch_projection_addrs(post),
        atomic_branch_metadata_loaded_flag(pre.program.state.branch),
        persistent_branch_image_i(post) == persistent_branch_image_i(pre),
        frozen_branch_image_i(post) == frozen_branch_image_i(pre),
        atomic_superblock_prepared_i(post) == atomic_superblock_prepared_i(pre),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            crash_aware_caching_disk_branch_i(pre),
            crash_aware_caching_disk_branch_i(post),
            CrashAwareCachingDiskBranch::Label::Append{
                keys: seq![req.input.arrow_PutInput_key()],
                msgs: seq![Message::Define{value: req.input.arrow_PutInput_value()}],
            },
        ),
{
    let key = req.input.arrow_PutInput_key();
    let value = req.input.arrow_PutInput_value();
    let msg = Message::Define{value};
    let keys = seq![key];
    let msgs = seq![msg];
    let read_nodes = crate::implementation::AnotherAtomicState_v::to_branch_nodes(reads);
    let write_nodes = crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes);
    let atomic_lbl = AtomicBranchState::Label::Append{
        keys,
        msgs,
        receipt,
        init_root,
        read_nodes,
        write_nodes,
    };
    assert(AtomicBranchState::State::next(
        pre.program.state.branch,
        branch,
        atomic_lbl,
    ));
    assert(Cache::State::next(
        pre.program.state.cache,
        post.program.state.cache,
        Cache::Label::Access{reads, writes},
    ));
    assert(post.program.state.branch == branch) by {
        assert(AnotherAtomicState::execute_put(
            pre.program.state,
            post.program.state,
            req,
            reply,
            receipt,
            init_root,
            reads,
            writes,
            branch,
        ));
    }
    assert(pre.program.state.superblock_metadata_known());
    assert(post.program.state.superblock_metadata_known());
    branch_append_refines(
        pre,
        post,
        keys,
        msgs,
        receipt,
        init_root,
        reads,
        reads,
        writes,
        branch,
    );
}

pub proof fn branch_fill_aus_refines(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    aus: Set<AU>,
)
    requires
        branch_component_refinement_inv(pre),
        AnotherAtomicState::branch_fill_aus(pre.program.state, post.program.state, aus),
        post.disk == pre.disk,
        branch_caching_disk_i(post) == branch_caching_disk_i(pre),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            crash_aware_caching_disk_branch_i(pre),
            crash_aware_caching_disk_branch_i(post),
            CrashAwareCachingDiskBranch::Label::InternalAlloc{
                allocs: aus,
                deallocs: Set::<AU>::empty(),
            },
        ),
{
    let atomic_lbl = AtomicBranchState::Label::FillAUs{aus};
    reveal(AtomicBranchState::State::next);
    reveal(AtomicBranchState::State::next_by);
    let atomic_step = choose |step: AtomicBranchState::Step|
        AtomicBranchState::State::next_by(pre.program.state.branch, post.program.state.branch, atomic_lbl, step);
    match atomic_step {
        AtomicBranchState::Step::fill_aus() => {
            assert(AtomicBranchState::State::fill_aus(
                pre.program.state.branch,
                post.program.state.branch,
                atomic_lbl,
            )) by {
                reveal(AtomicBranchState::State::fill_aus);
            }
        },
        _ => { assert(false); }
    }

    let src = crash_aware_caching_disk_branch_i(pre);
    let dst = crash_aware_caching_disk_branch_i(post);
    let lbl = CrashAwareCachingDiskBranch::Label::InternalAlloc{
        allocs: aus,
        deallocs: Set::<AU>::empty(),
    };
    let inner_lbl = CachingDiskBranch::Label::InternalAlloc{
        allocs: aus,
        deallocs: Set::<AU>::empty(),
    };
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(dst.ephemeral->v.disk == src.ephemeral->v.disk);
    assert(pre.program.state.client_ready());
    assert(pre.program.state.recovery_metadata_wf());
    assert(pre.program.state.branch_metadata_loaded());
    atomic_branch_metadata_loaded_flag_from_metadata_loaded(pre.program.state.branch);
    branch_projected_visible_aus_subset_owned(pre);
    assert(src.ephemeral->v.metadata_loaded);
    assert(aus.disjoint(to_aus(src.ephemeral->v.disk.visible().dom()))) by {
        assert(aus <= pre.program.state.free_aus);
        assert(pre.program.state.allocation_wf());
        assert(pre.program.state.free_aus.disjoint(pre.program.state.branch_owned_aus()));
        assert(to_aus(branch_caching_disk_i(pre).visible().dom())
            <= pre.program.state.branch_owned_aus());
    }
    assert(aus.disjoint(summary_aus(src.ephemeral->v.branch_summary))) by {
        assert(pre.program.state.allocation_wf());
        assert(aus <= pre.program.state.free_aus);
        assert(pre.program.state.free_aus.disjoint(pre.program.state.branch_owned_aus()));
        assert(summary_aus(pre.program.state.branch.branch_summary) <= pre.program.state.branch_owned_aus());
    }
    assert(aus.disjoint(src.ephemeral->v.mini_allocator.all_aus())) by {
        assert(pre.program.state.allocation_wf());
        assert(aus <= pre.program.state.free_aus);
        assert(pre.program.state.free_aus.disjoint(pre.program.state.branch_owned_aus()));
        assert(pre.program.state.branch.mini_allocator.all_aus() <= pre.program.state.branch_owned_aus());
    }
    assert(CachingDiskBranch::State::next_by(
        src.ephemeral->v,
        dst.ephemeral->v,
        inner_lbl,
        CachingDiskBranch::Step::internal_fill_au(aus),
    )) by {
        reveal(CachingDiskBranch::State::next_by);
    }
    reveal(CachingDiskBranch::State::next);
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        lbl,
        CrashAwareCachingDiskBranch::Step::internal_alloc(dst.ephemeral->v),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);
}

pub proof fn branch_grow_refines(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    new_root_addr: Address,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    branch: AtomicBranchState::State,
)
    requires
        branch_component_refinement_inv(pre),
        AnotherAtomicState::branch_grow(
            pre.program.state,
            post.program.state,
            new_root_addr,
            reads,
            writes,
            branch,
        ),
        post.disk == pre.disk,
        branch_projection_addrs(post) =~= branch_projection_addrs(pre),
        branch_persistent_projection_addrs(post) =~= branch_persistent_projection_addrs(pre),
        reads <= branch_disk_cache_i(pre),
        writes.dom() <= branch_projection_addrs(pre),
        atomic_branch_metadata_loaded_flag(pre.program.state.branch),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            crash_aware_caching_disk_branch_i(pre),
            crash_aware_caching_disk_branch_i(post),
            CrashAwareCachingDiskBranch::Label::Internal,
        ),
{
    let read_nodes = crate::implementation::AnotherAtomicState_v::to_branch_nodes(reads);
    let write_nodes = crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes);
    let atomic_lbl = AtomicBranchState::Label::Grow{
        new_root_addr,
        read_nodes,
        write_nodes,
    };
    cache_access_refines_branch_caching_disk_access_same_domain(pre, post, reads, writes);

    reveal(AtomicBranchState::State::next);
    reveal(AtomicBranchState::State::next_by);
    let atomic_step = choose |step: AtomicBranchState::Step|
        AtomicBranchState::State::next_by(pre.program.state.branch, branch, atomic_lbl, step);
    match atomic_step {
        AtomicBranchState::Step::grow(new_active_branch) => {
            assert(AtomicBranchState::State::grow(
                pre.program.state.branch,
                branch,
                atomic_lbl,
                new_active_branch,
            )) by {
                reveal(AtomicBranchState::State::grow);
            }
            let branch_lbl = CachedBranch::Label::Grow{
                mini_allocator: pre.program.state.branch.mini_allocator,
                new_root_addr,
                read_nodes,
                write_nodes,
            };
            reveal(CachedBranch::State::next);
            reveal(CachedBranch::State::next_by);
            let cb_step = choose |step: CachedBranch::Step|
                CachedBranch::State::next_by(
                    pre.program.state.branch.active_branch,
                    new_active_branch,
                    branch_lbl,
                    step,
                );
            match cb_step {
                CachedBranch::Step::grow_step() => {
                    assert(CachedBranch::State::grow_step(
                        pre.program.state.branch.active_branch,
                        new_active_branch,
                        branch_lbl,
                    )) by {
                        reveal(CachedBranch::State::grow_step);
                    }
                    assert(new_active_branch == CachedBranch::State{root: Some(new_root_addr)});
                },
                _ => { assert(false); }
            }
            assert(branch == post.program.state.branch);
        },
        _ => { assert(false); }
    }

    let src = crash_aware_caching_disk_branch_i(pre);
    let dst = crash_aware_caching_disk_branch_i(post);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(read_nodes == to_branch_nodes(reads));
    assert(write_nodes == to_branch_nodes(writes));
    assert(CachingDiskBranch::State::internal_grow(
        src.ephemeral->v,
        dst.ephemeral->v,
        CachingDiskBranch::Label::Internal,
        dst.ephemeral->v.disk,
        new_root_addr,
        reads,
        writes,
    )) by {
        reveal(CachingDiskBranch::State::internal_grow);
    }
    assert(CachingDiskBranch::State::next_by(
        src.ephemeral->v,
        dst.ephemeral->v,
        CachingDiskBranch::Label::Internal,
        CachingDiskBranch::Step::internal_grow(
            dst.ephemeral->v.disk,
            new_root_addr,
            reads,
            writes,
        ),
    )) by {
        reveal(CachingDiskBranch::State::next_by);
    }
    reveal(CachingDiskBranch::State::next);
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        CrashAwareCachingDiskBranch::Label::Internal,
        CrashAwareCachingDiskBranch::Step::internal(dst.ephemeral->v),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);
}

pub proof fn branch_split_refines(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    new_child_addr: Address,
    receipt: LoadedPathReceipt,
    split_arg: SplitArg,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    branch: AtomicBranchState::State,
)
    requires
        branch_component_refinement_inv(pre),
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
        post.disk == pre.disk,
        branch_projection_addrs(post) =~= branch_projection_addrs(pre),
        branch_persistent_projection_addrs(post) =~= branch_persistent_projection_addrs(pre),
        reads <= branch_disk_cache_i(pre),
        writes.dom() <= branch_projection_addrs(pre),
        atomic_branch_metadata_loaded_flag(pre.program.state.branch),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            crash_aware_caching_disk_branch_i(pre),
            crash_aware_caching_disk_branch_i(post),
            CrashAwareCachingDiskBranch::Label::Internal,
        ),
{
    let read_nodes = crate::implementation::AnotherAtomicState_v::to_branch_nodes(reads);
    let write_nodes = crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes);
    let atomic_lbl = AtomicBranchState::Label::Split{
        new_child_addr,
        receipt,
        split_arg,
        read_nodes,
        write_nodes,
    };
    cache_access_refines_branch_caching_disk_access_same_domain(pre, post, reads, writes);

    reveal(AtomicBranchState::State::next);
    reveal(AtomicBranchState::State::next_by);
    let atomic_step = choose |step: AtomicBranchState::Step|
        AtomicBranchState::State::next_by(pre.program.state.branch, branch, atomic_lbl, step);
    match atomic_step {
        AtomicBranchState::Step::split(new_active_branch) => {
            assert(AtomicBranchState::State::split(
                pre.program.state.branch,
                branch,
                atomic_lbl,
                new_active_branch,
            )) by {
                reveal(AtomicBranchState::State::split);
            }
            let branch_lbl = CachedBranch::Label::Split{
                mini_allocator: pre.program.state.branch.mini_allocator,
                new_child_addr,
                receipt,
                split_arg,
                read_nodes,
                write_nodes,
            };
            reveal(CachedBranch::State::next);
            reveal(CachedBranch::State::next_by);
            let cb_step = choose |step: CachedBranch::Step|
                CachedBranch::State::next_by(
                    pre.program.state.branch.active_branch,
                    new_active_branch,
                    branch_lbl,
                    step,
                );
            match cb_step {
                CachedBranch::Step::split_step() => {
                    assert(CachedBranch::State::split_step(
                        pre.program.state.branch.active_branch,
                        new_active_branch,
                        branch_lbl,
                    )) by {
                        reveal(CachedBranch::State::split_step);
                    }
                    assert(new_active_branch == pre.program.state.branch.active_branch);
                    assert(receipt.needed_addrs() <= read_nodes.dom());
                    assert(read_nodes.contains_key(receipt.child_addr()));
                    assert(split_read_addrs(receipt) <= reads.dom()) by {
                        assert forall |addr: Address| #[trigger] split_read_addrs(receipt).contains(addr)
                            implies reads.dom().contains(addr) by {
                            if receipt.needed_addrs().contains(addr) {
                                assert(read_nodes.dom().contains(addr));
                                assert(read_nodes.contains_key(addr));
                                assert(reads.contains_key(addr));
                            } else {
                                assert(addr == receipt.child_addr());
                                assert(read_nodes.contains_key(addr));
                                assert(reads.contains_key(addr));
                            }
                        }
                    }
                },
                _ => { assert(false); }
            }
            assert(branch == post.program.state.branch);
        },
        _ => { assert(false); }
    }

    let src = crash_aware_caching_disk_branch_i(pre);
    let dst = crash_aware_caching_disk_branch_i(post);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(read_nodes == to_branch_nodes(reads));
    assert(write_nodes == to_branch_nodes(writes));
    assert(CachingDiskBranch::State::internal_split(
        src.ephemeral->v,
        dst.ephemeral->v,
        CachingDiskBranch::Label::Internal,
        dst.ephemeral->v.disk,
        new_child_addr,
        receipt,
        split_arg,
        reads,
        writes,
    )) by {
        reveal(CachingDiskBranch::State::internal_split);
    }
    assert(CachingDiskBranch::State::next_by(
        src.ephemeral->v,
        dst.ephemeral->v,
        CachingDiskBranch::Label::Internal,
        CachingDiskBranch::Step::internal_split(
            dst.ephemeral->v.disk,
            new_child_addr,
            receipt,
            split_arg,
            reads,
            writes,
        ),
    )) by {
        reveal(CachingDiskBranch::State::next_by);
    }
    reveal(CachingDiskBranch::State::next);
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        CrashAwareCachingDiskBranch::Label::Internal,
        CrashAwareCachingDiskBranch::Step::internal(dst.ephemeral->v),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);
}

pub proof fn branch_seal_refines(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    aux_ptr: Pointer,
    summary: Summary,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    branch: AtomicBranchState::State,
)
    requires
        branch_component_refinement_inv(pre),
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
        branch_projection_addrs(post) =~= branch_projection_addrs(pre),
        branch_persistent_projection_addrs(post) =~= branch_persistent_projection_addrs(pre),
        reads <= branch_disk_cache_i(pre),
        writes.dom() <= branch_projection_addrs(pre),
        atomic_branch_metadata_loaded_flag(pre.program.state.branch),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            crash_aware_caching_disk_branch_i(pre),
            crash_aware_caching_disk_branch_i(post),
            CrashAwareCachingDiskBranch::Label::Internal,
        ),
{
    let read_nodes = crate::implementation::AnotherAtomicState_v::to_branch_nodes(reads);
    let write_nodes = crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes);
    let atomic_lbl = AtomicBranchState::Label::Seal{
        aux_ptr,
        summary,
        read_nodes,
        write_nodes,
    };
    cache_access_refines_branch_caching_disk_access_same_domain(pre, post, reads, writes);

    reveal(AtomicBranchState::State::next);
    reveal(AtomicBranchState::State::next_by);
    let atomic_step = choose |step: AtomicBranchState::Step|
        AtomicBranchState::State::next_by(pre.program.state.branch, branch, atomic_lbl, step);
    match atomic_step {
        AtomicBranchState::Step::seal() => {
            assert(AtomicBranchState::State::seal(
                pre.program.state.branch,
                branch,
                atomic_lbl,
            )) by {
                reveal(AtomicBranchState::State::seal);
            }
            let root = pre.program.state.branch.active_branch.root.unwrap();
            let branch_lbl = CachedBranch::Label::Seal{
                mini_allocator: pre.program.state.branch.mini_allocator,
                aux_ptr,
                read_nodes,
                write_nodes,
            };
            reveal(CachedBranch::State::next);
            reveal(CachedBranch::State::next_by);
            let cb_step = choose |step: CachedBranch::Step|
                CachedBranch::State::next_by(
                    pre.program.state.branch.active_branch,
                    pre.program.state.branch.active_branch,
                    branch_lbl,
                    step,
                );
            match cb_step {
                CachedBranch::Step::seal_step() => {
                    assert(CachedBranch::State::seal_step(
                        pre.program.state.branch.active_branch,
                        pre.program.state.branch.active_branch,
                        branch_lbl,
                    )) by {
                        reveal(CachedBranch::State::seal_step);
                    }
                    assert(read_nodes.contains_key(root));
                    assert(reads.contains_key(root));
                },
                _ => { assert(false); }
            }
            assert(branch == post.program.state.branch);
        },
        _ => { assert(false); }
    }

    let src = crash_aware_caching_disk_branch_i(pre);
    let dst = crash_aware_caching_disk_branch_i(post);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(read_nodes == to_branch_nodes(reads));
    assert(write_nodes == to_branch_nodes(writes));
    assert(atomic_branch_metadata_loaded_flag(post.program.state.branch)) by {
        let pre_branch = pre.program.state.branch;
        let post_branch = post.program.state.branch;
        let root = pre_branch.active_branch.root.unwrap();
        assert(post_branch.image.sealed_roots == pre_branch.image.sealed_roots.push(root));
        assert(post_branch.branch_summary == pre_branch.branch_summary.insert(root.au, summary));
        assert forall |au: AU| #[trigger] root_aus_up_to(
            post_branch.image.sealed_roots,
            post_branch.image.sealed_roots.len() as nat,
        ).contains(au)
            implies post_branch.branch_summary.dom().contains(au) by {
            let idx = root_aus_up_to_member_has_index(
                post_branch.image.sealed_roots,
                post_branch.image.sealed_roots.len() as nat,
                au,
            );
            if idx == pre_branch.image.sealed_roots.len() {
                assert(post_branch.image.sealed_roots[idx] == root);
                assert(au == root.au);
                assert(post_branch.branch_summary.dom().contains(au));
            } else {
                assert(0 <= idx < pre_branch.image.sealed_roots.len());
                assert(post_branch.image.sealed_roots[idx] == pre_branch.image.sealed_roots[idx]);
                root_aus_up_to_contains(
                    pre_branch.image.sealed_roots,
                    pre_branch.image.sealed_roots.len() as nat,
                    idx,
                );
                assert(root_aus_up_to(
                    pre_branch.image.sealed_roots,
                    pre_branch.image.sealed_roots.len() as nat,
                ).contains(au));
                assert(pre_branch.branch_summary.dom().contains(au));
                assert(post_branch.branch_summary.dom().contains(au));
            }
        }
    }
    assert(CachingDiskBranch::State::internal_seal(
        src.ephemeral->v,
        dst.ephemeral->v,
        CachingDiskBranch::Label::Internal,
        dst.ephemeral->v.disk,
        aux_ptr,
        reads,
        writes,
    )) by {
        reveal(CachingDiskBranch::State::internal_seal);
    }
    assert(CachingDiskBranch::State::next_by(
        src.ephemeral->v,
        dst.ephemeral->v,
        CachingDiskBranch::Label::Internal,
        CachingDiskBranch::Step::internal_seal(
            dst.ephemeral->v.disk,
            aux_ptr,
            reads,
            writes,
        ),
    )) by {
        reveal(CachingDiskBranch::State::next_by);
    }
    reveal(CachingDiskBranch::State::next);
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        CrashAwareCachingDiskBranch::Label::Internal,
        CrashAwareCachingDiskBranch::Step::internal(dst.ephemeral->v),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);
}

pub proof fn observe_persisted_branch_roots_cache_observe_refines(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    target_count: nat,
    aus: Set<AU>,
)
    requires
        branch_component_refinement_inv(pre),
        AnotherAtomicState::observe_persisted_branch_roots(
            pre.program.state,
            post.program.state,
            target_count,
            aus,
        ),
        post.disk == pre.disk,
    ensures
        post.program.state.cache == pre.program.state.cache,
        CachingDisk::State::next(
            branch_caching_disk_i(pre),
            branch_caching_disk_i(pre),
            CachingDisk::Label::ObserveCleanAUs{aus},
        ),
{
    let cache_lbl = Cache::Label::EvictableCheck{aus};
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let cache_step = choose |step: Cache::Step|
        Cache::State::next_by(pre.program.state.cache, post.program.state.cache, cache_lbl, step);
    match cache_step {
        Cache::Step::evictable() => {
            assert(Cache::State::evictable(
                pre.program.state.cache,
                post.program.state.cache,
                cache_lbl,
            )) by {
                reveal(Cache::State::evictable);
            }
            assert(post.program.state.cache == pre.program.state.cache);
        },
        _ => { assert(false); }
    }
    assert(Cache::State::next_by(
        pre.program.state.cache,
        pre.program.state.cache,
        cache_lbl,
        Cache::Step::evictable(),
    )) by {
        reveal(Cache::State::next_by);
    }
    reveal(Cache::State::next);
    cache_evictable_refines_observe_clean_aus_by_tight_domains(
        pre.program.state.cache,
        pre.disk,
        branch_projection_addrs(pre),
        branch_persistent_projection_addrs(pre),
        aus,
    );
}

pub proof fn observe_persisted_branch_roots_atomic_step(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    target_count: nat,
    aus: Set<AU>,
)
    requires
        AnotherAtomicState::observe_persisted_branch_roots(
            pre.program.state,
            post.program.state,
            target_count,
            aus,
        ),
    ensures
        aus == sealed_summary_aus_between(
            pre.program.state.branch.image.sealed_roots,
            pre.program.state.branch.branch_summary,
            pre.program.state.branch.persisted_root_count,
            target_count,
        ),
        post.program.state.in_flight == pre.program.state.in_flight,
        post.program.state.journal == pre.program.state.journal,
        post.program.state.branch.image == pre.program.state.branch.image,
        post.program.state.branch.in_flight == pre.program.state.branch.in_flight,
        pre.program.state.branch.persisted_root_count <= target_count,
        target_count <= pre.program.state.branch.image.sealed_roots.len(),
        post.program.state.branch.persisted_root_count == target_count,
        post.program.state.branch.seq_end == pre.program.state.branch.seq_end,
        post.program.state.branch.persistent_image == pre.program.state.branch.persistent_image,
        post.program.state.branch.branch_summary == pre.program.state.branch.branch_summary,
        post.program.state.branch.active_branch == pre.program.state.branch.active_branch,
        post.program.state.branch.mini_allocator == pre.program.state.branch.mini_allocator,
        AtomicBranchState::State::next_by(
            pre.program.state.branch,
            post.program.state.branch,
            AtomicBranchState::Label::ObservePersistedRoots{target_count},
            AtomicBranchState::Step::observe_persisted_roots(),
        ),
{
    let atomic_lbl = AtomicBranchState::Label::ObservePersistedRoots{target_count};
    reveal(AtomicBranchState::State::next);
    reveal(AtomicBranchState::State::next_by);
    let atomic_step = choose |step: AtomicBranchState::Step|
        AtomicBranchState::State::next_by(pre.program.state.branch, post.program.state.branch, atomic_lbl, step);
    match atomic_step {
        AtomicBranchState::Step::observe_persisted_roots() => {
            assert(AtomicBranchState::State::observe_persisted_roots(
                pre.program.state.branch,
                post.program.state.branch,
                atomic_lbl,
            )) by {
                reveal(AtomicBranchState::State::observe_persisted_roots);
            }
        },
        _ => { assert(false); }
    }
}

pub proof fn observe_persisted_branch_roots_refines(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    target_count: nat,
    aus: Set<AU>,
)
    requires
        branch_component_refinement_inv(pre),
        AnotherAtomicState::observe_persisted_branch_roots(
            pre.program.state,
            post.program.state,
            target_count,
            aus,
        ),
        post.disk == pre.disk,
        branch_projection_addrs(post) =~= branch_projection_addrs(pre),
        branch_persistent_projection_addrs(post) =~= branch_persistent_projection_addrs(pre),
        atomic_branch_metadata_loaded_flag(pre.program.state.branch),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            crash_aware_caching_disk_branch_i(pre),
            crash_aware_caching_disk_branch_i(post),
            CrashAwareCachingDiskBranch::Label::Internal,
        ),
{
    observe_persisted_branch_roots_cache_observe_refines(pre, post, target_count, aus);
    observe_persisted_branch_roots_atomic_step(pre, post, target_count, aus);

    let src = crash_aware_caching_disk_branch_i(pre);
    let dst = crash_aware_caching_disk_branch_i(post);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(src.ephemeral->v.disk == branch_caching_disk_i(pre));
    assert(dst.ephemeral->v.disk == branch_caching_disk_i(post));
    assert(dst.ephemeral->v.disk == src.ephemeral->v.disk);
    assert(src.ephemeral->v.metadata_loaded);
    assert(aus == sealed_summary_aus_between(
        src.ephemeral->v.sealed_roots,
        src.ephemeral->v.branch_summary,
        src.ephemeral->v.persisted_root_count,
        target_count,
    ));
    assert(CachingDiskBranch::State::observe_persisted_roots(
        src.ephemeral->v,
        dst.ephemeral->v,
        CachingDiskBranch::Label::Internal,
        target_count,
    )) by {
        reveal(CachingDiskBranch::State::observe_persisted_roots);
    }
    assert(CachingDiskBranch::State::next_by(
        src.ephemeral->v,
        dst.ephemeral->v,
        CachingDiskBranch::Label::Internal,
        CachingDiskBranch::Step::observe_persisted_roots(target_count),
    )) by {
        reveal(CachingDiskBranch::State::next_by);
    }
    reveal(CachingDiskBranch::State::next);
    assert(dst.frozen == src.frozen);
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        CrashAwareCachingDiskBranch::Label::Internal,
        CrashAwareCachingDiskBranch::Step::internal(dst.ephemeral->v),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);
}

} // verus!
