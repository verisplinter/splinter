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

use crate::allocation_layer::AllocationBranch_v::Summary;
use crate::allocation_layer::AllocationBranchBetree_v::summary_aus;
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::LinkedBranch_v::SplitArg;
use crate::disk::GenericDisk_v::{Address, AU, Pointer, to_aus, to_aus_domain};
use crate::implementation::AbstractSuperblock_v::{
    AbstractSuperblockImage, abstract_superblock_raw_wf, parse_abstract_superblock,
};
use crate::implementation::AnotherAtomicJournalRefinement_v::{
    async_disk_superblock_image_i, async_disk_superblock_page_wf,
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
    cache_access_refines_caching_disk_access, cache_evictable_refines_observe_clean_aus,
    cache_filled_addr, filled_cache_pages, caching_disk_i as adapter_caching_disk_i,
    project_cache_pages, project_cache_status, project_persistent,
    projected_cache_read_only_access_unchanged,
};
use crate::implementation::CachingDisk_v::{
    addresses_in_aus, CachingDisk, PageStatus as CachingDiskPageStatus,
};
use crate::implementation::CachingDiskBranch_v::{
    self as CachingDiskBranchModule, CachingDiskBranch, CachingDiskBranchFrozenImage,
    CachingDiskBranchImage,
    root_aus_up_to, root_aus_up_to_contains, root_aus_up_to_full,
    root_aus_up_to_member_has_index, sealed_summary_aus_between,
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
    summary_aus(branch_interpreted_summary_i(model))
        + model.program.state.branch.mini_allocator.all_aus()
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

pub open spec fn branch_disk_persistent_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> Map<Address, RawPage>
{
    project_persistent(model.disk, branch_projection_aus(model))
}

pub open spec fn branch_disk_cache_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> Map<Address, RawPage>
{
    project_cache_pages(model.program.state.cache, branch_projection_aus(model))
}

pub open spec fn branch_disk_status_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> Map<Address, CachingDiskPageStatus>
{
    project_cache_status(model.program.state.cache, branch_projection_aus(model))
}

pub open spec fn branch_caching_disk_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> CachingDisk::State
{
    adapter_caching_disk_i(
        model.program.state.cache,
        model.disk,
        branch_projection_aus(model),
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
        persistent: branch_disk_persistent_i(model),
        sealed_roots: image.branch_roots,
        seq_end: image.branch_seq_end,
    }
}

pub open spec fn persistent_branch_image_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> CachingDiskBranchImage
{
    branch_image_i(model, async_disk_superblock_image_i(model.disk.content))
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
        prepared: Option::None,
    }
}

pub open spec fn branch_component_refinement_inv(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    &&& model.program.state.wf()
    &&& model.disk.inv()
    &&& async_disk_superblock_page_wf(model.disk.content)
    &&& crash_aware_caching_disk_branch_i(model).inv()
    &&& branch_caching_disk_state_i(model).active_branch_i().inv()
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
        branch_projection_aus(post) =~= branch_projection_aus(pre),
    ensures
        branch_caching_disk_i(post) == branch_caching_disk_i(pre),
{
    projected_cache_read_only_access_unchanged(
        pre.program.state.cache,
        post.program.state.cache,
        branch_projection_aus(pre),
        reads,
    );
    assert_maps_equal!(branch_disk_cache_i(post), branch_disk_cache_i(pre), addr => {
        assert(addresses_in_aus(branch_projection_aus(post)).contains(addr)
            <==> addresses_in_aus(branch_projection_aus(pre)).contains(addr));
    });
    assert_maps_equal!(branch_disk_status_i(post), branch_disk_status_i(pre), addr => {
        assert(addresses_in_aus(branch_projection_aus(post)).contains(addr)
            <==> addresses_in_aus(branch_projection_aus(pre)).contains(addr));
    });
    assert_maps_equal!(branch_disk_persistent_i(post), branch_disk_persistent_i(pre), addr => {
        assert(addresses_in_aus(branch_projection_aus(post)).contains(addr)
            <==> addresses_in_aus(branch_projection_aus(pre)).contains(addr));
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
        branch_projection_aus(post) =~= branch_projection_aus(pre),
        writes.dom() <= addresses_in_aus(branch_projection_aus(pre)),
        reads <= branch_disk_cache_i(pre),
    ensures
        CachingDisk::State::next(
            branch_caching_disk_i(pre),
            branch_caching_disk_i(post),
            CachingDisk::Label::Access{reads, writes},
        ),
{
    cache_access_reads_available_in_branch_projection(pre, post, reads, writes);
    cache_access_refines_caching_disk_access(
        pre.program.state.cache,
        post.program.state.cache,
        pre.disk,
        branch_projection_aus(pre),
        reads,
        writes,
    );
    assert(branch_caching_disk_i(post) == adapter_caching_disk_i(
        post.program.state.cache,
        pre.disk,
        branch_projection_aus(pre),
    )) by {
        assert_maps_equal!(
            project_cache_pages(post.program.state.cache, branch_projection_aus(post)),
            project_cache_pages(post.program.state.cache, branch_projection_aus(pre)),
            addr => {
                assert(addresses_in_aus(branch_projection_aus(post)).contains(addr)
                    <==> addresses_in_aus(branch_projection_aus(pre)).contains(addr));
            }
        );
        assert_maps_equal!(
            project_cache_status(post.program.state.cache, branch_projection_aus(post)),
            project_cache_status(post.program.state.cache, branch_projection_aus(pre)),
            addr => {
                assert(addresses_in_aus(branch_projection_aus(post)).contains(addr)
                    <==> addresses_in_aus(branch_projection_aus(pre)).contains(addr));
            }
        );
        assert_maps_equal!(
            project_persistent(post.disk, branch_projection_aus(post)),
            project_persistent(pre.disk, branch_projection_aus(pre)),
            addr => {
                assert(post.disk == pre.disk);
                assert(addresses_in_aus(branch_projection_aus(post)).contains(addr)
                    <==> addresses_in_aus(branch_projection_aus(pre)).contains(addr));
            }
        );
    };
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
        branch_projection_aus(post) =~= branch_projection_aus(pre),
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
    cache_access_refines_branch_caching_disk_access(pre, post, reads, Map::empty());
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
        branch_projection_aus(post) =~= branch_projection_aus(pre),
        reads <= branch_disk_cache_i(pre),
        atomic_branch_metadata_loaded_flag(pre.program.state.branch),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            crash_aware_caching_disk_branch_i(pre),
            crash_aware_caching_disk_branch_i(post),
            CrashAwareCachingDiskBranch::Label::Query{key, value},
        ),
{
    cache_access_refines_branch_caching_disk_access(pre, post, reads, Map::empty());
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
        branch_projection_aus(post) =~= branch_projection_aus(pre),
        reads <= branch_disk_cache_i(pre),
        writes.dom() <= addresses_in_aus(branch_projection_aus(pre)),
        atomic_branch_metadata_loaded_flag(pre.program.state.branch),
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
    cache_access_refines_branch_caching_disk_access(pre, post, reads, writes);

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

pub proof fn branch_append_from_recovery_refines(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    addr: Address,
    keys: Seq<Key>,
    msgs: Seq<Message>,
    receipt: LoadedPathReceipt,
    init_root: Option<Address>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    branch: AtomicBranchState::State,
)
    requires
        branch_component_refinement_inv(pre),
        AnotherAtomicState::read_for_recovery(
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
        ),
        post.disk == pre.disk,
        branch_projection_aus(post) =~= branch_projection_aus(pre),
        reads <= branch_disk_cache_i(pre),
        writes.dom() <= addresses_in_aus(branch_projection_aus(pre)),
        atomic_branch_metadata_loaded_flag(pre.program.state.branch),
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
    cache_access_refines_branch_caching_disk_access(pre, post, reads, writes);

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
        aus.disjoint(to_aus(branch_caching_disk_i(pre).visible().dom())),
        atomic_branch_metadata_loaded_flag(pre.program.state.branch),
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
    assert(src.ephemeral->v.metadata_loaded);
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
        branch_projection_aus(post) =~= branch_projection_aus(pre),
        reads <= branch_disk_cache_i(pre),
        writes.dom() <= addresses_in_aus(branch_projection_aus(pre)),
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
    cache_access_refines_branch_caching_disk_access(pre, post, reads, writes);

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
        branch_projection_aus(post) =~= branch_projection_aus(pre),
        reads <= branch_disk_cache_i(pre),
        writes.dom() <= addresses_in_aus(branch_projection_aus(pre)),
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
    cache_access_refines_branch_caching_disk_access(pre, post, reads, writes);

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
        branch_projection_aus(post) =~= branch_projection_aus(pre),
        reads <= branch_disk_cache_i(pre),
        writes.dom() <= addresses_in_aus(branch_projection_aus(pre)),
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
    cache_access_refines_branch_caching_disk_access(pre, post, reads, writes);

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
        branch_projection_aus(post) =~= branch_projection_aus(pre),
        atomic_branch_metadata_loaded_flag(pre.program.state.branch),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            crash_aware_caching_disk_branch_i(pre),
            crash_aware_caching_disk_branch_i(post),
            CrashAwareCachingDiskBranch::Label::Internal,
        ),
{
    let atomic_lbl = AtomicBranchState::Label::ObservePersistedRoots{target_count};
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
    cache_evictable_refines_observe_clean_aus(
        pre.program.state.cache,
        pre.disk,
        branch_projection_aus(pre),
        aus,
    );

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

    let src = crash_aware_caching_disk_branch_i(pre);
    let dst = crash_aware_caching_disk_branch_i(post);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(dst.ephemeral->v.disk == src.ephemeral->v.disk);
    assert(aus == sealed_summary_aus_between(
        src.ephemeral->v.sealed_roots,
        src.ephemeral->v.branch_summary,
        src.ephemeral->v.persisted_root_count,
        target_count,
    ));
    assert(CachingDiskBranch::State::next_by(
        src.ephemeral->v,
        dst.ephemeral->v,
        CachingDiskBranch::Label::Internal,
        CachingDiskBranch::Step::observe_persisted_roots(target_count),
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

} // verus!
