// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Skeleton refinement boundary:
// UnifiedCache branch projection -> CrashAwareCachingDiskBranch.

#![allow(unused_imports)]
#![allow(unused_variables)]

use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::map_lib::lemma_values_finite;

use crate::allocation_layer::AllocationBranch_v::{BranchNode, Summary};
use crate::allocation_layer::AllocationBranchBetree_v::summary_aus;
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::LinkedBranch_v::{
    LinkedBranch, Refinement_v as LinkedBranchRefinement, SplitArg,
};
use crate::betree::Utils_v::{
    lemma_set_subset_of_union_seq_of_sets, lemma_union_set_of_sets_contains,
    lemma_union_set_of_sets_subset,
};
use crate::disk::GenericDisk_v::{
    addrs_closed, set_addrs_disjoint_aus, to_aus_domain, to_aus_finite,
    Address, AU, Pointer, Ranking, to_aus,
};
use crate::implementation::AbstractSuperblock_v::{
    AbstractSuperblockImage, abstract_superblock_raw_wf,
    empty_abstract_superblock_image, parse_abstract_superblock,
};
use crate::implementation::AllocationBranchStack_v::{
    mini_allocator_add_aus_preserves_all_aus, normalize_value,
};
use crate::implementation::AtomicBranchState_v::{
    AtomicBranchImage, AtomicBranchState, query_receipts_read_addrs,
};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedBranch_v::{
    loaded_append_write_nodes, loaded_grow_write_nodes,
    loaded_initialize_write_nodes, loaded_split_write_nodes,
    loaded_seal_write_nodes, receipt_valid_implies_tail_valid, root_summary_from_read,
    root_summary_read_valid, CachedBranch, LoadedBranch, LoadedPathReceipt,
};
use crate::implementation::CachingDiskAdapterRefinement_v::{
    cache_filled_addr, cache_filled_page,
    cache_access_refines_caching_disk_access,
    cache_evictable_refines_observe_clean_aus,
    cache_internal_refines_caching_disk_internal,
    cache_internal_preserves_readable_on_preserved_filled_addrs,
    cache_disk_ops_begin_refines_caching_disk_internal,
    cache_disk_ops_end_refines_caching_disk_internal,
    cache_disk_ops_end_preserves_readable_on_addrs,
    async_disk_process_write_preserves_readable,
    caching_disk_i as adapter_caching_disk_i,
    filled_cache_status,
    project_cache_pages,
    project_cache_status,
    projected_cache_access_outside_aus_unchanged,
    projected_cache_read_only_access_unchanged,
};
use crate::implementation::CachingDiskBranch_v::{
    active_loaded_nodes_of, active_loaded_nodes_preserved_by_readable_agreement,
    active_loaded_nodes_submap_visible_from_readable_visible,
    active_branch_i_visible_candidate, semantic_active_branch_candidate,
    branch_summary_reads_valid,
    branch_summary_from_reads_up_to_self_ensures,
    completed_branch_summary_from_reads, empty_caching_disk_branch_image,
    empty_caching_disk_branch_image_wf,
	    loaded_branch_summary_agrees, loaded_branch_summary_agrees_at,
	    loaded_branch_summary_agrees_domain_contains,
    mini_allocator_allocated_addrs, mini_allocator_allocated_addrs_subset_all_aus,
    sealed_nodes_of,
    sealed_summary_aus_between,
    split_read_addrs, to_branch_nodes, root_aus_up_to, root_aus_up_to_contains,
    root_aus_up_to_full,
    root_aus_up_to_member_has_index, CachingDiskBranch,
    CachingDiskBranchImage, CachingDiskBranchMetadata,
};
use crate::implementation::CachingDisk_v::{addresses_in_aus, CachingDisk, PageStatus};
use crate::implementation::CrashAwareAllocationBranchStack_v::{
    empty_sealed_stack, CrashAwareAllocationBranchStack,
};
use crate::implementation::CrashAwareCachingDiskBranch_v::{
    CrashAwareCachingDiskBranch, EphemeralCachingDiskBranch,
    PersistentCachingDiskBranch,
};
use crate::implementation::CrashAwareCachingDiskBranchRefinement_v::*;
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::UnifiedCacheProgramModel_v::UnifiedCacheProgramModel;
use crate::implementation::UnifiedCacheSystem_v::UnifiedCacheSystem;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Message, Value};
use crate::spec::AsyncDisk_t::{DiskRequest, DiskResponse, RawPage};
use crate::trusted::ProgramModelTrait_t::{DiskModel, ProgramModelTrait};
use crate::trusted::SystemModel_t::SystemModel;

verus! {

proof fn to_branch_nodes_restrict_submap(reads: Map<Address, RawPage>, addrs: Set<Address>)
    ensures
        to_branch_nodes(reads.restrict(addrs)) <= to_branch_nodes(reads),
{
    assert forall |addr: Address| #[trigger] to_branch_nodes(reads.restrict(addrs)).contains_key(addr)
        implies {
            &&& to_branch_nodes(reads).contains_key(addr)
            &&& to_branch_nodes(reads.restrict(addrs))[addr] == to_branch_nodes(reads)[addr]
        } by {
        assert(reads.restrict(addrs).contains_key(addr));
        assert(reads.contains_key(addr));
    };
}

#[verifier::ext_equal]
pub struct UnifiedCacheBranchSource {
    pub branch: AtomicBranchState::State,
    pub cache: Cache::State,
    pub disk: DiskModel,
    pub persistent_image: Option<AbstractSuperblockImage>,
    pub in_flight: Option<AbstractSuperblockImage>,
    pub in_flight_image: Option<AbstractSuperblockImage>,
}

pub open spec fn unified_cache_branch_source(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> UnifiedCacheBranchSource
{
    let state = model.program.state;
    UnifiedCacheBranchSource{
        branch: state.branch,
        cache: state.cache,
        disk: model.disk,
        persistent_image: state.persistent_image,
        in_flight: state.sync_image(),
        in_flight_image: state.sync_image(),
    }
}

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

pub proof fn addresses_in_aus_to_aus_addresses_in_aus(aus: Set<AU>)
    ensures
        addresses_in_aus(to_aus(addresses_in_aus(aus))) =~= addresses_in_aus(aus),
{
    assert forall |addr: Address| #[trigger] addresses_in_aus(
        to_aus(addresses_in_aus(aus)),
    ).contains(addr) implies addresses_in_aus(aus).contains(addr) by {
        let witness = choose |witness: Address| {
            &&& #[trigger] addresses_in_aus(aus).contains(witness)
            &&& witness.au == addr.au
        };
        assert(aus.contains(witness.au));
    }
    assert forall |addr: Address| #[trigger] addresses_in_aus(aus).contains(addr)
        implies addresses_in_aus(to_aus(addresses_in_aus(aus))).contains(addr) by {
        to_aus_domain(addresses_in_aus(aus));
        assert(to_aus(addresses_in_aus(aus)).contains(addr.au));
    }
}

pub proof fn to_aus_addresses_in_aus(aus: Set<AU>)
    ensures
        to_aus(addresses_in_aus(aus)) =~= aus,
{
    assert forall |au: AU| #[trigger] to_aus(addresses_in_aus(aus)).contains(au)
        implies aus.contains(au) by {
        let addr = choose |addr: Address| #![auto] addresses_in_aus(aus).contains(addr) && addr.au == au;
        assert(aus.contains(addr.au));
    }
    assert forall |au: AU| #[trigger] aus.contains(au)
        implies to_aus(addresses_in_aus(aus)).contains(au) by {
        let addr = Address{au, page: 0};
        assert(addresses_in_aus(aus).contains(addr));
        to_aus_domain(addresses_in_aus(aus));
    }
}

pub proof fn branch_image_summary_aus_matches_completed_summary(
    disk_content: Map<Address, RawPage>,
    roots: Seq<Address>,
)
    requires
        set_addrs_disjoint_aus(roots.to_set()),
        branch_summary_reads_valid(roots, to_branch_nodes(disk_content)),
    ensures
        UnifiedCacheBranchSource::branch_image_summary_aus_i(disk_content, roots)
            =~= summary_aus(completed_branch_summary_from_reads(
                roots,
                to_branch_nodes(disk_content),
            )),
{
    let nodes = to_branch_nodes(disk_content);
    let full_summary = completed_branch_summary_from_reads(roots, nodes);
    assert(UnifiedCacheBranchSource::branch_image_summary_i(disk_content, roots)
        == full_summary);
    assert(UnifiedCacheBranchSource::branch_image_summary_aus_i(disk_content, roots)
        == summary_aus(full_summary));
}

pub proof fn recovery_branch_projection_aus_matches_image_summary(
    src: UnifiedCacheBranchSource,
)
    requires
        src.branch.mini_allocator == MiniAllocator::empty(),
        src.branch.image.sealed_roots == src.persistent_superblock_image_i().branch_roots,
        set_addrs_disjoint_aus(src.branch.image.sealed_roots.to_set()),
        branch_summary_reads_valid(
            src.branch.image.sealed_roots,
            to_branch_nodes(src.disk.content),
        ),
        loaded_branch_summary_agrees(
            src.branch.image.sealed_roots,
            to_branch_nodes(src.disk.content),
            src.branch.branch_summary,
        ),
    ensures
        src.branch_projection_aus() =~= UnifiedCacheBranchSource::branch_image_summary_aus_i(
            src.disk.content,
            src.branch.image.sealed_roots,
        ),
{
    let roots = src.branch.image.sealed_roots;
    let nodes = to_branch_nodes(src.disk.content);
    let image_aus = UnifiedCacheBranchSource::branch_image_summary_aus_i(src.disk.content, roots);
    let completed = completed_branch_summary_from_reads(roots, nodes);
    assert(set_addrs_disjoint_aus(roots.to_set()));
    branch_image_summary_aus_matches_completed_summary(src.disk.content, roots);

    if src.branch.metadata_loaded() {
        branch_summary_from_reads_up_to_self_ensures(roots, nodes, roots.len() as nat);
        root_aus_up_to_full(roots);
        assert(src.branch.branch_summary =~= completed) by {
            assert_maps_equal!(
                src.branch.branch_summary,
                completed,
	                au => {
	                    if src.branch.branch_summary.contains_key(au) {
	                        loaded_branch_summary_agrees_domain_contains(
	                            roots,
	                            nodes,
	                            src.branch.branch_summary,
	                            au,
	                        );
	                        assert(root_aus_up_to(roots, roots.len() as nat).contains(au));
	                        let idx = root_aus_up_to_member_has_index(
	                            roots,
	                            roots.len() as nat,
	                            au,
	                        );
	                        assert(roots[idx].au == au);
	                        loaded_branch_summary_agrees_at(
	                            roots,
	                            nodes,
	                            src.branch.branch_summary,
	                            idx,
	                        );
	                        assert(completed[au] == crate::implementation::CachedBranch_v::root_summary_from_read(
	                            roots[idx],
                            nodes,
                        ));
                        assert(src.branch.branch_summary[au]
                            == crate::implementation::CachedBranch_v::root_summary_from_read(
                                roots[idx],
                                nodes,
                            ));
                    }
                    if completed.contains_key(au) {
                        assert(root_aus_up_to(roots, roots.len() as nat).contains(au));
                        let idx = root_aus_up_to_member_has_index(
                            roots,
                            roots.len() as nat,
                            au,
                        );
                        assert(roots[idx].au == au);
                        assert(src.branch.branch_summary.contains_key(roots[idx].au));
                        assert(src.branch.branch_summary.contains_key(au));
                        assert(completed[au] == crate::implementation::CachedBranch_v::root_summary_from_read(
                            roots[idx],
                            nodes,
                        ));
                        assert(src.branch.branch_summary[au]
                            == crate::implementation::CachedBranch_v::root_summary_from_read(
                                roots[idx],
                                nodes,
                            ));
                    }
                }
            );
        }
        assert(summary_aus(src.branch.branch_summary) =~= summary_aus(completed));
        assert(src.branch_projection_aus() == src.branch.owned_aus());
        assert(src.branch.owned_aus() == summary_aus(src.branch.branch_summary));
        assert(src.branch_projection_aus() =~= image_aus);
    } else {
        assert(src.persistent_superblock_image_i().branch_roots == roots);
        assert(src.branch_projection_aus() == to_aus(
            UnifiedCacheBranchSource::branch_image_projection_addrs_i(
                src.disk.content,
                roots,
            ),
        ));
        assert(UnifiedCacheBranchSource::branch_image_projection_addrs_i(
            src.disk.content,
            roots,
        ) == addresses_in_aus(image_aus));
        to_aus_addresses_in_aus(image_aus);
        assert(src.branch_projection_aus() =~= image_aus);
    }
}

impl UnifiedCacheBranchSource {
    pub open spec fn superblock_loaded(self) -> bool
    {
        self.persistent_image is Some
    }

    pub open spec fn persistent_superblock_image_i(self) -> AbstractSuperblockImage
    {
        if self.persistent_image is Some {
            self.persistent_image.unwrap()
        } else {
            async_disk_superblock_image_i(self.disk.content)
        }
    }

    pub closed spec fn branch_image_summary_i(
        disk_content: Map<Address, RawPage>,
        roots: Seq<Address>,
    ) -> Map<AU, crate::allocation_layer::AllocationBranch_v::Summary>
    {
        let nodes = to_branch_nodes(disk_content);
        if branch_summary_reads_valid(roots, nodes) {
            completed_branch_summary_from_reads(roots, nodes)
        } else {
            Map::<AU, crate::allocation_layer::AllocationBranch_v::Summary>::empty()
        }
    }

    pub closed spec fn branch_image_summary_aus_i(
        disk_content: Map<Address, RawPage>,
        roots: Seq<Address>,
    ) -> Set<AU>
    {
        summary_aus(Self::branch_image_summary_i(disk_content, roots))
    }

    pub closed spec fn branch_image_projection_addrs_i(
        disk_content: Map<Address, RawPage>,
        roots: Seq<Address>,
    ) -> Set<Address>
    {
        crate::implementation::CachingDisk_v::addresses_in_aus(
            Self::branch_image_summary_aus_i(disk_content, roots),
        )
    }

    pub open spec fn branch_image_i(self, image: AbstractSuperblockImage) -> CachingDiskBranchImage
    {
        CachingDiskBranchImage{
            persistent: self.disk.content.restrict(
                Self::branch_image_projection_addrs_i(self.disk.content, image.branch_roots),
            ),
            sealed_roots: image.branch_roots,
            seq_end: image.branch_seq_end,
        }
    }

    pub open spec fn persistent_branch_image_i(self) -> CachingDiskBranchImage
    {
        self.branch_image_i(self.persistent_superblock_image_i())
    }

    pub open spec fn branch_projection_aus(self) -> Set<AU>
    {
        if self.branch.metadata_loaded() {
            self.branch.owned_aus()
        } else {
            to_aus(Self::branch_image_projection_addrs_i(
                self.disk.content,
                self.persistent_superblock_image_i().branch_roots,
            ))
        }
    }

    pub open spec fn branch_caching_disk_i_for_aus(self, aus: Set<AU>) -> CachingDisk::State
    {
        adapter_caching_disk_i(self.cache, self.disk, aus)
    }

    pub open spec fn branch_caching_disk_i(self) -> CachingDisk::State
    {
        self.branch_caching_disk_i_for_aus(self.branch_projection_aus())
    }

    pub open spec fn branch_fill_aus_shared_projection_inv(self, aus: Set<AU>) -> bool
    {
        let disk = self.branch_caching_disk_i_for_aus(self.branch_projection_aus() + aus);
        &&& disk.inv()
        &&& disk.cache.dom() <= Set::new(|addr: Address| addr.wf())
        &&& disk.persistent.dom() <= Set::new(|addr: Address| addr.wf())
    }

    pub open spec fn branch_caching_disk_state_i(self) -> CachingDiskBranch::State
    {
        CachingDiskBranch::State{
            sealed_roots: self.branch.image.sealed_roots,
            branch_summary: self.branch.branch_summary,
            metadata_loaded: self.branch.metadata_loaded(),
            persisted_root_count: self.branch.persisted_root_count,
            active_branch: self.branch.active_branch,
            mini_allocator: self.branch.mini_allocator,
            disk: self.branch_caching_disk_i(),
            seq_end: self.branch.seq_end,
        }
    }

    pub open spec fn ephemeral_branch_i(self) -> EphemeralCachingDiskBranch
    {
        if self.superblock_loaded() {
            EphemeralCachingDiskBranch::Known{v: self.branch_caching_disk_state_i()}
        } else {
            EphemeralCachingDiskBranch::Unknown
        }
    }

    pub open spec fn frozen_branch_metadata_i(self) -> Option<CachingDiskBranchMetadata>
    {
        if self.branch.in_flight is Some {
            let image = self.branch.in_flight.unwrap();
            Option::Some(CachingDiskBranchMetadata{
                sealed_roots: image.sealed_roots,
                seq_end: image.seq_end,
            })
        } else {
            Option::None
        }
    }

    pub open spec fn persistent_branch_i(self) -> PersistentCachingDiskBranch
    {
        let persistent_image = self.persistent_branch_image_i();
        if self.superblock_loaded() {
            PersistentCachingDiskBranch::Metadata{meta: persistent_image.metadata()}
        } else {
            PersistentCachingDiskBranch::Image{image: persistent_image}
        }
    }

    pub open spec fn i(self) -> CrashAwareCachingDiskBranch::State
    {
        CrashAwareCachingDiskBranch::State{
            persistent: self.persistent_branch_i(),
            ephemeral: self.ephemeral_branch_i(),
            frozen: self.frozen_branch_metadata_i(),
            prepared: self.branch.prepared,
        }
    }

    pub open spec fn inv(self) -> bool
    {
        &&& self.branch.wf()
        &&& async_disk_superblock_page_wf(self.disk.content)
        &&& self.persistent_superblock_image_i().wf()
        &&& self.cache.inv()
        &&& self.disk.inv()
        &&& self.branch_caching_disk_i().inv()
        &&& self.superblock_loaded() ==> {
            &&& self.branch.persistent_image.sealed_roots
                == self.persistent_superblock_image_i().branch_roots
            &&& self.branch.persistent_image.seq_end
                == self.persistent_superblock_image_i().branch_seq_end
        }
        &&& !self.superblock_loaded() ==> {
            &&& self.branch == AtomicBranchState::State::empty()
            &&& self.in_flight is None
            &&& self.in_flight_image is None
        }
        &&& self.in_flight is Some <==> self.branch.in_flight is Some
        &&& self.in_flight is Some <==> self.in_flight_image is Some
        &&& self.in_flight_image is Some ==> {
            let image = self.in_flight_image.unwrap();
            let branch_image = self.branch.in_flight.unwrap();
            &&& image.wf()
            &&& image.branch_roots == branch_image.sealed_roots
            &&& image.branch_seq_end == branch_image.seq_end
        }
    }

    pub open spec fn semantic_inv(self) -> bool
    {
        self.i().refinement_inv()
    }

    pub open spec fn same_except_cache_and_disk(self, post: Self) -> bool
    {
        &&& post.branch == self.branch
        &&& post.persistent_image == self.persistent_image
        &&& post.in_flight == self.in_flight
        &&& post.in_flight_image == self.in_flight_image
    }

    pub proof fn branch_interpretation_unchanged_by_same_projection(
        self,
        post: Self,
    )
        requires
            self.same_except_cache_and_disk(post),
            self.persistent_branch_i() == post.persistent_branch_i(),
            self.branch_caching_disk_i() == post.branch_caching_disk_i(),
        ensures
            self.i() == post.i(),
    {
        assert(self.superblock_loaded() == post.superblock_loaded());
        assert(self.branch_caching_disk_state_i() == post.branch_caching_disk_state_i());
        assert(self.ephemeral_branch_i() == post.ephemeral_branch_i());
        assert(self.frozen_branch_metadata_i() == post.frozen_branch_metadata_i());
        assert(self.i() == post.i());
    }

    pub proof fn loaded_caching_disk_internal_refines_branch_internal_preserves_inv(
        self,
        post: Self,
    )
        requires
            inv(self),
            self.same_except_cache_and_disk(post),
            self.superblock_loaded(),
            post.cache == self.cache,
            post.disk.inv(),
            async_disk_superblock_page_wf(post.disk.content),
            post.persistent_superblock_image_i() == self.persistent_superblock_image_i(),
            CachingDisk::State::next(
                self.branch_caching_disk_i(),
                post.branch_caching_disk_i(),
                CachingDisk::Label::Internal{},
            ),
            forall |addr: Address| {
                #[trigger] mini_allocator_allocated_addrs(
                    self.branch_caching_disk_state_i().mini_allocator,
                ).contains(addr)
            } ==> {
                &&& post.branch_caching_disk_i().readable().contains_key(addr)
                    == self.branch_caching_disk_state_i().disk.readable().contains_key(addr)
                &&& post.branch_caching_disk_i().readable().contains_key(addr) ==>
                    post.branch_caching_disk_i().readable()[addr]
                        == self.branch_caching_disk_state_i().disk.readable()[addr]
            },
        ensures
            CrashAwareCachingDiskBranch::State::next(
                self.i(),
                post.i(),
                CrashAwareCachingDiskBranch::Label::Internal,
            ),
            inv(post),
    {
        assert(post.superblock_loaded());
        assert(self.persistent_branch_i() == post.persistent_branch_i());
        assert(self.frozen_branch_metadata_i() == post.frozen_branch_metadata_i());
        assert(self.branch_caching_disk_state_i().sealed_roots
            == post.branch_caching_disk_state_i().sealed_roots);
        assert(self.branch_caching_disk_state_i().branch_summary
            == post.branch_caching_disk_state_i().branch_summary);
        assert(self.branch_caching_disk_state_i().metadata_loaded
            == post.branch_caching_disk_state_i().metadata_loaded);
        assert(self.branch_caching_disk_state_i().persisted_root_count
            == post.branch_caching_disk_state_i().persisted_root_count);
        assert(self.branch_caching_disk_state_i().active_branch
            == post.branch_caching_disk_state_i().active_branch);
        assert(self.branch_caching_disk_state_i().mini_allocator
            == post.branch_caching_disk_state_i().mini_allocator);
        assert(self.branch_caching_disk_state_i().seq_end
            == post.branch_caching_disk_state_i().seq_end);
        CachingDisk::State::internal_visible_unchanged(
            self.branch_caching_disk_state_i().disk,
            post.branch_caching_disk_i(),
        );
        active_loaded_nodes_preserved_by_readable_agreement(
            self.branch_caching_disk_state_i().disk,
            post.branch_caching_disk_i(),
            self.branch_caching_disk_state_i().mini_allocator,
        );

        assert(CachingDiskBranch::State::disk_internal(
            self.branch_caching_disk_state_i(),
            post.branch_caching_disk_state_i(),
            CachingDiskBranch::Label::Internal,
            post.branch_caching_disk_i(),
        )) by {
            reveal(CachingDiskBranch::State::disk_internal);
        }
        assert(CachingDiskBranch::State::next_by(
            self.branch_caching_disk_state_i(),
            post.branch_caching_disk_state_i(),
            CachingDiskBranch::Label::Internal,
            CachingDiskBranch::Step::disk_internal(post.branch_caching_disk_i()),
        )) by {
            reveal(CachingDiskBranch::State::next_by);
        }
        reveal(CachingDiskBranch::State::next);
        assert(CrashAwareCachingDiskBranch::State::internal(
            self.i(),
            post.i(),
            CrashAwareCachingDiskBranch::Label::Internal,
            post.branch_caching_disk_state_i(),
        )) by {
            reveal(CrashAwareCachingDiskBranch::State::internal);
        }
        assert(CrashAwareCachingDiskBranch::State::next_by(
            self.i(),
            post.i(),
            CrashAwareCachingDiskBranch::Label::Internal,
            CrashAwareCachingDiskBranch::Step::internal(post.branch_caching_disk_state_i()),
        )) by {
            reveal(CrashAwareCachingDiskBranch::State::next_by);
        }
        reveal(CrashAwareCachingDiskBranch::State::next);
        CachingDisk::State::inv_next(
            self.branch_caching_disk_i(),
            post.branch_caching_disk_i(),
            CachingDisk::Label::Internal{},
        );
        assert(post.inv()) by {
            assert(post.branch.wf());
            assert(async_disk_superblock_page_wf(post.disk.content));
            assert(post.persistent_superblock_image_i().wf());
            assert(post.cache.inv());
            assert(post.disk.inv());
            assert(post.branch_caching_disk_i().inv());
        }
        self.i().next_refines(post.i(), CrashAwareCachingDiskBranch::Label::Internal);
        assert(post.semantic_inv());
        assert(inv(post));
    }

    pub proof fn unchanged_by_same_cache_and_disk_content(
        self,
        post: Self,
    )
        requires
            inv(self),
            self.same_except_cache_and_disk(post),
            post.cache == self.cache,
            post.disk.content == self.disk.content,
            post.disk.inv(),
        ensures
            post.i() == self.i(),
            inv(post),
    {
        assert(post.superblock_loaded() == self.superblock_loaded());
        assert(post.persistent_superblock_image_i()
            == self.persistent_superblock_image_i()) by {
            if self.persistent_image is Some {
                assert(post.persistent_image == self.persistent_image);
            } else {
                assert(post.persistent_image is None);
                assert(async_disk_superblock_raw_i(post.disk.content)
                    == async_disk_superblock_raw_i(self.disk.content));
            }
        }

        assert(post.branch_projection_aus() =~= self.branch_projection_aus()) by {
            if self.branch.metadata_loaded() {
                assert(post.branch == self.branch);
            } else {
                assert(post.persistent_superblock_image_i()
                    == self.persistent_superblock_image_i());
                assert(post.disk.content == self.disk.content);
            }
        }

        assert(post.persistent_branch_image_i() == self.persistent_branch_image_i()) by {
            let image = self.persistent_superblock_image_i();
            assert(post.persistent_superblock_image_i() == image);
            assert(UnifiedCacheBranchSource::branch_image_projection_addrs_i(
                post.disk.content,
                image.branch_roots,
            ) =~= UnifiedCacheBranchSource::branch_image_projection_addrs_i(
                self.disk.content,
                image.branch_roots,
            ));
            assert_maps_equal!(
                post.persistent_branch_image_i().persistent,
                self.persistent_branch_image_i().persistent,
                addr => {
                    if post.persistent_branch_image_i().persistent.contains_key(addr) {
                        assert(self.persistent_branch_image_i().persistent.contains_key(addr));
                    }
                    if self.persistent_branch_image_i().persistent.contains_key(addr) {
                        assert(post.persistent_branch_image_i().persistent.contains_key(addr));
                    }
                }
            );
        }
        assert(post.persistent_branch_i() == self.persistent_branch_i());

        assert(post.branch_caching_disk_i() == self.branch_caching_disk_i()) by {
            assert(post.branch_projection_aus() =~= self.branch_projection_aus());
            assert_maps_equal!(
                post.branch_caching_disk_i().cache,
                self.branch_caching_disk_i().cache,
                addr => {}
            );
            assert_maps_equal!(
                post.branch_caching_disk_i().status,
                self.branch_caching_disk_i().status,
                addr => {}
            );
            assert_maps_equal!(
                post.branch_caching_disk_i().persistent,
                self.branch_caching_disk_i().persistent,
                addr => {
                    if post.branch_caching_disk_i().persistent.contains_key(addr) {
                        assert(self.branch_caching_disk_i().persistent.contains_key(addr));
                    }
                    if self.branch_caching_disk_i().persistent.contains_key(addr) {
                        assert(post.branch_caching_disk_i().persistent.contains_key(addr));
                    }
                }
            );
        }
        self.branch_interpretation_unchanged_by_same_projection(post);
        assert(post.i() == self.i());

        assert(post.inv()) by {
            assert(post.branch.wf());
            assert(async_disk_superblock_page_wf(post.disk.content));
            assert(post.persistent_superblock_image_i().wf());
            assert(post.cache.inv());
            assert(post.disk.inv());
            assert(post.branch_caching_disk_i().inv());
            if !post.superblock_loaded() {
                assert(!self.superblock_loaded());
                assert(post.branch == AtomicBranchState::State::empty());
                assert(post.in_flight is None);
                assert(post.in_flight_image is None);
            }
        }
        assert(post.semantic_inv()) by {
            assert(self.semantic_inv());
            assert(post.i() == self.i());
        }
        assert(inv(post));
    }

    pub proof fn loaded_branch_image_matches_materialized(
        self,
        image: AbstractSuperblockImage,
        frozen: CachingDiskBranchMetadata,
    )
        requires
            inv(self),
            self.superblock_loaded(),
            self.branch.metadata_loaded(),
            image.wf(),
            frozen.sealed_roots == image.branch_roots,
            frozen.seq_end == image.branch_seq_end,
            CachingDiskBranch::State::next(
                self.branch_caching_disk_state_i(),
                self.branch_caching_disk_state_i(),
                CachingDiskBranch::Label::FreezePrepared{image: frozen},
            ),
        ensures
            self.branch_image_i(image)
                == CachingDiskBranchImage::materialized_from_persistent(
                    self.branch_caching_disk_state_i(),
                    frozen,
                ),
            self.branch_image_i(image).loadable(),
            self.branch_image_i(image).stack_wf(),
    {
        let state = self.branch_caching_disk_state_i();
        let materialized = CachingDiskBranchImage::materialized_from_persistent(state, frozen);
        let full_image = CachingDiskBranchImage{
            persistent: self.disk.content,
            sealed_roots: image.branch_roots,
            seq_end: image.branch_seq_end,
        };

        state.materialized_image_matches_visible_prefix(frozen);
        assert(materialized.wf());
        assert(materialized.sealed_roots == full_image.sealed_roots);
        assert(materialized.seq_end == full_image.seq_end);
        let materialized_aus = summary_aus(materialized.branch_summary());
        let materialized_addrs = addresses_in_aus(materialized_aus);

        assert(materialized_aus <= self.branch_projection_aus()) by {
            assert(state.metadata_loaded);
            assert(state.branch_metadata_loaded());
            assert(state.branch_summary == state.interpreted_branch_summary());
            assert(materialized_aus <= summary_aus(state.interpreted_branch_summary()));
            assert(self.branch_projection_aus() == self.branch.owned_aus());
            assert(self.branch.owned_aus() == summary_aus(self.branch.branch_summary)
                + self.branch.mini_allocator.all_aus());
            assert(state.branch_summary == self.branch.branch_summary);
            assert forall |au: AU| #[trigger] materialized_aus.contains(au)
                implies self.branch_projection_aus().contains(au) by {
                assert(summary_aus(state.interpreted_branch_summary()).contains(au));
                assert(summary_aus(self.branch.branch_summary).contains(au));
            }
        };

        assert(materialized.persistent == self.disk.content.restrict(materialized_addrs)) by {
            assert(CachingDiskBranchImage::materialized_summary_addrs(
                state.disk.persistent,
                frozen,
            ) == materialized_addrs) by {
                assert(completed_branch_summary_from_reads(
                    frozen.sealed_roots,
                    to_branch_nodes(state.disk.persistent),
                ) == materialized.branch_summary());
            }
            assert_maps_equal!(
                materialized.persistent,
                self.disk.content.restrict(materialized_addrs),
                addr => {
                    if materialized.persistent.contains_key(addr) {
                        assert(materialized_addrs.contains(addr));
                        assert(addresses_in_aus(self.branch_projection_aus()).contains(addr));
                    }
                    if self.disk.content.restrict(materialized_addrs).contains_key(addr) {
                        assert(materialized_addrs.contains(addr));
                        assert(addresses_in_aus(self.branch_projection_aus()).contains(addr));
                        assert(state.disk.persistent.contains_key(addr));
                    }
                }
            );
        };

        assert(full_image.persistent.restrict(materialized_addrs)
            == materialized.persistent.restrict(materialized_addrs)) by {
            assert_maps_equal!(
                full_image.persistent.restrict(materialized_addrs),
                materialized.persistent.restrict(materialized_addrs),
                addr => {}
            );
        }
        CachingDiskBranchImage::same_summary_aus_preserves_sealed_stack(
            materialized,
            full_image,
        );

        assert(UnifiedCacheBranchSource::branch_image_projection_addrs_i(
            self.disk.content,
            image.branch_roots,
        ) == materialized_addrs) by {
            assert(branch_summary_reads_valid(
                image.branch_roots,
                to_branch_nodes(self.disk.content),
            ));
            assert(UnifiedCacheBranchSource::branch_image_summary_i(
                self.disk.content,
                image.branch_roots,
            ) == completed_branch_summary_from_reads(
                image.branch_roots,
                to_branch_nodes(self.disk.content),
            ));
            assert(completed_branch_summary_from_reads(
                image.branch_roots,
                to_branch_nodes(self.disk.content),
            ) == full_image.branch_summary());
            assert(full_image.branch_summary() == materialized.branch_summary());
        }

        assert(self.branch_image_i(image).persistent == materialized.persistent) by {
            assert_maps_equal!(
                self.branch_image_i(image).persistent,
                materialized.persistent,
                addr => {}
            );
        }
        assert(self.branch_image_i(image).sealed_roots == materialized.sealed_roots);
        assert(self.branch_image_i(image).seq_end == materialized.seq_end);
        assert(self.branch_image_i(image) == materialized);
        assert(self.branch_image_i(image).loadable());
        assert(self.branch_image_i(image).stack_wf());
    }

    pub proof fn unloaded_branch_image_matches_materialized(
        self,
        image: AbstractSuperblockImage,
        frozen: CachingDiskBranchMetadata,
    )
        requires
            inv(self),
            self.superblock_loaded(),
            !self.branch.metadata_loaded(),
            image == self.persistent_superblock_image_i(),
            image.wf(),
            frozen.sealed_roots == image.branch_roots,
            frozen.seq_end == image.branch_seq_end,
            CachingDiskBranch::State::next(
                self.branch_caching_disk_state_i(),
                self.branch_caching_disk_state_i(),
                CachingDiskBranch::Label::FreezePrepared{image: frozen},
            ),
        ensures
            self.branch_image_i(image)
                == CachingDiskBranchImage::materialized_from_persistent(
                    self.branch_caching_disk_state_i(),
                    frozen,
                ),
            self.branch_image_i(image).loadable(),
            self.branch_image_i(image).stack_wf(),
    {
        let state = self.branch_caching_disk_state_i();
        let materialized = CachingDiskBranchImage::materialized_from_persistent(state, frozen);
        let full_image = CachingDiskBranchImage{
            persistent: self.disk.content,
            sealed_roots: image.branch_roots,
            seq_end: image.branch_seq_end,
        };

        state.materialized_image_matches_visible_prefix(frozen);
        assert(materialized.wf());
        assert(materialized.sealed_roots == full_image.sealed_roots);
        assert(materialized.seq_end == full_image.seq_end);
        let materialized_aus = summary_aus(materialized.branch_summary());
        let materialized_addrs = addresses_in_aus(materialized_aus);

        assert(materialized_aus <= self.branch_projection_aus()) by {
            let mat_nodes = materialized.persistent_branch_nodes();
            let full_nodes = to_branch_nodes(self.disk.content);
            assert(branch_summary_reads_valid(frozen.sealed_roots, mat_nodes));
            assert(branch_summary_reads_valid(frozen.sealed_roots, full_nodes)) by {
                assert forall |i: int| #![auto]
                    0 <= i < frozen.sealed_roots.len()
                    implies root_summary_read_valid(frozen.sealed_roots[i], full_nodes)
                by {
                    let root = frozen.sealed_roots[i];
                    assert(root_summary_read_valid(root, mat_nodes));
                    assert(mat_nodes.contains_key(root));
                    assert(materialized.persistent.contains_key(root));
                    assert(self.disk.content.contains_key(root));
                    assert(full_nodes.contains_key(root));
                    assert(full_nodes[root] == mat_nodes[root]);
                    if mat_nodes[root] is Index {
                        let aux = mat_nodes[root]->aux_ptr.unwrap();
                        assert(mat_nodes.contains_key(aux));
                        assert(materialized.persistent.contains_key(aux));
                        assert(self.disk.content.contains_key(aux));
                        assert(full_nodes.contains_key(aux));
                        assert(full_nodes[aux] == mat_nodes[aux]);
                    }
                }
            };
            branch_summary_from_reads_up_to_self_ensures(
                frozen.sealed_roots,
                mat_nodes,
                frozen.sealed_roots.len() as nat,
            );
            branch_summary_from_reads_up_to_self_ensures(
                frozen.sealed_roots,
                full_nodes,
                frozen.sealed_roots.len() as nat,
            );
            materialized.branch_summary_finite();
            let full_summary = completed_branch_summary_from_reads(
                frozen.sealed_roots,
                full_nodes,
            );
            root_aus_up_to_full(frozen.sealed_roots);
            to_aus_finite(frozen.sealed_roots.to_set());
            assert(full_summary.dom().finite()) by {
                assert(full_summary.dom()
                    =~= root_aus_up_to(frozen.sealed_roots, frozen.sealed_roots.len() as nat));
                assert(root_aus_up_to(frozen.sealed_roots, frozen.sealed_roots.len() as nat)
                    =~= to_aus(frozen.sealed_roots.to_set()));
            }
            lemma_values_finite(full_summary);
            assert forall |au: AU| #[trigger] materialized_aus.contains(au)
                implies self.branch_projection_aus().contains(au) by {
                let summary = lemma_union_set_of_sets_contains(
                    materialized.branch_summary().values(),
                    au,
                );
                let root_au = choose |root_au: AU| #![auto] {
                    &&& materialized.branch_summary().contains_key(root_au)
                    &&& materialized.branch_summary()[root_au] == summary
                };
                assert(materialized.branch_summary().dom().contains(root_au));
                assert(root_aus_up_to(
                    frozen.sealed_roots,
                    frozen.sealed_roots.len() as nat,
                ).contains(root_au));
                let idx = root_aus_up_to_member_has_index(
                    frozen.sealed_roots,
                    frozen.sealed_roots.len() as nat,
                    root_au,
                );
                let root = frozen.sealed_roots[idx];
                assert(root.au == root_au);
                assert(materialized.branch_summary()[root.au]
                    == root_summary_from_read(root, mat_nodes));
                assert(summary == root_summary_from_read(root, mat_nodes));
                assert(root_summary_from_read(root, full_nodes) == summary) by {
                    assert(root_summary_read_valid(root, mat_nodes));
                    assert(root_summary_read_valid(root, full_nodes));
                    assert(full_nodes[root] == mat_nodes[root]);
                    if mat_nodes[root] is Index {
                        let aux = mat_nodes[root]->aux_ptr.unwrap();
                        assert(full_nodes[root]->aux_ptr == Some(aux));
                        assert(full_nodes[aux] == mat_nodes[aux]);
                    }
                }
                assert(full_summary[root.au] == summary);
                assert(UnifiedCacheBranchSource::branch_image_summary_i(
                    self.disk.content,
                    image.branch_roots,
                ) == full_summary);
                assert(UnifiedCacheBranchSource::branch_image_summary_aus_i(
                    self.disk.content,
                    image.branch_roots,
                ).contains(au)) by {
                    assert(full_summary.values().contains(summary));
                    lemma_union_set_of_sets_subset(full_summary.values(), summary);
                }
                let addr = Address{au, page: 0};
                assert(UnifiedCacheBranchSource::branch_image_projection_addrs_i(
                    self.disk.content,
                    image.branch_roots,
                ).contains(addr));
                to_aus_domain(UnifiedCacheBranchSource::branch_image_projection_addrs_i(
                    self.disk.content,
                    image.branch_roots,
                ));
                assert(self.branch_projection_aus() == to_aus(
                    UnifiedCacheBranchSource::branch_image_projection_addrs_i(
                        self.disk.content,
                        image.branch_roots,
                    ),
                ));
            }
        };

        assert(materialized.persistent == self.disk.content.restrict(materialized_addrs)) by {
            assert(CachingDiskBranchImage::materialized_summary_addrs(
                state.disk.persistent,
                frozen,
            ) == materialized_addrs) by {
                let full_state_image = CachingDiskBranchImage{
                    persistent: state.disk.persistent,
                    sealed_roots: frozen.sealed_roots,
                    seq_end: frozen.seq_end,
                };
                assert(full_state_image.branch_summary() == materialized.branch_summary());
                assert(completed_branch_summary_from_reads(
                    frozen.sealed_roots,
                    to_branch_nodes(state.disk.persistent),
                ) == materialized.branch_summary());
            }
            assert_maps_equal!(
                materialized.persistent,
                self.disk.content.restrict(materialized_addrs),
                addr => {
                    if materialized.persistent.contains_key(addr) {
                        assert(materialized_addrs.contains(addr));
                        assert(addresses_in_aus(self.branch_projection_aus()).contains(addr));
                    }
                    if self.disk.content.restrict(materialized_addrs).contains_key(addr) {
                        assert(materialized_addrs.contains(addr));
                        assert(addresses_in_aus(self.branch_projection_aus()).contains(addr));
                        assert(state.disk.persistent.contains_key(addr));
                    }
                }
            );
        };

        assert(full_image.persistent.restrict(materialized_addrs)
            == materialized.persistent.restrict(materialized_addrs)) by {
            assert_maps_equal!(
                full_image.persistent.restrict(materialized_addrs),
                materialized.persistent.restrict(materialized_addrs),
                addr => {}
            );
        }
        CachingDiskBranchImage::same_summary_aus_preserves_sealed_stack(
            materialized,
            full_image,
        );

        assert(UnifiedCacheBranchSource::branch_image_projection_addrs_i(
            self.disk.content,
            image.branch_roots,
        ) == materialized_addrs) by {
            assert(branch_summary_reads_valid(
                image.branch_roots,
                to_branch_nodes(self.disk.content),
            ));
            assert(UnifiedCacheBranchSource::branch_image_summary_i(
                self.disk.content,
                image.branch_roots,
            ) == completed_branch_summary_from_reads(
                image.branch_roots,
                to_branch_nodes(self.disk.content),
            ));
            assert(completed_branch_summary_from_reads(
                image.branch_roots,
                to_branch_nodes(self.disk.content),
            ) == full_image.branch_summary());
            assert(full_image.branch_summary() == materialized.branch_summary());
        }

        assert(self.branch_image_i(image).persistent == materialized.persistent) by {
            assert_maps_equal!(
                self.branch_image_i(image).persistent,
                materialized.persistent,
                addr => {}
            );
        }
        assert(self.branch_image_i(image).sealed_roots == materialized.sealed_roots);
        assert(self.branch_image_i(image).seq_end == materialized.seq_end);
        assert(self.branch_image_i(image) == materialized);
        assert(self.branch_image_i(image).loadable());
        assert(self.branch_image_i(image).stack_wf());
    }

    pub proof fn post_crash_persistent_image_matches_materialized(
        self,
        post: Self,
        image: AbstractSuperblockImage,
        frozen: CachingDiskBranchMetadata,
    )
        requires
            inv(self),
            self.superblock_loaded(),
            post.persistent_image is None,
            post.disk.content == self.disk.content,
            post.persistent_superblock_image_i() == image,
            image.wf(),
            frozen.sealed_roots == image.branch_roots,
            frozen.seq_end == image.branch_seq_end,
            self.branch.metadata_loaded() || image == self.persistent_superblock_image_i(),
            CachingDiskBranch::State::next(
                self.branch_caching_disk_state_i(),
                self.branch_caching_disk_state_i(),
                CachingDiskBranch::Label::FreezePrepared{image: frozen},
            ),
        ensures
            post.persistent_branch_image_i()
                == CachingDiskBranchImage::materialized_from_persistent(
                    self.branch_caching_disk_state_i(),
                    frozen,
                ),
            post.persistent_branch_image_i().loadable(),
            post.persistent_branch_image_i().stack_wf(),
    {
        if self.branch.metadata_loaded() {
            self.loaded_branch_image_matches_materialized(image, frozen);
        } else {
            self.unloaded_branch_image_matches_materialized(image, frozen);
        }

        assert(post.branch_image_i(image) == self.branch_image_i(image)) by {
            assert(post.disk.content == self.disk.content);
            assert_maps_equal!(
                post.branch_image_i(image).persistent,
                self.branch_image_i(image).persistent,
                addr => {
                    assert(UnifiedCacheBranchSource::branch_image_projection_addrs_i(
                        post.disk.content,
                        image.branch_roots,
                    ) =~= UnifiedCacheBranchSource::branch_image_projection_addrs_i(
                        self.disk.content,
                        image.branch_roots,
                    ));
                }
            );
        }
        assert(post.persistent_branch_image_i() == post.branch_image_i(image));
        assert(post.persistent_branch_image_i()
            == CachingDiskBranchImage::materialized_from_persistent(
                self.branch_caching_disk_state_i(),
                frozen,
            ));
        assert(post.persistent_branch_image_i().loadable());
        assert(post.persistent_branch_image_i().stack_wf());
    }

    pub proof fn unchanged_by_cache_access_outside_branch_projection(
        self,
        post: Self,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    )
        requires
            inv(self),
            self.same_except_cache_and_disk(post),
            post.disk.content == self.disk.content,
            post.disk.inv(),
            Cache::State::next(
                self.cache,
                post.cache,
                Cache::Label::Access{reads, writes},
            ),
            writes.dom().disjoint(addresses_in_aus(self.branch_projection_aus())),
        ensures
            post.i() == self.i(),
            inv(post),
    {
        let aus = self.branch_projection_aus();
        projected_cache_access_outside_aus_unchanged(
            self.cache,
            post.cache,
            aus,
            reads,
            writes,
        );
        assert(post.superblock_loaded() == self.superblock_loaded());
        assert(post.persistent_superblock_image_i()
            == self.persistent_superblock_image_i()) by {
            if self.persistent_image is Some {
                assert(post.persistent_image == self.persistent_image);
            } else {
                assert(post.persistent_image is None);
                assert(async_disk_superblock_raw_i(post.disk.content)
                    == async_disk_superblock_raw_i(self.disk.content));
            }
        }

        assert(post.branch_projection_aus() =~= aus) by {
            if self.branch.metadata_loaded() {
                assert(post.branch == self.branch);
            } else {
                assert(post.persistent_superblock_image_i()
                    == self.persistent_superblock_image_i());
                assert(post.disk.content == self.disk.content);
            }
        }

        assert(post.persistent_branch_image_i() == self.persistent_branch_image_i()) by {
            let image = self.persistent_superblock_image_i();
            assert(post.persistent_superblock_image_i() == image);
            assert(UnifiedCacheBranchSource::branch_image_projection_addrs_i(
                post.disk.content,
                image.branch_roots,
            ) =~= UnifiedCacheBranchSource::branch_image_projection_addrs_i(
                self.disk.content,
                image.branch_roots,
            ));
            assert_maps_equal!(
                post.persistent_branch_image_i().persistent,
                self.persistent_branch_image_i().persistent,
                addr => {
                    if post.persistent_branch_image_i().persistent.contains_key(addr) {
                        assert(self.persistent_branch_image_i().persistent.contains_key(addr));
                    }
                    if self.persistent_branch_image_i().persistent.contains_key(addr) {
                        assert(post.persistent_branch_image_i().persistent.contains_key(addr));
                    }
                }
            );
        }
        assert(post.persistent_branch_i() == self.persistent_branch_i());

        assert(post.branch_caching_disk_i() == self.branch_caching_disk_i()) by {
            assert(post.branch_projection_aus() =~= aus);
            assert_maps_equal!(
                post.branch_caching_disk_i().cache,
                self.branch_caching_disk_i().cache,
                addr => {}
            );
            assert_maps_equal!(
                post.branch_caching_disk_i().status,
                self.branch_caching_disk_i().status,
                addr => {}
            );
            assert_maps_equal!(
                post.branch_caching_disk_i().persistent,
                self.branch_caching_disk_i().persistent,
                addr => {
                    if post.branch_caching_disk_i().persistent.contains_key(addr) {
                        assert(post.disk.content.contains_key(addr));
                        assert(post.disk.content[addr] == self.disk.content[addr]);
                    }
                    if self.branch_caching_disk_i().persistent.contains_key(addr) {
                        assert(self.disk.content.contains_key(addr));
                        assert(post.disk.content.contains_key(addr));
                        assert(post.disk.content[addr] == self.disk.content[addr]);
                    }
                }
            );
        }
        self.branch_interpretation_unchanged_by_same_projection(post);
        assert(post.i() == self.i());

        assert(post.inv()) by {
            assert(post.branch.wf());
            assert(async_disk_superblock_page_wf(post.disk.content));
            assert(post.persistent_superblock_image_i().wf());
            assert(post.cache.inv()) by {
                Cache::State::inv_next(
                    self.cache,
                    post.cache,
                    Cache::Label::Access{reads, writes},
                );
            }
            assert(post.disk.inv());
            assert(post.branch_caching_disk_i().inv());
            if !post.superblock_loaded() {
                assert(!self.superblock_loaded());
                assert(post.branch == AtomicBranchState::State::empty());
                assert(post.in_flight is None);
                assert(post.in_flight_image is None);
            }
        }
        assert(post.semantic_inv()) by {
            assert(self.semantic_inv());
            assert(post.i() == self.i());
        }
        assert(inv(post));
    }

    pub proof fn loaded_cache_disk_ops_begin_refines_branch_internal(
        self,
        post: Self,
        requests: Set<DiskRequest>,
    )
        requires
            inv(self),
            self.same_except_cache_and_disk(post),
            self.superblock_loaded(),
            post.disk.content == self.disk.content,
            post.disk.inv(),
            Cache::State::next(
                self.cache,
                post.cache,
                Cache::Label::DiskOps{requests, responses: Map::empty()},
            ),
        ensures
            CrashAwareCachingDiskBranch::State::next(
                self.i(),
                post.i(),
                CrashAwareCachingDiskBranch::Label::Internal,
            ),
            inv(post),
    {
        let aus = self.branch_projection_aus();
        let projected_post = adapter_caching_disk_i(post.cache, self.disk, aus);
        cache_disk_ops_begin_refines_caching_disk_internal(
            self.cache,
            post.cache,
            self.disk,
            aus,
            requests,
        );
        assert(post.branch_projection_aus() =~= aus);
        assert(post.branch_caching_disk_i() == projected_post) by {
            assert_maps_equal!(
                post.branch_caching_disk_i().cache,
                projected_post.cache,
                addr => {}
            );
            assert_maps_equal!(
                post.branch_caching_disk_i().status,
                projected_post.status,
                addr => {}
            );
            assert_maps_equal!(
                post.branch_caching_disk_i().persistent,
                projected_post.persistent,
                addr => {
                    if post.branch_caching_disk_i().persistent.contains_key(addr) {
                        assert(post.disk.content.contains_key(addr));
                        assert(post.disk.content[addr] == self.disk.content[addr]);
                    }
                    if projected_post.persistent.contains_key(addr) {
                        assert(self.disk.content.contains_key(addr));
                        assert(post.disk.content.contains_key(addr));
                        assert(post.disk.content[addr] == self.disk.content[addr]);
                    }
                }
            );
        }
        assert(post.branch_caching_disk_i().readable()
            == self.branch_caching_disk_i().readable());
        assert(CachingDisk::State::next(
            self.branch_caching_disk_i(),
            post.branch_caching_disk_i(),
            CachingDisk::Label::Internal{},
        ));
        CachingDisk::State::internal_visible_unchanged(
            self.branch_caching_disk_i(),
            post.branch_caching_disk_i(),
        );
        active_loaded_nodes_preserved_by_readable_agreement(
            self.branch_caching_disk_state_i().disk,
            post.branch_caching_disk_i(),
            self.branch_caching_disk_state_i().mini_allocator,
        );
        assert(CachingDisk::State::next(
            self.branch_caching_disk_i(),
            post.branch_caching_disk_i(),
            CachingDisk::Label::Internal{},
        ));
        assert(CachingDiskBranch::State::disk_internal(
            self.branch_caching_disk_state_i(),
            post.branch_caching_disk_state_i(),
            CachingDiskBranch::Label::Internal,
            post.branch_caching_disk_i(),
        )) by {
            reveal(CachingDiskBranch::State::disk_internal);
        }
        assert(CachingDiskBranch::State::next_by(
            self.branch_caching_disk_state_i(),
            post.branch_caching_disk_state_i(),
            CachingDiskBranch::Label::Internal,
            CachingDiskBranch::Step::disk_internal(post.branch_caching_disk_i()),
        )) by {
            reveal(CachingDiskBranch::State::next_by);
        }
        reveal(CachingDiskBranch::State::next);
        assert(CrashAwareCachingDiskBranch::State::internal(
            self.i(),
            post.i(),
            CrashAwareCachingDiskBranch::Label::Internal,
            post.branch_caching_disk_state_i(),
        )) by {
            reveal(CrashAwareCachingDiskBranch::State::internal);
        }
        assert(CrashAwareCachingDiskBranch::State::next_by(
            self.i(),
            post.i(),
            CrashAwareCachingDiskBranch::Label::Internal,
            CrashAwareCachingDiskBranch::Step::internal(post.branch_caching_disk_state_i()),
        )) by {
            reveal(CrashAwareCachingDiskBranch::State::next_by);
        }
        reveal(CrashAwareCachingDiskBranch::State::next);
        CachingDisk::State::inv_next(
            self.branch_caching_disk_i(),
            post.branch_caching_disk_i(),
            CachingDisk::Label::Internal{},
        );
        assert(post.inv()) by {
            assert(post.branch.wf());
            assert(async_disk_superblock_page_wf(post.disk.content));
            assert(post.persistent_superblock_image_i() == self.persistent_superblock_image_i());
            assert(post.persistent_superblock_image_i().wf());
            assert(post.cache.inv()) by {
                Cache::State::inv_next(
                    self.cache,
                    post.cache,
                    Cache::Label::DiskOps{requests, responses: Map::empty()},
                );
            }
            assert(post.branch_caching_disk_i().inv());
        }
        self.i().next_refines(post.i(), CrashAwareCachingDiskBranch::Label::Internal);
        assert(post.semantic_inv());
        assert(inv(post));
    }

    pub proof fn loaded_cache_internal_refines_branch_internal(
        self,
        post: Self,
    )
        requires
            inv(self),
            self.same_except_cache_and_disk(post),
            self.superblock_loaded(),
            post.disk.content == self.disk.content,
            post.disk.inv(),
            Cache::State::next(self.cache, post.cache, Cache::Label::Internal{}),
            // Old active-readable preservation precondition kept for reference.
            // forall |addr: Address| {
            //     &&& #[trigger] mini_allocator_allocated_addrs(
            //         self.branch_caching_disk_state_i().mini_allocator,
            //     ).contains(addr)
            //     &&& cache_filled_addr(self.cache, addr)
            // } ==> {
            //     &&& cache_filled_addr(post.cache, addr)
            //     &&& cache_filled_page(post.cache, addr) == cache_filled_page(self.cache, addr)
            // },
        ensures
            CrashAwareCachingDiskBranch::State::next(
                self.i(),
                post.i(),
                CrashAwareCachingDiskBranch::Label::Internal,
            ),
            inv(post),
    {
        let aus = self.branch_projection_aus();
        let projected_post = adapter_caching_disk_i(post.cache, self.disk, aus);
        cache_internal_refines_caching_disk_internal(self.cache, post.cache, self.disk, aus);
        assert(post.branch_projection_aus() =~= aus);
        assert(post.branch_caching_disk_i() == projected_post) by {
            assert_maps_equal!(
                post.branch_caching_disk_i().cache,
                projected_post.cache,
                addr => {}
            );
            assert_maps_equal!(
                post.branch_caching_disk_i().status,
                projected_post.status,
                addr => {}
            );
            assert_maps_equal!(
                post.branch_caching_disk_i().persistent,
                projected_post.persistent,
                addr => {
                    if post.branch_caching_disk_i().persistent.contains_key(addr) {
                        assert(post.disk.content.contains_key(addr));
                        assert(post.disk.content[addr] == self.disk.content[addr]);
                    }
                    if projected_post.persistent.contains_key(addr) {
                        assert(self.disk.content.contains_key(addr));
                        assert(post.disk.content.contains_key(addr));
                        assert(post.disk.content[addr] == self.disk.content[addr]);
                    }
                }
            );
        }
        // Old active-readable preservation proof kept for reference.
        // let active_addrs = mini_allocator_allocated_addrs(
        //     self.branch_caching_disk_state_i().mini_allocator,
        // );
        // let projected_active_addrs = active_addrs * addresses_in_aus(aus);
        // cache_internal_preserves_readable_on_preserved_filled_addrs(
        //     self.cache,
        //     post.cache,
        //     self.disk,
        //     aus,
        //     projected_active_addrs,
        // );
        // assert forall |addr: Address| #[trigger] active_addrs.contains(addr) implies {
        //     &&& post.branch_caching_disk_i().readable().contains_key(addr)
        //         == self.branch_caching_disk_i().readable().contains_key(addr)
        //     &&& post.branch_caching_disk_i().readable().contains_key(addr) ==>
        //         post.branch_caching_disk_i().readable()[addr]
        //             == self.branch_caching_disk_i().readable()[addr]
        // } by {
        //     if projected_active_addrs.contains(addr) {
        //         assert(addresses_in_aus(aus).contains(addr));
        //     } else {
        //         assert(!addresses_in_aus(aus).contains(addr));
        //         assert(!self.branch_caching_disk_i().readable().contains_key(addr)) by {
        //             if self.branch_caching_disk_i().readable().contains_key(addr) {
        //                 if self.branch_caching_disk_i().cache.contains_key(addr) {
        //                     assert(project_cache_pages(self.cache, aus).contains_key(addr));
        //                     assert(addresses_in_aus(aus).contains(addr));
        //                 } else {
        //                     assert(self.branch_caching_disk_i().persistent.contains_key(addr));
        //                     assert(self.disk.content.restrict(addresses_in_aus(aus)).contains_key(addr));
        //                     assert(addresses_in_aus(aus).contains(addr));
        //                 }
        //             }
        //         }
        //         assert(!post.branch_caching_disk_i().readable().contains_key(addr)) by {
        //             if post.branch_caching_disk_i().readable().contains_key(addr) {
        //                 if post.branch_caching_disk_i().cache.contains_key(addr) {
        //                     assert(project_cache_pages(post.cache, aus).contains_key(addr));
        //                     assert(addresses_in_aus(aus).contains(addr));
        //                 } else {
        //                     assert(post.branch_caching_disk_i().persistent.contains_key(addr));
        //                     assert(projected_post.persistent.contains_key(addr));
        //                     assert(self.disk.content.restrict(addresses_in_aus(aus)).contains_key(addr));
        //                     assert(addresses_in_aus(aus).contains(addr));
        //                 }
        //             }
        //         }
        //     }
        // }
        // active_loaded_nodes_preserved_by_readable_agreement(
        //     self.branch_caching_disk_state_i().disk,
        //     post.branch_caching_disk_i(),
        //     self.branch_caching_disk_state_i().mini_allocator,
        // );
        assert(CachingDisk::State::next(
            self.branch_caching_disk_i(),
            post.branch_caching_disk_i(),
            CachingDisk::Label::Internal{},
        ));
        assert(CachingDiskBranch::State::disk_internal(
            self.branch_caching_disk_state_i(),
            post.branch_caching_disk_state_i(),
            CachingDiskBranch::Label::Internal,
            post.branch_caching_disk_i(),
        )) by {
            reveal(CachingDiskBranch::State::disk_internal);
        }
        assert(CachingDiskBranch::State::next_by(
            self.branch_caching_disk_state_i(),
            post.branch_caching_disk_state_i(),
            CachingDiskBranch::Label::Internal,
            CachingDiskBranch::Step::disk_internal(post.branch_caching_disk_i()),
        )) by {
            reveal(CachingDiskBranch::State::next_by);
        }
        reveal(CachingDiskBranch::State::next);
        assert(CrashAwareCachingDiskBranch::State::internal(
            self.i(),
            post.i(),
            CrashAwareCachingDiskBranch::Label::Internal,
            post.branch_caching_disk_state_i(),
        )) by {
            reveal(CrashAwareCachingDiskBranch::State::internal);
        }
        assert(CrashAwareCachingDiskBranch::State::next_by(
            self.i(),
            post.i(),
            CrashAwareCachingDiskBranch::Label::Internal,
            CrashAwareCachingDiskBranch::Step::internal(post.branch_caching_disk_state_i()),
        )) by {
            reveal(CrashAwareCachingDiskBranch::State::next_by);
        }
        reveal(CrashAwareCachingDiskBranch::State::next);
        CachingDisk::State::inv_next(
            self.branch_caching_disk_i(),
            post.branch_caching_disk_i(),
            CachingDisk::Label::Internal{},
        );
        assert(post.inv()) by {
            assert(post.branch.wf());
            assert(async_disk_superblock_page_wf(post.disk.content));
            assert(post.persistent_superblock_image_i() == self.persistent_superblock_image_i());
            assert(post.persistent_superblock_image_i().wf());
            assert(post.cache.inv()) by {
                Cache::State::inv_next(self.cache, post.cache, Cache::Label::Internal{});
            }
            assert(post.branch_caching_disk_i().inv());
        }
        self.i().next_refines(post.i(), CrashAwareCachingDiskBranch::Label::Internal);
        assert(post.semantic_inv());
        assert(inv(post));
    }

    pub proof fn loaded_cache_disk_ops_end_refines_branch_internal(
        self,
        post: Self,
        responses: Map<Address, DiskResponse>,
    )
        requires
            inv(self),
            self.same_except_cache_and_disk(post),
            self.superblock_loaded(),
            post.disk.content == self.disk.content,
            post.disk.inv(),
            Cache::State::next(
                self.cache,
                post.cache,
                Cache::Label::DiskOps{requests: Set::empty(), responses},
            ),
            // Old active read-response exclusion kept for reference.
            // forall |addr: Address| {
            //     &&& #[trigger] responses.contains_key(addr)
            //     &&& mini_allocator_allocated_addrs(
            //         self.branch_caching_disk_state_i().mini_allocator,
            //     ).contains(addr)
            //     &&& responses[addr] is ReadResp
            // } ==> false,
            forall |addr: Address| {
                &&& #[trigger] responses.contains_key(addr)
                &&& addresses_in_aus(self.branch_projection_aus()).contains(addr)
            } ==> {
                // Old read-response coupling:
                // &&& self.disk.content.contains_key(addr)
                &&& responses[addr] is ReadResp ==> {
                    self.disk.content.contains_key(addr) ==> responses[addr]->data
                        == self.disk.content[addr]
                }
                &&& responses[addr] is WriteResp ==> {
                    &&& self.disk.content.contains_key(addr)
                    &&& cache_filled_addr(self.cache, addr)
                    &&& self.disk.content[addr] == cache_filled_page(self.cache, addr)
                }
            },
        ensures
            CrashAwareCachingDiskBranch::State::next(
                self.i(),
                post.i(),
                CrashAwareCachingDiskBranch::Label::Internal,
            ),
            inv(post),
    {
        let aus = self.branch_projection_aus();
        let projected_post = adapter_caching_disk_i(post.cache, self.disk, aus);
        cache_disk_ops_end_refines_caching_disk_internal(
            self.cache,
            post.cache,
            self.disk,
            aus,
            responses,
        );
        assert(post.branch_projection_aus() =~= aus);
        assert(post.branch_caching_disk_i() == projected_post) by {
            assert_maps_equal!(
                post.branch_caching_disk_i().cache,
                projected_post.cache,
                addr => {}
            );
            assert_maps_equal!(
                post.branch_caching_disk_i().status,
                projected_post.status,
                addr => {}
            );
            assert_maps_equal!(
                post.branch_caching_disk_i().persistent,
                projected_post.persistent,
                addr => {
                    if post.branch_caching_disk_i().persistent.contains_key(addr) {
                        assert(post.disk.content.contains_key(addr));
                        assert(post.disk.content[addr] == self.disk.content[addr]);
                    }
                    if projected_post.persistent.contains_key(addr) {
                        assert(self.disk.content.contains_key(addr));
                        assert(post.disk.content.contains_key(addr));
                        assert(post.disk.content[addr] == self.disk.content[addr]);
                    }
                }
            );
        }
        // Old active-readable preservation proof kept for reference. Read
        // completions are no longer filtered out of active branch AUs here.
        //
        // let active_addrs = mini_allocator_allocated_addrs(
        //     self.branch_caching_disk_state_i().mini_allocator,
        // );
        // let projected_active_addrs = active_addrs * addresses_in_aus(aus);
        // cache_disk_ops_end_preserves_readable_on_addrs(
        //     self.cache,
        //     post.cache,
        //     self.disk,
        //     aus,
        //     responses,
        //     projected_active_addrs,
        // );
        // assert forall |addr: Address| #[trigger] active_addrs.contains(addr) implies {
        //     &&& post.branch_caching_disk_i().readable().contains_key(addr)
        //         == self.branch_caching_disk_i().readable().contains_key(addr)
        //     &&& post.branch_caching_disk_i().readable().contains_key(addr) ==>
        //         post.branch_caching_disk_i().readable()[addr]
        //             == self.branch_caching_disk_i().readable()[addr]
        // } by {
        //     if projected_active_addrs.contains(addr) {
        //         assert(addresses_in_aus(aus).contains(addr));
        //     } else {
        //         assert(!addresses_in_aus(aus).contains(addr));
        //         assert(!self.branch_caching_disk_i().readable().contains_key(addr)) by {
        //             if self.branch_caching_disk_i().readable().contains_key(addr) {
        //                 if self.branch_caching_disk_i().cache.contains_key(addr) {
        //                     assert(project_cache_pages(self.cache, aus).contains_key(addr));
        //                     assert(addresses_in_aus(aus).contains(addr));
        //                 } else {
        //                     assert(self.branch_caching_disk_i().persistent.contains_key(addr));
        //                     assert(self.disk.content.restrict(addresses_in_aus(aus)).contains_key(addr));
        //                     assert(addresses_in_aus(aus).contains(addr));
        //                 }
        //             }
        //         }
        //         assert(!post.branch_caching_disk_i().readable().contains_key(addr)) by {
        //             if post.branch_caching_disk_i().readable().contains_key(addr) {
        //                 if post.branch_caching_disk_i().cache.contains_key(addr) {
        //                     assert(project_cache_pages(post.cache, aus).contains_key(addr));
        //                     assert(addresses_in_aus(aus).contains(addr));
        //                 } else {
        //                     assert(post.branch_caching_disk_i().persistent.contains_key(addr));
        //                     assert(projected_post.persistent.contains_key(addr));
        //                     assert(self.disk.content.restrict(addresses_in_aus(aus)).contains_key(addr));
        //                     assert(addresses_in_aus(aus).contains(addr));
        //                 }
        //             }
        //         }
        //     }
        // }
        // active_loaded_nodes_preserved_by_readable_agreement(
        //     self.branch_caching_disk_state_i().disk,
        //     post.branch_caching_disk_i(),
        //     self.branch_caching_disk_state_i().mini_allocator,
        // );
        assert(CachingDisk::State::next(
            self.branch_caching_disk_i(),
            post.branch_caching_disk_i(),
            CachingDisk::Label::Internal{},
        ));
        assert(CachingDiskBranch::State::disk_internal(
            self.branch_caching_disk_state_i(),
            post.branch_caching_disk_state_i(),
            CachingDiskBranch::Label::Internal,
            post.branch_caching_disk_i(),
        )) by {
            reveal(CachingDiskBranch::State::disk_internal);
        }
        assert(CachingDiskBranch::State::next_by(
            self.branch_caching_disk_state_i(),
            post.branch_caching_disk_state_i(),
            CachingDiskBranch::Label::Internal,
            CachingDiskBranch::Step::disk_internal(post.branch_caching_disk_i()),
        )) by {
            reveal(CachingDiskBranch::State::next_by);
        }
        reveal(CachingDiskBranch::State::next);
        assert(CrashAwareCachingDiskBranch::State::internal(
            self.i(),
            post.i(),
            CrashAwareCachingDiskBranch::Label::Internal,
            post.branch_caching_disk_state_i(),
        )) by {
            reveal(CrashAwareCachingDiskBranch::State::internal);
        }
        assert(CrashAwareCachingDiskBranch::State::next_by(
            self.i(),
            post.i(),
            CrashAwareCachingDiskBranch::Label::Internal,
            CrashAwareCachingDiskBranch::Step::internal(post.branch_caching_disk_state_i()),
        )) by {
            reveal(CrashAwareCachingDiskBranch::State::next_by);
        }
        reveal(CrashAwareCachingDiskBranch::State::next);
        CachingDisk::State::inv_next(
            self.branch_caching_disk_i(),
            post.branch_caching_disk_i(),
            CachingDisk::Label::Internal{},
        );
        assert(post.inv()) by {
            assert(post.branch.wf());
            assert(async_disk_superblock_page_wf(post.disk.content));
            assert(post.persistent_superblock_image_i() == self.persistent_superblock_image_i());
            assert(post.persistent_superblock_image_i().wf());
            assert(post.cache.inv()) by {
                Cache::State::inv_next(
                    self.cache,
                    post.cache,
                    Cache::Label::DiskOps{requests: Set::empty(), responses},
                );
            }
            assert(post.branch_caching_disk_i().inv());
        }
        self.i().next_refines(post.i(), CrashAwareCachingDiskBranch::Label::Internal);
        assert(post.semantic_inv());
        assert(inv(post));
    }
}

pub open spec fn unified_cache_branch_i(
    src: UnifiedCacheBranchSource,
) -> CrashAwareCachingDiskBranch::State
{
    src.i()
}

pub open spec fn inv(src: UnifiedCacheBranchSource) -> bool
{
    &&& src.inv()
    &&& src.semantic_inv()
}

proof fn atomic_branch_metadata_loaded_equiv_root_aus(
    branch: AtomicBranchState::State,
)
    ensures
        branch.metadata_loaded()
            == (root_aus_up_to(branch.image.sealed_roots, branch.image.sealed_roots.len() as nat)
                <= branch.branch_summary.dom()),
{
    let root_aus = root_aus_up_to(branch.image.sealed_roots, branch.image.sealed_roots.len() as nat);
    assert(branch.metadata_loaded() ==> root_aus <= branch.branch_summary.dom());
    assert(root_aus <= branch.branch_summary.dom() ==> branch.metadata_loaded());
}

pub open spec fn init_shared_facts(src: UnifiedCacheBranchSource) -> bool
{
    &&& async_disk_superblock_page_wf(src.disk.content)
    &&& src.persistent_superblock_image_i() == empty_abstract_superblock_image()
    &&& src.cache.inv()
    &&& src.disk.inv()
}

pub proof fn init_refines(pre: SystemModel::State<UnifiedCacheProgramModel>)
    requires
        SystemModel::State::initialize(pre, pre.program, pre.disk),
        init_shared_facts(unified_cache_branch_source(pre)),
    ensures
        CrashAwareCachingDiskBranch::State::init(
            unified_cache_branch_i(unified_cache_branch_source(pre)),
        ),
        inv(unified_cache_branch_source(pre)),
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
            }

            let src = unified_cache_branch_source(pre);
            let dst = unified_cache_branch_i(src);

            assert(src.persistent_superblock_image_i() == empty_abstract_superblock_image());
            assert(src.branch == AtomicBranchState::State::empty());
            assert(src.branch == pre.program.state.branch);
            assert(src.branch.image.sealed_roots == Seq::<Address>::empty());
            assert(src.branch.persistent_image.sealed_roots == Seq::<Address>::empty());
            assert(src.branch.image.sealed_roots.take(0) == Seq::<Address>::empty());
            assert(src.branch.wf());
            assert(!src.superblock_loaded());
            assert(src.in_flight is None);
            assert(src.in_flight_image is None);
            assert(src.cache.inv());
            assert(src.disk.inv());

            assert(UnifiedCacheBranchSource::branch_image_projection_addrs_i(
                src.disk.content,
                src.persistent_superblock_image_i().branch_roots,
            ) =~= Set::<Address>::empty()) by {
                let roots = src.persistent_superblock_image_i().branch_roots;
                assert(roots == Seq::<Address>::empty());
                assert(branch_summary_reads_valid(roots, to_branch_nodes(src.disk.content))) by {
                    assert forall |i: int| #![auto]
                        0 <= i < roots.len()
                        implies crate::implementation::CachedBranch_v::root_summary_read_valid(
                            roots[i],
                            to_branch_nodes(src.disk.content),
                        ) by {
                        assert(false);
                    }
                }
                assert(completed_branch_summary_from_reads(
                    roots,
                    to_branch_nodes(src.disk.content),
                ) == Map::<AU, Summary>::empty());
                assert(UnifiedCacheBranchSource::branch_image_summary_i(
                    src.disk.content,
                    roots,
                ) == Map::<AU, Summary>::empty());
                assert(UnifiedCacheBranchSource::branch_image_summary_aus_i(
                    src.disk.content,
                    roots,
                ) =~= Set::<AU>::empty()) by {
                    lemma_values_finite(Map::<AU, Summary>::empty());
                    assert forall |au: AU| #[trigger] UnifiedCacheBranchSource::branch_image_summary_aus_i(
                        src.disk.content,
                        roots,
                    ).contains(au) implies false by {
                        let s = lemma_union_set_of_sets_contains(
                            Map::<AU, Summary>::empty().values(),
                            au,
                        );
                        assert(Map::<AU, Summary>::empty().values().contains(s));
                        assert(false);
                    }
                }
                assert forall |addr: Address| #[trigger] UnifiedCacheBranchSource::branch_image_projection_addrs_i(
                    src.disk.content,
                    roots,
                ).contains(addr) implies false by {
                    assert(addresses_in_aus(Set::<AU>::empty()).contains(addr));
                }
            }
            let init_branch_addrs = UnifiedCacheBranchSource::branch_image_projection_addrs_i(
                src.disk.content,
                src.persistent_superblock_image_i().branch_roots,
            );
            assert(src.branch.branch_summary == Map::<AU, crate::allocation_layer::AllocationBranch_v::Summary>::empty());
            assert(summary_aus(src.branch.branch_summary) =~= Set::<AU>::empty()) by {
                lemma_values_finite(src.branch.branch_summary);
                assert forall |au: AU| #[trigger] summary_aus(src.branch.branch_summary).contains(au)
                    implies false by {
                    let s = lemma_union_set_of_sets_contains(
                        src.branch.branch_summary.values(),
                        au,
                    );
                    assert(src.branch.branch_summary.values().contains(s));
                    assert(false);
                }
            };
            assert(src.branch.mini_allocator.all_aus() =~= Set::<AU>::empty());
            assert(src.branch.owned_aus() =~= Set::<AU>::empty());
            assert(src.branch.metadata_loaded());
            assert(src.branch_projection_aus() =~= Set::<AU>::empty()) by {
                assert(init_branch_addrs =~= Set::<Address>::empty());
                assert forall |au: AU| #[trigger] src.branch_projection_aus().contains(au)
                    implies false by {
                    assert(src.branch_projection_aus() == src.branch.owned_aus());
                    assert(src.branch.owned_aus().contains(au));
                    assert(false);
                }
            }
            assert(src.branch_caching_disk_i().cache == Map::<Address, RawPage>::empty()) by {
                assert_maps_equal!(
                    src.branch_caching_disk_i().cache,
                    Map::<Address, RawPage>::empty(),
                    addr => {
                        assert(!crate::implementation::CachingDisk_v::addresses_in_aus(
                            src.branch_projection_aus(),
                        ).contains(addr));
                    }
                );
            }
            assert(src.branch_caching_disk_i().persistent == Map::<Address, RawPage>::empty()) by {
                assert_maps_equal!(
                    src.branch_caching_disk_i().persistent,
                    Map::<Address, RawPage>::empty(),
                    addr => {
                        assert(!crate::implementation::CachingDisk_v::addresses_in_aus(
                            src.branch_projection_aus(),
                        ).contains(addr));
                    }
                );
            }
            assert(src.branch_caching_disk_i().status == Map::<Address, crate::implementation::CachingDisk_v::PageStatus>::empty()) by {
                assert_maps_equal!(
                    src.branch_caching_disk_i().status,
                    Map::<Address, crate::implementation::CachingDisk_v::PageStatus>::empty(),
                    addr => {
                        assert(!crate::implementation::CachingDisk_v::addresses_in_aus(
                            src.branch_projection_aus(),
                        ).contains(addr));
                    }
                );
            }
            src.branch_caching_disk_i().empty_status_clean_pages_agree();
            assert(src.branch_caching_disk_i().inv());

            assert(src.persistent_branch_image_i() == empty_caching_disk_branch_image()) by {
                assert(src.persistent_branch_image_i().persistent == Map::<Address, RawPage>::empty());
                assert(src.persistent_branch_image_i().sealed_roots == Seq::<Address>::empty());
                assert(src.persistent_branch_image_i().seq_end == 0);
            }

            assert(dst.persistent == PersistentCachingDiskBranch::Image{
                image: empty_caching_disk_branch_image(),
            });
            assert(dst.ephemeral is Unknown);
            assert(dst.frozen is None);
            assert(dst.prepared == false);
            assert(CrashAwareCachingDiskBranch::State::initialize(dst)) by {
                reveal(CrashAwareCachingDiskBranch::State::initialize);
            }
            assert(CrashAwareCachingDiskBranch::State::init(dst)) by {
                reveal(CrashAwareCachingDiskBranch::State::init);
                reveal(CrashAwareCachingDiskBranch::State::init_by);
                assert(CrashAwareCachingDiskBranch::State::init_by(
                    dst,
                    CrashAwareCachingDiskBranch::Config::initialize(),
                ));
            }
            dst.init_refines();
            assert(dst.inv());
            assert(dst.i().inv()) by {
                assert(CrashAwareAllocationBranchStack::State::initialize(dst.i()));
                reveal(CrashAwareAllocationBranchStack::State::initialize);
                assert(dst.i().persistent == empty_sealed_stack());
                assert(dst.i().persistent_branch_summary == Map::<AU, crate::allocation_layer::AllocationBranch_v::Summary>::empty());
                assert(dst.i().ephemeral is Unknown);
                assert(dst.i().frozen is None);
                assert(dst.i().persistent.sealed_roots.to_set() =~= Set::<Address>::empty());
                assert(to_aus(dst.i().persistent.sealed_roots.to_set()) =~= Set::<AU>::empty()) by {
                    assert forall |au: AU| #[trigger] to_aus(dst.i().persistent.sealed_roots.to_set()).contains(au)
                        implies false by {
                        let addr = choose |addr: Address| #[trigger] dst.i().persistent.sealed_roots.to_set().contains(addr)
                            && addr.au == au;
                        assert(false);
                    }
                }
                assert(dst.i().persistent_branch_summary.dom() =~= Set::<AU>::empty());
                assert(dst.i().persistent_branch_summary.dom()
                    =~= to_aus(dst.i().persistent.sealed_roots.to_set()));
                assert(dst.i().persistent.wf(dst.i().persistent_branch_summary));
                assert(dst.i().wf());
                assert(dst.i().stack_compatible());
            };
            dst.i_inv_implies_semantic_inv();
            assert(src.semantic_inv());
            assert(src.inv());
            assert(inv(src));
        },
        UnifiedCacheSystem::Config::dummy_to_use_type_params(_) => {
            assert(false);
        },
    }
}

pub proof fn load_ephemeral_refines(
    pre: UnifiedCacheBranchSource,
    post: UnifiedCacheBranchSource,
    image: AbstractSuperblockImage,
)
    requires
        inv(pre),
        !pre.superblock_loaded(),
        pre.persistent_superblock_image_i() == image,
        post.persistent_image == Option::Some(image),
        post.cache == pre.cache,
        post.disk.content == pre.disk.content,
        post.disk.inv(),
        post.in_flight is None,
        post.in_flight_image is None,
        AtomicBranchState::State::initialize(
            post.branch,
            AtomicBranchImage{
                sealed_roots: image.branch_roots,
                seq_end: image.branch_seq_end,
            },
            image.branch_roots.len() as nat,
        ),
        pre.branch_caching_disk_i().cache == Map::<Address, RawPage>::empty(),
        pre.branch_caching_disk_i().status == Map::<Address, PageStatus>::empty(),
        pre.persistent_branch_image_i().loadable(),
        pre.persistent_branch_image_i().stack_wf(),
        project_cache_pages(
            post.cache,
            UnifiedCacheBranchSource::branch_image_summary_aus_i(
                post.disk.content,
                image.branch_roots,
            ),
        ) == Map::<Address, RawPage>::empty(),
        project_cache_status(
            post.cache,
            UnifiedCacheBranchSource::branch_image_summary_aus_i(
                post.disk.content,
                image.branch_roots,
            ),
        ) == Map::<Address, PageStatus>::empty(),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            unified_cache_branch_i(pre),
            unified_cache_branch_i(post),
            CrashAwareCachingDiskBranch::Label::LoadEphemeral,
        ),
        inv(post),
{
    reveal(AtomicBranchState::State::initialize);

    assert(pre.branch == AtomicBranchState::State::empty());
    assert(pre.in_flight is None);
    assert(pre.in_flight_image is None);
    assert(post.superblock_loaded());
    assert(post.persistent_superblock_image_i() == image);
    assert(post.persistent_superblock_image_i().wf());
    assert(image.branch_roots.take(image.branch_roots.len() as int) == image.branch_roots);
    assert(post.branch.wf());
    assert(post.cache.inv());

    let image_aus = UnifiedCacheBranchSource::branch_image_summary_aus_i(
        post.disk.content,
        image.branch_roots,
    );
    addresses_in_aus_to_aus_addresses_in_aus(image_aus);
    assert(addresses_in_aus(post.branch_projection_aus())
        =~= UnifiedCacheBranchSource::branch_image_projection_addrs_i(
            post.disk.content,
            image.branch_roots,
        )) by {
        if post.branch.metadata_loaded() {
            if image.branch_roots.len() > 0 {
                assert(0 <= 0 < image.branch_roots.len());
                assert(post.branch.image.sealed_roots == image.branch_roots);
                root_aus_up_to_contains(
                    post.branch.image.sealed_roots,
                    post.branch.image.sealed_roots.len() as nat,
                    0,
                );
                assert(root_aus_up_to(
                    post.branch.image.sealed_roots,
                    post.branch.image.sealed_roots.len() as nat,
                ).contains(image.branch_roots[0].au));
                assert(post.branch.branch_summary.contains_key(image.branch_roots[0].au));
                assert(false);
            }
            assert(image.branch_roots == Seq::<Address>::empty());
            assert(post.branch.branch_summary == Map::<AU, Summary>::empty());
            assert(summary_aus(post.branch.branch_summary) =~= Set::<AU>::empty()) by {
                lemma_values_finite(post.branch.branch_summary);
                assert forall |au: AU| #[trigger] summary_aus(post.branch.branch_summary).contains(au)
                    implies false by {
                    let s = lemma_union_set_of_sets_contains(
                        post.branch.branch_summary.values(),
                        au,
                    );
                    assert(post.branch.branch_summary.values().contains(s));
                    assert(false);
                }
            }
            assert(post.branch.mini_allocator.all_aus() =~= Set::<AU>::empty());
            assert(post.branch.owned_aus() =~= Set::<AU>::empty());
            assert(image_aus =~= Set::<AU>::empty()) by {
                assert forall |au: AU| #[trigger] image_aus.contains(au)
                    implies false by {
                    let i = choose |i: int| {
                        &&& 0 <= i < image.branch_roots.len()
                        &&& crate::implementation::CachedBranch_v::root_summary_read_valid(
                            image.branch_roots[i],
                            to_branch_nodes(post.disk.content),
                        )
                        &&& #[trigger] crate::implementation::CachedBranch_v::root_summary_from_read(
                            image.branch_roots[i],
                            to_branch_nodes(post.disk.content),
                        ).contains(au)
                    };
                    assert(false);
                }
            }
            assert(addresses_in_aus(post.branch_projection_aus()) =~= Set::<Address>::empty());
            assert(UnifiedCacheBranchSource::branch_image_projection_addrs_i(
                post.disk.content,
                image.branch_roots,
            ) =~= Set::<Address>::empty());
        } else {
            assert(post.branch_projection_aus() == to_aus(
                UnifiedCacheBranchSource::branch_image_projection_addrs_i(
                    post.disk.content,
                    image.branch_roots,
                ),
            ));
            assert(UnifiedCacheBranchSource::branch_image_projection_addrs_i(
                post.disk.content,
                image.branch_roots,
            ) == addresses_in_aus(image_aus));
        }
    }
    assert(post.branch_caching_disk_i().cache == Map::<Address, RawPage>::empty()) by {
        assert_maps_equal!(
            post.branch_caching_disk_i().cache,
            Map::<Address, RawPage>::empty(),
            addr => {
                if post.branch_caching_disk_i().cache.contains_key(addr) {
                    assert(addresses_in_aus(post.branch_projection_aus()).contains(addr));
                    assert(UnifiedCacheBranchSource::branch_image_projection_addrs_i(
                        post.disk.content,
                        image.branch_roots,
                    ).contains(addr));
                    assert(addresses_in_aus(image_aus).contains(addr));
                    assert(project_cache_pages(post.cache, image_aus).contains_key(addr));
                    assert(false);
                }
            }
        );
    }
    assert(post.branch_caching_disk_i().status == Map::<Address, PageStatus>::empty()) by {
        assert_maps_equal!(
            post.branch_caching_disk_i().status,
            Map::<Address, PageStatus>::empty(),
            addr => {
                if post.branch_caching_disk_i().status.contains_key(addr) {
                    assert(addresses_in_aus(post.branch_projection_aus()).contains(addr));
                    assert(UnifiedCacheBranchSource::branch_image_projection_addrs_i(
                        post.disk.content,
                        image.branch_roots,
                    ).contains(addr));
                    assert(addresses_in_aus(image_aus).contains(addr));
                    assert(project_cache_status(post.cache, image_aus).contains_key(addr));
                    assert(false);
                }
            }
        );
    }

    assert(post.persistent_branch_image_i() == pre.persistent_branch_image_i()) by {
        assert(UnifiedCacheBranchSource::branch_image_projection_addrs_i(
            post.disk.content,
            image.branch_roots,
        ) =~= UnifiedCacheBranchSource::branch_image_projection_addrs_i(
            pre.disk.content,
            image.branch_roots,
        )) by {
            assert(post.disk.content == pre.disk.content);
        }
        assert_maps_equal!(
            post.persistent_branch_image_i().persistent,
            pre.persistent_branch_image_i().persistent,
            addr => {
                if post.persistent_branch_image_i().persistent.contains_key(addr) {
                    assert(pre.persistent_branch_image_i().persistent.contains_key(addr));
                }
                if pre.persistent_branch_image_i().persistent.contains_key(addr) {
                    assert(post.persistent_branch_image_i().persistent.contains_key(addr));
                }
            }
        );
    }
    let persistent_image = pre.persistent_branch_image_i();
    assert(post.persistent_branch_image_i() == persistent_image);
    assert(pre.persistent_branch_i() == PersistentCachingDiskBranch::Image{
        image: persistent_image,
    });
    assert(post.persistent_branch_i() == PersistentCachingDiskBranch::Metadata{
        meta: persistent_image.metadata(),
    });

    assert(post.branch_caching_disk_i().persistent == persistent_image.persistent) by {
        assert_maps_equal!(
            post.branch_caching_disk_i().persistent,
            persistent_image.persistent,
            addr => {
                if post.branch_caching_disk_i().persistent.contains_key(addr) {
                    assert(persistent_image.persistent.contains_key(addr));
                }
                if persistent_image.persistent.contains_key(addr) {
                    assert(post.branch_caching_disk_i().persistent.contains_key(addr));
                }
            }
        );
    }
    assert(post.branch_caching_disk_i()
        == CachingDiskBranch::State::disk_from_persistent(persistent_image.persistent));
    CachingDisk::State::persistent_only_inv(persistent_image.persistent);
    assert(CachingDiskBranch::State::disk_from_persistent(persistent_image.persistent).inv()) by {
        assert(post.branch_caching_disk_i().inv());
    }

    let src = unified_cache_branch_i(pre);
    let dst = unified_cache_branch_i(post);
    assert(src.refinement_inv());
    assert(src.semantic_inv());
    assert(src.persistent_image_i() == persistent_image);
    assert(src.persistent == PersistentCachingDiskBranch::Image{image: persistent_image});
    assert(src.ephemeral is Unknown);
    assert(persistent_image.stack_wf());
    assert(persistent_image.loadable());
    assert(CachingDiskBranch::State::can_load_from_persistent(persistent_image));
    assert(post.branch_caching_disk_state_i().metadata_loaded
        == CachingDiskBranch::State::load_from_persistent(persistent_image).metadata_loaded) by {
        assert(post.branch_caching_disk_state_i().metadata_loaded == post.branch.metadata_loaded());
        assert(post.branch.image.sealed_roots == image.branch_roots);
        assert(persistent_image.sealed_roots == image.branch_roots);
        assert(post.branch.branch_summary == Map::<AU, Summary>::empty());
        if image.branch_roots.len() == 0 {
            assert(root_aus_up_to(
                post.branch.image.sealed_roots,
                post.branch.image.sealed_roots.len() as nat,
            ) =~= Set::<AU>::empty());
            assert(post.branch.metadata_loaded());
        } else {
            assert(!post.branch.metadata_loaded()) by {
                if post.branch.metadata_loaded() {
                    root_aus_up_to_contains(
                        post.branch.image.sealed_roots,
                        post.branch.image.sealed_roots.len() as nat,
                        0,
                    );
                    assert(root_aus_up_to(
                        post.branch.image.sealed_roots,
                        post.branch.image.sealed_roots.len() as nat,
                    ).contains(image.branch_roots[0].au));
                    assert(post.branch.branch_summary.contains_key(image.branch_roots[0].au));
                    assert(false);
                }
            }
        }
    }
    assert(post.branch_caching_disk_state_i()
        == CachingDiskBranch::State::load_from_persistent(persistent_image));

    assert(src.ephemeral is Unknown);
    assert(src.persistent == PersistentCachingDiskBranch::Image{image: persistent_image});
    assert(dst.ephemeral == EphemeralCachingDiskBranch::Known{
        v: CachingDiskBranch::State::load_from_persistent(persistent_image),
    });
    assert(dst.persistent == PersistentCachingDiskBranch::Metadata{
        meta: persistent_image.metadata(),
    });
    assert(CachingDiskBranch::State::initialize(
        post.branch_caching_disk_state_i(),
        persistent_image,
    )) by {
        reveal(CachingDiskBranch::State::initialize);
    }
    assert(CrashAwareCachingDiskBranch::State::load_ephemeral(
        src,
        dst,
        CrashAwareCachingDiskBranch::Label::LoadEphemeral,
        post.branch_caching_disk_state_i(),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::load_ephemeral);
    }
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        CrashAwareCachingDiskBranch::Label::LoadEphemeral,
        CrashAwareCachingDiskBranch::Step::load_ephemeral(
            post.branch_caching_disk_state_i(),
        ),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);
    src.next_refines(dst, CrashAwareCachingDiskBranch::Label::LoadEphemeral);
    assert(post.semantic_inv());
    assert(post.inv());
    assert(inv(post));
}

pub proof fn query_from_receipts_up_to_equiv(
    receipts: Seq<LoadedPathReceipt>,
    end: nat,
)
    requires
        end <= receipts.len(),
    ensures
        crate::implementation::AtomicBranchState_v::query_from_receipts_up_to(receipts, end)
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
        crate::implementation::AtomicBranchState_v::query_receipts_valid(
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

pub proof fn query_receipts_read_addrs_member_has_receipt(
    receipts: Seq<LoadedPathReceipt>,
    end: nat,
    addr: Address,
)
    requires
        end <= receipts.len(),
        query_receipts_read_addrs(receipts, end).contains(addr),
    ensures
        exists |i: int| #![auto] {
            &&& 0 <= i < end
            &&& receipts[i].needed_addrs().contains(addr)
        },
    decreases end
{
    if end == 0 {
        assert(false);
    } else {
        let idx = (end - 1) as int;
        if receipts[idx].needed_addrs().contains(addr) {
        } else {
            assert(query_receipts_read_addrs(receipts, (end - 1) as nat).contains(addr));
            query_receipts_read_addrs_member_has_receipt(
                receipts,
                (end - 1) as nat,
                addr,
            );
        }
    }
}

proof fn linked_child_inv_internal_from_parent(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    child_idx: int,
)
    requires
        branch.inv_internal(ranking),
        branch.root().valid_child_index(child_idx),
    ensures
        branch.child_at_idx(child_idx).inv_internal(ranking),
{
    assert(branch.child_at_idx(child_idx).valid_ranking(ranking)) by {
        assert(branch.disk_view.valid_ranking(ranking));
        assert(ranking.contains_key(branch.root));
        assert(branch.disk_view.node_children_respects_rank(ranking, branch.root));
        assert(ranking.contains_key(branch.root()->children[child_idx]));
    };
    assert(branch.child_at_idx(child_idx).keys_strictly_sorted_internal(ranking));
    assert(branch.child_at_idx(child_idx).all_keys_in_range_internal(ranking));
}

proof fn receipt_needed_addr_in_linked_branch_internal(
    src: UnifiedCacheBranchSource,
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    reads: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    addr: Address,
)
    requires
        inv(src),
        src.superblock_loaded(),
        branch.inv_internal(ranking),
        receipt.valid_for(branch.root, to_branch_nodes(reads)),
        receipt.needed_addrs().contains(addr),
        forall |branch_addr: Address|
            #[trigger] branch.reachable_addrs_using_ranking(ranking).contains(branch_addr)
            ==> addresses_in_aus(src.branch_projection_aus()).contains(branch_addr),
        forall |branch_addr: Address|
            #[trigger] branch.disk_view.entries.contains_key(branch_addr)
                && reads.contains_key(branch_addr)
            ==> branch.disk_view.entries[branch_addr] == to_branch_nodes(reads)[branch_addr],
        forall |read_addr: Address| #[trigger] reads.contains_key(read_addr)
            ==> src.cache.valid_read(read_addr, reads[read_addr]),
    ensures
        branch.reachable_addrs_using_ranking(ranking).contains(addr),
    decreases receipt.depth(),
{
    let read_nodes = to_branch_nodes(reads);
    assert(receipt.root == branch.root);
    assert(read_nodes.contains_key(branch.root));
    assert(branch.disk_view.entries.contains_key(branch.root));
    assert(reads.contains_key(branch.root));
    assert(branch.reachable_addrs_using_ranking(ranking).contains(branch.root)) by {
        if branch.root() is Leaf {
            assert(branch.reachable_addrs_using_ranking(ranking) == set!{branch.root});
        } else {
            assert(branch.reachable_addrs_using_ranking(ranking).contains(branch.root));
        }
    }
    projected_read_node_matches_branch_entry(src, reads, branch, branch.root);
    assert(read_nodes[branch.root] == branch.disk_view.entries[branch.root]);
    assert(read_nodes[branch.root] == receipt.lines[0].node);
    assert(branch.root() == receipt.lines[0].node);

    if addr == branch.root {
        if branch.root() is Index {
            assert(branch.reachable_addrs_using_ranking(ranking).contains(addr));
        } else {
            assert(branch.reachable_addrs_using_ranking(ranking) == set!{branch.root});
        }
    } else {
        assert(receipt.lines.len() > 1) by {
            if receipt.lines.len() <= 1 {
                let i = choose |i: int| #![auto] 0 <= i < receipt.lines.len()
                    && receipt.lines[i].addr == addr;
                assert(i == 0);
                assert(receipt.lines[0].addr == branch.root);
                assert(false);
            }
        }
        assert(receipt.depth() > 0);
        assert(receipt.lines[0].node is Index);
        assert(branch.root() is Index);
        let child_idx = branch.root().route(receipt.key) + 1;
        LinkedBranchRefinement::lemma_route_ensures(branch.root(), receipt.key);
        assert(branch.root().valid_child_index(child_idx));
        let child_branch = branch.child_at_idx(child_idx);
        let child_receipt = receipt.tail();
        receipt_valid_implies_tail_valid(receipt, read_nodes);
        assert(child_branch.root == child_receipt.root) by {
            assert(receipt.lines[0].node->children[child_idx] == receipt.lines[1].addr);
            assert(branch.root()->children[child_idx] == receipt.lines[1].addr);
            assert(child_branch.root == branch.root()->children[child_idx]);
            assert(child_receipt.root == receipt.lines[1].addr);
        }
        assert(child_receipt.needed_addrs().contains(addr)) by {
            let i = choose |i: int| #![auto] 0 <= i < receipt.lines.len()
                && receipt.lines[i].addr == addr;
            assert(i != 0);
            assert(child_receipt.lines[i - 1] == receipt.lines[i]);
        }
        linked_child_inv_internal_from_parent(branch, ranking, child_idx);
        assert forall |branch_addr: Address|
            #[trigger] child_branch.reachable_addrs_using_ranking(ranking).contains(branch_addr)
            implies addresses_in_aus(src.branch_projection_aus()).contains(branch_addr)
        by {
            let child_sets = branch.children_reachable_addrs_using_ranking(ranking);
            assert(child_sets[child_idx] == child_branch.reachable_addrs_using_ranking(ranking));
            lemma_set_subset_of_union_seq_of_sets(child_sets, branch_addr);
            assert(branch.reachable_addrs_using_ranking(ranking).contains(branch_addr));
        }
        assert forall |branch_addr: Address|
            #[trigger] child_branch.disk_view.entries.contains_key(branch_addr)
                && reads.contains_key(branch_addr)
            implies child_branch.disk_view.entries[branch_addr]
                == to_branch_nodes(reads)[branch_addr]
        by {
            assert(child_branch.disk_view == branch.disk_view);
        }
        receipt_needed_addr_in_linked_branch_internal(
            src,
            child_branch,
            ranking,
            reads,
            child_receipt,
            addr,
        );
        let child_sets = branch.children_reachable_addrs_using_ranking(ranking);
        assert(child_sets[child_idx] == child_branch.reachable_addrs_using_ranking(ranking));
        lemma_set_subset_of_union_seq_of_sets(child_sets, addr);
        assert(branch.reachable_addrs_using_ranking(ranking).contains(addr));
    }
}

proof fn projected_read_node_matches_branch_entry(
    src: UnifiedCacheBranchSource,
    reads: Map<Address, RawPage>,
    branch: LinkedBranch<Summary>,
    addr: Address,
)
    requires
        inv(src),
        branch.disk_view.entries.contains_key(addr),
        addresses_in_aus(src.branch_projection_aus()).contains(addr),
        reads.contains_key(addr),
        src.cache.valid_read(addr, reads[addr]),
        forall |branch_addr: Address|
            #[trigger] branch.disk_view.entries.contains_key(branch_addr)
                && reads.contains_key(branch_addr)
            // Old live-read view:
            // ==> branch.disk_view.entries[branch_addr]
            //     == to_branch_nodes(src.branch_caching_disk_i().visible())[branch_addr],
            // ==> branch.disk_view.entries[branch_addr]
            //     == to_branch_nodes(src.branch_caching_disk_i().readable())[branch_addr],
            ==> branch.disk_view.entries[branch_addr] == to_branch_nodes(reads)[branch_addr],
    ensures
        to_branch_nodes(reads)[addr] == branch.disk_view.entries[addr],
{
    let cdb = src.branch_caching_disk_i();
    src.cache.build_lookup_map_ensures();
    assert(cache_filled_addr(src.cache, addr));
    assert(cache_filled_page(src.cache, addr) == reads[addr]);
    assert(project_cache_pages(src.cache, src.branch_projection_aus()).contains_key(addr));
    assert(project_cache_pages(src.cache, src.branch_projection_aus())[addr] == reads[addr]);
    assert(cdb.cache.contains_key(addr));
    assert(cdb.cache[addr] == reads[addr]);
    assert(cdb.readable().contains_key(addr));
    assert(cdb.readable()[addr] == reads[addr]);
    assert(to_branch_nodes(cdb.readable()).contains_key(addr));
    assert(to_branch_nodes(reads).contains_key(addr));
	    assert(to_branch_nodes(reads)[addr] == to_branch_nodes(cdb.readable())[addr]);
    assert(branch.disk_view.entries[addr] == to_branch_nodes(reads)[addr]);
	}

proof fn projected_read_node_matches_visible_branch_entry(
    src: UnifiedCacheBranchSource,
    reads: Map<Address, RawPage>,
    branch: LinkedBranch<Summary>,
    addr: Address,
)
    requires
        inv(src),
        src.superblock_loaded(),
        branch.disk_view.entries.contains_key(addr),
        branch.disk_view.entries <= src.branch_caching_disk_state_i().visible_branch_nodes(),
        addresses_in_aus(src.branch_projection_aus()).contains(addr),
        reads.contains_key(addr),
        src.cache.valid_read(addr, reads[addr]),
    ensures
        to_branch_nodes(reads)[addr] == branch.disk_view.entries[addr],
{
    let cdb = src.branch_caching_disk_state_i();
    src.cache.build_lookup_map_ensures();
    assert(cache_filled_addr(src.cache, addr));
    assert(cache_filled_page(src.cache, addr) == reads[addr]);
    assert(project_cache_pages(src.cache, src.branch_projection_aus()).contains_key(addr));
    assert(project_cache_pages(src.cache, src.branch_projection_aus())[addr] == reads[addr]);
    assert(cdb.disk.cache.contains_key(addr));
    assert(cdb.disk.cache[addr] == reads[addr]);
    assert(cdb.disk.status.contains_key(addr));
    assert(cdb.visible_branch_nodes().contains_key(addr));
    assert(cdb.disk.visible().contains_key(addr));
    if cdb.disk.status[addr] == PageStatus::Clean {
        assert(!cdb.disk.visible_cache().contains_key(addr));
        assert(cdb.disk.persistent.contains_key(addr));
        cdb.disk.clean_page_agrees(addr);
        assert(cdb.disk.persistent[addr] == cdb.disk.cache[addr]);
        assert(cdb.disk.visible()[addr] == cdb.disk.persistent[addr]);
    } else {
        assert(cdb.disk.visible_cache().contains_key(addr));
        assert(cdb.disk.visible()[addr] == cdb.disk.cache[addr]);
    }
    assert(cdb.disk.visible()[addr] == reads[addr]);
    assert(branch.disk_view.entries[addr] == cdb.visible_branch_nodes()[addr]);
    assert(to_branch_nodes(reads)[addr] == cdb.visible_branch_nodes()[addr]);
}

proof fn receipt_needed_addr_in_linked_branch(
    src: UnifiedCacheBranchSource,
    branch: LinkedBranch<Summary>,
    reads: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    addr: Address,
)
    requires
        inv(src),
        src.superblock_loaded(),
        branch.inv(),
        receipt.valid_for(branch.root, to_branch_nodes(reads)),
        receipt.needed_addrs().contains(addr),
        forall |branch_addr: Address|
            #[trigger] branch.representation().contains(branch_addr)
            ==> addresses_in_aus(src.branch_projection_aus()).contains(branch_addr),
        forall |branch_addr: Address|
            #[trigger] branch.disk_view.entries.contains_key(branch_addr)
                && reads.contains_key(branch_addr)
            // Old live-read view:
            // ==> branch.disk_view.entries[branch_addr]
            //     == to_branch_nodes(src.branch_caching_disk_i().visible())[branch_addr],
            // ==> branch.disk_view.entries[branch_addr]
            //     == to_branch_nodes(src.branch_caching_disk_i().readable())[branch_addr],
            ==> branch.disk_view.entries[branch_addr] == to_branch_nodes(reads)[branch_addr],
        forall |read_addr: Address| #[trigger] reads.contains_key(read_addr)
            ==> src.cache.valid_read(read_addr, reads[read_addr]),
    ensures
        branch.representation().contains(addr),
{
    let ranking = branch.the_ranking();
    assert forall |branch_addr: Address|
        #[trigger] branch.reachable_addrs_using_ranking(ranking).contains(branch_addr)
        implies addresses_in_aus(src.branch_projection_aus()).contains(branch_addr)
    by {
        assert(branch.representation() == branch.reachable_addrs_using_ranking(ranking));
    }
    receipt_needed_addr_in_linked_branch_internal(
        src,
        branch,
        ranking,
        reads,
        receipt,
        addr,
    );
}

proof fn query_receipt_needed_addr_in_branch_projection(
    src: UnifiedCacheBranchSource,
    key: Key,
    receipts: Seq<LoadedPathReceipt>,
    reads: Map<Address, RawPage>,
    receipt_idx: int,
    addr: Address,
)
    requires
        inv(src),
        src.superblock_loaded(),
        src.branch.metadata_loaded(),
        crate::implementation::AtomicBranchState_v::query_receipts_valid(
            crate::implementation::AtomicBranchState_v::query_roots(
                src.branch.image.sealed_roots,
                src.branch.active_branch,
            ),
            receipts,
            to_branch_nodes(reads),
            key,
        ),
        forall |read_addr: Address| #[trigger] reads.contains_key(read_addr)
            ==> src.cache.valid_read(read_addr, reads[read_addr]),
        0 <= receipt_idx < receipts.len(),
        receipts[receipt_idx].needed_addrs().contains(addr),
    ensures
        addresses_in_aus(src.branch_projection_aus()).contains(addr),
{
    let cdb = src.branch_caching_disk_state_i();
    let roots = crate::implementation::AtomicBranchState_v::query_roots(
        src.branch.image.sealed_roots,
        src.branch.active_branch,
    );
    let read_nodes = to_branch_nodes(reads);
    let root_idx = roots.len() as int - receipts.len() as int + receipt_idx;
    assert(cdb.inv());
    assert(cdb.metadata_loaded);
    assert(cdb.branch_metadata_loaded());
    assert(cdb.branch_summary == cdb.interpreted_branch_summary());

    assert(root_idx < roots.len());
    let receipt = receipts[receipt_idx];
    assert(receipt.valid_for(roots[root_idx], read_nodes));

    if root_idx < src.branch.image.sealed_roots.len() {
        let root = src.branch.image.sealed_roots[root_idx];
        assert(roots[root_idx] == root);
        assert(cdb.sealed_roots == src.branch.image.sealed_roots);
        assert(cdb.sealed_stack_i().wf(cdb.branch_summary));
        assert(cdb.sealed_stack_i().sealed_roots.to_set().contains(root));
        cdb.sealed_stack_i().tight_branch_facts(cdb.branch_summary, root);
        let branch = cdb.sealed_stack_i().sealed_branch_at(cdb.branch_summary, root_idx as nat);
        assert(branch.root == root);
        assert(branch.root == roots[root_idx]);
        assert(branch.valid_sealed_branch());
        assert(branch.inv());
        assert forall |branch_addr: Address|
            #[trigger] branch.representation().contains(branch_addr)
            implies addresses_in_aus(src.branch_projection_aus()).contains(branch_addr)
        by {
            assert(branch.full_repr().contains(branch_addr)) by {
                assert(branch.representation().contains(branch_addr));
            }
            assert(addrs_closed(branch.full_repr(), branch.get_summary()));
            assert(branch.get_summary().contains(branch_addr.au));
            assert(branch.get_summary() == cdb.branch_summary[root.au]);
            assert(cdb.branch_summary.values().contains(cdb.branch_summary[root.au]));
            lemma_union_set_of_sets_subset(cdb.branch_summary.values(), cdb.branch_summary[root.au]);
            assert(summary_aus(cdb.branch_summary).contains(branch_addr.au));
            assert(src.branch_projection_aus() == src.branch.owned_aus());
            assert(src.branch.owned_aus() == summary_aus(cdb.branch_summary) + cdb.mini_allocator.all_aus());
        }
        assert forall |read_addr: Address|
            #[trigger] branch.disk_view.entries.contains_key(read_addr)
                && reads.contains_key(read_addr)
            implies branch.disk_view.entries[read_addr] == read_nodes[read_addr]
        by {
            assert(branch.disk_view.entries <= cdb.sealed_stack_i().sealed_disk.entries);
            assert(cdb.sealed_stack_i().sealed_disk.entries.contains_key(read_addr));
            assert(sealed_nodes_of(cdb.disk.visible(), cdb.branch_summary).contains_key(read_addr));
            assert(src.cache.valid_read(read_addr, reads[read_addr]));
            src.cache.build_lookup_map_ensures();
            assert(cache_filled_addr(src.cache, read_addr));
            assert(cache_filled_page(src.cache, read_addr) == reads[read_addr]);
            assert(project_cache_pages(src.cache, src.branch_projection_aus()).contains_key(read_addr));
            assert(project_cache_pages(src.cache, src.branch_projection_aus())[read_addr] == reads[read_addr]);
            assert(cdb.disk.cache.contains_key(read_addr));
            assert(cdb.disk.cache[read_addr] == reads[read_addr]);
            assert(cdb.disk.readable().contains_key(read_addr));
            assert(cdb.disk.readable()[read_addr] == reads[read_addr]);
            assert(cdb.disk.status.contains_key(read_addr));
            if cdb.disk.status[read_addr] == PageStatus::Clean {
                assert(!cdb.disk.visible_cache().contains_key(read_addr));
                assert(cdb.disk.persistent.contains_key(read_addr));
                cdb.disk.clean_page_agrees(read_addr);
                assert(cdb.disk.persistent[read_addr] == cdb.disk.cache[read_addr]);
                assert(cdb.disk.visible()[read_addr] == cdb.disk.persistent[read_addr]);
            } else {
                assert(cdb.disk.visible_cache().contains_key(read_addr));
                assert(cdb.disk.visible()[read_addr] == cdb.disk.cache[read_addr]);
            }
            assert(cdb.disk.visible()[read_addr] == cdb.disk.readable()[read_addr]);
            assert(branch.disk_view.entries[read_addr] == to_branch_nodes(cdb.disk.visible())[read_addr]);
            assert(to_branch_nodes(cdb.disk.visible())[read_addr]
                == to_branch_nodes(cdb.disk.readable())[read_addr]);
            assert(read_nodes[read_addr] == to_branch_nodes(cdb.disk.readable())[read_addr]);
        }
        receipt_needed_addr_in_linked_branch(src, branch, reads, receipt, addr);
        assert(branch.full_repr().contains(addr)) by {
            assert(branch.representation().contains(addr));
        }
        assert(addrs_closed(branch.full_repr(), branch.get_summary()));
        assert(branch.get_summary().contains(addr.au));
        assert(branch.get_summary() == cdb.branch_summary[root.au]);
        assert(cdb.branch_summary.values().contains(cdb.branch_summary[root.au]));
        lemma_union_set_of_sets_subset(cdb.branch_summary.values(), cdb.branch_summary[root.au]);
        assert(summary_aus(cdb.branch_summary).contains(addr.au));
    } else {
        assert(src.branch.active_branch.root is Some);
        assert(root_idx == src.branch.image.sealed_roots.len());
        assert(cdb.active_branch_i().inv());
        assert(cdb.active_branch_i().branch is Some);
        let branch = cdb.active_branch_i().branch.unwrap();
        assert(branch.root == roots[root_idx]);
        assert(branch.inv());
        assert forall |branch_addr: Address|
            #[trigger] branch.representation().contains(branch_addr)
            implies addresses_in_aus(src.branch_projection_aus()).contains(branch_addr)
        by {
            assert(branch.disk_view.entries.contains_key(branch_addr)) by {
                assert(branch.tight_disk_view());
                assert(branch.representation() == branch.disk_view.entries.dom());
            }
            assert(cdb.active_branch_i().addrs_closed_under_mini_allocator());
            assert(cdb.active_branch_i().mini_allocator.page_is_reserved(branch_addr));
            assert(cdb.active_branch_i().mini_allocator == cdb.mini_allocator);
            assert(cdb.mini_allocator.page_is_reserved(branch_addr));
            assert(cdb.mini_allocator.all_aus().contains(branch_addr.au));
            assert(src.branch_projection_aus() == src.branch.owned_aus());
            assert(src.branch.owned_aus() == summary_aus(cdb.branch_summary) + cdb.mini_allocator.all_aus());
        }
        active_branch_i_visible_candidate(cdb.active_branch, cdb.mini_allocator, cdb.disk);
        assert(semantic_active_branch_candidate(
            cdb.active_branch.root.unwrap(),
            cdb.visible_branch_nodes(),
            cdb.mini_allocator,
            branch,
        ));
        assert(branch.disk_view.entries <= cdb.visible_branch_nodes());
        // Old loaded-node equality:
        // assert(branch.disk_view.entries == active_loaded_nodes_of(cdb.disk, cdb.mini_allocator));
        assert forall |read_addr: Address|
            #[trigger] branch.disk_view.entries.contains_key(read_addr)
                && reads.contains_key(read_addr)
            implies branch.disk_view.entries[read_addr]
                == read_nodes[read_addr]
        by {
            assert(branch.representation().contains(read_addr)) by {
                assert(branch.tight_disk_view());
                assert(branch.representation() == branch.disk_view.entries.dom());
            }
            assert(addresses_in_aus(src.branch_projection_aus()).contains(read_addr));
            projected_read_node_matches_visible_branch_entry(src, reads, branch, read_addr);
        }
        receipt_needed_addr_in_linked_branch(src, branch, reads, receipt, addr);
        assert(branch.disk_view.entries.contains_key(addr)) by {
            assert(branch.tight_disk_view());
            assert(branch.representation().contains(addr));
            assert(branch.representation() == branch.disk_view.entries.dom());
        }
        assert(cdb.active_branch_i().addrs_closed_under_mini_allocator());
        assert(cdb.active_branch_i().mini_allocator.page_is_reserved(addr));
        assert(cdb.active_branch_i().mini_allocator == cdb.mini_allocator);
        assert(cdb.mini_allocator.page_is_reserved(addr));
        assert(cdb.mini_allocator.all_aus().contains(addr.au));
    }
    assert(src.branch_projection_aus() == src.branch.owned_aus());
    assert(src.branch.owned_aus() == summary_aus(cdb.branch_summary) + cdb.mini_allocator.all_aus());
    assert(addresses_in_aus(src.branch_projection_aus()).contains(addr));
}

proof fn active_receipt_needed_addr_in_branch_projection(
    src: UnifiedCacheBranchSource,
    reads: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    addr: Address,
)
    requires
        inv(src),
        src.superblock_loaded(),
        src.branch.metadata_loaded(),
        src.branch.active_branch.root is Some,
        receipt.valid_for(src.branch.active_branch.root.unwrap(), to_branch_nodes(reads)),
        forall |read_addr: Address| #[trigger] reads.contains_key(read_addr)
            ==> src.cache.valid_read(read_addr, reads[read_addr]),
        receipt.needed_addrs().contains(addr),
    ensures
        addresses_in_aus(src.branch_projection_aus()).contains(addr),
        addr.wf(),
{
    let cdb = src.branch_caching_disk_state_i();
    assert(cdb.inv());
    assert(cdb.metadata_loaded);
    assert(cdb.branch_metadata_loaded());
    assert(cdb.branch_summary == cdb.interpreted_branch_summary());
    assert(cdb.active_branch_i().inv());
    assert(cdb.active_branch_i().branch is Some);

    let branch = cdb.active_branch_i().branch.unwrap();
    assert(branch.root == src.branch.active_branch.root.unwrap());
    assert(branch.inv());
    assert forall |branch_addr: Address|
        #[trigger] branch.representation().contains(branch_addr)
        implies addresses_in_aus(src.branch_projection_aus()).contains(branch_addr)
    by {
        assert(branch.disk_view.entries.contains_key(branch_addr)) by {
            assert(branch.tight_disk_view());
            assert(branch.representation() == branch.disk_view.entries.dom());
        }
        assert(cdb.active_branch_i().addrs_closed_under_mini_allocator());
        assert(cdb.active_branch_i().mini_allocator.page_is_reserved(branch_addr));
        assert(cdb.active_branch_i().mini_allocator == cdb.mini_allocator);
        assert(cdb.mini_allocator.page_is_reserved(branch_addr));
        assert(cdb.mini_allocator.all_aus().contains(branch_addr.au));
        assert(src.branch_projection_aus() == src.branch.owned_aus());
        assert(src.branch.owned_aus() == summary_aus(cdb.branch_summary) + cdb.mini_allocator.all_aus());
    }
    active_branch_i_visible_candidate(cdb.active_branch, cdb.mini_allocator, cdb.disk);
    assert(semantic_active_branch_candidate(
        cdb.active_branch.root.unwrap(),
        cdb.visible_branch_nodes(),
        cdb.mini_allocator,
        branch,
    ));
    assert(branch.disk_view.entries <= cdb.visible_branch_nodes());
    // Old loaded-node equality:
    // assert(branch.disk_view.entries == active_loaded_nodes_of(cdb.disk, cdb.mini_allocator));
    assert forall |read_addr: Address|
        #[trigger] branch.disk_view.entries.contains_key(read_addr)
            && reads.contains_key(read_addr)
        implies branch.disk_view.entries[read_addr]
            == to_branch_nodes(reads)[read_addr]
    by {
        assert(branch.representation().contains(read_addr)) by {
            assert(branch.tight_disk_view());
            assert(branch.representation() == branch.disk_view.entries.dom());
        }
        assert(addresses_in_aus(src.branch_projection_aus()).contains(read_addr));
        projected_read_node_matches_visible_branch_entry(src, reads, branch, read_addr);
    }
    receipt_needed_addr_in_linked_branch(src, branch, reads, receipt, addr);
    assert(branch.disk_view.entries.contains_key(addr)) by {
        assert(branch.tight_disk_view());
        assert(branch.representation().contains(addr));
        assert(branch.representation() == branch.disk_view.entries.dom());
    }
    assert(branch.disk_view.wf());
    assert(addr.wf());
    assert(cdb.active_branch_i().addrs_closed_under_mini_allocator());
    assert(cdb.active_branch_i().mini_allocator.page_is_reserved(addr));
    assert(cdb.active_branch_i().mini_allocator == cdb.mini_allocator);
    assert(cdb.mini_allocator.page_is_reserved(addr));
    assert(cdb.mini_allocator.all_aus().contains(addr.au));
    assert(src.branch_projection_aus() == src.branch.owned_aus());
    assert(src.branch.owned_aus() == summary_aus(cdb.branch_summary) + cdb.mini_allocator.all_aus());
    assert(addresses_in_aus(src.branch_projection_aus()).contains(addr));
}

proof fn active_root_in_branch_projection(
    src: UnifiedCacheBranchSource,
)
    requires
        inv(src),
        src.superblock_loaded(),
        src.branch.metadata_loaded(),
        src.branch.active_branch.root is Some,
    ensures
        addresses_in_aus(src.branch_projection_aus()).contains(
            src.branch.active_branch.root.unwrap(),
        ),
{
    let cdb = src.branch_caching_disk_state_i();
    assert(cdb.inv());
    assert(cdb.metadata_loaded);
    assert(cdb.branch_metadata_loaded());
    assert(cdb.active_branch_i().inv());
    assert(cdb.active_branch_i().branch is Some);

    let branch = cdb.active_branch_i().branch.unwrap();
    let root = src.branch.active_branch.root.unwrap();
    assert(branch.root == root);
    assert(branch.disk_view.entries.contains_key(root)) by {
        assert(branch.inv());
        assert(branch.wf());
        assert(branch.has_root());
    }
    assert(cdb.active_branch_i().addrs_closed_under_mini_allocator());
    assert(cdb.active_branch_i().mini_allocator.page_is_reserved(root));
    assert(cdb.active_branch_i().mini_allocator == cdb.mini_allocator);
    assert(cdb.mini_allocator.page_is_reserved(root));
    assert(cdb.mini_allocator.all_aus().contains(root.au));
    assert(src.branch_projection_aus() == src.branch.owned_aus());
    assert(src.branch.owned_aus() == summary_aus(cdb.branch_summary) + cdb.mini_allocator.all_aus());
    assert(addresses_in_aus(src.branch_projection_aus()).contains(root));
}

proof fn active_root_au_in_branch_mini_allocator(
    src: UnifiedCacheBranchSource,
)
    requires
        inv(src),
        src.superblock_loaded(),
        src.branch.metadata_loaded(),
        src.branch.active_branch.root is Some,
    ensures
        src.branch.mini_allocator.all_aus().contains(
            src.branch.active_branch.root.unwrap().au,
        ),
{
    let cdb = src.branch_caching_disk_state_i();
    let root = src.branch.active_branch.root.unwrap();

    assert(cdb.inv());
    assert(cdb.metadata_loaded);
    assert(cdb.active_branch_i().inv());
    assert(cdb.active_branch_i().branch is Some);
    let branch = cdb.active_branch_i().branch.unwrap();
    assert(branch.root == root);
    assert(branch.disk_view.entries.contains_key(root)) by {
        assert(branch.inv());
        assert(branch.wf());
        assert(branch.has_root());
    }
    assert(cdb.active_branch_i().addrs_closed_under_mini_allocator());
    assert(cdb.active_branch_i().mini_allocator.page_is_reserved(root));
    assert(cdb.active_branch_i().mini_allocator == cdb.mini_allocator);
    assert(cdb.mini_allocator.page_is_reserved(root));
    assert(cdb.mini_allocator.all_aus().contains(root.au));
}

proof fn active_root_not_in_branch_summary(
    src: UnifiedCacheBranchSource,
)
    requires
        inv(src),
        src.superblock_loaded(),
        src.branch.metadata_loaded(),
        src.branch.active_branch.root is Some,
    ensures
        !src.branch.branch_summary.contains_key(src.branch.active_branch.root.unwrap().au),
{
    let cdb = src.branch_caching_disk_state_i();
    let root = src.branch.active_branch.root.unwrap();
    active_root_au_in_branch_mini_allocator(src);
    assert(cdb.mini_allocator.all_aus().contains(root.au));
    cdb.loaded_summary_aus_disjoint_mini_allocator();

    if src.branch.branch_summary.contains_key(root.au) {
        assert(cdb.branch_summary.contains_key(root.au));
        assert(cdb.branch_metadata_loaded());
        assert(cdb.branch_summary == cdb.interpreted_branch_summary());
        assert(cdb.sealed_stack_i().wf(cdb.branch_summary));
        assert(cdb.branch_summary.dom() == to_aus(cdb.sealed_roots.to_set()));
        assert(to_aus(cdb.sealed_roots.to_set()).contains(root.au));
        to_aus_domain(cdb.sealed_roots.to_set());
        let sealed_root = choose |sealed_root: Address| #![auto]
            cdb.sealed_roots.to_set().contains(sealed_root) && sealed_root.au == root.au;
        cdb.sealed_stack_i().root_au_in_summary(cdb.branch_summary, sealed_root);
        assert(summary_aus(cdb.branch_summary).contains(root.au));
        assert(summary_aus(cdb.branch_summary).disjoint(cdb.mini_allocator.all_aus()));
        assert(false);
    }
}

proof fn active_split_child_in_branch_projection(
    src: UnifiedCacheBranchSource,
    reads: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    split_arg: SplitArg,
)
    requires
        inv(src),
        src.superblock_loaded(),
        src.branch.metadata_loaded(),
        src.branch.active_branch.root is Some,
        receipt.valid_for(src.branch.active_branch.root.unwrap(), to_branch_nodes(reads)),
        receipt.target().node is Index,
        split_arg.get_pivot() == receipt.key,
        forall |read_addr: Address| #[trigger] reads.contains_key(read_addr)
            ==> src.cache.valid_read(read_addr, reads[read_addr]),
    ensures
        addresses_in_aus(src.branch_projection_aus()).contains(receipt.child_addr()),
        receipt.child_addr().wf(),
{
    let cdb = src.branch_caching_disk_state_i();
    let read_nodes = to_branch_nodes(reads);
    let target = receipt.target().addr;
    let child = receipt.child_addr();

    assert(cdb.inv());
    assert(cdb.metadata_loaded);
    assert(cdb.branch_metadata_loaded());
    assert(cdb.active_branch_i().inv());
    assert(cdb.active_branch_i().branch is Some);
    let branch = cdb.active_branch_i().branch.unwrap();
    assert(branch.root == src.branch.active_branch.root.unwrap());
    assert(branch.inv());

    assert(receipt.needed_addrs().contains(target)) by {
        let i = receipt.lines.len() - 1;
        assert(0 <= i < receipt.lines.len());
        assert(receipt.lines[i].addr == target);
    }
    active_receipt_needed_addr_in_branch_projection(src, reads, receipt, target);
    active_branch_i_visible_candidate(cdb.active_branch, cdb.mini_allocator, cdb.disk);
    assert(semantic_active_branch_candidate(
        cdb.active_branch.root.unwrap(),
        cdb.visible_branch_nodes(),
        cdb.mini_allocator,
        branch,
    ));
    assert(branch.disk_view.entries <= cdb.visible_branch_nodes());
    // Old loaded-node equality:
    // assert(branch.disk_view.entries == active_loaded_nodes_of(cdb.disk, cdb.mini_allocator));
    assert forall |branch_addr: Address|
        #[trigger] branch.disk_view.entries.contains_key(branch_addr)
            && reads.contains_key(branch_addr)
        implies branch.disk_view.entries[branch_addr]
            == to_branch_nodes(reads)[branch_addr]
    by {
        assert(branch.representation().contains(branch_addr)) by {
            assert(branch.tight_disk_view());
            assert(branch.representation() == branch.disk_view.entries.dom());
        }
        assert(addresses_in_aus(src.branch_projection_aus()).contains(branch_addr));
        projected_read_node_matches_visible_branch_entry(src, reads, branch, branch_addr);
    }
    assert(branch.disk_view.entries.contains_key(target)) by {
        assert(branch.tight_disk_view());
        receipt_needed_addr_in_linked_branch(src, branch, reads, receipt, target);
        assert(branch.representation().contains(target));
        assert(branch.representation() == branch.disk_view.entries.dom());
    }
    projected_read_node_matches_branch_entry(src, reads, branch, target);
    assert(read_nodes[target] == branch.disk_view.entries[target]);
    assert(read_nodes[target] == receipt.target().node);
    assert(branch.disk_view.entries[target] is Index);
    assert(receipt.target().wf());
    assert(receipt.target().node.wf());
    let child_idx = receipt.target().node.route(receipt.key) + 1;
    LinkedBranchRefinement::lemma_route_ensures(receipt.target().node, receipt.key);
    assert(child_idx == receipt.target().node.route(receipt.key) + 1);
    assert(child_idx == branch.disk_view.entries[target].route(receipt.key) + 1);
    assert(child == branch.disk_view.entries[target]->children[child_idx]);
    assert(branch.disk_view.wf());
    assert(branch.disk_view.no_dangling_address());
    assert(branch.disk_view.node_has_valid_child_address(branch.disk_view.entries[target]));
    assert(branch.disk_view.entries.contains_key(child));
    assert(child.wf());
    assert(cdb.active_branch_i().addrs_closed_under_mini_allocator());
    assert(cdb.active_branch_i().mini_allocator.page_is_reserved(child));
    assert(cdb.active_branch_i().mini_allocator == cdb.mini_allocator);
    assert(cdb.mini_allocator.page_is_reserved(child));
    assert(cdb.mini_allocator.all_aus().contains(child.au));
    assert(src.branch_projection_aus() == src.branch.owned_aus());
    assert(src.branch.owned_aus() == summary_aus(cdb.branch_summary) + cdb.mini_allocator.all_aus());
    assert(addresses_in_aus(src.branch_projection_aus()).contains(child));
}

proof fn split_projection_preserves_loaded_split(
    src: UnifiedCacheBranchSource,
    reads: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    split_arg: SplitArg,
    new_child_addr: Address,
)
    requires
        inv(src),
        src.superblock_loaded(),
        src.branch.metadata_loaded(),
        src.branch.active_branch.root is Some,
        receipt.valid_for(src.branch.active_branch.root.unwrap(), to_branch_nodes(reads)),
        crate::implementation::CachedBranch_v::loaded_split_ready(
            receipt,
            to_branch_nodes(reads),
            split_arg,
        ),
        forall |read_addr: Address| #[trigger] reads.contains_key(read_addr)
            ==> src.cache.valid_read(read_addr, reads[read_addr]),
    ensures
        split_read_addrs(receipt)
            <= reads.restrict(addresses_in_aus(src.branch_projection_aus())).dom(),
        receipt.valid_for(
            src.branch.active_branch.root.unwrap(),
            to_branch_nodes(reads.restrict(addresses_in_aus(src.branch_projection_aus()))),
        ),
        crate::implementation::CachedBranch_v::loaded_split_ready(
            receipt,
            to_branch_nodes(reads.restrict(addresses_in_aus(src.branch_projection_aus()))),
            split_arg,
        ),
        loaded_split_write_nodes(
            receipt,
            to_branch_nodes(reads.restrict(addresses_in_aus(src.branch_projection_aus()))),
            split_arg,
            new_child_addr,
        ) == loaded_split_write_nodes(
            receipt,
            to_branch_nodes(reads),
            split_arg,
            new_child_addr,
        ),
{
    let read_nodes = to_branch_nodes(reads);
    let addrs = addresses_in_aus(src.branch_projection_aus());
    let projected_reads = reads.restrict(addrs);
    let projected_nodes = to_branch_nodes(projected_reads);

    assert(split_read_addrs(receipt) <= projected_reads.dom()) by {
        assert forall |addr: Address| #[trigger] split_read_addrs(receipt).contains(addr)
            implies projected_reads.dom().contains(addr) by {
            if addr == receipt.child_addr() {
                assert(read_nodes.contains_key(addr)) by {
                    assert(crate::implementation::CachedBranch_v::loaded_split_ready(
                        receipt,
                        read_nodes,
                        split_arg,
                    ));
                    assert(crate::implementation::CachedBranch_v::loaded_line_wf(
                        read_nodes,
                        receipt.child_addr(),
                    ));
                }
                assert(reads.contains_key(addr));
                active_split_child_in_branch_projection(src, reads, receipt, split_arg);
                assert(addrs.contains(addr));
            } else {
                assert(receipt.needed_addrs().contains(addr));
                assert(reads.contains_key(addr)) by {
                    assert(receipt.valid_for(src.branch.active_branch.root.unwrap(), read_nodes));
                }
                active_receipt_needed_addr_in_branch_projection(src, reads, receipt, addr);
                assert(addrs.contains(addr));
            }
        }
    }

    assert(receipt.valid_for(src.branch.active_branch.root.unwrap(), projected_nodes)) by {
        assert(receipt.wf());
        assert(receipt.root == src.branch.active_branch.root.unwrap());
        assert(receipt.needed_addrs() <= projected_nodes.dom()) by {
            assert forall |addr: Address| #[trigger] receipt.needed_addrs().contains(addr)
                implies projected_nodes.dom().contains(addr) by {
                assert(split_read_addrs(receipt).contains(addr));
                assert(projected_reads.contains_key(addr));
            }
        }
        assert forall |i: int| #![auto] 0 <= i < receipt.lines.len()
            implies {
                &&& projected_nodes.contains_key(receipt.lines[i].addr)
                &&& projected_nodes[receipt.lines[i].addr] == receipt.lines[i].node
            } by {
            let addr = receipt.lines[i].addr;
            assert(receipt.needed_addrs().contains(addr));
            assert(projected_reads.contains_key(addr));
            assert(projected_reads[addr] == reads[addr]);
            assert(read_nodes[addr] == receipt.lines[i].node);
        }
    }

    assert(projected_reads.contains_key(receipt.child_addr())) by {
        assert(split_read_addrs(receipt).contains(receipt.child_addr()));
    }
    assert(projected_nodes[receipt.child_addr()] == read_nodes[receipt.child_addr()]) by {
        assert(projected_reads[receipt.child_addr()] == reads[receipt.child_addr()]);
    }
    assert(crate::implementation::CachedBranch_v::loaded_split_ready(
        receipt,
        projected_nodes,
        split_arg,
    )) by {
        assert(receipt.valid_for(receipt.root, projected_nodes));
        assert(receipt.target().node is Index);
        assert(receipt.key == split_arg.get_pivot());
        assert(crate::implementation::CachedBranch_v::loaded_line_wf(
            projected_nodes,
            receipt.child_addr(),
        ));
        assert(projected_nodes[receipt.child_addr()] == read_nodes[receipt.child_addr()]);
        assert(crate::implementation::CachedBranch_v::split_arg_matches_child(
            read_nodes[receipt.child_addr()],
            split_arg,
        ));
    }
    assert(loaded_split_write_nodes(receipt, projected_nodes, split_arg, new_child_addr)
        == loaded_split_write_nodes(receipt, read_nodes, split_arg, new_child_addr)) by {
        assert(projected_nodes[receipt.target().addr] == read_nodes[receipt.target().addr]);
        assert(projected_nodes[receipt.child_addr()] == read_nodes[receipt.child_addr()]);
    }
}

proof fn summary_aus_insert_fresh(
    branch_summary: Map<AU, Summary>,
    root_au: AU,
    new_summary: Summary,
)
    requires
        branch_summary.dom().finite(),
        !branch_summary.contains_key(root_au),
    ensures
        summary_aus(branch_summary.insert(root_au, new_summary))
            == summary_aus(branch_summary) + new_summary,
{
    let post_summary = branch_summary.insert(root_au, new_summary);
    lemma_values_finite(branch_summary);
    lemma_values_finite(post_summary);
    assert forall |au: AU| #[trigger] summary_aus(post_summary).contains(au)
        implies (summary_aus(branch_summary) + new_summary).contains(au) by {
        let witness = lemma_union_set_of_sets_contains(post_summary.values(), au);
        assert(witness.contains(au));
        let key = choose |key: AU| #![auto] post_summary.contains_key(key) && post_summary[key] == witness;
        if key == root_au {
            assert(witness == new_summary);
        } else {
            assert(branch_summary.contains_key(key));
            assert(branch_summary[key] == witness);
            assert(branch_summary.values().contains(witness));
            lemma_union_set_of_sets_subset(branch_summary.values(), witness);
        }
    }
    assert forall |au: AU| #[trigger] (summary_aus(branch_summary) + new_summary).contains(au)
        implies summary_aus(post_summary).contains(au) by {
        if summary_aus(branch_summary).contains(au) {
            let witness = lemma_union_set_of_sets_contains(branch_summary.values(), au);
            assert(witness.contains(au));
            let key = choose |key: AU| #![auto]
                branch_summary.contains_key(key) && branch_summary[key] == witness;
            assert(key != root_au);
            assert(post_summary.contains_key(key));
            assert(post_summary[key] == witness);
            assert(post_summary.values().contains(witness));
            lemma_union_set_of_sets_subset(post_summary.values(), witness);
        } else {
            assert(new_summary.contains(au));
            assert(post_summary.contains_key(root_au));
            assert(post_summary[root_au] == new_summary);
            assert(post_summary.values().contains(new_summary));
            lemma_union_set_of_sets_subset(post_summary.values(), new_summary);
        }
    }
}

pub proof fn cache_access_restrict_reads_same_post(
    pre: Cache::State,
    post: Cache::State,
    reads: Map<Address, RawPage>,
    restricted_reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        Cache::State::next(pre, post, Cache::Label::Access{reads, writes}),
        restricted_reads <= reads,
    ensures
        Cache::State::next(pre, post, Cache::Label::Access{reads: restricted_reads, writes}),
{
    let full_lbl = Cache::Label::Access{reads, writes};
    let restricted_lbl = Cache::Label::Access{reads: restricted_reads, writes};
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    assert(Cache::State::next_by(pre, post, full_lbl, Cache::Step::access()));
    assert(Cache::State::access(pre, post, full_lbl)) by {
        reveal(Cache::State::access);
    }
    assert forall |addr: Address| #[trigger] restricted_reads.contains_key(addr)
        implies pre.valid_read(addr, restricted_reads[addr]) by {
        assert(reads.contains_key(addr));
        assert(full_lbl->reads.contains_key(addr));
        assert(pre.valid_read(addr, reads[addr]));
        assert(restricted_reads[addr] == reads[addr]);
    }
    assert(Cache::State::access(pre, post, restricted_lbl)) by {
        reveal(Cache::State::access);
    }
    assert(Cache::State::next_by(pre, post, restricted_lbl, Cache::Step::access())) by {
        reveal(Cache::State::next_by);
    }
    reveal(Cache::State::next);
}

proof fn load_metadata_projected_reads_valid(
    src: UnifiedCacheBranchSource,
    root: Address,
    reads: Map<Address, RawPage>,
    discovered_aus: Set<AU>,
)
    requires
        inv(src),
        src.superblock_loaded(),
        src.branch.image.sealed_roots.to_set().contains(root),
        crate::implementation::CachedBranch_v::root_summary_read_valid(root, to_branch_nodes(reads)),
        discovered_aus == crate::implementation::CachedBranch_v::root_summary_from_read(
            root,
            to_branch_nodes(reads),
        ),
        forall |read_addr: Address| #[trigger] reads.contains_key(read_addr)
            ==> src.cache.valid_read(read_addr, reads[read_addr]),
        ({
            let addrs = addresses_in_aus(src.branch_projection_aus());
            let projected_reads = reads.restrict(addrs);
            &&& crate::implementation::CachedBranch_v::root_summary_read_valid(
                root,
                to_branch_nodes(projected_reads),
            )
            &&& crate::implementation::CachedBranch_v::root_summary_from_read(
                root,
                to_branch_nodes(projected_reads),
            ) == discovered_aus
            &&& crate::implementation::CachedBranch_v::root_summary_from_read(
                root,
                to_branch_nodes(projected_reads),
            ) == crate::implementation::CachedBranch_v::root_summary_from_read(
                root,
                src.branch_caching_disk_state_i().visible_branch_nodes(),
            )
        }),
    ensures
        ({
            let addrs = addresses_in_aus(src.branch_projection_aus());
            let projected_reads = reads.restrict(addrs);
            &&& crate::implementation::CachedBranch_v::root_summary_read_valid(
                root,
                to_branch_nodes(projected_reads),
            )
            &&& crate::implementation::CachedBranch_v::root_summary_from_read(
                root,
                to_branch_nodes(projected_reads),
            ) == discovered_aus
            &&& crate::implementation::CachedBranch_v::root_summary_from_read(
                root,
                to_branch_nodes(projected_reads),
            ) == crate::implementation::CachedBranch_v::root_summary_from_read(
                root,
                src.branch_caching_disk_state_i().visible_branch_nodes(),
            )
            &&& projected_reads <= src.branch_caching_disk_i().cache
        }),
{
    let cdb = src.branch_caching_disk_state_i();
    let addrs = addresses_in_aus(src.branch_projection_aus());
    let projected_reads = reads.restrict(addrs);
    let read_nodes = to_branch_nodes(reads);
    let projected_nodes = to_branch_nodes(projected_reads);
    let visible_nodes = cdb.visible_branch_nodes();

    src.cache.build_lookup_map_ensures();
    assert(cdb.inv());
    assert(cdb.sealed_roots == src.branch.image.sealed_roots);
    assert(cdb.sealed_roots.to_set().contains(root));
    assert(crate::implementation::CachingDiskBranch_v::branch_summary_reads_valid(
        cdb.sealed_roots,
        visible_nodes,
    ));
    assert(crate::implementation::CachedBranch_v::root_summary_read_valid(root, visible_nodes));
    assert(visible_nodes.contains_key(root));
    assert(cdb.disk.visible().contains_key(root));
    // Old proof reconstructed the projected receipt point-by-point from
    // visible(). The refinement boundary now carries that receipt explicitly.
    assert(crate::implementation::CachedBranch_v::root_summary_read_valid(
        root,
        projected_nodes,
    ));
    assert(crate::implementation::CachedBranch_v::root_summary_from_read(
        root,
        projected_nodes,
    ) == discovered_aus);
    assert(crate::implementation::CachedBranch_v::root_summary_from_read(
        root,
        projected_nodes,
    ) == crate::implementation::CachedBranch_v::root_summary_from_read(root, visible_nodes));

    assert(projected_reads <= src.branch_caching_disk_i().cache) by {
        assert forall |addr: Address| #[trigger] projected_reads.contains_key(addr)
            implies src.branch_caching_disk_i().cache.contains_key(addr)
                && src.branch_caching_disk_i().cache[addr] == projected_reads[addr] by {
            assert(reads.contains_key(addr));
            assert(addrs.contains(addr));
            assert(src.cache.valid_read(addr, reads[addr]));
            assert(src.cache.entries.contains_key(src.cache.lookup_map[addr]));
            assert(cache_filled_addr(src.cache, addr));
            assert(src.branch_caching_disk_i().cache.contains_key(addr));
            assert(src.branch_caching_disk_i().cache[addr] == cache_filled_page(src.cache, addr));
            assert(cache_filled_page(src.cache, addr) == reads[addr]);
            assert(projected_reads[addr] == reads[addr]);
        }
    }
}

pub proof fn load_metadata_refines(
    pre: UnifiedCacheBranchSource,
    post: UnifiedCacheBranchSource,
    root: Address,
    reads: Map<Address, RawPage>,
    discovered_aus: Set<AU>,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.in_flight == pre.in_flight,
        post.in_flight_image == pre.in_flight_image,
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access{reads, writes: Map::empty()},
        ),
        AtomicBranchState::State::next(
            pre.branch,
            post.branch,
            AtomicBranchState::Label::LoadMetadata{
                root,
                discovered_aus,
                read_nodes: to_branch_nodes(reads),
            },
        ),
        post.branch_projection_aus() =~= pre.branch_projection_aus(),
        ({
            let addrs = addresses_in_aus(pre.branch_projection_aus());
            let projected_reads = reads.restrict(addrs);
            &&& crate::implementation::CachedBranch_v::root_summary_read_valid(
                root,
                to_branch_nodes(projected_reads),
            )
            &&& crate::implementation::CachedBranch_v::root_summary_from_read(
                root,
                to_branch_nodes(projected_reads),
            ) == discovered_aus
            &&& crate::implementation::CachedBranch_v::root_summary_from_read(
                root,
                to_branch_nodes(projected_reads),
            ) == crate::implementation::CachedBranch_v::root_summary_from_read(
                root,
                pre.branch_caching_disk_state_i().visible_branch_nodes(),
            )
        }),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            unified_cache_branch_i(pre),
            unified_cache_branch_i(post),
            CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus},
        ),
        post.branch.seq_end() == pre.branch.seq_end(),
        post.branch.in_flight == pre.branch.in_flight,
        post.branch.prepared == pre.branch.prepared,
        inv(post),
{
    let empty = Map::<Address, RawPage>::empty();
    let cache_lbl = Cache::Label::Access{reads, writes: empty};
    let atomic_lbl = AtomicBranchState::Label::LoadMetadata{
        root,
        discovered_aus,
        read_nodes: to_branch_nodes(reads),
    };

    AtomicBranchState::State::wf_next(pre.branch, post.branch, atomic_lbl);
    Cache::State::inv_next(pre.cache, post.cache, cache_lbl);
    Cache::State::access_read_only_is_noop(pre.cache, post.cache, reads);
    assert(post.cache == pre.cache);

    reveal(AtomicBranchState::State::next);
    reveal(AtomicBranchState::State::next_by);
    let atomic_step = choose |step: AtomicBranchState::Step|
        AtomicBranchState::State::next_by(pre.branch, post.branch, atomic_lbl, step);
    match atomic_step {
        AtomicBranchState::Step::load_metadata() => {
            assert(AtomicBranchState::State::load_metadata(pre.branch, post.branch, atomic_lbl)) by {
                reveal(AtomicBranchState::State::load_metadata);
            }
        },
        _ => {
            assert(false);
        },
    }
    assert(pre.branch.image.sealed_roots.to_set().contains(root));
    assert(crate::implementation::CachedBranch_v::root_summary_read_valid(
        root,
        to_branch_nodes(reads),
    ));
    assert(discovered_aus == crate::implementation::CachedBranch_v::root_summary_from_read(
        root,
        to_branch_nodes(reads),
    ));
    assert forall |read_addr: Address| #[trigger] reads.contains_key(read_addr)
        implies pre.cache.valid_read(read_addr, reads[read_addr]) by {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        assert(Cache::State::next_by(pre.cache, post.cache, cache_lbl, Cache::Step::access()));
        reveal(Cache::State::access);
        assert(Cache::State::access(pre.cache, post.cache, cache_lbl));
        assert(cache_lbl->reads.contains_key(read_addr));
    }

    load_metadata_projected_reads_valid(pre, root, reads, discovered_aus);
    let addrs = addresses_in_aus(pre.branch_projection_aus());
    let projected_reads = reads.restrict(addrs);
    let cdb_lbl = CachingDiskBranch::Label::LoadMetadata{root, discovered_aus};
    let cd_lbl = CachingDisk::Label::Access{reads: projected_reads, writes: empty};
    let old_cdb = pre.branch_caching_disk_state_i();
    let new_cdb = CachingDiskBranch::State{
        branch_summary: post.branch.branch_summary,
        metadata_loaded: post.branch.metadata_loaded(),
        disk: old_cdb.disk,
        ..old_cdb
    };
    atomic_branch_metadata_loaded_equiv_root_aus(post.branch);
    assert(new_cdb.metadata_loaded == (root_aus_up_to(
        old_cdb.sealed_roots,
        old_cdb.sealed_roots.len() as nat,
    ) <= new_cdb.branch_summary.dom())) by {
        assert(new_cdb.sealed_roots == post.branch.image.sealed_roots);
        assert(new_cdb.branch_summary == post.branch.branch_summary);
    }
    assert(CachingDisk::State::next(
        old_cdb.disk,
        old_cdb.disk,
        cd_lbl,
    )) by {
        assert(old_cdb.disk.cache.union_prefer_right(empty) == old_cdb.disk.cache) by {
            assert_maps_equal!(
                old_cdb.disk.cache.union_prefer_right(empty),
                old_cdb.disk.cache,
                addr => {}
            );
        }
        assert(crate::implementation::CachingDisk_v::status_map(
            empty.dom(),
            crate::implementation::CachingDisk_v::PageStatus::Dirty,
        ) == Map::<Address, crate::implementation::CachingDisk_v::PageStatus>::empty()) by {
            assert_maps_equal!(
                crate::implementation::CachingDisk_v::status_map(
                    empty.dom(),
                    crate::implementation::CachingDisk_v::PageStatus::Dirty,
                ),
                Map::<Address, crate::implementation::CachingDisk_v::PageStatus>::empty(),
                addr => {}
            );
        }
        assert(old_cdb.disk.status.union_prefer_right(
            crate::implementation::CachingDisk_v::status_map(
                empty.dom(),
                crate::implementation::CachingDisk_v::PageStatus::Dirty,
            ),
        ) == old_cdb.disk.status) by {
            assert_maps_equal!(
                old_cdb.disk.status.union_prefer_right(
                    crate::implementation::CachingDisk_v::status_map(
                        empty.dom(),
                        crate::implementation::CachingDisk_v::PageStatus::Dirty,
                    ),
                ),
                old_cdb.disk.status,
                addr => {}
            );
        }
        assert(CachingDisk::State::access(old_cdb.disk, old_cdb.disk, cd_lbl)) by {
            reveal(CachingDisk::State::access);
        }
        assert(CachingDisk::State::next_by(
            old_cdb.disk,
            old_cdb.disk,
            cd_lbl,
            CachingDisk::Step::access(),
        )) by {
            reveal(CachingDisk::State::next_by);
        }
        reveal(CachingDisk::State::next);
    }
    assert(CachingDiskBranch::State::load_metadata(
        old_cdb,
        new_cdb,
        cdb_lbl,
        projected_reads,
    )) by {
        reveal(CachingDiskBranch::State::load_metadata);
        assert(projected_reads <= old_cdb.disk.cache);
        assert(crate::implementation::CachedBranch_v::root_summary_read_valid(
            root,
            to_branch_nodes(projected_reads),
        ));
        assert(discovered_aus == crate::implementation::CachedBranch_v::root_summary_from_read(
            root,
            to_branch_nodes(projected_reads),
        ));
    }
    assert(CachingDiskBranch::State::next_by(
        old_cdb,
        new_cdb,
        cdb_lbl,
        CachingDiskBranch::Step::load_metadata(projected_reads),
    )) by {
        reveal(CachingDiskBranch::State::next_by);
    }
    reveal(CachingDiskBranch::State::next);
    CachingDiskBranch::State::inv_next(old_cdb, new_cdb, cdb_lbl);
    assert(post.branch_projection_aus() =~= pre.branch_projection_aus());
    assert(post.branch_caching_disk_i() == old_cdb.disk) by {
        assert(post.cache == pre.cache);
        assert(post.disk == pre.disk);
        assert(post.branch_projection_aus() =~= pre.branch_projection_aus());
        assert_maps_equal!(
            post.branch_caching_disk_i().cache,
            old_cdb.disk.cache,
            addr => {}
        );
        assert_maps_equal!(
            post.branch_caching_disk_i().status,
            old_cdb.disk.status,
            addr => {}
        );
        assert_maps_equal!(
            post.branch_caching_disk_i().persistent,
            old_cdb.disk.persistent,
            addr => {}
        );
    }
    assert(post.branch_caching_disk_state_i() == new_cdb);

    let src = unified_cache_branch_i(pre);
    let dst = unified_cache_branch_i(post);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(CrashAwareCachingDiskBranch::State::load_metadata(
        src,
        dst,
        CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus},
        new_cdb,
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::load_metadata);
    }
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus},
        CrashAwareCachingDiskBranch::Step::load_metadata(new_cdb),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);
    src.next_refines(dst, CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus});

    assert(post.inv()) by {
        assert(post.branch.wf());
        assert(async_disk_superblock_page_wf(post.disk.content));
        assert(post.persistent_superblock_image_i() == pre.persistent_superblock_image_i());
        assert(post.persistent_superblock_image_i().wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.branch_caching_disk_i().inv());
        assert(post.branch.persistent_image.sealed_roots
            == post.persistent_superblock_image_i().branch_roots);
        assert(post.branch.persistent_image.seq_end
            == post.persistent_superblock_image_i().branch_seq_end);
        assert(post.in_flight is Some <==> post.branch.in_flight is Some);
        assert(post.in_flight is Some <==> post.in_flight_image is Some);
    }
    assert(post.semantic_inv());
    assert(inv(post));
}

pub proof fn query_refines(
    pre: UnifiedCacheBranchSource,
    post: UnifiedCacheBranchSource,
    key: Key,
    value: Value,
    msg: Message,
    receipts: Seq<LoadedPathReceipt>,
    reads: Map<Address, RawPage>,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        pre.branch.metadata_loaded(),
        post.branch == pre.branch,
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.in_flight == pre.in_flight,
        post.in_flight_image == pre.in_flight_image,
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access{reads, writes: Map::empty()},
        ),
        AtomicBranchState::State::next(
            pre.branch,
            pre.branch,
            AtomicBranchState::Label::Query{
                key,
                msg,
                receipts,
                read_nodes: to_branch_nodes(reads),
            },
        ),
        normalize_value(msg) == value,
        reads.dom() == query_receipts_read_addrs(receipts, receipts.len() as nat),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            unified_cache_branch_i(pre),
            unified_cache_branch_i(post),
            CrashAwareCachingDiskBranch::Label::Query{key, value},
        ),
        inv(post),
{
    let empty_writes = Map::<Address, RawPage>::empty();
    let cache_lbl = Cache::Label::Access{reads, writes: empty_writes};
    let aus = pre.branch_projection_aus();

    Cache::State::inv_next(pre.cache, post.cache, cache_lbl);
    assert(post.superblock_loaded());
    assert(post.branch.metadata_loaded());
    assert(post.branch_projection_aus() =~= aus);

    let read_nodes = to_branch_nodes(reads);
    let atomic_lbl = AtomicBranchState::Label::Query{key, msg, receipts, read_nodes};
    reveal(AtomicBranchState::State::next);
    reveal(AtomicBranchState::State::next_by);
    let atomic_step = choose |step: AtomicBranchState::Step|
        AtomicBranchState::State::next_by(pre.branch, pre.branch, atomic_lbl, step);
    match atomic_step {
            AtomicBranchState::Step::query() => {
                assert(AtomicBranchState::State::query(pre.branch, pre.branch, atomic_lbl)) by {
                    reveal(AtomicBranchState::State::query);
                }
                let roots = crate::implementation::AtomicBranchState_v::query_roots(
                    pre.branch.image.sealed_roots,
                    pre.branch.active_branch,
                );
                assert(crate::implementation::AtomicBranchState_v::query_receipts_valid(
                    roots,
                    receipts,
                    read_nodes,
                    key,
                ));
            },
            _ => {
                assert(false);
            },
        }

    projected_cache_read_only_access_unchanged(pre.cache, post.cache, aus, reads);
    assert(reads <= pre.branch_caching_disk_i().cache) by {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        assert(Cache::State::next_by(pre.cache, post.cache, cache_lbl, Cache::Step::access()));
        reveal(Cache::State::access);
        assert(Cache::State::access(pre.cache, post.cache, cache_lbl));
        assert(cache_lbl is Access);
        assert(cache_lbl->reads == reads);
        pre.cache.build_lookup_map_ensures();
        let inner_state = pre.branch_caching_disk_state_i();
        assert(inner_state == pre.branch_caching_disk_state_i());
        assert(inner_state.inv());
        assert(inner_state.metadata_loaded);
        assert(inner_state.refinement_inv());
        inner_state.semantic_inv_implies_i_inv();
        assert(inner_state.i().inv());
        assert forall |read_addr: Address| #[trigger] reads.contains_key(read_addr)
            implies pre.cache.valid_read(read_addr, reads[read_addr]) by {
            assert(cache_lbl->reads.contains_key(read_addr));
        }
        assert forall |addr: Address| #[trigger] reads.contains_key(addr)
            implies {
                &&& pre.branch_caching_disk_i().cache.contains_key(addr)
                &&& reads[addr] == pre.branch_caching_disk_i().cache[addr]
            } by {
            assert(reads.dom().contains(addr));
            assert(query_receipts_read_addrs(receipts, receipts.len() as nat).contains(addr));
            query_receipts_read_addrs_member_has_receipt(
                receipts,
                receipts.len() as nat,
                addr,
            );
            let receipt_idx = choose |i: int| #![auto] {
                &&& 0 <= i < receipts.len()
                &&& receipts[i].needed_addrs().contains(addr)
            };
            let roots = crate::implementation::AtomicBranchState_v::query_roots(
                pre.branch.image.sealed_roots,
                pre.branch.active_branch,
            );
            let root_idx = roots.len() as int - receipts.len() as int + receipt_idx;
            assert(receipts.len() <= roots.len());
            assert(0 <= root_idx < roots.len());
            assert(receipts[receipt_idx].valid_for(roots[root_idx], read_nodes));
            assert(read_nodes.contains_key(addr));
            assert(pre.cache.valid_read(addr, reads[addr]));
            assert(cache_filled_addr(pre.cache, addr));
            assert(cache_filled_page(pre.cache, addr) == reads[addr]);
            query_receipt_needed_addr_in_branch_projection(
                pre,
                key,
                receipts,
                reads,
                receipt_idx,
                addr,
            );
            assert(addresses_in_aus(aus).contains(addr));
            assert(project_cache_pages(pre.cache, aus).contains_key(addr));
            assert(pre.branch_caching_disk_i().cache.contains_key(addr));
            assert(pre.branch_caching_disk_i().cache[addr] == reads[addr]);
        }
    }
    assert(reads.dom() <= addresses_in_aus(aus)) by {
        assert forall |addr: Address| #[trigger] reads.dom().contains(addr)
            implies addresses_in_aus(aus).contains(addr) by {
            assert(reads.contains_key(addr));
            assert(pre.branch_caching_disk_i().cache.contains_key(addr));
            assert(pre.branch_caching_disk_i() == adapter_caching_disk_i(pre.cache, pre.disk, aus));
            assert(project_cache_pages(pre.cache, aus).contains_key(addr));
        }
    }
    cache_access_refines_caching_disk_access(
        pre.cache,
        post.cache,
        pre.disk,
        aus,
        reads,
        empty_writes,
    );

    assert(post.branch_caching_disk_i() == pre.branch_caching_disk_i()) by {
        assert_maps_equal!(
            post.branch_caching_disk_i().cache,
            pre.branch_caching_disk_i().cache,
            addr => {
                assert(addresses_in_aus(post.branch_projection_aus()).contains(addr)
                    <==> addresses_in_aus(aus).contains(addr));
            }
        );
        assert_maps_equal!(
            post.branch_caching_disk_i().status,
            pre.branch_caching_disk_i().status,
            addr => {
                assert(addresses_in_aus(post.branch_projection_aus()).contains(addr)
                    <==> addresses_in_aus(aus).contains(addr));
            }
        );
        assert_maps_equal!(
            post.branch_caching_disk_i().persistent,
            pre.branch_caching_disk_i().persistent,
            addr => {
                assert(addresses_in_aus(post.branch_projection_aus()).contains(addr)
                    <==> addresses_in_aus(aus).contains(addr));
            }
        );
    }

    assert(post.branch_caching_disk_state_i() == pre.branch_caching_disk_state_i());
    assert(post.i() == pre.i());

    let src = unified_cache_branch_i(pre);
    let dst = unified_cache_branch_i(post);
    let inner = pre.branch_caching_disk_state_i();
    let cd_lbl = CachingDisk::Label::Access{reads, writes: empty_writes};
    assert(CachingDisk::State::next(pre.branch_caching_disk_i(), post.branch_caching_disk_i(), cd_lbl));
    assert(CachingDisk::State::next(pre.branch_caching_disk_i(), pre.branch_caching_disk_i(), cd_lbl));

    assert(crate::implementation::AtomicBranchState_v::query_roots(
        pre.branch.image.sealed_roots,
        pre.branch.active_branch,
    ) == crate::implementation::CachingDiskBranch_v::query_roots(
        inner.sealed_roots,
        inner.active_branch,
    ));
    let roots = crate::implementation::CachingDiskBranch_v::query_roots(
        inner.sealed_roots,
        inner.active_branch,
    );
    query_receipts_valid_equiv(roots, receipts, read_nodes, key);
    query_from_receipts_up_to_equiv(receipts, receipts.len() as nat);

    let branch_lbl = CachingDiskBranch::Label::QueryLabel{key, msg};
    assert(CachingDiskBranch::State::query(
        inner,
        inner,
        branch_lbl,
        receipts,
        reads,
    )) by {
        reveal(CachingDiskBranch::State::query);
    }
    assert(CachingDiskBranch::State::next_by(
        inner,
        inner,
        branch_lbl,
        CachingDiskBranch::Step::query(receipts, reads),
    )) by {
        reveal(CachingDiskBranch::State::next_by);
    }
    reveal(CachingDiskBranch::State::next);

    let lbl = CrashAwareCachingDiskBranch::Label::Query{key, value};
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(dst == src);
    assert(CrashAwareCachingDiskBranch::State::query(src, dst, lbl, msg)) by {
        reveal(CrashAwareCachingDiskBranch::State::query);
    }
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        lbl,
        CrashAwareCachingDiskBranch::Step::query(msg),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);

    assert(post.inv()) by {
        assert(post.branch.wf());
        assert(async_disk_superblock_page_wf(post.disk.content));
        assert(post.persistent_superblock_image_i() == pre.persistent_superblock_image_i());
        assert(post.persistent_superblock_image_i().wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.branch_caching_disk_i().inv());
    }
    assert(post.semantic_inv());
    assert(inv(post));
}

pub proof fn append_refines(
    pre: UnifiedCacheBranchSource,
    post: UnifiedCacheBranchSource,
    keys: Seq<Key>,
    msgs: Seq<Message>,
    receipt: LoadedPathReceipt,
    init_root: Option<Address>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        pre.branch.metadata_loaded(),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.in_flight == pre.in_flight,
        post.in_flight_image == pre.in_flight_image,
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access{reads, writes},
        ),
        AtomicBranchState::State::next(
            pre.branch,
            post.branch,
            AtomicBranchState::Label::Append{
                keys,
                msgs,
                receipt,
                init_root,
                read_nodes: to_branch_nodes(reads),
                write_nodes: to_branch_nodes(writes),
            },
        ),
        if pre.branch.active_branch.root is Some {
            reads.dom() == receipt.needed_addrs()
        } else {
            reads.dom() == Set::<Address>::empty()
        },
    ensures
        CrashAwareCachingDiskBranch::State::next(
            unified_cache_branch_i(pre),
            unified_cache_branch_i(post),
            CrashAwareCachingDiskBranch::Label::Append{keys, msgs},
        ),
        writes.dom() <= addresses_in_aus(pre.branch_projection_aus()),
        writes.dom() <= Set::new(|addr: Address| addr.wf()),
        post.branch_projection_aus() =~= pre.branch_projection_aus(),
        post.branch.seq_end() == pre.branch.seq_end() + keys.len(),
        post.branch.metadata_loaded(),
        post.branch.prepared == pre.branch.prepared,
        inv(post),
{
    let cache_lbl = Cache::Label::Access{reads, writes};
    let atomic_lbl = AtomicBranchState::Label::Append{
        keys,
        msgs,
        receipt,
        init_root,
        read_nodes: to_branch_nodes(reads),
        write_nodes: to_branch_nodes(writes),
    };
    let read_nodes = to_branch_nodes(reads);
    let write_nodes = to_branch_nodes(writes);
    let aus = pre.branch_projection_aus();

    Cache::State::inv_next(pre.cache, post.cache, cache_lbl);
    AtomicBranchState::State::wf_next(pre.branch, post.branch, atomic_lbl);
    AtomicBranchState::State::append_effect(pre.branch, post.branch, atomic_lbl);
    AtomicBranchState::State::append_preserves_owned_aus(pre.branch, post.branch, atomic_lbl);
    assert(post.superblock_loaded());
    assert(post.branch.metadata_loaded()) by {
        assert(post.branch.image == pre.branch.image);
        assert(post.branch.branch_summary == pre.branch.branch_summary);
    }
    assert(post.branch_projection_aus() =~= aus);

    reveal(AtomicBranchState::State::next);
    reveal(AtomicBranchState::State::next_by);
    let atomic_step = choose |step: AtomicBranchState::Step|
        AtomicBranchState::State::next_by(pre.branch, post.branch, atomic_lbl, step);
    match atomic_step {
        AtomicBranchState::Step::append_nonempty(new_active_branch) => {
            assert(AtomicBranchState::State::append_nonempty(
                pre.branch,
                post.branch,
                atomic_lbl,
                new_active_branch,
            )) by {
                reveal(AtomicBranchState::State::append_nonempty);
            }
            reveal(AtomicBranchState::State::append_nonempty);
            assert(pre.branch.active_branch.root is Some);
            assert(init_root is None);
            assert(post.branch.active_branch == new_active_branch);
            assert(post.branch.mini_allocator == pre.branch.mini_allocator);
            assert(post.branch.prepared == pre.branch.prepared);
            let branch_lbl = CachedBranch::Label::Append{
                mini_allocator: pre.branch.mini_allocator,
                receipt,
                keys,
                msgs,
                read_nodes,
                write_nodes,
            };
            assert(CachedBranch::State::next(
                pre.branch.active_branch,
                post.branch.active_branch,
                branch_lbl,
            ));
            reveal(CachedBranch::State::next);
            reveal(CachedBranch::State::next_by);
            assert(CachedBranch::State::next_by(
                pre.branch.active_branch,
                post.branch.active_branch,
                branch_lbl,
                CachedBranch::Step::append_step(),
            ));
            assert(CachedBranch::State::append_step(
                pre.branch.active_branch,
                post.branch.active_branch,
                branch_lbl,
            )) by {
                reveal(CachedBranch::State::append_step);
            }
            reveal(CachedBranch::State::append_step);
            assert(write_nodes == loaded_append_write_nodes(receipt, keys, msgs));
        },
        AtomicBranchState::Step::append_empty(new_active_branch) => {
            assert(AtomicBranchState::State::append_empty(
                pre.branch,
                post.branch,
                atomic_lbl,
                new_active_branch,
            )) by {
                reveal(AtomicBranchState::State::append_empty);
            }
            reveal(AtomicBranchState::State::append_empty);
            assert(pre.branch.active_branch.root is None);
            assert(init_root is Some);
            let init_addr = init_root.unwrap();
            assert(post.branch.active_branch == new_active_branch);
            assert(post.branch.mini_allocator == pre.branch.mini_allocator.allocate(init_addr));
            assert(post.branch.prepared == pre.branch.prepared);
            let branch_lbl = CachedBranch::Label::Initialize{
                mini_allocator: pre.branch.mini_allocator,
                init_root: init_addr,
                keys,
                msgs,
                write_nodes,
            };
            assert(CachedBranch::State::next(
                pre.branch.active_branch,
                post.branch.active_branch,
                branch_lbl,
            ));
            reveal(CachedBranch::State::next);
            reveal(CachedBranch::State::next_by);
            assert(CachedBranch::State::next_by(
                pre.branch.active_branch,
                post.branch.active_branch,
                branch_lbl,
                CachedBranch::Step::initialize_branch(),
            ));
            assert(CachedBranch::State::initialize_branch(
                pre.branch.active_branch,
                post.branch.active_branch,
                branch_lbl,
            )) by {
                reveal(CachedBranch::State::initialize_branch);
            }
            reveal(CachedBranch::State::initialize_branch);
            assert(write_nodes == loaded_initialize_write_nodes(init_addr, keys, msgs));
            assert(pre.branch.mini_allocator.can_allocate(init_addr));
        },
        _ => {
            assert(false);
        },
    }

    assert forall |read_addr: Address| #[trigger] reads.contains_key(read_addr)
        implies pre.cache.valid_read(read_addr, reads[read_addr])
    by {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        assert(Cache::State::next_by(pre.cache, post.cache, cache_lbl, Cache::Step::access()));
        reveal(Cache::State::access);
        assert(cache_lbl->reads.contains_key(read_addr));
    }
    assert(reads <= project_cache_pages(pre.cache, aus)) by {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        assert(Cache::State::next_by(
            pre.cache,
            post.cache,
            cache_lbl,
            Cache::Step::access(),
        ));
        reveal(Cache::State::access);
        assert(Cache::State::access(pre.cache, post.cache, cache_lbl));
        pre.cache.build_lookup_map_ensures();
        assert forall |addr: Address| #[trigger] reads.contains_key(addr)
            implies {
                &&& project_cache_pages(pre.cache, aus).contains_key(addr)
                &&& reads[addr] == project_cache_pages(pre.cache, aus)[addr]
            } by {
            assert(pre.cache.valid_read(addr, reads[addr])) by {
                assert(cache_lbl->reads.contains_key(addr));
            }
            if pre.branch.active_branch.root is Some {
                assert(reads.dom().contains(addr));
                assert(receipt.needed_addrs().contains(addr));
                active_receipt_needed_addr_in_branch_projection(
                    pre,
                    reads,
                    receipt,
                    addr,
                );
                assert(addresses_in_aus(aus).contains(addr));
                assert(cache_filled_addr(pre.cache, addr));
                assert(cache_filled_page(pre.cache, addr) == reads[addr]);
                assert(project_cache_pages(pre.cache, aus).contains_key(addr));
                assert(project_cache_pages(pre.cache, aus)[addr] == reads[addr]);
            } else {
                assert(reads.dom().contains(addr));
                assert(false);
            }
        }
    }
    assert(reads.dom() <= addresses_in_aus(aus)) by {
        assert forall |addr: Address| #[trigger] reads.dom().contains(addr)
            implies addresses_in_aus(aus).contains(addr) by {
            assert(reads.contains_key(addr));
            assert(project_cache_pages(pre.cache, aus).contains_key(addr));
        }
    }

    assert(writes.dom() <= addresses_in_aus(aus)) by {
        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
            implies addresses_in_aus(aus).contains(addr) by {
            assert(writes.contains_key(addr));
            assert(write_nodes.contains_key(addr));
            if pre.branch.active_branch.root is Some {
                let branch_lbl = CachedBranch::Label::Append{
                    mini_allocator: pre.branch.mini_allocator,
                    receipt,
                    keys,
                    msgs,
                    read_nodes,
                    write_nodes,
                };
                assert(CachedBranch::State::next(
                    pre.branch.active_branch,
                    post.branch.active_branch,
                    branch_lbl,
                ));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                assert(CachedBranch::State::next_by(
                    pre.branch.active_branch,
                    post.branch.active_branch,
                    branch_lbl,
                    CachedBranch::Step::append_step(),
                ));
                assert(CachedBranch::State::append_step(
                    pre.branch.active_branch,
                    post.branch.active_branch,
                    branch_lbl,
                )) by {
                    reveal(CachedBranch::State::append_step);
                }
                reveal(CachedBranch::State::append_step);
                assert(write_nodes == loaded_append_write_nodes(receipt, keys, msgs));
                assert(addr == receipt.target().addr);
                assert(receipt.needed_addrs().contains(addr)) by {
                    let i = receipt.lines.len() - 1;
                    assert(0 <= i < receipt.lines.len());
                    assert(receipt.lines[i].addr == addr);
                }
                active_receipt_needed_addr_in_branch_projection(
                    pre,
                    reads,
                    receipt,
                    addr,
                );
                assert(addresses_in_aus(aus).contains(addr));
            } else {
                assert(init_root is Some);
                let init_addr = init_root.unwrap();
                let branch_lbl = CachedBranch::Label::Initialize{
                    mini_allocator: pre.branch.mini_allocator,
                    init_root: init_addr,
                    keys,
                    msgs,
                    write_nodes,
                };
                assert(CachedBranch::State::next(
                    pre.branch.active_branch,
                    post.branch.active_branch,
                    branch_lbl,
                ));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                assert(CachedBranch::State::next_by(
                    pre.branch.active_branch,
                    post.branch.active_branch,
                    branch_lbl,
                    CachedBranch::Step::initialize_branch(),
                ));
                assert(CachedBranch::State::initialize_branch(
                    pre.branch.active_branch,
                    post.branch.active_branch,
                    branch_lbl,
                )) by {
                    reveal(CachedBranch::State::initialize_branch);
                }
                reveal(CachedBranch::State::initialize_branch);
                assert(write_nodes == loaded_initialize_write_nodes(init_addr, keys, msgs));
                assert(addr == init_addr);
                assert(pre.branch.mini_allocator.can_allocate(init_addr));
                assert(pre.branch.mini_allocator.all_aus().contains(init_addr.au));
                assert(pre.branch.owned_aus().contains(init_addr.au));
                assert(addresses_in_aus(aus).contains(addr));
            }
        }
    }
    assert(writes.dom() <= Set::new(|addr: Address| addr.wf())) by {
        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
            implies Set::new(|addr: Address| addr.wf()).contains(addr) by {
            assert(writes.contains_key(addr));
            assert(write_nodes.contains_key(addr));
            if pre.branch.active_branch.root is Some {
                let branch_lbl = CachedBranch::Label::Append{
                    mini_allocator: pre.branch.mini_allocator,
                    receipt,
                    keys,
                    msgs,
                    read_nodes,
                    write_nodes,
                };
                assert(CachedBranch::State::next(
                    pre.branch.active_branch,
                    post.branch.active_branch,
                    branch_lbl,
                ));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                assert(CachedBranch::State::next_by(
                    pre.branch.active_branch,
                    post.branch.active_branch,
                    branch_lbl,
                    CachedBranch::Step::append_step(),
                ));
                assert(CachedBranch::State::append_step(
                    pre.branch.active_branch,
                    post.branch.active_branch,
                    branch_lbl,
                )) by {
                    reveal(CachedBranch::State::append_step);
                }
                reveal(CachedBranch::State::append_step);
                assert(write_nodes == loaded_append_write_nodes(receipt, keys, msgs));
                assert(addr == receipt.target().addr);
                assert(receipt.needed_addrs().contains(addr)) by {
                    let i = receipt.lines.len() - 1;
                    assert(0 <= i < receipt.lines.len());
                    assert(receipt.lines[i].addr == addr);
                }
                active_receipt_needed_addr_in_branch_projection(
                    pre,
                    reads,
                    receipt,
                    addr,
                );
                assert(addr.wf());
            } else {
                assert(init_root is Some);
                let init_addr = init_root.unwrap();
                let branch_lbl = CachedBranch::Label::Initialize{
                    mini_allocator: pre.branch.mini_allocator,
                    init_root: init_addr,
                    keys,
                    msgs,
                    write_nodes,
                };
                assert(CachedBranch::State::next(
                    pre.branch.active_branch,
                    post.branch.active_branch,
                    branch_lbl,
                ));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                assert(CachedBranch::State::next_by(
                    pre.branch.active_branch,
                    post.branch.active_branch,
                    branch_lbl,
                    CachedBranch::Step::initialize_branch(),
                ));
                assert(CachedBranch::State::initialize_branch(
                    pre.branch.active_branch,
                    post.branch.active_branch,
                    branch_lbl,
                )) by {
                    reveal(CachedBranch::State::initialize_branch);
                }
                reveal(CachedBranch::State::initialize_branch);
                assert(write_nodes == loaded_initialize_write_nodes(init_addr, keys, msgs));
                assert(addr == init_addr);
                assert(pre.branch.mini_allocator.can_allocate(init_addr));
                assert(init_addr.wf());
            }
        }
    }

    cache_access_refines_caching_disk_access(
        pre.cache,
        post.cache,
        pre.disk,
        aus,
        reads,
        writes,
    );
    assert(CachingDisk::State::next(
        pre.branch_caching_disk_i(),
        post.branch_caching_disk_i(),
        CachingDisk::Label::Access{reads, writes},
    )) by {
        assert(pre.branch_caching_disk_i() == adapter_caching_disk_i(pre.cache, pre.disk, aus));
        assert(post.branch_caching_disk_i() == adapter_caching_disk_i(post.cache, pre.disk, aus));
    }

    let inner_pre = pre.branch_caching_disk_state_i();
    let inner_post = post.branch_caching_disk_state_i();
    let branch_lbl = CachingDiskBranch::Label::AppendLabel{keys, msgs};
    assert(inner_pre.disk == pre.branch_caching_disk_i());
    assert(inner_post.disk == post.branch_caching_disk_i());
    assert(CachingDiskBranch::State::append(
        inner_pre,
        inner_post,
        branch_lbl,
        inner_post.disk,
        post.branch.active_branch,
        receipt,
        init_root,
        reads,
        writes,
    )) by {
        reveal(CachingDiskBranch::State::append);
        assert(inner_pre.metadata_loaded);
        assert(CachingDisk::State::next(
            inner_pre.disk,
            inner_post.disk,
            CachingDisk::Label::Access{reads, writes},
        ));
        if pre.branch.active_branch.root is Some {
            let cached_lbl = CachedBranch::Label::Append{
                mini_allocator: pre.branch.mini_allocator,
                receipt,
                keys,
                msgs,
                read_nodes,
                write_nodes,
            };
            assert(CachedBranch::State::next(
                inner_pre.active_branch,
                inner_post.active_branch,
                cached_lbl,
            ));
            assert(init_root is None);
        } else {
            assert(init_root is Some);
            let init_addr = init_root.unwrap();
            let cached_lbl = CachedBranch::Label::Initialize{
                mini_allocator: pre.branch.mini_allocator,
                init_root: init_addr,
                keys,
                msgs,
                write_nodes,
            };
            assert(CachedBranch::State::next(
                inner_pre.active_branch,
                inner_post.active_branch,
                cached_lbl,
            ));
        }
        assert(pre.branch.active_branch.root is Some <==> init_root is None);
        assert(inner_post.sealed_roots == inner_pre.sealed_roots);
        assert(inner_post.branch_summary == inner_pre.branch_summary);
        assert(inner_post.metadata_loaded == inner_pre.metadata_loaded);
        assert(inner_post.active_branch == post.branch.active_branch);
        assert(inner_post.mini_allocator == if inner_pre.active_branch.root is Some {
            inner_pre.mini_allocator
        } else {
            inner_pre.mini_allocator.allocate(init_root.unwrap())
        });
        assert(inner_post.seq_end == inner_pre.seq_end + keys.len());
    }
    assert(CachingDiskBranch::State::next_by(
        inner_pre,
        inner_post,
        branch_lbl,
        CachingDiskBranch::Step::append(
            inner_post.disk,
            post.branch.active_branch,
            receipt,
            init_root,
            reads,
            writes,
        ),
    )) by {
        reveal(CachingDiskBranch::State::next_by);
    }
    reveal(CachingDiskBranch::State::next);
    CachingDiskBranch::State::inv_next(inner_pre, inner_post, branch_lbl);

    let src = unified_cache_branch_i(pre);
    let dst = unified_cache_branch_i(post);
    let lbl = CrashAwareCachingDiskBranch::Label::Append{keys, msgs};
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(CrashAwareCachingDiskBranch::State::append(src, dst, lbl, inner_post)) by {
        reveal(CrashAwareCachingDiskBranch::State::append);
    }
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        lbl,
        CrashAwareCachingDiskBranch::Step::append(inner_post),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);
    src.next_refines(dst, lbl);

    assert(post.inv()) by {
        assert(post.branch.wf());
        assert(async_disk_superblock_page_wf(post.disk.content));
        assert(post.persistent_superblock_image_i() == pre.persistent_superblock_image_i());
        assert(post.persistent_superblock_image_i().wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.branch_caching_disk_i().inv());
        assert(post.in_flight is Some <==> post.branch.in_flight is Some);
        assert(post.in_flight is Some <==> post.in_flight_image is Some);
    }
    assert(post.semantic_inv());
    assert(inv(post));
}

pub proof fn append_refines_with_extra_reads(
    pre: UnifiedCacheBranchSource,
    post: UnifiedCacheBranchSource,
    keys: Seq<Key>,
    msgs: Seq<Message>,
    receipt: LoadedPathReceipt,
    init_root: Option<Address>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        pre.branch.metadata_loaded(),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.in_flight == pre.in_flight,
        post.in_flight_image == pre.in_flight_image,
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access{reads, writes},
        ),
        AtomicBranchState::State::next(
            pre.branch,
            post.branch,
            AtomicBranchState::Label::Append{
                keys,
                msgs,
                receipt,
                init_root,
                read_nodes: to_branch_nodes(reads),
                write_nodes: to_branch_nodes(writes),
            },
        ),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            unified_cache_branch_i(pre),
            unified_cache_branch_i(post),
            CrashAwareCachingDiskBranch::Label::Append{keys, msgs},
        ),
        writes.dom() <= addresses_in_aus(pre.branch_projection_aus()),
        writes.dom() <= Set::new(|addr: Address| addr.wf()),
        post.branch_projection_aus() =~= pre.branch_projection_aus(),
        post.branch.seq_end() == pre.branch.seq_end() + keys.len(),
        post.branch.metadata_loaded(),
        post.branch.prepared == pre.branch.prepared,
        inv(post),
{
    let tight_reads = if pre.branch.active_branch.root is Some {
        reads.restrict(receipt.needed_addrs())
    } else {
        Map::<Address, RawPage>::empty()
    };
    let read_nodes = to_branch_nodes(reads);
    let tight_read_nodes = to_branch_nodes(tight_reads);
    let write_nodes = to_branch_nodes(writes);
    let atomic_lbl = AtomicBranchState::Label::Append{
        keys,
        msgs,
        receipt,
        init_root,
        read_nodes,
        write_nodes,
    };
    let tight_atomic_lbl = AtomicBranchState::Label::Append{
        keys,
        msgs,
        receipt,
        init_root,
        read_nodes: tight_read_nodes,
        write_nodes,
    };

    assert(tight_reads <= reads) by {
        assert forall |addr: Address| #[trigger] tight_reads.contains_key(addr)
            implies {
                &&& reads.contains_key(addr)
                &&& tight_reads[addr] == reads[addr]
            } by {
            if pre.branch.active_branch.root is Some {
                assert(tight_reads == reads.restrict(receipt.needed_addrs()));
            } else {
                assert(tight_reads == Map::<Address, RawPage>::empty());
            }
        }
    }
    cache_access_restrict_reads_same_post(pre.cache, post.cache, reads, tight_reads, writes);
    assert(Cache::State::next(
        pre.cache,
        post.cache,
        Cache::Label::Access{reads: tight_reads, writes},
    ));

    assert(if pre.branch.active_branch.root is Some {
        tight_reads.dom() == receipt.needed_addrs()
    } else {
        tight_reads.dom() == Set::<Address>::empty()
    }) by {
        if pre.branch.active_branch.root is Some {
            reveal(AtomicBranchState::State::next);
            reveal(AtomicBranchState::State::next_by);
            let atomic_step = choose |step: AtomicBranchState::Step|
                AtomicBranchState::State::next_by(pre.branch, post.branch, atomic_lbl, step);
            match atomic_step {
                AtomicBranchState::Step::append_nonempty(new_active_branch) => {
                    assert(AtomicBranchState::State::append_nonempty(
                        pre.branch,
                        post.branch,
                        atomic_lbl,
                        new_active_branch,
                    )) by {
                        reveal(AtomicBranchState::State::append_nonempty);
                    }
                    reveal(AtomicBranchState::State::append_nonempty);
                    let branch_lbl = CachedBranch::Label::Append{
                        mini_allocator: pre.branch.mini_allocator,
                        receipt,
                        keys,
                        msgs,
                        read_nodes,
                        write_nodes,
                    };
                    assert(CachedBranch::State::next(
                        pre.branch.active_branch,
                        new_active_branch,
                        branch_lbl,
                    ));
                    reveal(CachedBranch::State::next);
                    reveal(CachedBranch::State::next_by);
                    assert(CachedBranch::State::next_by(
                        pre.branch.active_branch,
                        new_active_branch,
                        branch_lbl,
                        CachedBranch::Step::append_step(),
                    ));
                    assert(CachedBranch::State::append_step(
                        pre.branch.active_branch,
                        new_active_branch,
                        branch_lbl,
                    )) by {
                        reveal(CachedBranch::State::append_step);
                    }
                    reveal(CachedBranch::State::append_step);
                    assert(pre.branch.active_branch.can_append(
                        pre.branch.mini_allocator,
                        receipt,
                        keys,
                        msgs,
                        read_nodes,
                        write_nodes,
                    ));
                    assert(receipt.valid_for(
                        pre.branch.active_branch.root.unwrap(),
                        read_nodes,
                    ));
                    assert(receipt.needed_addrs() <= reads.dom()) by {
                        assert forall |addr: Address| #[trigger] receipt.needed_addrs().contains(addr)
                            implies reads.dom().contains(addr) by {
                            assert(read_nodes.contains_key(addr));
                            assert(reads.contains_key(addr));
                        }
                    }
                    assert(tight_reads.dom() =~= receipt.needed_addrs()) by {
                        assert forall |addr: Address| #[trigger] tight_reads.dom().contains(addr)
                            implies receipt.needed_addrs().contains(addr) by {
                            assert(tight_reads.contains_key(addr));
                            assert(tight_reads == reads.restrict(receipt.needed_addrs()));
                        }
                        assert forall |addr: Address| #[trigger] receipt.needed_addrs().contains(addr)
                            implies tight_reads.dom().contains(addr) by {
                            assert(reads.dom().contains(addr));
                            assert(tight_reads == reads.restrict(receipt.needed_addrs()));
                            assert(tight_reads.contains_key(addr));
                        }
                    }
                },
                _ => {
                    assert(false);
                },
            }
        } else {
            assert(tight_reads == Map::<Address, RawPage>::empty());
        }
    }

    assert(AtomicBranchState::State::next(pre.branch, post.branch, tight_atomic_lbl)) by {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let atomic_step = choose |step: AtomicBranchState::Step|
            AtomicBranchState::State::next_by(pre.branch, post.branch, atomic_lbl, step);
        match atomic_step {
            AtomicBranchState::Step::append_nonempty(new_active_branch) => {
                assert(AtomicBranchState::State::append_nonempty(
                    pre.branch,
                    post.branch,
                    atomic_lbl,
                    new_active_branch,
                )) by {
                    reveal(AtomicBranchState::State::append_nonempty);
                }
                reveal(AtomicBranchState::State::append_nonempty);
                assert(pre.branch.active_branch.root is Some);
                assert(init_root is None);
                let branch_lbl = CachedBranch::Label::Append{
                    mini_allocator: pre.branch.mini_allocator,
                    receipt,
                    keys,
                    msgs,
                    read_nodes,
                    write_nodes,
                };
                assert(CachedBranch::State::next(
                    pre.branch.active_branch,
                    new_active_branch,
                    branch_lbl,
                ));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                assert(CachedBranch::State::next_by(
                    pre.branch.active_branch,
                    new_active_branch,
                    branch_lbl,
                    CachedBranch::Step::append_step(),
                ));
                assert(CachedBranch::State::append_step(
                    pre.branch.active_branch,
                    new_active_branch,
                    branch_lbl,
                )) by {
                    reveal(CachedBranch::State::append_step);
                }
                reveal(CachedBranch::State::append_step);
                assert(pre.branch.active_branch.can_append(
                    pre.branch.mini_allocator,
                    receipt,
                    keys,
                    msgs,
                    read_nodes,
                    write_nodes,
                ));
                assert(receipt.valid_for(pre.branch.active_branch.root.unwrap(), read_nodes));
                assert(receipt.needed_addrs() <= reads.dom()) by {
                    assert forall |addr: Address| #[trigger] receipt.needed_addrs().contains(addr)
                        implies reads.dom().contains(addr) by {
                        assert(read_nodes.contains_key(addr));
                        assert(reads.contains_key(addr));
                    }
                }
                assert(tight_reads.dom() =~= receipt.needed_addrs()) by {
                    assert forall |addr: Address| #[trigger] tight_reads.dom().contains(addr)
                        implies receipt.needed_addrs().contains(addr) by {
                        assert(tight_reads.contains_key(addr));
                        assert(tight_reads == reads.restrict(receipt.needed_addrs()));
                    }
                    assert forall |addr: Address| #[trigger] receipt.needed_addrs().contains(addr)
                        implies tight_reads.dom().contains(addr) by {
                        assert(reads.dom().contains(addr));
                        assert(tight_reads == reads.restrict(receipt.needed_addrs()));
                        assert(tight_reads.contains_key(addr));
                    }
                }
                assert(receipt.valid_for(
                    pre.branch.active_branch.root.unwrap(),
                    tight_read_nodes,
                )) by {
                    assert(receipt.wf());
                    assert(receipt.root == pre.branch.active_branch.root.unwrap());
                    assert(receipt.needed_addrs() <= tight_read_nodes.dom()) by {
                        assert forall |addr: Address| #[trigger] receipt.needed_addrs().contains(addr)
                            implies tight_read_nodes.dom().contains(addr) by {
                            assert(tight_reads.contains_key(addr));
                            assert(tight_read_nodes.contains_key(addr));
                        }
                    }
                    assert forall |i: int| #![auto] 0 <= i < receipt.lines.len()
                        implies {
                            &&& tight_read_nodes.contains_key(receipt.lines[i].addr)
                            &&& tight_read_nodes[receipt.lines[i].addr]
                                == receipt.lines[i].node
                        } by {
                        let addr = receipt.lines[i].addr;
                        assert(receipt.needed_addrs().contains(addr));
                        assert(tight_reads.contains_key(addr));
                        assert(tight_reads[addr] == reads[addr]);
                        assert(tight_read_nodes[addr] == read_nodes[addr]);
                        assert(read_nodes[addr] == receipt.lines[i].node);
                    }
                }
                assert(crate::implementation::CachedBranch_v::loaded_append_ready(
                    receipt,
                    tight_read_nodes,
                    keys,
                    msgs,
                )) by {
                    assert(crate::implementation::CachedBranch_v::loaded_append_ready(
                        receipt,
                        read_nodes,
                        keys,
                        msgs,
                    ));
                    assert(receipt.valid_for(receipt.root, tight_read_nodes));
                }
                let tight_branch_lbl = CachedBranch::Label::Append{
                    mini_allocator: pre.branch.mini_allocator,
                    receipt,
                    keys,
                    msgs,
                    read_nodes: tight_read_nodes,
                    write_nodes,
                };
                assert(pre.branch.active_branch.can_append(
                    pre.branch.mini_allocator,
                    receipt,
                    keys,
                    msgs,
                    tight_read_nodes,
                    write_nodes,
                ));
                assert(CachedBranch::State::append_step(
                    pre.branch.active_branch,
                    new_active_branch,
                    tight_branch_lbl,
                )) by {
                    reveal(CachedBranch::State::append_step);
                }
                assert(CachedBranch::State::next_by(
                    pre.branch.active_branch,
                    new_active_branch,
                    tight_branch_lbl,
                    CachedBranch::Step::append_step(),
                )) by {
                    reveal(CachedBranch::State::next_by);
                }
                reveal(CachedBranch::State::next);
                assert(CachedBranch::State::next(
                    pre.branch.active_branch,
                    new_active_branch,
                    tight_branch_lbl,
                ));
                assert(AtomicBranchState::State::append_nonempty(
                    pre.branch,
                    post.branch,
                    tight_atomic_lbl,
                    new_active_branch,
                )) by {
                    reveal(AtomicBranchState::State::append_nonempty);
                }
                assert(AtomicBranchState::State::next_by(
                    pre.branch,
                    post.branch,
                    tight_atomic_lbl,
                    AtomicBranchState::Step::append_nonempty(new_active_branch),
                )) by {
                    reveal(AtomicBranchState::State::next_by);
                }
            },
            AtomicBranchState::Step::append_empty(new_active_branch) => {
                assert(AtomicBranchState::State::append_empty(
                    pre.branch,
                    post.branch,
                    atomic_lbl,
                    new_active_branch,
                )) by {
                    reveal(AtomicBranchState::State::append_empty);
                }
                reveal(AtomicBranchState::State::append_empty);
                assert(pre.branch.active_branch.root is None);
                assert(init_root is Some);
                assert(tight_reads == Map::<Address, RawPage>::empty());
                let branch_lbl = CachedBranch::Label::Initialize{
                    mini_allocator: pre.branch.mini_allocator,
                    init_root: init_root.unwrap(),
                    keys,
                    msgs,
                    write_nodes,
                };
                assert(CachedBranch::State::next(
                    pre.branch.active_branch,
                    new_active_branch,
                    branch_lbl,
                ));
                assert(AtomicBranchState::State::append_empty(
                    pre.branch,
                    post.branch,
                    tight_atomic_lbl,
                    new_active_branch,
                )) by {
                    reveal(AtomicBranchState::State::append_empty);
                }
                assert(AtomicBranchState::State::next_by(
                    pre.branch,
                    post.branch,
                    tight_atomic_lbl,
                    AtomicBranchState::Step::append_empty(new_active_branch),
                )) by {
                    reveal(AtomicBranchState::State::next_by);
                }
            },
            _ => {
                assert(false);
            },
        }
    }

    append_refines(
        pre,
        post,
        keys,
        msgs,
        receipt,
        init_root,
        tight_reads,
        writes,
    );
}

pub proof fn grow_refines(
    pre: UnifiedCacheBranchSource,
    post: UnifiedCacheBranchSource,
    new_root_addr: Address,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        pre.branch.metadata_loaded(),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.in_flight == pre.in_flight,
        post.in_flight_image == pre.in_flight_image,
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access{reads, writes},
        ),
        AtomicBranchState::State::next(
            pre.branch,
            post.branch,
            AtomicBranchState::Label::Grow{
                new_root_addr,
                read_nodes: to_branch_nodes(reads),
                write_nodes: to_branch_nodes(writes),
            },
        ),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            unified_cache_branch_i(pre),
            unified_cache_branch_i(post),
            CrashAwareCachingDiskBranch::Label::Internal,
        ),
        writes.dom() <= addresses_in_aus(pre.branch_projection_aus()),
        writes.dom() <= Set::new(|addr: Address| addr.wf()),
        post.branch_projection_aus() =~= pre.branch_projection_aus(),
        post.branch.seq_end() == pre.branch.seq_end(),
        post.branch.metadata_loaded(),
        post.branch.in_flight == pre.branch.in_flight,
        post.branch.prepared == pre.branch.prepared,
        inv(post),
{
    let cache_lbl = Cache::Label::Access{reads, writes};
    let atomic_lbl = AtomicBranchState::Label::Grow{
        new_root_addr,
        read_nodes: to_branch_nodes(reads),
        write_nodes: to_branch_nodes(writes),
    };
    let read_nodes = to_branch_nodes(reads);
    let write_nodes = to_branch_nodes(writes);
    let aus = pre.branch_projection_aus();
    let addrs = addresses_in_aus(aus);
    let projected_reads = reads.restrict(addrs);
    let projected_nodes = to_branch_nodes(projected_reads);

    Cache::State::inv_next(pre.cache, post.cache, cache_lbl);
    AtomicBranchState::State::wf_next(pre.branch, post.branch, atomic_lbl);
    AtomicBranchState::State::grow_preserves_backing_aus(pre.branch, post.branch, atomic_lbl);
    assert(post.superblock_loaded());
    assert(post.branch.metadata_loaded()) by {
        assert(post.branch.image == pre.branch.image);
        assert(post.branch.branch_summary == pre.branch.branch_summary);
    }
    assert(post.branch_projection_aus() =~= aus) by {
        assert(post.branch_projection_aus() == post.branch.owned_aus());
        assert(pre.branch_projection_aus() == pre.branch.owned_aus());
        assert(post.branch.owned_aus() == pre.branch.owned_aus()) by {
            assert(post.branch.branch_summary == pre.branch.branch_summary);
            assert(post.branch.mini_allocator.all_aus()
                == pre.branch.mini_allocator.all_aus());
        }
    }

    reveal(AtomicBranchState::State::next);
    reveal(AtomicBranchState::State::next_by);
    let atomic_step = choose |step: AtomicBranchState::Step|
        AtomicBranchState::State::next_by(pre.branch, post.branch, atomic_lbl, step);
    match atomic_step {
        AtomicBranchState::Step::grow(new_active_branch) => {
            assert(AtomicBranchState::State::grow(
                pre.branch,
                post.branch,
                atomic_lbl,
                new_active_branch,
            )) by {
                reveal(AtomicBranchState::State::grow);
            }
            reveal(AtomicBranchState::State::grow);
            let branch_lbl = CachedBranch::Label::Grow{
                mini_allocator: pre.branch.mini_allocator,
                new_root_addr,
                read_nodes,
                write_nodes,
            };
            assert(CachedBranch::State::next(
                pre.branch.active_branch,
                post.branch.active_branch,
                branch_lbl,
            ));
            reveal(CachedBranch::State::next);
            reveal(CachedBranch::State::next_by);
            assert(CachedBranch::State::next_by(
                pre.branch.active_branch,
                post.branch.active_branch,
                branch_lbl,
                CachedBranch::Step::grow_step(),
            ));
            assert(CachedBranch::State::grow_step(
                pre.branch.active_branch,
                post.branch.active_branch,
                branch_lbl,
            )) by {
                reveal(CachedBranch::State::grow_step);
            }
            reveal(CachedBranch::State::grow_step);
            assert(post.branch.active_branch == pre.branch.active_branch.grow(
                pre.branch.mini_allocator,
                new_root_addr,
                read_nodes,
                write_nodes,
            ));
            assert(post.branch.mini_allocator
                == pre.branch.mini_allocator.allocate(new_root_addr));
            assert(pre.branch.mini_allocator.can_allocate(new_root_addr));
            assert(pre.branch.active_branch.root is Some);
            assert(write_nodes == loaded_grow_write_nodes(
                pre.branch.active_branch.root.unwrap(),
                new_root_addr,
            ));
        },
        _ => {
            assert(false);
        },
    }

    assert(projected_reads <= project_cache_pages(pre.cache, aus)) by {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        assert(Cache::State::next_by(
            pre.cache,
            post.cache,
            cache_lbl,
            Cache::Step::access(),
        ));
        reveal(Cache::State::access);
        pre.cache.build_lookup_map_ensures();
        assert forall |addr: Address| #[trigger] projected_reads.contains_key(addr)
            implies {
                &&& project_cache_pages(pre.cache, aus).contains_key(addr)
                &&& projected_reads[addr] == project_cache_pages(pre.cache, aus)[addr]
            } by {
            assert(reads.contains_key(addr));
            assert(addrs.contains(addr));
            assert(pre.cache.valid_read(addr, reads[addr])) by {
                assert(cache_lbl->reads.contains_key(addr));
            }
            assert(cache_filled_addr(pre.cache, addr));
            assert(cache_filled_page(pre.cache, addr) == reads[addr]);
            assert(project_cache_pages(pre.cache, aus).contains_key(addr));
            assert(project_cache_pages(pre.cache, aus)[addr] == reads[addr]);
            assert(projected_reads[addr] == reads[addr]);
        }
    }

    assert(writes.dom() <= addrs) by {
        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
            implies addrs.contains(addr) by {
            assert(writes.contains_key(addr));
            assert(write_nodes.contains_key(addr));
            assert(write_nodes == loaded_grow_write_nodes(
                pre.branch.active_branch.root.unwrap(),
                new_root_addr,
            ));
            assert(addr == new_root_addr);
            assert(pre.branch.mini_allocator.can_allocate(new_root_addr));
            assert(pre.branch.mini_allocator.all_aus().contains(new_root_addr.au));
            assert(pre.branch.owned_aus().contains(new_root_addr.au));
            assert(pre.branch_projection_aus() == pre.branch.owned_aus());
            assert(addrs.contains(addr));
        }
    }
    assert(writes.dom() <= Set::new(|addr: Address| addr.wf())) by {
        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
            implies Set::new(|addr: Address| addr.wf()).contains(addr) by {
            assert(writes.contains_key(addr));
            assert(write_nodes.contains_key(addr));
            assert(write_nodes == loaded_grow_write_nodes(
                pre.branch.active_branch.root.unwrap(),
                new_root_addr,
            ));
            assert(addr == new_root_addr);
            assert(pre.branch.mini_allocator.can_allocate(new_root_addr));
            assert(new_root_addr.wf());
        }
    }

    active_root_in_branch_projection(pre);
    assert(projected_reads.contains_key(pre.branch.active_branch.root.unwrap())) by {
        assert(read_nodes.contains_key(pre.branch.active_branch.root.unwrap()));
        assert(reads.contains_key(pre.branch.active_branch.root.unwrap()));
        assert(addrs.contains(pre.branch.active_branch.root.unwrap()));
    }
    assert(to_branch_nodes(projected_reads)[pre.branch.active_branch.root.unwrap()]
        == read_nodes[pre.branch.active_branch.root.unwrap()]) by {
        assert(projected_reads[pre.branch.active_branch.root.unwrap()]
            == reads[pre.branch.active_branch.root.unwrap()]);
    }
    assert(crate::implementation::CachedBranch_v::loaded_line_wf(
        to_branch_nodes(projected_reads),
        pre.branch.active_branch.root.unwrap(),
    )) by {
        assert(crate::implementation::CachedBranch_v::loaded_line_wf(
            read_nodes,
            pre.branch.active_branch.root.unwrap(),
        ));
    }

    cache_access_restrict_reads_same_post(pre.cache, post.cache, reads, projected_reads, writes);
    cache_access_refines_caching_disk_access(
        pre.cache,
        post.cache,
        pre.disk,
        aus,
        projected_reads,
        writes,
    );
    assert(CachingDisk::State::next(
        pre.branch_caching_disk_i(),
        post.branch_caching_disk_i(),
        CachingDisk::Label::Access{reads: projected_reads, writes},
    )) by {
        assert(pre.branch_caching_disk_i() == adapter_caching_disk_i(pre.cache, pre.disk, aus));
        assert(post.branch_caching_disk_i() == adapter_caching_disk_i(post.cache, pre.disk, aus));
    }

    let inner_pre = pre.branch_caching_disk_state_i();
    let inner_post = post.branch_caching_disk_state_i();
    let branch_lbl = CachingDiskBranch::Label::Internal;
    assert(inner_pre.disk == pre.branch_caching_disk_i());
    assert(inner_post.disk == post.branch_caching_disk_i());
    assert(CachingDiskBranch::State::internal_grow(
        inner_pre,
        inner_post,
        branch_lbl,
        inner_post.disk,
        new_root_addr,
        projected_reads,
        writes,
    )) by {
        reveal(CachingDiskBranch::State::internal_grow);
        to_branch_nodes_restrict_submap(reads, addrs);
        let cached_lbl = CachedBranch::Label::Grow{
            mini_allocator: inner_pre.mini_allocator,
            new_root_addr,
            read_nodes: projected_nodes,
            write_nodes,
        };
        assert(CachedBranch::State::next(
            inner_pre.active_branch,
            inner_post.active_branch,
            cached_lbl,
        )) by {
            assert(CachedBranch::State::grow_step(
                inner_pre.active_branch,
                inner_post.active_branch,
                cached_lbl,
            )) by {
                reveal(CachedBranch::State::grow_step);
                assert(inner_pre.active_branch.can_grow(
                    inner_pre.mini_allocator,
                    new_root_addr,
                    projected_nodes,
                    write_nodes,
                ));
            }
            assert(CachedBranch::State::next_by(
                inner_pre.active_branch,
                inner_post.active_branch,
                cached_lbl,
                CachedBranch::Step::grow_step(),
            )) by {
                reveal(CachedBranch::State::next_by);
            }
            reveal(CachedBranch::State::next);
        }
    }
    assert(CachingDiskBranch::State::next_by(
        inner_pre,
        inner_post,
        branch_lbl,
        CachingDiskBranch::Step::internal_grow(
            inner_post.disk,
            new_root_addr,
            projected_reads,
            writes,
        ),
    )) by {
        reveal(CachingDiskBranch::State::next_by);
    }
    reveal(CachingDiskBranch::State::next);
    CachingDiskBranch::State::inv_next(inner_pre, inner_post, branch_lbl);

    let src = unified_cache_branch_i(pre);
    let dst = unified_cache_branch_i(post);
    let target_lbl = CrashAwareCachingDiskBranch::Label::Internal;
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(CrashAwareCachingDiskBranch::State::internal(
        src,
        dst,
        target_lbl,
        inner_post,
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::internal);
    }
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBranch::Step::internal(inner_post),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);
    src.next_refines(dst, target_lbl);

    assert(post.inv()) by {
        assert(post.branch.wf());
        assert(async_disk_superblock_page_wf(post.disk.content));
        assert(post.persistent_superblock_image_i() == pre.persistent_superblock_image_i());
        assert(post.persistent_superblock_image_i().wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.branch_caching_disk_i().inv());
        assert(post.in_flight is Some <==> post.branch.in_flight is Some);
        assert(post.in_flight is Some <==> post.in_flight_image is Some);
    }
    assert(post.semantic_inv());
    assert(inv(post));
}

pub proof fn split_refines(
    pre: UnifiedCacheBranchSource,
    post: UnifiedCacheBranchSource,
    new_child_addr: Address,
    receipt: LoadedPathReceipt,
    split_arg: SplitArg,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        pre.branch.metadata_loaded(),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.in_flight == pre.in_flight,
        post.in_flight_image == pre.in_flight_image,
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access{reads, writes},
        ),
        AtomicBranchState::State::next(
            pre.branch,
            post.branch,
            AtomicBranchState::Label::Split{
                new_child_addr,
                receipt,
                split_arg,
                read_nodes: to_branch_nodes(reads),
                write_nodes: to_branch_nodes(writes),
            },
        ),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            unified_cache_branch_i(pre),
            unified_cache_branch_i(post),
            CrashAwareCachingDiskBranch::Label::Internal,
        ),
        writes.dom() <= addresses_in_aus(pre.branch_projection_aus()),
        writes.dom() <= Set::new(|addr: Address| addr.wf()),
        post.branch_projection_aus() =~= pre.branch_projection_aus(),
        post.branch.seq_end() == pre.branch.seq_end(),
        post.branch.metadata_loaded(),
        post.branch.in_flight == pre.branch.in_flight,
        post.branch.prepared == pre.branch.prepared,
        inv(post),
{
    let cache_lbl = Cache::Label::Access{reads, writes};
    let atomic_lbl = AtomicBranchState::Label::Split{
        new_child_addr,
        receipt,
        split_arg,
        read_nodes: to_branch_nodes(reads),
        write_nodes: to_branch_nodes(writes),
    };
    let read_nodes = to_branch_nodes(reads);
    let write_nodes = to_branch_nodes(writes);
    let aus = pre.branch_projection_aus();
    let addrs = addresses_in_aus(aus);
    let projected_reads = reads.restrict(addrs);
    let projected_nodes = to_branch_nodes(projected_reads);

    Cache::State::inv_next(pre.cache, post.cache, cache_lbl);
    AtomicBranchState::State::wf_next(pre.branch, post.branch, atomic_lbl);
    AtomicBranchState::State::split_preserves_backing_aus(pre.branch, post.branch, atomic_lbl);
    assert(post.superblock_loaded());
    assert(post.branch.metadata_loaded()) by {
        assert(post.branch.image == pre.branch.image);
        assert(post.branch.branch_summary == pre.branch.branch_summary);
    }
    assert(post.branch_projection_aus() =~= aus) by {
        assert(post.branch_projection_aus() == post.branch.owned_aus());
        assert(pre.branch_projection_aus() == pre.branch.owned_aus());
        assert(post.branch.owned_aus() == pre.branch.owned_aus()) by {
            assert(post.branch.branch_summary == pre.branch.branch_summary);
            assert(post.branch.mini_allocator.all_aus()
                == pre.branch.mini_allocator.all_aus());
        }
    }

    reveal(AtomicBranchState::State::next);
    reveal(AtomicBranchState::State::next_by);
    let atomic_step = choose |step: AtomicBranchState::Step|
        AtomicBranchState::State::next_by(pre.branch, post.branch, atomic_lbl, step);
    match atomic_step {
        AtomicBranchState::Step::split(new_active_branch) => {
            assert(AtomicBranchState::State::split(
                pre.branch,
                post.branch,
                atomic_lbl,
                new_active_branch,
            )) by {
                reveal(AtomicBranchState::State::split);
            }
            reveal(AtomicBranchState::State::split);
            let branch_lbl = CachedBranch::Label::Split{
                mini_allocator: pre.branch.mini_allocator,
                new_child_addr,
                receipt,
                split_arg,
                read_nodes,
                write_nodes,
            };
            assert(CachedBranch::State::next(
                pre.branch.active_branch,
                post.branch.active_branch,
                branch_lbl,
            ));
            reveal(CachedBranch::State::next);
            reveal(CachedBranch::State::next_by);
            assert(CachedBranch::State::next_by(
                pre.branch.active_branch,
                post.branch.active_branch,
                branch_lbl,
                CachedBranch::Step::split_step(),
            ));
            assert(CachedBranch::State::split_step(
                pre.branch.active_branch,
                post.branch.active_branch,
                branch_lbl,
            )) by {
                reveal(CachedBranch::State::split_step);
            }
            reveal(CachedBranch::State::split_step);
            assert(post.branch.active_branch == pre.branch.active_branch.split(
                pre.branch.mini_allocator,
                new_child_addr,
                receipt,
                split_arg,
                read_nodes,
                write_nodes,
            ));
            assert(post.branch.mini_allocator
                == pre.branch.mini_allocator.allocate(new_child_addr));
            assert(pre.branch.mini_allocator.can_allocate(new_child_addr));
            assert(pre.branch.active_branch.root is Some);
            assert(receipt.valid_for(pre.branch.active_branch.root.unwrap(), read_nodes));
            assert(crate::implementation::CachedBranch_v::loaded_split_ready(
                receipt,
                read_nodes,
                split_arg,
            ));
            assert(write_nodes == loaded_split_write_nodes(
                receipt,
                read_nodes,
                split_arg,
                new_child_addr,
            ));
        },
        _ => {
            assert(false);
        },
    }

    assert(projected_reads <= project_cache_pages(pre.cache, aus)) by {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        assert(Cache::State::next_by(
            pre.cache,
            post.cache,
            cache_lbl,
            Cache::Step::access(),
        ));
        reveal(Cache::State::access);
        pre.cache.build_lookup_map_ensures();
        assert forall |addr: Address| #[trigger] projected_reads.contains_key(addr)
            implies {
                &&& project_cache_pages(pre.cache, aus).contains_key(addr)
                &&& projected_reads[addr] == project_cache_pages(pre.cache, aus)[addr]
            } by {
            assert(reads.contains_key(addr));
            assert(addrs.contains(addr));
            assert(pre.cache.valid_read(addr, reads[addr])) by {
                assert(cache_lbl->reads.contains_key(addr));
            }
            assert(cache_filled_addr(pre.cache, addr));
            assert(cache_filled_page(pre.cache, addr) == reads[addr]);
            assert(project_cache_pages(pre.cache, aus).contains_key(addr));
            assert(project_cache_pages(pre.cache, aus)[addr] == reads[addr]);
            assert(projected_reads[addr] == reads[addr]);
        }
    }

    assert forall |read_addr: Address| #[trigger] reads.contains_key(read_addr)
        implies pre.cache.valid_read(read_addr, reads[read_addr])
    by {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        assert(Cache::State::next_by(pre.cache, post.cache, cache_lbl, Cache::Step::access()));
        reveal(Cache::State::access);
        assert(cache_lbl->reads.contains_key(read_addr));
    }

    split_projection_preserves_loaded_split(pre, reads, receipt, split_arg, new_child_addr);
    assert(split_read_addrs(receipt) <= projected_reads.dom());
    assert(receipt.valid_for(pre.branch.active_branch.root.unwrap(), projected_nodes));
    assert(crate::implementation::CachedBranch_v::loaded_split_ready(
        receipt,
        projected_nodes,
        split_arg,
    ));
    assert(loaded_split_write_nodes(receipt, projected_nodes, split_arg, new_child_addr)
        == write_nodes) by {
        assert(loaded_split_write_nodes(receipt, projected_nodes, split_arg, new_child_addr)
            == loaded_split_write_nodes(receipt, read_nodes, split_arg, new_child_addr));
        assert(write_nodes == loaded_split_write_nodes(
            receipt,
            read_nodes,
            split_arg,
            new_child_addr,
        ));
    }

    assert(writes.dom() <= addrs) by {
        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
            implies addrs.contains(addr) by {
            assert(writes.contains_key(addr));
            assert(write_nodes.contains_key(addr));
            assert(write_nodes == loaded_split_write_nodes(
                receipt,
                read_nodes,
                split_arg,
                new_child_addr,
            ));
            if addr == new_child_addr {
                assert(pre.branch.mini_allocator.can_allocate(new_child_addr));
                assert(pre.branch.mini_allocator.all_aus().contains(new_child_addr.au));
                assert(pre.branch.owned_aus().contains(new_child_addr.au));
                assert(pre.branch_projection_aus() == pre.branch.owned_aus());
            } else if addr == receipt.child_addr() {
                active_split_child_in_branch_projection(pre, reads, receipt, split_arg);
            } else {
                assert(addr == receipt.target().addr);
                assert(receipt.needed_addrs().contains(addr)) by {
                    let i = receipt.lines.len() - 1;
                    assert(0 <= i < receipt.lines.len());
                    assert(receipt.lines[i].addr == addr);
                }
                active_receipt_needed_addr_in_branch_projection(pre, reads, receipt, addr);
            }
        }
    }
    assert(writes.dom() <= Set::new(|addr: Address| addr.wf())) by {
        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
            implies Set::new(|addr: Address| addr.wf()).contains(addr) by {
            assert(writes.contains_key(addr));
            assert(write_nodes.contains_key(addr));
            assert(write_nodes == loaded_split_write_nodes(
                receipt,
                read_nodes,
                split_arg,
                new_child_addr,
            ));
            if addr == new_child_addr {
                assert(pre.branch.mini_allocator.can_allocate(new_child_addr));
                assert(new_child_addr.wf());
            } else if addr == receipt.child_addr() {
                active_split_child_in_branch_projection(pre, reads, receipt, split_arg);
                assert(addr.wf());
            } else {
                let target_addr = receipt.target().addr;
                assert(addr == target_addr);
                assert(receipt.needed_addrs().contains(target_addr)) by {
                    let i = receipt.lines.len() - 1;
                    assert(0 <= i < receipt.lines.len());
                    assert(receipt.lines[i].addr == target_addr);
                }
                active_receipt_needed_addr_in_branch_projection(pre, reads, receipt, target_addr);
                assert(receipt.target().wf());
                assert(target_addr.wf());
                assert(addr.wf());
            }
        }
    }

    cache_access_restrict_reads_same_post(pre.cache, post.cache, reads, projected_reads, writes);
    cache_access_refines_caching_disk_access(
        pre.cache,
        post.cache,
        pre.disk,
        aus,
        projected_reads,
        writes,
    );
    assert(CachingDisk::State::next(
        pre.branch_caching_disk_i(),
        post.branch_caching_disk_i(),
        CachingDisk::Label::Access{reads: projected_reads, writes},
    )) by {
        assert(pre.branch_caching_disk_i() == adapter_caching_disk_i(pre.cache, pre.disk, aus));
        assert(post.branch_caching_disk_i() == adapter_caching_disk_i(post.cache, pre.disk, aus));
    }

    let inner_pre = pre.branch_caching_disk_state_i();
    let inner_post = post.branch_caching_disk_state_i();
    let branch_lbl = CachingDiskBranch::Label::Internal;
    assert(inner_pre.disk == pre.branch_caching_disk_i());
    assert(inner_post.disk == post.branch_caching_disk_i());
    assert(CachingDiskBranch::State::internal_split(
        inner_pre,
        inner_post,
        branch_lbl,
        inner_post.disk,
        new_child_addr,
        receipt,
        split_arg,
        projected_reads,
        writes,
    )) by {
        reveal(CachingDiskBranch::State::internal_split);
        to_branch_nodes_restrict_submap(reads, addrs);
        let cached_lbl = CachedBranch::Label::Split{
            mini_allocator: inner_pre.mini_allocator,
            new_child_addr,
            receipt,
            split_arg,
            read_nodes: projected_nodes,
            write_nodes,
        };
        assert(CachedBranch::State::next(
            inner_pre.active_branch,
            inner_post.active_branch,
            cached_lbl,
        )) by {
            assert(CachedBranch::State::split_step(
                inner_pre.active_branch,
                inner_post.active_branch,
                cached_lbl,
            )) by {
                reveal(CachedBranch::State::split_step);
                assert(inner_pre.active_branch.can_split(
                    inner_pre.mini_allocator,
                    new_child_addr,
                    receipt,
                    split_arg,
                    projected_nodes,
                    write_nodes,
                ));
            }
            assert(CachedBranch::State::next_by(
                inner_pre.active_branch,
                inner_post.active_branch,
                cached_lbl,
                CachedBranch::Step::split_step(),
            )) by {
                reveal(CachedBranch::State::next_by);
            }
            reveal(CachedBranch::State::next);
        }
    }
    assert(CachingDiskBranch::State::next_by(
        inner_pre,
        inner_post,
        branch_lbl,
        CachingDiskBranch::Step::internal_split(
            inner_post.disk,
            new_child_addr,
            receipt,
            split_arg,
            projected_reads,
            writes,
        ),
    )) by {
        reveal(CachingDiskBranch::State::next_by);
    }
    reveal(CachingDiskBranch::State::next);
    CachingDiskBranch::State::inv_next(inner_pre, inner_post, branch_lbl);

    let src = unified_cache_branch_i(pre);
    let dst = unified_cache_branch_i(post);
    let target_lbl = CrashAwareCachingDiskBranch::Label::Internal;
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(CrashAwareCachingDiskBranch::State::internal(
        src,
        dst,
        target_lbl,
        inner_post,
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::internal);
    }
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBranch::Step::internal(inner_post),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);
    src.next_refines(dst, target_lbl);

    assert(post.inv()) by {
        assert(post.branch.wf());
        assert(async_disk_superblock_page_wf(post.disk.content));
        assert(post.persistent_superblock_image_i() == pre.persistent_superblock_image_i());
        assert(post.persistent_superblock_image_i().wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.branch_caching_disk_i().inv());
        assert(post.in_flight is Some <==> post.branch.in_flight is Some);
        assert(post.in_flight is Some <==> post.in_flight_image is Some);
    }
    assert(post.semantic_inv());
    assert(inv(post));
}

pub proof fn seal_refines(
    pre: UnifiedCacheBranchSource,
    post: UnifiedCacheBranchSource,
    aux_ptr: Pointer,
    summary: Summary,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        pre.branch.metadata_loaded(),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.in_flight == pre.in_flight,
        post.in_flight_image == pre.in_flight_image,
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access{reads, writes},
        ),
        AtomicBranchState::State::next(
            pre.branch,
            post.branch,
            AtomicBranchState::Label::Seal{
                aux_ptr,
                summary,
                read_nodes: to_branch_nodes(reads),
                write_nodes: to_branch_nodes(writes),
            },
        ),
        forall |addr: Address| {
            &&& #[trigger] mini_allocator_allocated_addrs(
                pre.branch_caching_disk_state_i().mini_allocator,
            ).contains(addr)
            &&& filled_cache_status(pre.cache).contains_key(addr)
            &&& filled_cache_status(pre.cache)[addr] == PageStatus::Clean
            &&& !writes.contains_key(addr)
        } ==> false,
    ensures
        CrashAwareCachingDiskBranch::State::next(
            unified_cache_branch_i(pre),
            unified_cache_branch_i(post),
            CrashAwareCachingDiskBranch::Label::Internal,
        ),
        writes.dom() <= addresses_in_aus(pre.branch_projection_aus()),
        writes.dom() <= Set::new(|addr: Address| addr.wf()),
        post.branch_projection_aus() =~= pre.branch_projection_aus(),
        post.branch.seq_end() == pre.branch.seq_end(),
        post.branch.metadata_loaded(),
        post.branch.in_flight == pre.branch.in_flight,
        post.branch.prepared == pre.branch.prepared,
        inv(post),
{
    let cache_lbl = Cache::Label::Access{reads, writes};
    let atomic_lbl = AtomicBranchState::Label::Seal{
        aux_ptr,
        summary,
        read_nodes: to_branch_nodes(reads),
        write_nodes: to_branch_nodes(writes),
    };
    let read_nodes = to_branch_nodes(reads);
    let write_nodes = to_branch_nodes(writes);
    let aus = pre.branch_projection_aus();
    let addrs = addresses_in_aus(aus);
    let projected_reads = reads.restrict(addrs);
    let projected_nodes = to_branch_nodes(projected_reads);

    Cache::State::inv_next(pre.cache, post.cache, cache_lbl);
    AtomicBranchState::State::wf_next(pre.branch, post.branch, atomic_lbl);

    reveal(AtomicBranchState::State::next);
    reveal(AtomicBranchState::State::next_by);
    let atomic_step = choose |step: AtomicBranchState::Step|
        AtomicBranchState::State::next_by(pre.branch, post.branch, atomic_lbl, step);
    match atomic_step {
        AtomicBranchState::Step::seal() => {
            assert(AtomicBranchState::State::seal(pre.branch, post.branch, atomic_lbl)) by {
                reveal(AtomicBranchState::State::seal);
            }
            reveal(AtomicBranchState::State::seal);
            let root = pre.branch.active_branch.root.unwrap();
            let branch_lbl = CachedBranch::Label::Seal{
                mini_allocator: pre.branch.mini_allocator,
                aux_ptr,
                read_nodes,
                write_nodes,
            };
            assert(CachedBranch::State::next(
                pre.branch.active_branch,
                pre.branch.active_branch,
                branch_lbl,
            ));
            reveal(CachedBranch::State::next);
            reveal(CachedBranch::State::next_by);
            assert(CachedBranch::State::next_by(
                pre.branch.active_branch,
                pre.branch.active_branch,
                branch_lbl,
                CachedBranch::Step::seal_step(),
            ));
            assert(CachedBranch::State::seal_step(
                pre.branch.active_branch,
                pre.branch.active_branch,
                branch_lbl,
            )) by {
                reveal(CachedBranch::State::seal_step);
            }
            reveal(CachedBranch::State::seal_step);
            assert(pre.branch.active_branch.can_seal(
                pre.branch.mini_allocator,
                aux_ptr,
                read_nodes,
                write_nodes,
            ));
            assert(summary == pre.branch.mini_allocator.reserved_aus());
            assert(post.branch.image == AtomicBranchImage{
                sealed_roots: pre.branch.image.sealed_roots.push(root),
                seq_end: pre.branch.image.seq_end,
            });
            assert(post.branch.active_branch == CachedBranch::State::empty_active());
            assert(post.branch.mini_allocator == pre.branch.mini_allocator.prune(summary));
            assert(post.branch.branch_summary == pre.branch.branch_summary.insert(root.au, summary));
            assert(post.branch.seq_end == pre.branch.seq_end);
            assert(post.branch.in_flight == pre.branch.in_flight);
            assert(post.branch.prepared == pre.branch.prepared);
            assert(write_nodes == loaded_seal_write_nodes(
                root,
                read_nodes,
                aux_ptr,
                summary,
            ));
        },
        _ => {
            assert(false);
        },
    }

    let root = pre.branch.active_branch.root.unwrap();
    active_root_not_in_branch_summary(pre);
    pre.branch.mini_allocator.prune_preserves_wf(summary);
    summary_aus_insert_fresh(pre.branch.branch_summary, root.au, summary);
    assert(summary <= pre.branch.mini_allocator.all_aus()) by {
        assert forall |au: AU| #[trigger] summary.contains(au)
            implies pre.branch.mini_allocator.all_aus().contains(au) by {
            assert(summary == pre.branch.mini_allocator.reserved_aus());
            assert(pre.branch.mini_allocator.allocs.contains_key(au));
        }
    }
    assert(post.branch.owned_aus() =~= pre.branch.owned_aus()) by {
        assert(summary_aus(post.branch.branch_summary)
            == summary_aus(pre.branch.branch_summary) + summary);
        assert(post.branch.mini_allocator.all_aus()
            == pre.branch.mini_allocator.all_aus().difference(summary));
        assert forall |au: AU| #[trigger] post.branch.owned_aus().contains(au)
            implies pre.branch.owned_aus().contains(au) by {
            if summary_aus(post.branch.branch_summary).contains(au) {
                if summary_aus(pre.branch.branch_summary).contains(au) {
                } else {
                    assert(summary.contains(au));
                    assert(pre.branch.mini_allocator.all_aus().contains(au));
                }
            } else {
                assert(post.branch.mini_allocator.all_aus().contains(au));
                assert(pre.branch.mini_allocator.all_aus().contains(au));
            }
        }
        assert forall |au: AU| #[trigger] pre.branch.owned_aus().contains(au)
            implies post.branch.owned_aus().contains(au) by {
            if summary_aus(pre.branch.branch_summary).contains(au) {
                assert(summary_aus(post.branch.branch_summary).contains(au));
            } else {
                assert(pre.branch.mini_allocator.all_aus().contains(au));
                if summary.contains(au) {
                    assert(summary_aus(post.branch.branch_summary).contains(au));
                } else {
                    assert(post.branch.mini_allocator.all_aus().contains(au));
                }
            }
        }
    }
    assert(post.branch.metadata_loaded()) by {
        let post_roots = post.branch.image.sealed_roots;
        let pre_roots = pre.branch.image.sealed_roots;
        let post_root_aus = root_aus_up_to(post_roots, post_roots.len() as nat);
        assert forall |au: AU| #[trigger] post_root_aus.contains(au)
            implies post.branch.branch_summary.dom().contains(au)
        by {
            let i = root_aus_up_to_member_has_index(post_roots, post_roots.len() as nat, au);
            assert(post_roots[i].au == au);
            if i < pre_roots.len() {
                assert(post_roots[i] == pre_roots[i]);
                assert(pre.branch.metadata_loaded());
                root_aus_up_to_contains(pre_roots, pre_roots.len() as nat, i);
                assert(root_aus_up_to(pre_roots, pre_roots.len() as nat).contains(au));
                assert(pre.branch.branch_summary.dom().contains(au));
                assert(post.branch.branch_summary.contains_key(au));
            } else {
                assert(i == pre_roots.len());
                assert(post_roots[i] == root);
                assert(au == root.au);
                assert(post.branch.branch_summary.contains_key(au));
            }
        }
    }
    assert(post.superblock_loaded());
    assert(post.branch_projection_aus() =~= aus) by {
        assert(pre.branch_projection_aus() == pre.branch.owned_aus());
        assert(post.branch_projection_aus() == post.branch.owned_aus());
    }

    assert(projected_reads <= project_cache_pages(pre.cache, aus)) by {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        assert(Cache::State::next_by(
            pre.cache,
            post.cache,
            cache_lbl,
            Cache::Step::access(),
        ));
        reveal(Cache::State::access);
        pre.cache.build_lookup_map_ensures();
        assert forall |addr: Address| #[trigger] projected_reads.contains_key(addr)
            implies {
                &&& project_cache_pages(pre.cache, aus).contains_key(addr)
                &&& projected_reads[addr] == project_cache_pages(pre.cache, aus)[addr]
            } by {
            assert(reads.contains_key(addr));
            assert(addrs.contains(addr));
            assert(pre.cache.valid_read(addr, reads[addr])) by {
                assert(cache_lbl->reads.contains_key(addr));
            }
            assert(cache_filled_addr(pre.cache, addr));
            assert(cache_filled_page(pre.cache, addr) == reads[addr]);
            assert(project_cache_pages(pre.cache, aus).contains_key(addr));
            assert(project_cache_pages(pre.cache, aus)[addr] == reads[addr]);
            assert(projected_reads[addr] == reads[addr]);
        }
    }

    active_root_in_branch_projection(pre);
    assert(projected_reads.contains_key(root)) by {
        assert(crate::implementation::CachedBranch_v::loaded_line_wf(read_nodes, root));
        assert(read_nodes.contains_key(root));
        assert(reads.contains_key(root));
        assert(addrs.contains(root));
    }
    assert(projected_nodes[root] == read_nodes[root]) by {
        assert(projected_reads[root] == reads[root]);
    }
    assert(crate::implementation::CachedBranch_v::loaded_line_wf(projected_nodes, root)) by {
        assert(crate::implementation::CachedBranch_v::loaded_line_wf(read_nodes, root));
    }

    assert(writes.dom() <= addrs) by {
        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
            implies addrs.contains(addr) by {
            assert(writes.contains_key(addr));
            assert(write_nodes.contains_key(addr));
            assert(write_nodes == loaded_seal_write_nodes(
                root,
                read_nodes,
                aux_ptr,
                summary,
            ));
            if addr == root {
                assert(addrs.contains(addr));
            } else {
                assert(aux_ptr is Some);
                assert(addr == aux_ptr.unwrap());
                assert(pre.branch.active_branch.can_seal(
                    pre.branch.mini_allocator,
                    aux_ptr,
                    read_nodes,
                    write_nodes,
                ));
                assert(pre.branch.mini_allocator.reserved_aus().contains(addr.au));
                assert(pre.branch.mini_allocator.all_aus().contains(addr.au));
                assert(pre.branch.owned_aus().contains(addr.au));
                assert(pre.branch_projection_aus() == pre.branch.owned_aus());
            }
        }
    }
    assert(writes.dom() <= Set::new(|addr: Address| addr.wf())) by {
        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
            implies Set::new(|addr: Address| addr.wf()).contains(addr) by {
            assert(writes.contains_key(addr));
            assert(write_nodes.contains_key(addr));
            assert(write_nodes == loaded_seal_write_nodes(
                root,
                read_nodes,
                aux_ptr,
                summary,
            ));
            if addr == root {
                active_root_au_in_branch_mini_allocator(pre);
                assert(pre.branch.mini_allocator.all_aus().contains(root.au));
                assert(pre.branch.mini_allocator.wf());
                assert(pre.branch.mini_allocator.allocs.contains_key(root.au));
                assert(pre.branch.mini_allocator.allocs[root.au].wf());
                assert(pre.branch.mini_allocator.page_is_reserved(root));
                assert(pre.branch.mini_allocator.allocs[root.au].reserved.contains(root));
                assert(root.wf());
            } else {
                assert(aux_ptr is Some);
                assert(addr == aux_ptr.unwrap());
                assert(pre.branch.active_branch.can_seal(
                    pre.branch.mini_allocator,
                    aux_ptr,
                    read_nodes,
                    write_nodes,
                ));
                assert(pre.branch.mini_allocator.can_allocate(addr));
                assert(addr.wf());
            }
        }
    }

    cache_access_restrict_reads_same_post(pre.cache, post.cache, reads, projected_reads, writes);
    cache_access_refines_caching_disk_access(
        pre.cache,
        post.cache,
        pre.disk,
        aus,
        projected_reads,
        writes,
    );
    assert(CachingDisk::State::next(
        pre.branch_caching_disk_i(),
        post.branch_caching_disk_i(),
        CachingDisk::Label::Access{reads: projected_reads, writes},
    )) by {
        assert(pre.branch_caching_disk_i() == adapter_caching_disk_i(pre.cache, pre.disk, aus));
        assert(post.branch_caching_disk_i() == adapter_caching_disk_i(post.cache, pre.disk, aus));
    }
    CachingDisk::State::access_visible_effect(
        pre.branch_caching_disk_i(),
        post.branch_caching_disk_i(),
        projected_reads,
        writes,
    );
    assert(active_loaded_nodes_of(
            pre.branch_caching_disk_state_i().disk,
            pre.branch_caching_disk_state_i().mini_allocator,
        ).union_prefer_right(write_nodes)
        <= to_branch_nodes(post.branch_caching_disk_i().visible())) by {
        let old_nodes = active_loaded_nodes_of(
            pre.branch_caching_disk_state_i().disk,
            pre.branch_caching_disk_state_i().mini_allocator,
        );
        let post_visible_nodes = to_branch_nodes(post.branch_caching_disk_i().visible());
        assert forall |addr: Address| #[trigger] old_nodes.union_prefer_right(write_nodes).contains_key(addr)
            implies {
                &&& post_visible_nodes.contains_key(addr)
                &&& old_nodes.union_prefer_right(write_nodes)[addr]
                    == post_visible_nodes[addr]
            } by {
            if write_nodes.contains_key(addr) {
                assert(writes.contains_key(addr));
                assert(post.branch_caching_disk_i().visible().contains_key(addr));
                assert(post.branch_caching_disk_i().visible()[addr] == writes[addr]);
                assert(post_visible_nodes.contains_key(addr));
            } else {
                assert(old_nodes.contains_key(addr));
                assert(!writes.contains_key(addr));
                assert(to_branch_nodes(pre.branch_caching_disk_i().visible()).contains_key(addr));
                assert(old_nodes[addr] == to_branch_nodes(pre.branch_caching_disk_i().visible())[addr]);
                assert(post.branch_caching_disk_i().visible().contains_key(addr));
                assert(post.branch_caching_disk_i().visible()[addr]
                    == pre.branch_caching_disk_i().visible()[addr]);
                assert(to_branch_nodes(pre.branch_caching_disk_i().visible()).contains_key(addr));
                assert(old_nodes[addr]
                    == to_branch_nodes(pre.branch_caching_disk_i().visible())[addr]);
                assert(post_visible_nodes.contains_key(addr));
                assert(post_visible_nodes[addr]
                    == to_branch_nodes(pre.branch_caching_disk_i().visible())[addr]);
            }
        }
    }

    let inner_pre = pre.branch_caching_disk_state_i();
    let inner_post = post.branch_caching_disk_state_i();
    let branch_lbl = CachingDiskBranch::Label::Internal;
    assert(inner_pre.disk == pre.branch_caching_disk_i());
    assert(inner_post.disk == post.branch_caching_disk_i());
    assert(CachingDiskBranch::State::internal_seal(
        inner_pre,
        inner_post,
        branch_lbl,
        inner_post.disk,
        aux_ptr,
        projected_reads,
        writes,
    )) by {
        reveal(CachingDiskBranch::State::internal_seal);
        to_branch_nodes_restrict_submap(reads, addrs);
        let cached_lbl = CachedBranch::Label::Seal{
            mini_allocator: inner_pre.mini_allocator,
            aux_ptr,
            read_nodes: projected_nodes,
            write_nodes,
        };
        assert(CachedBranch::State::next(
            inner_pre.active_branch,
            inner_pre.active_branch,
            cached_lbl,
        )) by {
            assert(CachedBranch::State::seal_step(
                inner_pre.active_branch,
                inner_pre.active_branch,
                cached_lbl,
            )) by {
                reveal(CachedBranch::State::seal_step);
                assert(inner_pre.active_branch.can_seal(
                    inner_pre.mini_allocator,
                    aux_ptr,
                    projected_nodes,
                    write_nodes,
                )) by {
                    assert(projected_nodes[root] == read_nodes[root]);
                    assert(summary == inner_pre.mini_allocator.reserved_aus());
                    assert(write_nodes == loaded_seal_write_nodes(
                        root,
                        projected_nodes,
                        aux_ptr,
                        inner_pre.mini_allocator.reserved_aus(),
                    ));
                }
            }
            assert(CachedBranch::State::next_by(
                inner_pre.active_branch,
                inner_pre.active_branch,
                cached_lbl,
                CachedBranch::Step::seal_step(),
            )) by {
                reveal(CachedBranch::State::next_by);
            }
            reveal(CachedBranch::State::next);
        }
        assert(projected_reads.contains_key(root));
    }
    assert(CachingDiskBranch::State::next_by(
        inner_pre,
        inner_post,
        branch_lbl,
        CachingDiskBranch::Step::internal_seal(
            inner_post.disk,
            aux_ptr,
            projected_reads,
            writes,
        ),
    )) by {
        reveal(CachingDiskBranch::State::next_by);
    }
    reveal(CachingDiskBranch::State::next);
    CachingDiskBranch::State::inv_next(inner_pre, inner_post, branch_lbl);

    let src = unified_cache_branch_i(pre);
    let dst = unified_cache_branch_i(post);
    let target_lbl = CrashAwareCachingDiskBranch::Label::Internal;
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(CrashAwareCachingDiskBranch::State::internal(
        src,
        dst,
        target_lbl,
        inner_post,
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::internal);
    }
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBranch::Step::internal(inner_post),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);
    src.next_refines(dst, target_lbl);

    assert(post.inv()) by {
        assert(post.branch.wf());
        assert(async_disk_superblock_page_wf(post.disk.content));
        assert(post.persistent_superblock_image_i() == pre.persistent_superblock_image_i());
        assert(post.persistent_superblock_image_i().wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.branch_caching_disk_i().inv());
        assert(post.in_flight is Some <==> post.branch.in_flight is Some);
        assert(post.in_flight is Some <==> post.in_flight_image is Some);
    }
    assert(post.semantic_inv());
    assert(inv(post));
}

pub proof fn fill_aus_refines(
    pre: UnifiedCacheBranchSource,
    post: UnifiedCacheBranchSource,
    aus: Set<AU>,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        pre.branch.metadata_loaded(),
        post.cache == pre.cache,
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.in_flight == pre.in_flight,
        post.in_flight_image == pre.in_flight_image,
        aus.disjoint(pre.branch_projection_aus()),
        pre.branch_fill_aus_shared_projection_inv(aus),
        AtomicBranchState::State::next(
            pre.branch,
            post.branch,
            AtomicBranchState::Label::FillAUs{aus},
        ),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            unified_cache_branch_i(pre),
            unified_cache_branch_i(post),
            CrashAwareCachingDiskBranch::Label::InternalAlloc{
                allocs: aus,
                deallocs: Set::empty(),
            },
        ),
        post.branch_projection_aus() =~= pre.branch_projection_aus() + aus,
        post.branch.metadata_loaded(),
        post.branch.seq_end() == pre.branch.seq_end(),
        post.branch.in_flight == pre.branch.in_flight,
        post.branch.prepared == pre.branch.prepared,
        inv(post),
{
    let atomic_lbl = AtomicBranchState::Label::FillAUs{aus};
    AtomicBranchState::State::wf_next(pre.branch, post.branch, atomic_lbl);
    AtomicBranchState::State::fill_aus_effect(pre.branch, post.branch, atomic_lbl);
    assert(post.superblock_loaded());
    assert(post.persistent_superblock_image_i() == pre.persistent_superblock_image_i());
    assert(post.branch.metadata_loaded());
    mini_allocator_add_aus_preserves_all_aus(pre.branch.mini_allocator, aus);
    assert(post.branch.owned_aus() =~= pre.branch.owned_aus() + aus) by {
        assert(pre.branch.owned_aus()
            == summary_aus(pre.branch.branch_summary) + pre.branch.mini_allocator.all_aus());
        assert(post.branch.owned_aus()
            == summary_aus(post.branch.branch_summary) + post.branch.mini_allocator.all_aus());
        assert(post.branch.branch_summary == pre.branch.branch_summary);
        assert(post.branch.mini_allocator.all_aus()
            == pre.branch.mini_allocator.all_aus() + aus);
    }
    assert(post.branch_projection_aus() =~= pre.branch_projection_aus() + aus) by {
        assert(pre.branch_projection_aus() == pre.branch.owned_aus());
        assert(post.branch_projection_aus() == post.branch.owned_aus());
    }

    let empty = Set::<AU>::empty();
    let target_lbl = CrashAwareCachingDiskBranch::Label::InternalAlloc{
        allocs: aus,
        deallocs: empty,
    };
    let cdb_lbl = CachingDiskBranch::Label::InternalAlloc{
        allocs: aus,
        deallocs: empty,
    };
    let old_cdb = pre.branch_caching_disk_state_i();
    let new_cdb = post.branch_caching_disk_state_i();
    assert(new_cdb.disk == pre.branch_caching_disk_i_for_aus(
        pre.branch_projection_aus() + aus,
    )) by {
        assert(post.cache == pre.cache);
        assert(post.disk == pre.disk);
        assert(post.branch_projection_aus() =~= pre.branch_projection_aus() + aus);
        assert_maps_equal!(
            new_cdb.disk.cache,
            pre.branch_caching_disk_i_for_aus(pre.branch_projection_aus() + aus).cache,
            addr => {}
        );
        assert_maps_equal!(
            new_cdb.disk.status,
            pre.branch_caching_disk_i_for_aus(pre.branch_projection_aus() + aus).status,
            addr => {}
        );
        assert_maps_equal!(
            new_cdb.disk.persistent,
            pre.branch_caching_disk_i_for_aus(pre.branch_projection_aus() + aus).persistent,
            addr => {}
        );
    }
    assert(aus.disjoint(summary_aus(old_cdb.branch_summary))) by {
        assert(pre.branch_projection_aus() == pre.branch.owned_aus());
        assert(pre.branch.owned_aus()
            == summary_aus(pre.branch.branch_summary) + pre.branch.mini_allocator.all_aus());
        assert(old_cdb.branch_summary == pre.branch.branch_summary);
        assert forall |au: AU| #[trigger] aus.contains(au)
            implies !summary_aus(old_cdb.branch_summary).contains(au) by {
            if summary_aus(old_cdb.branch_summary).contains(au) {
                assert(pre.branch_projection_aus().contains(au));
                assert(false);
            }
        }
    }
    assert(aus.disjoint(old_cdb.mini_allocator.all_aus())) by {
        assert(pre.branch_projection_aus() == pre.branch.owned_aus());
        assert(pre.branch.owned_aus()
            == summary_aus(pre.branch.branch_summary) + pre.branch.mini_allocator.all_aus());
        assert(old_cdb.mini_allocator == pre.branch.mini_allocator);
        assert forall |au: AU| #[trigger] aus.contains(au)
            implies !old_cdb.mini_allocator.all_aus().contains(au) by {
            if old_cdb.mini_allocator.all_aus().contains(au) {
                assert(pre.branch_projection_aus().contains(au));
                assert(false);
            }
        }
    }
    assert(new_cdb.disk.inv());
    assert(old_cdb.disk.cache <= new_cdb.disk.cache) by {
        assert forall |addr: Address| #[trigger] old_cdb.disk.cache.contains_key(addr)
            implies new_cdb.disk.cache.contains_key(addr)
                && new_cdb.disk.cache[addr] == old_cdb.disk.cache[addr] by {
            assert(addresses_in_aus(pre.branch_projection_aus()).contains(addr));
            assert(addresses_in_aus(post.branch_projection_aus()).contains(addr));
        }
    }
    assert(old_cdb.disk.status <= new_cdb.disk.status) by {
        assert forall |addr: Address| #[trigger] old_cdb.disk.status.contains_key(addr)
            implies new_cdb.disk.status.contains_key(addr)
                && new_cdb.disk.status[addr] == old_cdb.disk.status[addr] by {
            assert(addresses_in_aus(pre.branch_projection_aus()).contains(addr));
            assert(addresses_in_aus(post.branch_projection_aus()).contains(addr));
        }
    }
    assert(old_cdb.disk.persistent <= new_cdb.disk.persistent) by {
        assert forall |addr: Address| #[trigger] old_cdb.disk.persistent.contains_key(addr)
            implies new_cdb.disk.persistent.contains_key(addr)
                && new_cdb.disk.persistent[addr] == old_cdb.disk.persistent[addr] by {
            assert(addresses_in_aus(pre.branch_projection_aus()).contains(addr));
            assert(addresses_in_aus(post.branch_projection_aus()).contains(addr));
        }
    }
    let filled_aus = summary_aus(pre.branch.branch_summary)
        + pre.branch.mini_allocator.all_aus() + aus;
    assert(post.branch_projection_aus() =~= filled_aus) by {
        assert(post.branch_projection_aus() == post.branch.owned_aus());
        assert(post.branch.owned_aus()
            == summary_aus(post.branch.branch_summary)
                + post.branch.mini_allocator.all_aus());
        assert(post.branch.branch_summary == pre.branch.branch_summary);
        assert(post.branch.mini_allocator.all_aus()
            == pre.branch.mini_allocator.all_aus() + aus);
    }
    assert(new_cdb.disk.cache.dom() <= addresses_in_aus(filled_aus)) by {
        assert(new_cdb.disk.cache.dom() <= addresses_in_aus(post.branch_projection_aus()));
    }
    assert(new_cdb.disk.status.dom() <= addresses_in_aus(filled_aus)) by {
        assert(new_cdb.disk.status.dom() <= addresses_in_aus(post.branch_projection_aus()));
    }
    assert(new_cdb.disk.persistent.dom() <= addresses_in_aus(filled_aus)) by {
        assert(new_cdb.disk.persistent.dom() <= addresses_in_aus(post.branch_projection_aus()));
    }
    assert(new_cdb.disk.cache.dom() - old_cdb.disk.cache.dom()
        <= addresses_in_aus(aus)) by {
        assert forall |addr: Address| #[trigger] (new_cdb.disk.cache.dom()
            - old_cdb.disk.cache.dom()).contains(addr)
            implies addresses_in_aus(aus).contains(addr) by {
            assert(new_cdb.disk.cache.contains_key(addr));
            assert(!old_cdb.disk.cache.contains_key(addr));
            assert(addresses_in_aus(post.branch_projection_aus()).contains(addr));
            if !addresses_in_aus(aus).contains(addr) {
                assert(addresses_in_aus(pre.branch_projection_aus()).contains(addr)) by {
                    assert(post.branch_projection_aus() =~= pre.branch_projection_aus() + aus);
                    assert(!aus.contains(addr.au));
                }
                assert(old_cdb.disk.cache.contains_key(addr));
                assert(false);
            }
        }
    }
    assert(new_cdb.disk.status.dom() - old_cdb.disk.status.dom()
        <= addresses_in_aus(aus)) by {
        assert forall |addr: Address| #[trigger] (new_cdb.disk.status.dom()
            - old_cdb.disk.status.dom()).contains(addr)
            implies addresses_in_aus(aus).contains(addr) by {
            assert(new_cdb.disk.status.contains_key(addr));
            assert(!old_cdb.disk.status.contains_key(addr));
            assert(addresses_in_aus(post.branch_projection_aus()).contains(addr));
            if !addresses_in_aus(aus).contains(addr) {
                assert(addresses_in_aus(pre.branch_projection_aus()).contains(addr)) by {
                    assert(post.branch_projection_aus() =~= pre.branch_projection_aus() + aus);
                    assert(!aus.contains(addr.au));
                }
                assert(old_cdb.disk.status.contains_key(addr));
                assert(false);
            }
        }
    }
    assert(new_cdb.disk.persistent.dom() - old_cdb.disk.persistent.dom()
        <= addresses_in_aus(aus)) by {
        assert forall |addr: Address| #[trigger] (new_cdb.disk.persistent.dom()
            - old_cdb.disk.persistent.dom()).contains(addr)
            implies addresses_in_aus(aus).contains(addr) by {
            assert(new_cdb.disk.persistent.contains_key(addr));
            assert(!old_cdb.disk.persistent.contains_key(addr));
            assert(addresses_in_aus(post.branch_projection_aus()).contains(addr));
            if !addresses_in_aus(aus).contains(addr) {
                assert(addresses_in_aus(pre.branch_projection_aus()).contains(addr)) by {
                    assert(post.branch_projection_aus() =~= pre.branch_projection_aus() + aus);
                    assert(!aus.contains(addr.au));
                }
                assert(old_cdb.disk.persistent.contains_key(addr));
                assert(false);
            }
        }
    }
    assert(CachingDiskBranch::State::internal_fill_au(
        old_cdb,
        new_cdb,
        cdb_lbl,
        aus,
        new_cdb.disk,
    )) by {
        reveal(CachingDiskBranch::State::internal_fill_au);
    }
    assert(CachingDiskBranch::State::next_by(
        old_cdb,
        new_cdb,
        cdb_lbl,
        CachingDiskBranch::Step::internal_fill_au(aus, new_cdb.disk),
    )) by {
        reveal(CachingDiskBranch::State::next_by);
    }
    reveal(CachingDiskBranch::State::next);

    let src = unified_cache_branch_i(pre);
    let dst = unified_cache_branch_i(post);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(dst.prepared == src.prepared);
    assert(CrashAwareCachingDiskBranch::State::internal_alloc(
        src,
        dst,
        target_lbl,
        new_cdb,
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::internal_alloc);
    }
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBranch::Step::internal_alloc(new_cdb),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);
    src.next_refines(dst, target_lbl);

    assert(post.inv()) by {
        assert(post.branch.wf());
        assert(async_disk_superblock_page_wf(post.disk.content));
        assert(post.persistent_superblock_image_i().wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.branch_caching_disk_i().inv());
        assert(post.branch.persistent_image.sealed_roots
            == post.persistent_superblock_image_i().branch_roots);
        assert(post.branch.persistent_image.seq_end
            == post.persistent_superblock_image_i().branch_seq_end);
        assert(post.in_flight is Some <==> post.branch.in_flight is Some);
        assert(post.in_flight is Some <==> post.in_flight_image is Some);
    }
    assert(post.semantic_inv());
    assert(inv(post));
}

pub proof fn observe_persisted_roots_refines(
    pre: UnifiedCacheBranchSource,
    post: UnifiedCacheBranchSource,
    target_count: nat,
    aus: Set<AU>,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        pre.branch.metadata_loaded(),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.in_flight == pre.in_flight,
        post.in_flight_image == pre.in_flight_image,
        aus == sealed_summary_aus_between(
            pre.branch.image.sealed_roots,
            pre.branch.branch_summary,
            pre.branch.persisted_root_count,
            target_count,
        ),
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::EvictableCheck{aus},
        ),
        AtomicBranchState::State::next(
            pre.branch,
            post.branch,
            AtomicBranchState::Label::ObservePersistedRoots{target_count},
        ),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            unified_cache_branch_i(pre),
            unified_cache_branch_i(post),
            CrashAwareCachingDiskBranch::Label::Internal,
        ),
        post.cache == pre.cache,
        post.branch_projection_aus() =~= pre.branch_projection_aus(),
        post.branch.metadata_loaded(),
        post.branch.seq_end() == pre.branch.seq_end(),
        post.branch.in_flight == pre.branch.in_flight,
        post.branch.prepared == pre.branch.prepared,
        inv(post),
{
    let cache_lbl = Cache::Label::EvictableCheck{aus};
    let atomic_lbl = AtomicBranchState::Label::ObservePersistedRoots{target_count};

    Cache::State::inv_next(pre.cache, post.cache, cache_lbl);
    AtomicBranchState::State::wf_next(pre.branch, post.branch, atomic_lbl);

    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let cache_step = choose |step: Cache::Step|
        Cache::State::next_by(pre.cache, post.cache, cache_lbl, step);
    match cache_step {
        Cache::Step::evictable() => {
            assert(Cache::State::evictable(pre.cache, post.cache, cache_lbl)) by {
                reveal(Cache::State::evictable);
            }
            reveal(Cache::State::evictable);
            assert(post.cache == pre.cache);
        },
        _ => {
            assert(false);
        },
    }

    reveal(AtomicBranchState::State::next);
    reveal(AtomicBranchState::State::next_by);
    let atomic_step = choose |step: AtomicBranchState::Step|
        AtomicBranchState::State::next_by(pre.branch, post.branch, atomic_lbl, step);
    match atomic_step {
        AtomicBranchState::Step::observe_persisted_roots() => {
            assert(AtomicBranchState::State::observe_persisted_roots(
                pre.branch,
                post.branch,
                atomic_lbl,
            )) by {
                reveal(AtomicBranchState::State::observe_persisted_roots);
            }
            reveal(AtomicBranchState::State::observe_persisted_roots);
            assert(post.branch.image == pre.branch.image);
            assert(post.branch.persistent_image == pre.branch.persistent_image);
            assert(post.branch.in_flight == pre.branch.in_flight);
            assert(post.branch.prepared == pre.branch.prepared);
            assert(post.branch.branch_summary == pre.branch.branch_summary);
            assert(post.branch.persisted_root_count == target_count);
            assert(post.branch.active_branch == pre.branch.active_branch);
            assert(post.branch.mini_allocator == pre.branch.mini_allocator);
            assert(post.branch.seq_end == pre.branch.seq_end);
        },
        _ => {
            assert(false);
        },
    }

    assert(post.superblock_loaded());
    assert(post.persistent_superblock_image_i() == pre.persistent_superblock_image_i());
    assert(post.branch.metadata_loaded()) by {
        assert(post.branch.image == pre.branch.image);
        assert(post.branch.branch_summary == pre.branch.branch_summary);
        assert(pre.branch.metadata_loaded());
    }
    assert(post.branch.owned_aus() =~= pre.branch.owned_aus()) by {
        assert(post.branch.branch_summary == pre.branch.branch_summary);
        assert(post.branch.mini_allocator == pre.branch.mini_allocator);
    }
    assert(post.branch_projection_aus() =~= pre.branch_projection_aus()) by {
        assert(pre.branch_projection_aus() == pre.branch.owned_aus());
        assert(post.branch_projection_aus() == post.branch.owned_aus());
    }

    cache_evictable_refines_observe_clean_aus(
        pre.cache,
        pre.disk,
        pre.branch_projection_aus(),
        aus,
    );
    assert(CachingDisk::State::next(
        pre.branch_caching_disk_i(),
        pre.branch_caching_disk_i(),
        CachingDisk::Label::ObserveCleanAUs{aus},
    ));

    assert(post.branch_caching_disk_i() == pre.branch_caching_disk_i()) by {
        assert(post.cache == pre.cache);
        assert(post.disk == pre.disk);
        assert(post.branch_projection_aus() =~= pre.branch_projection_aus());
        assert_maps_equal!(
            post.branch_caching_disk_i().cache,
            pre.branch_caching_disk_i().cache,
            addr => {}
        );
        assert_maps_equal!(
            post.branch_caching_disk_i().status,
            pre.branch_caching_disk_i().status,
            addr => {}
        );
        assert_maps_equal!(
            post.branch_caching_disk_i().persistent,
            pre.branch_caching_disk_i().persistent,
            addr => {
                if post.branch_caching_disk_i().persistent.contains_key(addr) {
                    assert(pre.branch_caching_disk_i().persistent.contains_key(addr));
                }
                if pre.branch_caching_disk_i().persistent.contains_key(addr) {
                    assert(post.branch_caching_disk_i().persistent.contains_key(addr));
                }
            }
        );
    }

    let inner_pre = pre.branch_caching_disk_state_i();
    let inner_post = post.branch_caching_disk_state_i();
    assert(inner_pre.disk == pre.branch_caching_disk_i());
    assert(inner_post.disk == pre.branch_caching_disk_i());
    assert(inner_pre.sealed_roots == pre.branch.image.sealed_roots);
    assert(inner_post.sealed_roots == inner_pre.sealed_roots);
    assert(inner_post.branch_summary == inner_pre.branch_summary);
    assert(inner_post.metadata_loaded == inner_pre.metadata_loaded);
    assert(inner_pre.metadata_loaded);
    assert(inner_post.persisted_root_count == target_count);
    assert(inner_post.active_branch == inner_pre.active_branch);
    assert(inner_post.mini_allocator == inner_pre.mini_allocator);
    assert(inner_post.seq_end == inner_pre.seq_end);
    assert(aus == sealed_summary_aus_between(
        inner_pre.sealed_roots,
        inner_pre.branch_summary,
        inner_pre.persisted_root_count,
        target_count,
    ));
    assert(CachingDiskBranch::State::observe_persisted_roots(
        inner_pre,
        inner_post,
        CachingDiskBranch::Label::Internal,
        target_count,
    )) by {
        reveal(CachingDiskBranch::State::observe_persisted_roots);
    }
    assert(CachingDiskBranch::State::next_by(
        inner_pre,
        inner_post,
        CachingDiskBranch::Label::Internal,
        CachingDiskBranch::Step::observe_persisted_roots(target_count),
    )) by {
        reveal(CachingDiskBranch::State::next_by);
    }
    reveal(CachingDiskBranch::State::next);
    CachingDiskBranch::State::inv_next(inner_pre, inner_post, CachingDiskBranch::Label::Internal);

    let src = unified_cache_branch_i(pre);
    let dst = unified_cache_branch_i(post);
    let target_lbl = CrashAwareCachingDiskBranch::Label::Internal;
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(dst.prepared == src.prepared);
    assert(CrashAwareCachingDiskBranch::State::internal(
        src,
        dst,
        target_lbl,
        inner_post,
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::internal);
    }
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBranch::Step::internal(inner_post),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);
    src.next_refines(dst, target_lbl);

    assert(post.inv()) by {
        assert(post.branch.wf());
        assert(async_disk_superblock_page_wf(post.disk.content));
        assert(post.persistent_superblock_image_i().wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.branch_caching_disk_i().inv());
        assert(post.branch.persistent_image.sealed_roots
            == post.persistent_superblock_image_i().branch_roots);
        assert(post.branch.persistent_image.seq_end
            == post.persistent_superblock_image_i().branch_seq_end);
        assert(post.in_flight is Some <==> post.branch.in_flight is Some);
        assert(post.in_flight is Some <==> post.in_flight_image is Some);
    }
    assert(post.semantic_inv());
    assert(inv(post));
}

pub proof fn commit_start_refines(
    pre: UnifiedCacheBranchSource,
    post: UnifiedCacheBranchSource,
    branch_image: AtomicBranchImage,
    reads: Map<Address, RawPage>,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        pre.branch.metadata_loaded(),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.in_flight is Some,
        post.in_flight_image is Some,
        post.in_flight_image.unwrap().wf(),
        post.in_flight_image.unwrap().branch_roots == branch_image.sealed_roots,
        post.in_flight_image.unwrap().branch_seq_end == branch_image.seq_end,
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access{reads, writes: Map::empty()},
        ),
        AtomicBranchState::State::next(
            pre.branch,
            post.branch,
            AtomicBranchState::Label::CommitStart{branch_image},
        ),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            unified_cache_branch_i(pre),
            unified_cache_branch_i(post),
            CrashAwareCachingDiskBranch::Label::CommitStart{
                new_boundary_lsn: branch_image.seq_end,
                sealed_roots: branch_image.sealed_roots,
            },
        ),
        inv(post),
{
    let empty_writes = Map::<Address, RawPage>::empty();
    let cache_lbl = Cache::Label::Access{reads, writes: empty_writes};
    let atomic_lbl = AtomicBranchState::Label::CommitStart{branch_image};

    AtomicBranchState::State::wf_next(pre.branch, post.branch, atomic_lbl);
    AtomicBranchState::State::commit_start_effect(pre.branch, post.branch, atomic_lbl);
    Cache::State::inv_next(pre.cache, post.cache, cache_lbl);

    let aus = pre.branch_projection_aus();
    assert(post.superblock_loaded());
    assert(post.branch.metadata_loaded()) by {
        assert(post.branch.image == pre.branch.image);
        assert(post.branch.branch_summary == pre.branch.branch_summary);
    }
    assert(post.branch_projection_aus() =~= aus) by {
        assert(post.branch.branch_summary == pre.branch.branch_summary);
        assert(post.branch.mini_allocator == pre.branch.mini_allocator);
    }
    projected_cache_read_only_access_unchanged(pre.cache, post.cache, aus, reads);
    assert(post.branch_caching_disk_i() == pre.branch_caching_disk_i()) by {
        assert_maps_equal!(
            post.branch_caching_disk_i().cache,
            pre.branch_caching_disk_i().cache,
            addr => {
                assert(addresses_in_aus(post.branch_projection_aus()).contains(addr)
                    <==> addresses_in_aus(aus).contains(addr));
            }
        );
        assert_maps_equal!(
            post.branch_caching_disk_i().status,
            pre.branch_caching_disk_i().status,
            addr => {
                assert(addresses_in_aus(post.branch_projection_aus()).contains(addr)
                    <==> addresses_in_aus(aus).contains(addr));
            }
        );
        assert_maps_equal!(
            post.branch_caching_disk_i().persistent,
            pre.branch_caching_disk_i().persistent,
            addr => {
                assert(addresses_in_aus(post.branch_projection_aus()).contains(addr)
                    <==> addresses_in_aus(aus).contains(addr));
            }
        );
    }
    assert(post.branch_caching_disk_state_i() == pre.branch_caching_disk_state_i()) by {
        assert(post.branch.image == pre.branch.image);
        assert(post.branch.branch_summary == pre.branch.branch_summary);
        assert(post.branch.persisted_root_count == pre.branch.persisted_root_count);
        assert(post.branch.active_branch == pre.branch.active_branch);
        assert(post.branch.mini_allocator == pre.branch.mini_allocator);
        assert(post.branch.seq_end == pre.branch.seq_end);
    }

    let src = unified_cache_branch_i(pre);
    let dst = unified_cache_branch_i(post);
    let target_lbl = CrashAwareCachingDiskBranch::Label::CommitStart{
        new_boundary_lsn: branch_image.seq_end,
        sealed_roots: branch_image.sealed_roots,
    };
    let frozen = CachingDiskBranchMetadata{
        sealed_roots: branch_image.sealed_roots,
        seq_end: branch_image.seq_end,
    };
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(pre.branch.in_flight is None) by {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        assert(AtomicBranchState::State::next_by(
            pre.branch,
            post.branch,
            atomic_lbl,
            AtomicBranchState::Step::commit_start(),
        ));
        reveal(AtomicBranchState::State::commit_start);
        assert(AtomicBranchState::State::commit_start(pre.branch, post.branch, atomic_lbl));
    }
    assert(src.frozen is None);
    assert(dst.frozen == Option::Some(frozen));
    assert(!dst.prepared);

    assert(CrashAwareCachingDiskBranch::State::commit_start(src, dst, target_lbl)) by {
        reveal(CrashAwareCachingDiskBranch::State::commit_start);
        assert(src.ephemeral is Known);
        assert(src.frozen is None);
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        assert(AtomicBranchState::State::next_by(
            pre.branch,
            post.branch,
            atomic_lbl,
            AtomicBranchState::Step::commit_start(),
        ));
        reveal(AtomicBranchState::State::commit_start);
        assert(AtomicBranchState::State::commit_start(pre.branch, post.branch, atomic_lbl));
        if branch_image == pre.branch.persistent_image {
            let persistent = src.persistent.metadata();
            assert(persistent.sealed_roots == branch_image.sealed_roots);
            assert(persistent.seq_end == branch_image.seq_end);
        } else {
            assert(pre.branch.metadata_loaded());
            assert(pre.branch.active_branch.root is None);
            assert(branch_image == pre.branch.freeze_image());
            assert(frozen == pre.branch_caching_disk_state_i().freeze_metadata());
            assert(CachingDiskBranch::State::freeze_as(
                pre.branch_caching_disk_state_i(),
                pre.branch_caching_disk_state_i(),
                CachingDiskBranch::Label::FreezeAsLabel{image: frozen},
            )) by {
                reveal(CachingDiskBranch::State::freeze_as);
            }
            assert(CachingDiskBranch::State::next_by(
                pre.branch_caching_disk_state_i(),
                pre.branch_caching_disk_state_i(),
                CachingDiskBranch::Label::FreezeAsLabel{image: frozen},
                CachingDiskBranch::Step::freeze_as(),
            )) by {
                reveal(CachingDiskBranch::State::next_by);
            }
            reveal(CachingDiskBranch::State::next);
        }
    }
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBranch::Step::commit_start(),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);
    src.next_refines(dst, target_lbl);

    assert(post.inv()) by {
        assert(post.branch.wf());
        assert(async_disk_superblock_page_wf(post.disk.content));
        assert(post.persistent_superblock_image_i() == pre.persistent_superblock_image_i());
        assert(post.persistent_superblock_image_i().wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.branch_caching_disk_i().inv());
        assert(post.branch.persistent_image == pre.branch.persistent_image);
        assert(post.in_flight is Some <==> post.branch.in_flight is Some);
        assert(post.in_flight is Some <==> post.in_flight_image is Some);
    }
    assert(post.semantic_inv());
    assert(inv(post));
}

pub proof fn commit_prepared_refines(
    pre: UnifiedCacheBranchSource,
    post: UnifiedCacheBranchSource,
)
    requires
        inv(pre),
        post.cache == pre.cache,
        post.disk.content == pre.disk.content,
        post.disk.inv(),
        post.persistent_image == pre.persistent_image,
        post.in_flight == pre.in_flight,
        post.in_flight_image == pre.in_flight_image,
        !pre.branch.prepared,
        AtomicBranchState::State::next(
            pre.branch,
            post.branch,
            AtomicBranchState::Label::CommitPrepared,
        ),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            unified_cache_branch_i(pre),
            unified_cache_branch_i(post),
            CrashAwareCachingDiskBranch::Label::FreezePrepared,
        ),
        inv(post),
{
    let atomic_lbl = AtomicBranchState::Label::CommitPrepared;

    AtomicBranchState::State::wf_next(pre.branch, post.branch, atomic_lbl);
    reveal(AtomicBranchState::State::next);
    reveal(AtomicBranchState::State::next_by);
    assert(AtomicBranchState::State::next_by(
        pre.branch,
        post.branch,
        atomic_lbl,
        AtomicBranchState::Step::commit_prepared(),
    ));
    assert(AtomicBranchState::State::commit_prepared(
        pre.branch,
        post.branch,
        atomic_lbl,
    )) by {
        reveal(AtomicBranchState::State::commit_prepared);
    }
    assert(post.branch == AtomicBranchState::State{
        prepared: true,
        ..pre.branch
    });
    assert(post.branch.in_flight == pre.branch.in_flight);
    assert(post.branch.persistent_image == pre.branch.persistent_image);
    assert(post.branch.image == pre.branch.image);
    assert(post.branch.branch_summary == pre.branch.branch_summary);
    assert(post.branch.persisted_root_count == pre.branch.persisted_root_count);
    assert(post.branch.active_branch == pre.branch.active_branch);
    assert(post.branch.mini_allocator == pre.branch.mini_allocator);
    assert(post.branch.seq_end == pre.branch.seq_end);

    assert(post.superblock_loaded() == pre.superblock_loaded());
    assert(pre.superblock_loaded()) by {
        if !pre.superblock_loaded() {
            assert(pre.in_flight is None);
            assert(pre.branch.in_flight is None);
        }
    }
    assert(post.persistent_superblock_image_i()
        == pre.persistent_superblock_image_i()) by {
        if pre.persistent_image is Some {
            assert(post.persistent_image == pre.persistent_image);
        } else {
            assert(post.disk.content == pre.disk.content);
        }
    }
    assert(post.branch_projection_aus() =~= pre.branch_projection_aus()) by {
        assert(post.branch.branch_summary == pre.branch.branch_summary);
        assert(post.branch.mini_allocator == pre.branch.mini_allocator);
    }
    assert(post.branch_caching_disk_i() == pre.branch_caching_disk_i()) by {
        assert_maps_equal!(
            post.branch_caching_disk_i().cache,
            pre.branch_caching_disk_i().cache,
            addr => {}
        );
        assert_maps_equal!(
            post.branch_caching_disk_i().status,
            pre.branch_caching_disk_i().status,
            addr => {}
        );
        assert_maps_equal!(
            post.branch_caching_disk_i().persistent,
            pre.branch_caching_disk_i().persistent,
            addr => {
                if post.branch_caching_disk_i().persistent.contains_key(addr) {
                    assert(pre.branch_caching_disk_i().persistent.contains_key(addr));
                }
                if pre.branch_caching_disk_i().persistent.contains_key(addr) {
                    assert(post.branch_caching_disk_i().persistent.contains_key(addr));
                }
            }
        );
    }
    assert(post.branch_caching_disk_state_i() == pre.branch_caching_disk_state_i());

    let src = unified_cache_branch_i(pre);
    let dst = unified_cache_branch_i(post);
    let target_lbl = CrashAwareCachingDiskBranch::Label::FreezePrepared;
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(src.frozen is Some);
    assert(!src.prepared);
    assert(dst.prepared);
    assert(src.frozen == dst.frozen);
    assert(src.ephemeral == dst.ephemeral);
    assert(src.persistent == dst.persistent);
    assert(CachingDiskBranch::State::next(
        src.ephemeral->v,
        src.ephemeral->v,
        CachingDiskBranch::Label::FreezePrepared{image: src.frozen.unwrap()},
    )) by {
        reveal(CachingDiskBranch::State::next);
        reveal(CachingDiskBranch::State::next_by);
        assert(CachingDiskBranch::State::freeze_prepared(
            src.ephemeral->v,
            src.ephemeral->v,
            CachingDiskBranch::Label::FreezePrepared{image: src.frozen.unwrap()},
        )) by {
            reveal(CachingDiskBranch::State::freeze_prepared);
        }
        assert(CachingDiskBranch::State::next_by(
            src.ephemeral->v,
            src.ephemeral->v,
            CachingDiskBranch::Label::FreezePrepared{image: src.frozen.unwrap()},
            CachingDiskBranch::Step::freeze_prepared(),
        )) by {
            reveal(CachingDiskBranch::State::next_by);
        }
    }
    assert(CrashAwareCachingDiskBranch::State::freeze_prepared(
        src,
        dst,
        target_lbl,
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::freeze_prepared);
    }
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBranch::Step::freeze_prepared(),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);
    src.next_refines(dst, target_lbl);

    assert(post.inv()) by {
        assert(post.branch.wf());
        assert(async_disk_superblock_page_wf(post.disk.content));
        assert(post.persistent_superblock_image_i().wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.branch_caching_disk_i().inv());
        assert(post.in_flight is Some <==> post.branch.in_flight is Some);
        assert(post.in_flight is Some <==> post.in_flight_image is Some);
    }
    assert(post.semantic_inv());
    assert(inv(post));
}

pub proof fn commit_complete_refines(
    pre: UnifiedCacheBranchSource,
    post: UnifiedCacheBranchSource,
)
    requires
        inv(pre),
        post.cache == pre.cache,
        post.disk.content == pre.disk.content,
        post.disk.inv(),
        post.persistent_image == pre.in_flight_image,
        post.in_flight is None,
        post.in_flight_image is None,
        AtomicBranchState::State::next(
            pre.branch,
            post.branch,
            AtomicBranchState::Label::CommitComplete,
        ),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            unified_cache_branch_i(pre),
            unified_cache_branch_i(post),
            CrashAwareCachingDiskBranch::Label::CommitComplete,
        ),
        inv(post),
{
    let atomic_lbl = AtomicBranchState::Label::CommitComplete;

    AtomicBranchState::State::wf_next(pre.branch, post.branch, atomic_lbl);
    AtomicBranchState::State::commit_complete_effect(pre.branch, post.branch, atomic_lbl);

    assert(pre.in_flight is Some) by {
        assert(pre.in_flight is Some <==> pre.branch.in_flight is Some);
    }
    assert(pre.in_flight_image is Some) by {
        assert(pre.in_flight is Some <==> pre.in_flight_image is Some);
    }
    let image = pre.in_flight_image.unwrap();
    let branch_image = pre.branch.in_flight.unwrap();
    let frozen = CachingDiskBranchMetadata{
        sealed_roots: branch_image.sealed_roots,
        seq_end: branch_image.seq_end,
    };

    let src = unified_cache_branch_i(pre);
    let dst = unified_cache_branch_i(post);
    let target_lbl = CrashAwareCachingDiskBranch::Label::CommitComplete;

    assert(src.ephemeral is Known);
    assert(src.frozen == Option::Some(frozen));
    assert(src.prepared) by {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        assert(AtomicBranchState::State::next_by(
            pre.branch,
            post.branch,
            atomic_lbl,
            AtomicBranchState::Step::commit_complete(),
        ));
        reveal(AtomicBranchState::State::commit_complete);
    }
    assert(src.inv()) by {
        assert(pre.semantic_inv());
    }
    assert(frozen.sealed_roots.len() <= pre.branch.persisted_root_count) by {
        assert(src.prepared && src.ephemeral is Known && src.frozen is Some);
        assert(src.ephemeral->v == pre.branch_caching_disk_state_i());
        assert(src.ephemeral->v.persisted_root_count == pre.branch.persisted_root_count);
    }
    assert(post.branch.persisted_root_count == pre.branch.persisted_root_count) by {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        assert(AtomicBranchState::State::next_by(
            pre.branch,
            post.branch,
            atomic_lbl,
            AtomicBranchState::Step::commit_complete(),
        ));
        reveal(AtomicBranchState::State::commit_complete);
        let committed_root_count = pre.branch.in_flight.unwrap().sealed_roots.len() as nat;
        assert(!(pre.branch.persisted_root_count < committed_root_count));
    }
    assert(post.branch_caching_disk_state_i() == pre.branch_caching_disk_state_i()) by {
        assert(post.branch.image == pre.branch.image);
        assert(post.branch.branch_summary == pre.branch.branch_summary);
        assert(post.branch.active_branch == pre.branch.active_branch);
        assert(post.branch.mini_allocator == pre.branch.mini_allocator);
        assert(post.branch.seq_end == pre.branch.seq_end);
        assert(post.branch_projection_aus() =~= pre.branch_projection_aus()) by {
            assert(post.branch.metadata_loaded() == pre.branch.metadata_loaded());
            assert(post.branch.branch_summary == pre.branch.branch_summary);
            assert(post.branch.mini_allocator == pre.branch.mini_allocator);
        }
        assert_maps_equal!(
            post.branch_caching_disk_i().cache,
            pre.branch_caching_disk_i().cache,
            addr => {}
        );
        assert_maps_equal!(
            post.branch_caching_disk_i().persistent,
            pre.branch_caching_disk_i().persistent,
            addr => {
                if post.branch_caching_disk_i().persistent.contains_key(addr) {
                    assert(post.disk.content.contains_key(addr));
                    assert(pre.disk.content.contains_key(addr));
                    assert(post.disk.content[addr] == pre.disk.content[addr]);
                }
                if pre.branch_caching_disk_i().persistent.contains_key(addr) {
                    assert(pre.disk.content.contains_key(addr));
                    assert(post.disk.content.contains_key(addr));
                    assert(post.disk.content[addr] == pre.disk.content[addr]);
                }
            }
        );
        assert_maps_equal!(
            post.branch_caching_disk_i().status,
            pre.branch_caching_disk_i().status,
            addr => {}
        );
    }

    assert(image.branch_roots == branch_image.sealed_roots);
    assert(image.branch_seq_end == branch_image.seq_end);
    assert(post.superblock_loaded());
    assert(post.persistent_superblock_image_i() == image);
    assert(post.persistent_branch_i() == PersistentCachingDiskBranch::Metadata{
        meta: frozen,
    });
    assert(dst.ephemeral is Known);
    assert(dst.ephemeral->v == src.ephemeral->v);
    assert(dst.frozen is None);
    assert(!dst.prepared);
    assert(dst.persistent == PersistentCachingDiskBranch::Metadata{meta: frozen});

    let cdb_lbl = CachingDiskBranch::Label::FreezePrepared{image: frozen};
    assert(CachingDiskBranch::State::freeze_prepared(
        src.ephemeral->v,
        src.ephemeral->v,
        cdb_lbl,
    )) by {
        reveal(CachingDiskBranch::State::freeze_prepared);
        assert(src.ephemeral->v.sealed_roots.subrange(
            0,
            frozen.sealed_roots.len() as int,
        ) == frozen.sealed_roots);
    }
    assert(CachingDiskBranch::State::next_by(
        src.ephemeral->v,
        src.ephemeral->v,
        cdb_lbl,
        CachingDiskBranch::Step::freeze_prepared(),
    )) by {
        reveal(CachingDiskBranch::State::next_by);
    }
    reveal(CachingDiskBranch::State::next);

    assert(CrashAwareCachingDiskBranch::State::commit_complete(
        src,
        dst,
        target_lbl,
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::commit_complete);
    }
    assert(CrashAwareCachingDiskBranch::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBranch::Step::commit_complete(),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranch::State::next);
    src.next_refines(dst, target_lbl);

    assert(post.inv()) by {
        assert(post.branch.wf());
        assert(async_disk_superblock_page_wf(post.disk.content));
        assert(post.persistent_superblock_image_i().wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.branch_caching_disk_i().inv());
        assert(post.branch.persistent_image.sealed_roots
            == post.persistent_superblock_image_i().branch_roots);
        assert(post.branch.persistent_image.seq_end
            == post.persistent_superblock_image_i().branch_seq_end);
        assert(post.in_flight is Some <==> post.branch.in_flight is Some);
        assert(post.in_flight is Some <==> post.in_flight_image is Some);
    }
    assert(post.semantic_inv());
    assert(inv(post));
}

} // verus!
