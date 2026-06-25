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
use crate::betree::LinkedBranch_v::{
    LinkedBranch, Refinement_v as LinkedBranchRefinement,
};
use crate::betree::Utils_v::{
    lemma_set_subset_of_union_seq_of_sets, lemma_union_set_of_sets_contains,
    lemma_union_set_of_sets_subset,
};
use crate::disk::GenericDisk_v::{
    addrs_closed, to_aus_domain, Address, AU, Ranking, to_aus,
};
use crate::implementation::AbstractSuperblock_v::{
    AbstractSuperblockImage, abstract_superblock_raw_wf,
    empty_abstract_superblock_image, parse_abstract_superblock,
};
use crate::implementation::AllocationBranchStack_v::normalize_value;
use crate::implementation::AnotherAtomicState_v::{
    AtomicBranchImage, AtomicBranchState, query_receipts_read_addrs,
};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedBranch_v::{
    loaded_append_write_nodes, loaded_initialize_write_nodes,
    receipt_valid_implies_tail_valid, CachedBranch, LoadedBranch,
    LoadedPathReceipt,
};
use crate::implementation::CachingDiskAdapterRefinement_v::{
    cache_filled_addr, cache_filled_page,
    cache_access_refines_caching_disk_access,
    cache_disk_ops_begin_refines_caching_disk_internal,
    cache_disk_ops_end_refines_caching_disk_internal,
    caching_disk_i as adapter_caching_disk_i,
    project_cache_pages,
    project_cache_status,
    projected_cache_read_only_access_unchanged,
};
use crate::implementation::CachingDiskBranch_v::{
    active_loaded_nodes_of, branch_summary_reads_valid,
    completed_branch_summary_from_reads, empty_caching_disk_branch_image,
    empty_caching_disk_branch_image_wf,
    mini_allocator_allocated_addrs_subset_all_aus, sealed_nodes_of,
    to_branch_nodes, CachingDiskBranch, CachingDiskBranchImage,
    CachingDiskBranchMetadata,
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

    pub open spec fn branch_image_summary_i(
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

    pub open spec fn branch_image_summary_aus_i(
        disk_content: Map<Address, RawPage>,
        roots: Seq<Address>,
    ) -> Set<AU>
    {
        let nodes = to_branch_nodes(disk_content);
        Set::new(|au: AU| {
            exists |i: int| {
                &&& 0 <= i < roots.len()
                &&& crate::implementation::CachedBranch_v::root_summary_read_valid(roots[i], nodes)
                &&& #[trigger] crate::implementation::CachedBranch_v::root_summary_from_read(
                    roots[i],
                    nodes,
                ).contains(au)
            }
        })
    }

    pub open spec fn branch_image_projection_addrs_i(
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

    pub open spec fn branch_caching_disk_i(self) -> CachingDisk::State
    {
        adapter_caching_disk_i(self.cache, self.disk, self.branch_projection_aus())
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
            forall |addr: Address| {
                &&& #[trigger] responses.contains_key(addr)
                &&& addresses_in_aus(self.branch_projection_aus()).contains(addr)
            } ==> {
                &&& self.disk.content.contains_key(addr)
                &&& responses[addr] is ReadResp ==> responses[addr]->data
                    == self.disk.content[addr]
                &&& responses[addr] is WriteResp ==> {
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

pub open spec fn unified_cache_branch_i_lbl(
    lbl: AtomicBranchState::Label,
) -> CrashAwareCachingDiskBranch::Label
{
    match lbl {
        AtomicBranchState::Label::Query{key, msg, ..} => {
            CrashAwareCachingDiskBranch::Label::Query{
                key,
                value: normalize_value(msg),
            }
        },
        AtomicBranchState::Label::LoadMetadata{root, discovered_aus, ..} => {
            CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus}
        },
        AtomicBranchState::Label::Append{keys, msgs, ..} => {
            CrashAwareCachingDiskBranch::Label::Append{keys, msgs}
        },
        AtomicBranchState::Label::Grow{..}
        | AtomicBranchState::Label::Split{..}
        | AtomicBranchState::Label::Seal{..}
        | AtomicBranchState::Label::ObservePersistedRoots{..} => {
            CrashAwareCachingDiskBranch::Label::Internal
        },
        AtomicBranchState::Label::FillAUs{aus} => {
            CrashAwareCachingDiskBranch::Label::InternalAlloc{
                allocs: aus,
                deallocs: Set::empty(),
            }
        },
        AtomicBranchState::Label::CommitStart{branch_image} => {
            CrashAwareCachingDiskBranch::Label::CommitStart{
                new_boundary_lsn: branch_image.seq_end,
                sealed_roots: branch_image.sealed_roots,
            }
        },
        AtomicBranchState::Label::CommitPrepared => {
            CrashAwareCachingDiskBranch::Label::FreezePrepared
        },
        AtomicBranchState::Label::CommitComplete => {
            CrashAwareCachingDiskBranch::Label::CommitComplete
        },
    }
}

pub open spec fn inv(src: UnifiedCacheBranchSource) -> bool
{
    &&& src.inv()
    &&& src.semantic_inv()
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
                reveal(UnifiedCacheSystem::State::initialize);
            }
            reveal(UnifiedCacheSystem::State::initialize);

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
                assert(src.persistent_superblock_image_i().branch_roots == Seq::<Address>::empty());
                assert forall |addr: Address| #[trigger] UnifiedCacheBranchSource::branch_image_projection_addrs_i(
                    src.disk.content,
                    src.persistent_superblock_image_i().branch_roots,
                ).contains(addr) implies false by {
                    assert(false);
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

pub proof fn query_receipts_read_addrs_member_has_receipt(
    receipts: Seq<LoadedPathReceipt>,
    end: nat,
    addr: Address,
)
    requires
        end <= receipts.len(),
        query_receipts_read_addrs(receipts, end).contains(addr),
    ensures
        exists |i: int| {
            &&& 0 <= i < end
            &&& #[trigger] receipts[i].needed_addrs().contains(addr)
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
            ==> branch.disk_view.entries[branch_addr]
                == to_branch_nodes(src.branch_caching_disk_i().visible())[branch_addr],
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
                let i = choose |i: int| 0 <= i < receipt.lines.len()
                    && #[trigger] receipt.lines[i].addr == addr;
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
            let i = choose |i: int| 0 <= i < receipt.lines.len()
                && #[trigger] receipt.lines[i].addr == addr;
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
            implies child_branch.disk_view.entries[branch_addr]
                == to_branch_nodes(src.branch_caching_disk_i().visible())[branch_addr]
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
            ==> branch.disk_view.entries[branch_addr]
                == to_branch_nodes(src.branch_caching_disk_i().visible())[branch_addr],
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
    assert(cdb.visible().contains_key(addr));
    assert(cdb.visible()[addr] == reads[addr]);
    assert(to_branch_nodes(cdb.visible()).contains_key(addr));
    assert(to_branch_nodes(reads).contains_key(addr));
    assert(to_branch_nodes(reads)[addr] == to_branch_nodes(cdb.visible())[addr]);
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
            ==> branch.disk_view.entries[branch_addr]
                == to_branch_nodes(src.branch_caching_disk_i().visible())[branch_addr],
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
        crate::implementation::AnotherAtomicState_v::query_receipts_valid(
            crate::implementation::AnotherAtomicState_v::query_roots(
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
    let roots = crate::implementation::AnotherAtomicState_v::query_roots(
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
            implies branch.disk_view.entries[read_addr]
                == to_branch_nodes(cdb.disk.visible())[read_addr]
        by {
            assert(branch.disk_view.entries <= cdb.sealed_stack_i().sealed_disk.entries);
            assert(cdb.sealed_stack_i().sealed_disk.entries.contains_key(read_addr));
            assert(sealed_nodes_of(cdb.disk.visible(), cdb.branch_summary).contains_key(read_addr));
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
        assert forall |read_addr: Address|
            #[trigger] branch.disk_view.entries.contains_key(read_addr)
            implies branch.disk_view.entries[read_addr]
                == to_branch_nodes(cdb.disk.visible())[read_addr]
        by {
            assert(active_loaded_nodes_of(cdb.disk, cdb.mini_allocator).contains_key(read_addr));
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
    assert forall |read_addr: Address|
        #[trigger] branch.disk_view.entries.contains_key(read_addr)
        implies branch.disk_view.entries[read_addr]
            == to_branch_nodes(cdb.disk.visible())[read_addr]
    by {
        assert(active_loaded_nodes_of(cdb.disk, cdb.mini_allocator).contains_key(read_addr));
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
    assert(src.branch_projection_aus() == src.branch.owned_aus());
    assert(src.branch.owned_aus() == summary_aus(cdb.branch_summary) + cdb.mini_allocator.all_aus());
    assert(addresses_in_aus(src.branch_projection_aus()).contains(addr));
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
                let roots = crate::implementation::AnotherAtomicState_v::query_roots(
                    pre.branch.image.sealed_roots,
                    pre.branch.active_branch,
                );
                assert(crate::implementation::AnotherAtomicState_v::query_receipts_valid(
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
            let receipt_idx = choose |i: int| {
                &&& 0 <= i < receipts.len()
                &&& #[trigger] receipts[i].needed_addrs().contains(addr)
            };
            let roots = crate::implementation::AnotherAtomicState_v::query_roots(
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

    assert(crate::implementation::AnotherAtomicState_v::query_roots(
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

pub proof fn next_refines(
    pre: UnifiedCacheBranchSource,
    post: UnifiedCacheBranchSource,
    lbl: AtomicBranchState::Label,
)
    requires
        AtomicBranchState::State::next(pre.branch, post.branch, lbl),
        inv(pre),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            unified_cache_branch_i(pre),
            unified_cache_branch_i(post),
            unified_cache_branch_i_lbl(lbl),
        ),
        inv(post),
{
    match lbl {
        AtomicBranchState::Label::Query{..}
        | AtomicBranchState::Label::LoadMetadata{..}
        | AtomicBranchState::Label::Append{..}
        | AtomicBranchState::Label::Grow{..}
        | AtomicBranchState::Label::Split{..}
        | AtomicBranchState::Label::Seal{..}
        | AtomicBranchState::Label::FillAUs{..}
        | AtomicBranchState::Label::ObservePersistedRoots{..}
        | AtomicBranchState::Label::CommitStart{..}
        | AtomicBranchState::Label::CommitPrepared
        | AtomicBranchState::Label::CommitComplete => {
            assume(false);
        },
    }
}

} // verus!
