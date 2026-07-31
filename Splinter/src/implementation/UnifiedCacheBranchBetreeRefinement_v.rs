// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Unified-cache Betree projection into CrashAwareCachingDiskBranchBetree.

#![allow(unused_imports)]
#![allow(unused_variables)]

use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::assert_sets_equal;
use vstd::multiset::Multiset;

use crate::allocation_layer::AllocationBranchBetree_v::{
    branch_summary_insert_ensures, read_ref_aus,
    seq_addrs_to_aus, summary_aus, CompactorInput,
};
use crate::allocation_layer::AllocationBranch_v::{
    AllocationBranch, BranchNode, Summary,
};
use crate::allocation_layer::Likes_v::to_au_likes;
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::LinkedBetree_v::{
    Addrs, DiskView as BetreeDiskView, LinkedBetree,
    PathAddrs, SplitAddrs, TwoAddrs,
};
use crate::betree::SplitRequest_v::SplitRequest;
use crate::betree::LinkedBranch_v::{
    LinkedBranch, Refinement_v as LinkedBranchRefinement,
};
use crate::disk::GenericDisk_v::{
    addrs_closed, set_addrs_disjoint_aus, to_aus, AU, Address,
    Ranking,
};
use crate::implementation::AbstractSuperblock_v::{
    abstract_superblock_raw_wf, parse_abstract_superblock,
    empty_abstract_superblock_image, AbstractSuperblockImage,
};
use crate::implementation::AtomicBranchBetreeState_v::{
    empty_cached_betree, AtomicBranchBetreeControl,
};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedBranch_v::{
    receipt_valid_implies_tail_valid, CachedBranch,
    LoadedPathReceipt,
};
use crate::implementation::CachedBranchBetree_v::{
    added_path_likes, branch_receipts_valid,
    cached_allocation_branch_build_all_aus_subset,
    cached_branch_alloc_aus,
    cached_branch_alloc_aus_update_remove_exact,
    cached_branch_alloc_aus_remove_exact, compact_replacement,
    direct_buffer_likes, flush_replacement,
    loaded_branch_reads_for_roots, path_discard_likes,
    split_replacement, substitute_writes_dom_subset,
    valid_loaded_sealed_branch, valid_loaded_sealed_branches,
    CachedAllocationBranch, FrozenBranchBetree,
    CachedAllocationBranchEvent, CachedBranchBetree, LoadedBetreePath,
    LoadedBetreeQueryReceipt,
};
use crate::implementation::CachingDiskAdapterRefinement_v::{
    cache_access_reads_in_project_cache_by_addrs,
    cache_disk_ops_begin_refines_caching_disk_internal,
    cache_disk_ops_end_refines_caching_disk_internal,
    cache_internal_refines_caching_disk_internal,
    caching_disk_i as adapter_caching_disk_i,
    caching_disk_i_equal_from_raw_projection_agreement,
    caching_disk_i_inv_from_clean_cache_coupling,
    cache_status_i, filled_cache_pages, filled_cache_status,
    project_cache_pages, project_cache_status,
    project_persistent, projected_cache_read_only_access_unchanged,
    projected_cache_access_outside_aus_unchanged,
    valid_reads_in_project_cache_by_addrs,
    cache_access_refines_caching_disk_access,
    cache_evictable_refines_observe_clean_aus,
    ownership_projection_forget_refines,
};
use crate::implementation::CachingDiskBranchBetree_v::{
    disk_access_for_alloc, disk_extend_for_alloc,
    disk_namespace, reclaim_guarded_aus,
    reclaim_guarded_aus_preserves_inv,
    to_betree_nodes, to_branch_nodes,
    BranchBuildEvent, CachingDiskBranchBetree,
    DiskAccessWitness, PageAccess,
};
use crate::implementation::CachingDiskBranchBetreeRefinement_v::{
    betree_read_node_matches_visible,
    initial_refinement_witness_valid, initial_tight_tree,
    loaded_betree_path_matches_linked,
    loaded_betree_path_tail_valid,
    loaded_betree_path_wf_child,
    summary_partition_disjoint, tight_betree_candidate,
    tight_betree_exists, tight_betree_of,
};
use crate::implementation::CachingDiskBranchRefinement_v::
    query_read_node_matches_visible;
use crate::implementation::CachingDisk_v::{
    addresses_in_aus, CachingDisk, PageStatus,
};
use crate::implementation::CrashAwareCachingDiskBranchBetree_v::{
    BetreeMetadataRecovery, BetreeMetadataRecoveryCore,
    BetreeMetadataRecoveryLabel, CachingDiskBranchBetreeImage,
    CachingDiskBranchBetreeMetadata,
    CrashAwareCachingDiskBranchBetree,
    EphemeralCachingDiskBranchBetree,
    FrozenCachingDiskBranchBetree, empty_image_valid,
};
use crate::implementation::
    CrashAwareCachingDiskBranchBetreeRefinement_v::{
        recovery_complete_metadata_matches_image,
        recovery_core_loaded_betree_matches,
        recovery_frontier_pending_reads_persistent,
        recovery_witness_branch_facts,
    };
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::UnifiedCacheBetreeProgramModel_v::
    UnifiedCacheBetreeProgramModel;
use crate::implementation::UnifiedCacheBetreeSystem_v::{
    betree_metadata_from_superblock, AtomicBetreeSyncPhase,
    UnifiedCacheBetreeSystem,
};
use crate::trusted::ProgramModelTrait_t::{
    DiskModel, ProgramModelTrait,
};
use crate::trusted::SystemModel_t::SystemModel;
use crate::spec::AsyncDisk_t::{
    DiskRequest, DiskResponse, RawPage,
};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::Value;
use crate::abstract_system::StampedMap_v::LSN;

verus! {

#[verifier::ext_equal]
pub struct UnifiedCacheBranchBetreeSource {
    pub branch:
        crate::implementation::CachedBranchBetree_v::
            CachedBranchBetree::State,
    pub control: AtomicBranchBetreeControl,
    pub cache: Cache::State,
    pub disk: DiskModel,
    pub persistent_image: Option<AbstractSuperblockImage>,
    pub sync_phase: AtomicBetreeSyncPhase,
}

pub open spec fn unified_cache_branch_betree_source(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> UnifiedCacheBranchBetreeSource {
    let state = model.program.state;
    UnifiedCacheBranchBetreeSource {
        branch: state.branch.betree,
        control: state.branch.control,
        cache: state.cache,
        disk: model.disk,
        persistent_image: state.persistent_image,
        sync_phase: state.sync_phase,
    }
}

pub open spec fn async_disk_superblock_raw_i(
    disk_content: Map<Address, RawPage>,
) -> RawPage {
    if disk_content.contains_key(spec_superblock_addr()) {
        disk_content[spec_superblock_addr()]
    } else {
        arbitrary()
    }
}

pub open spec fn async_disk_superblock_image_i(
    disk_content: Map<Address, RawPage>,
) -> AbstractSuperblockImage {
    parse_abstract_superblock(
        async_disk_superblock_raw_i(disk_content),
    )
}

impl UnifiedCacheBranchBetreeSource {
    pub open spec fn superblock_loaded(self) -> bool {
        self.persistent_image is Some
    }

    pub open spec fn persistent_superblock_image_i(
        self,
    ) -> AbstractSuperblockImage {
        if self.persistent_image is Some {
            self.persistent_image.unwrap()
        } else {
            async_disk_superblock_image_i(self.disk.content)
        }
    }

    pub open spec fn persistent_metadata_i(
        self,
    ) -> CachingDiskBranchBetreeMetadata {
        betree_metadata_from_superblock(
            self.persistent_superblock_image_i(),
        )
    }

    pub open spec fn persistent_tight_betree_i(
        self,
    ) -> LinkedBetree<BranchNode> {
        tight_betree_of(
            self.persistent_metadata_i().root,
            to_betree_nodes(self.disk.content),
        )
    }

    pub open spec fn persistent_branch_roots_i(
        self,
    ) -> Set<Address> {
        let tree = self.persistent_tight_betree_i();
        if tree.acyclic() {
            tree.reachable_buffer_addrs()
        } else {
            Set::empty()
        }
    }

    pub open spec fn persistent_branch_summary_i(
        self,
    ) -> Map<AU, Summary> {
        let branch_disk = BufferDisk {
            entries: to_branch_nodes(self.disk.content),
        };
        branch_disk.build_branch_summary(
            self.persistent_branch_roots_i(),
        )
    }

    pub open spec fn canonical_persistent_aus_i(
        self,
    ) -> Set<AU> {
        let tree = self.persistent_tight_betree_i();
        let likes = tree.transitive_likes();
        if tree.acyclic() {
            to_au_likes(likes.0).dom()
                + to_au_likes(likes.1).dom()
                + summary_aus(
                    self.persistent_branch_summary_i(),
                )
        } else {
            Set::empty()
        }
    }

    pub open spec fn persistent_branch_image_i(
        self,
    ) -> CachingDiskBranchBetreeImage {
        let aus = if self.control.metadata_loaded {
            self.control.persistent_aus
        } else {
            self.canonical_persistent_aus_i()
        };
        CachingDiskBranchBetreeImage {
            persistent: self.disk.content.restrict(
                addresses_in_aus(aus),
            ),
            metadata: self.persistent_metadata_i(),
        }
    }

    pub open spec fn frozen_aus_i(self) -> Set<AU> {
        if self.control.frozen is Some {
            self.control.frozen.unwrap().aus
        } else {
            Set::empty()
        }
    }

    pub open spec fn branch_projection_aus(self) -> Set<AU> {
        if self.control.metadata_loaded {
            self.branch.owned_aus()
                + self.control.persistent_aus
                + self.frozen_aus_i()
        } else {
            self.canonical_persistent_aus_i()
        }
    }

    pub open spec fn branch_caching_disk_i(
        self,
    ) -> CachingDisk::State {
        adapter_caching_disk_i(
            self.cache,
            self.disk,
            self.branch_projection_aus(),
        )
    }

    pub open spec fn known_branch_i(
        self,
    ) -> CachingDiskBranchBetree::State {
        CachingDiskBranchBetree::State {
            disk: self.branch_caching_disk_i(),
            betree: self.branch,
        }
    }

    pub open spec fn ephemeral_branch_i(
        self,
    ) -> EphemeralCachingDiskBranchBetree {
        if self.control.loading {
            EphemeralCachingDiskBranchBetree::Loading {
                recovery: BetreeMetadataRecovery::from_core(
                    self.branch_caching_disk_i(),
                    self.control.recovery,
                ),
            }
        } else if self.control.metadata_loaded {
            EphemeralCachingDiskBranchBetree::Known {
                v: self.known_branch_i(),
                persistent_aus: self.control.persistent_aus,
            }
        } else {
            EphemeralCachingDiskBranchBetree::Unknown
        }
    }

    pub open spec fn prepared_branch_image_i(
        self,
    ) -> Option<CachingDiskBranchBetreeImage> {
        if self.sync_phase is SuperblockWriteIssued
            && self.control.frozen is Some
            && self.control.metadata_loaded
        {
            Some(
                CachingDiskBranchBetreeImage::
                    materialized_from_persistent(
                        self.known_branch_i(),
                        self.control.frozen.unwrap(),
                    ),
            )
        } else {
            None
        }
    }

    pub open spec fn i(
        self,
    ) -> CrashAwareCachingDiskBranchBetree::State {
        CrashAwareCachingDiskBranchBetree::State {
            persistent: self.persistent_branch_image_i(),
            ephemeral: self.ephemeral_branch_i(),
            frozen: self.control.frozen,
            prepared: self.prepared_branch_image_i(),
        }
    }

    pub open spec fn control_wf(self) -> bool {
        &&& !(self.control.loading
            && self.control.metadata_loaded)
        &&& self.control.loading
            ==> !self.control.metadata_loaded
        &&& self.control.metadata_loaded ==> {
            &&& !self.control.loading
            &&& self.control.recovery.complete()
            &&& self.control.metadata.seq_end
                <= self.branch.memtable.seq_end
        }
        &&& self.control.frozen is Some
            ==> self.control.frozen.unwrap().metadata.seq_end
                <= self.branch.memtable.seq_end
    }

    pub open spec fn inv(self) -> bool {
        &&& self.cache.inv()
        &&& self.disk.inv()
        &&& self.disk.content.contains_key(
            spec_superblock_addr(),
        )
        &&& abstract_superblock_raw_wf(
            self.disk.content[spec_superblock_addr()],
        )
        &&& self.persistent_superblock_image_i().wf()
        &&& self.control_wf()
        &&& self.superblock_loaded() ==>
            self.control.metadata
                == self.persistent_metadata_i()
        &&& tight_betree_exists(
            self.persistent_metadata_i().root,
            to_betree_nodes(self.disk.content),
        )
        &&& self.persistent_branch_image_i().valid()
        &&& self.branch_caching_disk_i().inv()
        &&& !self.control.metadata_loaded ==>
            self.branch_caching_disk_i().visible()
                == self.persistent_branch_image_i()
                    .disk().visible()
        &&& self.i().refinement_inv()
    }

    pub proof fn unchanged_by_same_cache_and_disk_content(
        self,
        post: Self,
    )
        requires
            self.inv(),
            post.branch == self.branch,
            post.control == self.control,
            post.cache == self.cache,
            post.disk.content == self.disk.content,
            post.disk.inv(),
            post.persistent_image == self.persistent_image,
            post.sync_phase == self.sync_phase,
        ensures
            post.i() == self.i(),
            post.inv(),
    {
        assert(post.persistent_superblock_image_i()
            == self.persistent_superblock_image_i());
        assert(post.persistent_metadata_i()
            == self.persistent_metadata_i());
        assert(post.persistent_tight_betree_i()
            == self.persistent_tight_betree_i());
        assert(post.persistent_branch_roots_i()
            == self.persistent_branch_roots_i());
        assert(post.persistent_branch_summary_i()
            == self.persistent_branch_summary_i());
        assert(post.canonical_persistent_aus_i()
            == self.canonical_persistent_aus_i());
        assert(post.branch_projection_aus()
            == self.branch_projection_aus());
        assert(post.branch_caching_disk_i()
            == self.branch_caching_disk_i()) by {
            assert_maps_equal!(
                post.branch_caching_disk_i().persistent,
                self.branch_caching_disk_i().persistent,
                addr => {}
            );
        }
        assert(post.persistent_branch_image_i()
            == self.persistent_branch_image_i());
        assert(post.ephemeral_branch_i()
            == self.ephemeral_branch_i());
        assert(post.prepared_branch_image_i()
            == self.prepared_branch_image_i());
        assert(post.i() == self.i());

        reveal(UnifiedCacheBranchBetreeSource::inv);
        assert(post.control_wf());
        assert(post.branch_caching_disk_i().inv());
        assert(!post.control.metadata_loaded ==> {
            post.branch_caching_disk_i().visible()
                == post.persistent_branch_image_i()
                    .disk().visible()
        });
        assert(post.i().refinement_inv());
        assert(post.inv());
    }

    pub proof fn install_from_superblock_refines(
        self,
        post: Self,
        image: AbstractSuperblockImage,
    )
        requires
            self.inv(),
            !self.superblock_loaded(),
            self.branch == empty_cached_betree(),
            self.control
                == AtomicBranchBetreeControl::empty(),
            post.branch == empty_cached_betree(),
            post.control == AtomicBranchBetreeControl::install(
                betree_metadata_from_superblock(image),
            ),
            post.cache == self.cache,
            post.disk.content == self.disk.content,
            post.disk.inv(),
            self.persistent_superblock_image_i() == image,
            post.persistent_image == Some(image),
            post.sync_phase == self.sync_phase,
        ensures
            post.i() == self.i(),
            post.inv(),
    {
        assert(post.persistent_superblock_image_i() == image);
        assert(post.persistent_metadata_i()
            == self.persistent_metadata_i());
        assert(post.control.metadata
            == post.persistent_metadata_i()) by {
            reveal(AtomicBranchBetreeControl::install);
        }
        assert(post.branch == self.branch) by {
            assert(self.branch == empty_cached_betree());
        }
        assert(post.persistent_tight_betree_i()
            == self.persistent_tight_betree_i());
        assert(post.persistent_branch_roots_i()
            == self.persistent_branch_roots_i());
        assert(post.persistent_branch_summary_i()
            == self.persistent_branch_summary_i());
        assert(post.canonical_persistent_aus_i()
            == self.canonical_persistent_aus_i());
        assert(post.branch_projection_aus()
            == self.branch_projection_aus());
        assert(post.branch_caching_disk_i()
            == self.branch_caching_disk_i()) by {
            assert_maps_equal!(
                post.branch_caching_disk_i().persistent,
                self.branch_caching_disk_i().persistent,
                addr => {}
            );
        }
        assert(post.persistent_branch_image_i()
            == self.persistent_branch_image_i());
        reveal(UnifiedCacheBranchBetreeSource::
            ephemeral_branch_i);
        assert(post.ephemeral_branch_i()
            == self.ephemeral_branch_i());
        reveal(UnifiedCacheBranchBetreeSource::
            prepared_branch_image_i);
        assert(post.prepared_branch_image_i()
            == self.prepared_branch_image_i());
        assert(post.i() == self.i());

        reveal(UnifiedCacheBranchBetreeSource::control_wf);
        assert(post.control_wf());
        reveal(UnifiedCacheBranchBetreeSource::inv);
        assert(post.branch_caching_disk_i().inv());
        assert(!post.control.metadata_loaded ==> {
            post.branch_caching_disk_i().visible()
                == post.persistent_branch_image_i()
                    .disk().visible()
        });
        assert(post.i().refinement_inv());
        assert(post.inv());
    }

    pub proof fn unchanged_by_cache_access_outside_branch_projection(
        self,
        post: Self,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    )
        requires
            self.inv(),
            post.branch == self.branch,
            post.control == self.control,
            post.disk == self.disk,
            post.persistent_image == self.persistent_image,
            post.sync_phase == self.sync_phase,
            Cache::State::next(
                self.cache,
                post.cache,
                Cache::Label::Access{reads, writes},
            ),
            writes.dom().disjoint(
                addresses_in_aus(self.branch_projection_aus()),
            ),
        ensures
            post.i() == self.i(),
            post.inv(),
    {
        let aus = self.branch_projection_aus();
        assert(post.branch_projection_aus() == aus);
        projected_cache_access_outside_aus_unchanged(
            self.cache,
            post.cache,
            aus,
            reads,
            writes,
        );
        Cache::State::inv_next(
            self.cache,
            post.cache,
            Cache::Label::Access{reads, writes},
        );
        assert(project_persistent(post.disk, aus)
            == project_persistent(self.disk, aus));
        caching_disk_i_equal_from_raw_projection_agreement(
            post.cache,
            self.cache,
            post.disk,
            self.disk,
            aus,
        );
        assert(post.branch_caching_disk_i()
            == self.branch_caching_disk_i());
        assert(post.persistent_branch_image_i()
            == self.persistent_branch_image_i());
        assert(post.ephemeral_branch_i()
            == self.ephemeral_branch_i());
        assert(post.prepared_branch_image_i()
            == self.prepared_branch_image_i());
        assert(post.i() == self.i());
        reveal(UnifiedCacheBranchBetreeSource::inv);
        assert(post.inv());
    }

    pub proof fn valid_image_implies_tight_betree_exists(
        self,
        image: CachingDiskBranchBetreeImage,
    )
        requires
            image.valid(),
            image.metadata == self.persistent_metadata_i(),
            image.persistent <= self.disk.content,
        ensures
            tight_betree_exists(
                self.persistent_metadata_i().root,
                to_betree_nodes(self.disk.content),
            ),
    {
        image.recovery_witness_valid();
        let witness = image.recovery_witness();
        let tree = initial_tight_tree(
            witness.initial_betree,
        );
        let image_entries = to_betree_nodes(
            image.disk().visible(),
        ).restrict(addresses_in_aus(
            witness.betree_aus.dom(),
        ));

        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetreeRefinement_v::
                RecoveredCachingDiskBranchBetreeMetadata::
                    valid_for);
        reveal(initial_refinement_witness_valid);
        assert(tight_betree_candidate(
            image.metadata.root,
            image_entries,
            tree,
        ));
        assert(image.metadata == self.persistent_metadata_i());
        assert(image.disk().visible() == image.persistent) by {
            reveal(CachingDiskBranchBetreeImage::disk);
            reveal(CachingDisk::State::visible);
            reveal(CachingDisk::State::visible_cache);
        }
        assert(image.persistent
            <= self.disk.content) by {
            reveal(UnifiedCacheBranchBetreeSource::
                persistent_branch_image_i);
        }
        assert(to_betree_nodes(image.disk().visible())
            <= to_betree_nodes(self.disk.content)) by {
            assert forall |addr: Address|
                #[trigger] to_betree_nodes(
                    image.disk().visible(),
                ).contains_key(addr)
                implies {
                    &&& to_betree_nodes(
                        self.disk.content,
                    ).contains_key(addr)
                    &&& to_betree_nodes(
                        image.disk().visible(),
                    )[addr] == to_betree_nodes(
                        self.disk.content,
                    )[addr]
                }
            by {
                reveal(to_betree_nodes);
            }
        }
        assert(image_entries
            <= to_betree_nodes(self.disk.content)) by {
            assert(image_entries
                <= to_betree_nodes(image.disk().visible()));
            vstd::map_lib::lemma_submap_of_trans(
                image_entries,
                to_betree_nodes(image.disk().visible()),
                to_betree_nodes(self.disk.content),
            );
        }
        assert(tree.dv.entries <= image_entries) by {
            reveal(tight_betree_candidate);
        }
        vstd::map_lib::lemma_submap_of_trans(
            tree.dv.entries,
            image_entries,
            to_betree_nodes(self.disk.content),
        );
        assert(tight_betree_candidate(
            self.persistent_metadata_i().root,
            to_betree_nodes(self.disk.content),
            tree,
        )) by {
            reveal(tight_betree_candidate);
        }
        reveal(tight_betree_exists);
    }

    pub proof fn persistent_image_implies_tight_betree_exists(
        self,
    )
        requires
            self.control.metadata_loaded,
            self.persistent_branch_image_i().valid(),
        ensures
            tight_betree_exists(
                self.persistent_metadata_i().root,
                to_betree_nodes(self.disk.content),
            ),
    {
        let image = self.persistent_branch_image_i();
        self.valid_image_implies_tight_betree_exists(
            image,
        );
    }

    pub proof fn projected_disk_internal_refines(
        self,
        post: Self,
    )
        requires
            self.inv(),
            post.branch == self.branch,
            post.control == self.control,
            post.persistent_image == self.persistent_image,
            post.sync_phase == self.sync_phase,
            post.disk.content == self.disk.content,
            post.cache.inv(),
            post.disk.inv(),
            CachingDisk::State::next(
                self.branch_caching_disk_i(),
                post.branch_caching_disk_i(),
                CachingDisk::Label::Internal{},
            ),
        ensures
            post.inv(),
            self.control.loading ==> (
                CrashAwareCachingDiskBranchBetree::State::next(
                    self.i(),
                    post.i(),
                    CrashAwareCachingDiskBranchBetree::Label::
                        RecoverMetadata {
                            recovery_op:
                                BetreeMetadataRecoveryLabel::
                                    DiskInternal,
                        },
                )
            ),
            self.control.metadata_loaded ==> (
                CrashAwareCachingDiskBranchBetree::State::next(
                    self.i(),
                    post.i(),
                    CrashAwareCachingDiskBranchBetree::Label::
                        Ephemeral {
                            op:
                                CachingDiskBranchBetree::Label::
                                    Internal,
                            deallocs: Set::empty(),
                        },
                )
            ),
            !self.control.loading
                && !self.control.metadata_loaded
                ==> post.i() == self.i(),
    {
        let pre_cd = self.branch_caching_disk_i();
        let post_cd = post.branch_caching_disk_i();
        let src = self.i();
        let dst = post.i();

        CachingDisk::State::inv_next(
            pre_cd,
            post_cd,
            CachingDisk::Label::Internal{},
        );
        CachingDisk::State::internal_visible_unchanged(
            pre_cd,
            post_cd,
        );

        assert(post.persistent_metadata_i()
            == self.persistent_metadata_i());
        assert(post.persistent_tight_betree_i()
            == self.persistent_tight_betree_i());
        assert(post.canonical_persistent_aus_i()
            == self.canonical_persistent_aus_i());
        assert(post.persistent_branch_image_i()
            == self.persistent_branch_image_i());

        if self.control.loading {
            let recovery_op =
                BetreeMetadataRecoveryLabel::DiskInternal;
            let old_recovery = src.ephemeral->recovery;
            let new_recovery = dst.ephemeral->recovery;

            reveal(
                UnifiedCacheBranchBetreeSource::
                    ephemeral_branch_i,
            );
            reveal(BetreeMetadataRecovery::from_core);
            assert(src.ephemeral is Loading);
            assert(dst.ephemeral is Loading);
            assert(old_recovery.disk == pre_cd);
            assert(new_recovery.disk == post_cd);
            assert(old_recovery.core()
                == self.control.recovery) by {
                reveal(BetreeMetadataRecovery::core);
            }
            assert(new_recovery.core()
                == self.control.recovery) by {
                reveal(BetreeMetadataRecovery::core);
            }
            assert(BetreeMetadataRecovery::next(
                old_recovery,
                new_recovery,
                recovery_op,
            ));
            let target_lbl =
                CrashAwareCachingDiskBranchBetree::Label::
                    RecoverMetadata{recovery_op};
            assert(
                CrashAwareCachingDiskBranchBetree::State::
                    recover_metadata(
                        src,
                        dst,
                        target_lbl,
                        new_recovery,
                    )
            ) by {
                reveal(
                    CrashAwareCachingDiskBranchBetree::State::
                        recover_metadata,
                );
            }
            assert(
                CrashAwareCachingDiskBranchBetree::State::next_by(
                    src,
                    dst,
                    target_lbl,
                    CrashAwareCachingDiskBranchBetree::Step::
                        recover_metadata(new_recovery),
                )
            ) by {
                reveal(
                    CrashAwareCachingDiskBranchBetree::State::
                        next_by,
                );
            }
            reveal(
                CrashAwareCachingDiskBranchBetree::State::next,
            );
            src.next_refines(dst, target_lbl);
        } else if self.control.metadata_loaded {
            let component_pre = self.known_branch_i();
            let component_post = post.known_branch_i();
            let component_lbl =
                CachingDiskBranchBetree::Label::Internal;
            let target_lbl =
                CrashAwareCachingDiskBranchBetree::Label::
                    Ephemeral {
                        op: component_lbl,
                        deallocs: Set::empty(),
                    };

            reveal(
                UnifiedCacheBranchBetreeSource::
                    ephemeral_branch_i,
            );
            assert(src.ephemeral is Known);
            assert(dst.ephemeral is Known);
            assert(component_pre.disk == pre_cd);
            assert(component_post.disk == post_cd);
            assert(
                CachingDiskBranchBetree::State::disk_internal(
                    component_pre,
                    component_post,
                    component_lbl,
                    post_cd,
                )
            ) by {
                reveal(
                    CachingDiskBranchBetree::State::
                        disk_internal,
                );
            }
            assert(CachingDiskBranchBetree::State::next_by(
                component_pre,
                component_post,
                component_lbl,
                CachingDiskBranchBetree::Step::
                    disk_internal(post_cd),
            )) by {
                reveal(CachingDiskBranchBetree::State::next_by);
            }
            reveal(CachingDiskBranchBetree::State::next);
            assert(crate::implementation::
                CrashAwareCachingDiskBranchBetree_v::
                    logical_deallocs(component_lbl)
                =~= Set::<AU>::empty()) by {
                reveal(crate::implementation::
                    CrashAwareCachingDiskBranchBetree_v::
                        logical_deallocs);
            }
            assert(Set::<AU>::empty()
                == crate::implementation::
                    CrashAwareCachingDiskBranchBetree_v::
                        logical_deallocs(component_lbl)
                    - crate::implementation::
                        CrashAwareCachingDiskBranchBetree_v::
                            protected_aus(
                                src.ephemeral->persistent_aus,
                                src.frozen,
                            ));
            assert(
                CrashAwareCachingDiskBranchBetree::State::
                    ephemeral_step(
                        src,
                        dst,
                        target_lbl,
                        component_post,
                    )
            ) by {
                reveal(
                    CrashAwareCachingDiskBranchBetree::State::
                        ephemeral_step,
                );
                reveal(
                    crate::implementation::
                        CrashAwareCachingDiskBranchBetree_v::
                            logical_deallocs,
                );
            }
            assert(
                CrashAwareCachingDiskBranchBetree::State::next_by(
                    src,
                    dst,
                    target_lbl,
                    CrashAwareCachingDiskBranchBetree::Step::
                        ephemeral_step(component_post),
                )
            ) by {
                reveal(
                    CrashAwareCachingDiskBranchBetree::State::
                        next_by,
                );
            }
            reveal(
                CrashAwareCachingDiskBranchBetree::State::next,
            );
            src.next_refines(dst, target_lbl);
        } else {
            reveal(
                UnifiedCacheBranchBetreeSource::
                    ephemeral_branch_i,
            );
            assert(src.ephemeral is Unknown);
            assert(dst.ephemeral is Unknown);
            assert(dst == src);
        }

        reveal(UnifiedCacheBranchBetreeSource::inv);
        assert(post.control_wf());
        assert(post.branch_caching_disk_i().inv());
        assert(!post.control.metadata_loaded ==> {
            post.branch_caching_disk_i().visible()
                == post.persistent_branch_image_i()
                    .disk().visible()
        });
        assert(post.i().refinement_inv());
        assert(post.inv());
    }

    pub proof fn projected_loaded_disk_internal_refines(
        self,
        post: Self,
    )
        requires
            self.inv(),
            self.control.metadata_loaded,
            post.branch == self.branch,
            post.control == self.control,
            post.cache == self.cache,
            post.persistent_image == self.persistent_image,
            post.sync_phase == self.sync_phase,
            post.disk.inv(),
            post.disk.content.contains_key(
                spec_superblock_addr(),
            ),
            abstract_superblock_raw_wf(
                post.disk.content[spec_superblock_addr()],
            ),
            post.persistent_superblock_image_i()
                == self.persistent_superblock_image_i(),
            post.persistent_branch_image_i()
                == self.persistent_branch_image_i(),
            post.prepared_branch_image_i()
                == self.prepared_branch_image_i(),
            CachingDisk::State::next(
                self.branch_caching_disk_i(),
                post.branch_caching_disk_i(),
                CachingDisk::Label::Internal{},
            ),
        ensures
            post.inv(),
            CrashAwareCachingDiskBranchBetree::State::next(
                self.i(),
                post.i(),
                CrashAwareCachingDiskBranchBetree::Label::
                    Ephemeral {
                        op:
                            CachingDiskBranchBetree::Label::
                                Internal,
                        deallocs: Set::empty(),
                    },
            ),
    {
        let pre_cd = self.branch_caching_disk_i();
        let post_cd = post.branch_caching_disk_i();
        let src = self.i();
        let dst = post.i();
        let component_pre = self.known_branch_i();
        let component_post = post.known_branch_i();
        let component_lbl =
            CachingDiskBranchBetree::Label::Internal;
        let target_lbl =
            CrashAwareCachingDiskBranchBetree::Label::
                Ephemeral {
                    op: component_lbl,
                    deallocs: Set::empty(),
                };

        assert(post.persistent_metadata_i()
            == self.persistent_metadata_i());
        assert(post.persistent_branch_image_i().valid());
        post.persistent_image_implies_tight_betree_exists();
        CachingDisk::State::inv_next(
            pre_cd,
            post_cd,
            CachingDisk::Label::Internal{},
        );

        reveal(
            UnifiedCacheBranchBetreeSource::
                ephemeral_branch_i,
        );
        assert(src.ephemeral is Known);
        assert(dst.ephemeral is Known);
        assert(component_pre.disk == pre_cd);
        assert(component_post.disk == post_cd);
        assert(
            CachingDiskBranchBetree::State::disk_internal(
                component_pre,
                component_post,
                component_lbl,
                post_cd,
            )
        ) by {
            reveal(
                CachingDiskBranchBetree::State::
                    disk_internal,
            );
        }
        assert(CachingDiskBranchBetree::State::next_by(
            component_pre,
            component_post,
            component_lbl,
            CachingDiskBranchBetree::Step::
                disk_internal(post_cd),
        )) by {
            reveal(CachingDiskBranchBetree::State::next_by);
        }
        reveal(CachingDiskBranchBetree::State::next);
        assert(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs(component_lbl)
            =~= Set::<AU>::empty()) by {
            reveal(crate::implementation::
                CrashAwareCachingDiskBranchBetree_v::
                    logical_deallocs);
        }
        assert(Set::<AU>::empty()
            == crate::implementation::
                CrashAwareCachingDiskBranchBetree_v::
                    logical_deallocs(component_lbl)
                - crate::implementation::
                    CrashAwareCachingDiskBranchBetree_v::
                        protected_aus(
                            src.ephemeral->persistent_aus,
                            src.frozen,
                        ));
        assert(
            CrashAwareCachingDiskBranchBetree::State::
                ephemeral_step(
                    src,
                    dst,
                    target_lbl,
                    component_post,
                )
        ) by {
            reveal(
                CrashAwareCachingDiskBranchBetree::State::
                    ephemeral_step,
            );
            reveal(
                crate::implementation::
                    CrashAwareCachingDiskBranchBetree_v::
                        logical_deallocs,
            );
        }
        assert(
            CrashAwareCachingDiskBranchBetree::State::next_by(
                src,
                dst,
                target_lbl,
                CrashAwareCachingDiskBranchBetree::Step::
                    ephemeral_step(component_post),
            )
        ) by {
            reveal(
                CrashAwareCachingDiskBranchBetree::State::
                    next_by,
            );
        }
        reveal(
            CrashAwareCachingDiskBranchBetree::State::next,
        );
        src.next_refines(dst, target_lbl);

        reveal(UnifiedCacheBranchBetreeSource::inv);
        assert(post.control_wf());
        assert(post.branch_caching_disk_i().inv());
        assert(post.i().refinement_inv());
        assert(post.inv());
    }

    pub proof fn cache_internal_refines(
        self,
        post: Self,
    )
        requires
            self.inv(),
            post.branch == self.branch,
            post.control == self.control,
            post.disk == self.disk,
            post.persistent_image == self.persistent_image,
            post.sync_phase == self.sync_phase,
            Cache::State::next(
                self.cache,
                post.cache,
                Cache::Label::Internal{},
            ),
        ensures
            post.inv(),
            self.control.loading ==> (
                CrashAwareCachingDiskBranchBetree::State::next(
                    self.i(),
                    post.i(),
                    CrashAwareCachingDiskBranchBetree::Label::
                        RecoverMetadata {
                            recovery_op:
                                BetreeMetadataRecoveryLabel::
                                    DiskInternal,
                        },
                )
            ),
            self.control.metadata_loaded ==> (
                CrashAwareCachingDiskBranchBetree::State::next(
                    self.i(),
                    post.i(),
                    CrashAwareCachingDiskBranchBetree::Label::
                        Ephemeral {
                            op:
                                CachingDiskBranchBetree::Label::
                                    Internal,
                            deallocs: Set::empty(),
                        },
                )
            ),
            !self.control.loading
                && !self.control.metadata_loaded
                ==> post.i() == self.i(),
    {
        let aus = self.branch_projection_aus();
        let pre_cd = self.branch_caching_disk_i();
        let post_cd = post.branch_caching_disk_i();
        let src = self.i();
        let dst = post.i();

        Cache::State::inv_next(
            self.cache,
            post.cache,
            Cache::Label::Internal{},
        );
        cache_internal_refines_caching_disk_internal(
            self.cache,
            post.cache,
            self.disk,
            aus,
        );
        assert(post.branch_projection_aus() == aus);
        assert(post_cd
            == adapter_caching_disk_i(
                post.cache,
                self.disk,
                aus,
            ));
        assert(CachingDisk::State::next(
            pre_cd,
            post_cd,
            CachingDisk::Label::Internal{},
        ));
        CachingDisk::State::inv_next(
            pre_cd,
            post_cd,
            CachingDisk::Label::Internal{},
        );
        CachingDisk::State::internal_visible_unchanged(
            pre_cd,
            post_cd,
        );

        assert(post.persistent_metadata_i()
            == self.persistent_metadata_i());
        assert(post.persistent_tight_betree_i()
            == self.persistent_tight_betree_i());
        assert(post.canonical_persistent_aus_i()
            == self.canonical_persistent_aus_i());
        assert(post.persistent_branch_image_i()
            == self.persistent_branch_image_i());

        if self.control.loading {
            let recovery_op =
                BetreeMetadataRecoveryLabel::DiskInternal;
            let old_recovery = src.ephemeral->recovery;
            let new_recovery = dst.ephemeral->recovery;

            reveal(
                UnifiedCacheBranchBetreeSource::
                    ephemeral_branch_i,
            );
            reveal(BetreeMetadataRecovery::from_core);
            assert(src.ephemeral is Loading);
            assert(dst.ephemeral is Loading);
            assert(old_recovery.disk == pre_cd);
            assert(new_recovery.disk == post_cd);
            assert(old_recovery.core()
                == self.control.recovery) by {
                reveal(BetreeMetadataRecovery::core);
            }
            assert(new_recovery.core()
                == self.control.recovery) by {
                reveal(BetreeMetadataRecovery::core);
            }
            assert(BetreeMetadataRecovery::next(
                old_recovery,
                new_recovery,
                recovery_op,
            ));
            let target_lbl =
                CrashAwareCachingDiskBranchBetree::Label::
                    RecoverMetadata{recovery_op};
            assert(
                CrashAwareCachingDiskBranchBetree::State::
                    recover_metadata(
                        src,
                        dst,
                        target_lbl,
                        new_recovery,
                    )
            ) by {
                reveal(
                    CrashAwareCachingDiskBranchBetree::State::
                        recover_metadata,
                );
            }
            assert(
                CrashAwareCachingDiskBranchBetree::State::next_by(
                    src,
                    dst,
                    target_lbl,
                    CrashAwareCachingDiskBranchBetree::Step::
                        recover_metadata(new_recovery),
                )
            ) by {
                reveal(
                    CrashAwareCachingDiskBranchBetree::State::
                        next_by,
                );
            }
            reveal(
                CrashAwareCachingDiskBranchBetree::State::next,
            );
            src.next_refines(dst, target_lbl);
        } else if self.control.metadata_loaded {
            let component_pre = self.known_branch_i();
            let component_post = post.known_branch_i();
            let component_lbl =
                CachingDiskBranchBetree::Label::Internal;
            let target_lbl =
                CrashAwareCachingDiskBranchBetree::Label::
                    Ephemeral {
                        op: component_lbl,
                        deallocs: Set::empty(),
                    };

            reveal(
                UnifiedCacheBranchBetreeSource::
                    ephemeral_branch_i,
            );
            assert(src.ephemeral is Known);
            assert(dst.ephemeral is Known);
            assert(component_pre.disk == pre_cd);
            assert(component_post.disk == post_cd);
            assert(
                CachingDiskBranchBetree::State::disk_internal(
                    component_pre,
                    component_post,
                    component_lbl,
                    post_cd,
                )
            ) by {
                reveal(
                    CachingDiskBranchBetree::State::
                        disk_internal,
                );
            }
            assert(CachingDiskBranchBetree::State::next_by(
                component_pre,
                component_post,
                component_lbl,
                CachingDiskBranchBetree::Step::
                    disk_internal(post_cd),
            )) by {
                reveal(CachingDiskBranchBetree::State::next_by);
            }
            reveal(CachingDiskBranchBetree::State::next);
            assert(crate::implementation::
                CrashAwareCachingDiskBranchBetree_v::
                    logical_deallocs(component_lbl)
                =~= Set::<AU>::empty()) by {
                reveal(crate::implementation::
                    CrashAwareCachingDiskBranchBetree_v::
                        logical_deallocs);
            }
            assert(Set::<AU>::empty()
                == crate::implementation::
                    CrashAwareCachingDiskBranchBetree_v::
                        logical_deallocs(component_lbl)
                    - crate::implementation::
                        CrashAwareCachingDiskBranchBetree_v::
                            protected_aus(
                                src.ephemeral->persistent_aus,
                                src.frozen,
                            ));
            assert(
                CrashAwareCachingDiskBranchBetree::State::
                    ephemeral_step(
                        src,
                        dst,
                        target_lbl,
                        component_post,
                    )
            ) by {
                reveal(
                    CrashAwareCachingDiskBranchBetree::State::
                        ephemeral_step,
                );
                reveal(
                    crate::implementation::
                        CrashAwareCachingDiskBranchBetree_v::
                            logical_deallocs,
                );
            }
            assert(
                CrashAwareCachingDiskBranchBetree::State::next_by(
                    src,
                    dst,
                    target_lbl,
                    CrashAwareCachingDiskBranchBetree::Step::
                        ephemeral_step(component_post),
                )
            ) by {
                reveal(
                    CrashAwareCachingDiskBranchBetree::State::
                        next_by,
                );
            }
            reveal(
                CrashAwareCachingDiskBranchBetree::State::next,
            );
            src.next_refines(dst, target_lbl);
        } else {
            reveal(
                UnifiedCacheBranchBetreeSource::
                    ephemeral_branch_i,
            );
            assert(src.ephemeral is Unknown);
            assert(dst.ephemeral is Unknown);
            assert(dst == src);
        }

        reveal(UnifiedCacheBranchBetreeSource::inv);
        assert(post.control_wf());
        assert(post.branch_caching_disk_i().inv());
        assert(!post.control.metadata_loaded ==> {
            post.branch_caching_disk_i().visible()
                == post.persistent_branch_image_i()
                    .disk().visible()
        });
        assert(post.i().refinement_inv());
        assert(post.inv());
    }

    pub proof fn cache_disk_ops_begin_refines(
        self,
        post: Self,
        requests: Set<DiskRequest>,
    )
        requires
            self.inv(),
            post.branch == self.branch,
            post.control == self.control,
            post.persistent_image == self.persistent_image,
            post.sync_phase == self.sync_phase,
            post.disk.content == self.disk.content,
            post.disk.inv(),
            Cache::State::next(
                self.cache,
                post.cache,
                Cache::Label::DiskOps{
                    requests,
                    responses: Map::empty(),
                },
            ),
        ensures
            post.inv(),
            self.control.loading ==> (
                CrashAwareCachingDiskBranchBetree::State::next(
                    self.i(),
                    post.i(),
                    CrashAwareCachingDiskBranchBetree::Label::
                        RecoverMetadata {
                            recovery_op:
                                BetreeMetadataRecoveryLabel::
                                    DiskInternal,
                        },
                )
            ),
            self.control.metadata_loaded ==> (
                CrashAwareCachingDiskBranchBetree::State::next(
                    self.i(),
                    post.i(),
                    CrashAwareCachingDiskBranchBetree::Label::
                        Ephemeral {
                            op:
                                CachingDiskBranchBetree::Label::
                                    Internal,
                            deallocs: Set::empty(),
                        },
                )
            ),
            !self.control.loading
                && !self.control.metadata_loaded
                ==> post.i() == self.i(),
    {
        let aus = self.branch_projection_aus();
        let projected_post = adapter_caching_disk_i(
            post.cache,
            self.disk,
            aus,
        );
        let post_cd = post.branch_caching_disk_i();
        let cache_lbl = Cache::Label::DiskOps{
            requests,
            responses: Map::empty(),
        };

        Cache::State::inv_next(
            self.cache,
            post.cache,
            cache_lbl,
        );
        cache_disk_ops_begin_refines_caching_disk_internal(
            self.cache,
            post.cache,
            self.disk,
            aus,
            requests,
        );
        assert(post.branch_projection_aus() == aus);
        assert(post_cd == projected_post) by {
            assert_maps_equal!(
                post_cd.persistent,
                projected_post.persistent,
                addr => {
                    if post_cd.persistent.contains_key(addr) {
                        assert(post.disk.content.contains_key(addr));
                        assert(self.disk.content.contains_key(addr));
                    }
                    if projected_post.persistent
                        .contains_key(addr)
                    {
                        assert(self.disk.content.contains_key(addr));
                        assert(post.disk.content.contains_key(addr));
                    }
                }
            );
        }
        assert(CachingDisk::State::next(
            self.branch_caching_disk_i(),
            post_cd,
            CachingDisk::Label::Internal{},
        ));
        self.projected_disk_internal_refines(post);
    }

    pub proof fn cache_disk_ops_end_refines(
        self,
        post: Self,
        responses: Map<Address, DiskResponse>,
    )
        requires
            self.inv(),
            post.branch == self.branch,
            post.control == self.control,
            post.persistent_image == self.persistent_image,
            post.sync_phase == self.sync_phase,
            post.disk.content == self.disk.content,
            post.disk.inv(),
            Cache::State::next(
                self.cache,
                post.cache,
                Cache::Label::DiskOps{
                    requests: Set::empty(),
                    responses,
                },
            ),
            forall |addr: Address| {
                &&& #[trigger] responses.contains_key(addr)
                &&& addresses_in_aus(
                    self.branch_projection_aus(),
                ).contains(addr)
            } ==> {
                &&& responses[addr] is ReadResp ==> {
                    self.disk.content.contains_key(addr)
                        ==> responses[addr]->data
                            == self.disk.content[addr]
                }
                &&& responses[addr] is WriteResp ==> {
                    &&& self.disk.content.contains_key(addr)
                    &&& crate::implementation::
                        CachingDiskAdapterRefinement_v::
                            cache_filled_addr(
                                self.cache,
                                addr,
                            )
                    &&& self.disk.content[addr]
                        == crate::implementation::
                            CachingDiskAdapterRefinement_v::
                                cache_filled_page(
                                    self.cache,
                                    addr,
                                )
                }
            },
        ensures
            post.inv(),
            self.control.loading ==> (
                CrashAwareCachingDiskBranchBetree::State::next(
                    self.i(),
                    post.i(),
                    CrashAwareCachingDiskBranchBetree::Label::
                        RecoverMetadata {
                            recovery_op:
                                BetreeMetadataRecoveryLabel::
                                    DiskInternal,
                        },
                )
            ),
            self.control.metadata_loaded ==> (
                CrashAwareCachingDiskBranchBetree::State::next(
                    self.i(),
                    post.i(),
                    CrashAwareCachingDiskBranchBetree::Label::
                        Ephemeral {
                            op:
                                CachingDiskBranchBetree::Label::
                                    Internal,
                            deallocs: Set::empty(),
                        },
                )
            ),
            !self.control.loading
                && !self.control.metadata_loaded
                ==> post.i() == self.i(),
    {
        let aus = self.branch_projection_aus();
        let projected_post = adapter_caching_disk_i(
            post.cache,
            self.disk,
            aus,
        );
        let post_cd = post.branch_caching_disk_i();
        let cache_lbl = Cache::Label::DiskOps{
            requests: Set::empty(),
            responses,
        };

        Cache::State::inv_next(
            self.cache,
            post.cache,
            cache_lbl,
        );
        cache_disk_ops_end_refines_caching_disk_internal(
            self.cache,
            post.cache,
            self.disk,
            aus,
            responses,
        );
        assert(post.branch_projection_aus() == aus);
        assert(post_cd == projected_post) by {
            assert_maps_equal!(
                post_cd.persistent,
                projected_post.persistent,
                addr => {
                    if post_cd.persistent.contains_key(addr) {
                        assert(post.disk.content.contains_key(addr));
                        assert(self.disk.content.contains_key(addr));
                    }
                    if projected_post.persistent
                        .contains_key(addr)
                    {
                        assert(self.disk.content.contains_key(addr));
                        assert(post.disk.content.contains_key(addr));
                    }
                }
            );
        }
        assert(CachingDisk::State::next(
            self.branch_caching_disk_i(),
            post_cd,
            CachingDisk::Label::Internal{},
        ));
        self.projected_disk_internal_refines(post);
    }
}

pub open spec fn unified_cache_branch_betree_i(
    src: UnifiedCacheBranchBetreeSource,
) -> CrashAwareCachingDiskBranchBetree::State {
    src.i()
}

pub open spec fn inv(
    src: UnifiedCacheBranchBetreeSource,
) -> bool {
    src.inv()
}

pub open spec fn clean_cache_disk_coupling_on_aus(
    cache: Cache::State,
    disk: DiskModel,
    aus: Set<AU>,
) -> bool {
    forall |addr: Address| {
        &&& #[trigger] filled_cache_status(cache)
            .contains_key(addr)
        &&& filled_cache_status(cache)[addr]
            == crate::implementation::CachingDisk_v::
                PageStatus::Clean
        &&& addresses_in_aus(aus).contains(addr)
        &&& project_persistent(disk, aus)
            .contains_key(addr)
    } ==> {
        disk.content[addr]
            == crate::implementation::
                CachingDiskAdapterRefinement_v::
                    cache_filled_page(cache, addr)
    }
}

proof fn projected_disk_extend_for_alloc(
    cache: Cache::State,
    disk: DiskModel,
    pre_aus: Set<AU>,
    allocs: Set<AU>,
)
    requires
        cache.inv(),
        adapter_caching_disk_i(
            cache,
            disk,
            pre_aus,
        ).inv(),
        clean_cache_disk_coupling_on_aus(
            cache,
            disk,
            pre_aus + allocs,
        ),
    ensures
        disk_extend_for_alloc(
            adapter_caching_disk_i(
                cache,
                disk,
                pre_aus,
            ),
            adapter_caching_disk_i(
                cache,
                disk,
                pre_aus + allocs,
            ),
            allocs,
        ),
{
    let pre_cd =
        adapter_caching_disk_i(cache, disk, pre_aus);
    let expanded = adapter_caching_disk_i(
        cache,
        disk,
        pre_aus + allocs,
    );
    reveal(clean_cache_disk_coupling_on_aus);
    caching_disk_i_inv_from_clean_cache_coupling(
        cache,
        disk,
        pre_aus + allocs,
    );
    assert(expanded.inv());

    assert(pre_cd.cache <= expanded.cache) by {
        assert forall |addr: Address|
            #[trigger] pre_cd.cache.contains_key(addr)
            implies {
                &&& expanded.cache.contains_key(addr)
                &&& pre_cd.cache[addr]
                    == expanded.cache[addr]
            }
        by {
            assert(addresses_in_aus(pre_aus)
                .contains(addr));
            assert(addresses_in_aus(pre_aus + allocs)
                .contains(addr));
        }
    }
    assert(pre_cd.persistent <= expanded.persistent) by {
        assert forall |addr: Address|
            #[trigger] pre_cd.persistent
                .contains_key(addr)
            implies {
                &&& expanded.persistent
                    .contains_key(addr)
                &&& pre_cd.persistent[addr]
                    == expanded.persistent[addr]
            }
        by {
            assert(addresses_in_aus(pre_aus)
                .contains(addr));
            assert(addresses_in_aus(pre_aus + allocs)
                .contains(addr));
        }
    }
    assert(pre_cd.status <= expanded.status) by {
        assert forall |addr: Address|
            #[trigger] pre_cd.status.contains_key(addr)
            implies {
                &&& expanded.status.contains_key(addr)
                &&& pre_cd.status[addr]
                    == expanded.status[addr]
            }
        by {
            assert(addresses_in_aus(pre_aus)
                .contains(addr));
            assert(addresses_in_aus(pre_aus + allocs)
                .contains(addr));
        }
    }
    assert(disk_namespace(expanded)
        - disk_namespace(pre_cd)
        <= addresses_in_aus(allocs)) by {
        assert forall |addr: Address|
            #[trigger] (disk_namespace(expanded)
                - disk_namespace(pre_cd)).contains(addr)
            implies addresses_in_aus(allocs)
                .contains(addr)
        by {
            assert(addresses_in_aus(pre_aus + allocs)
                .contains(addr));
            if pre_aus.contains(addr.au) {
                if expanded.cache.contains_key(addr) {
                    assert(pre_cd.cache.contains_key(addr));
                    assert(disk_namespace(pre_cd)
                        .contains(addr));
                } else {
                    assert(expanded.persistent
                        .contains_key(addr));
                    assert(pre_cd.persistent
                        .contains_key(addr));
                    assert(disk_namespace(pre_cd)
                        .contains(addr));
                }
            }
        }
    }
    assert(expanded.cache.dom()
        - pre_cd.cache.dom()
        <= addresses_in_aus(allocs)) by {
        assert forall |addr: Address|
            #[trigger] (expanded.cache.dom()
                - pre_cd.cache.dom()).contains(addr)
            implies addresses_in_aus(allocs)
                .contains(addr)
        by {
            assert(addresses_in_aus(pre_aus + allocs)
                .contains(addr));
            if pre_aus.contains(addr.au) {
                assert(pre_cd.cache.contains_key(addr));
            }
        }
    }
    assert(expanded.persistent.dom()
        - pre_cd.persistent.dom()
        <= addresses_in_aus(allocs)) by {
        assert forall |addr: Address|
            #[trigger] (expanded.persistent.dom()
                - pre_cd.persistent.dom()).contains(addr)
            implies addresses_in_aus(allocs)
                .contains(addr)
        by {
            assert(addresses_in_aus(pre_aus + allocs)
                .contains(addr));
            if pre_aus.contains(addr.au) {
                assert(pre_cd.persistent
                    .contains_key(addr));
            }
        }
    }
}

proof fn projected_disk_access_for_alloc(
    pre_cache: Cache::State,
    post_cache: Cache::State,
    disk: DiskModel,
    pre_aus: Set<AU>,
    post_aus: Set<AU>,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    guard_aus: Set<AU>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre_cache.inv(),
        adapter_caching_disk_i(
            pre_cache,
            disk,
            pre_aus,
        ).inv(),
        clean_cache_disk_coupling_on_aus(
            pre_cache,
            disk,
            pre_aus + allocs,
        ),
        Cache::State::next(
            pre_cache,
            post_cache,
            Cache::Label::Access{reads, writes},
        ),
        reads.dom()
            <= addresses_in_aus(pre_aus + allocs),
        writes.dom()
            <= addresses_in_aus(pre_aus + allocs),
        post_aus
            == (pre_aus + allocs)
                - (deallocs - guard_aus),
    ensures
        disk_access_for_alloc(
            adapter_caching_disk_i(
                pre_cache,
                disk,
                pre_aus,
            ),
            adapter_caching_disk_i(
                post_cache,
                disk,
                post_aus,
            ),
            allocs,
            deallocs,
            guard_aus,
            reads,
            writes,
        ),
{
    let expanded_aus = pre_aus + allocs;
    let forgotten = deallocs - guard_aus;
    let pre_cd = adapter_caching_disk_i(
        pre_cache,
        disk,
        pre_aus,
    );
    let expanded = adapter_caching_disk_i(
        pre_cache,
        disk,
        expanded_aus,
    );
    let accessed = adapter_caching_disk_i(
        post_cache,
        disk,
        expanded_aus,
    );
    let final_cd = adapter_caching_disk_i(
        post_cache,
        disk,
        post_aus,
    );

    projected_disk_extend_for_alloc(
        pre_cache,
        disk,
        pre_aus,
        allocs,
    );
    cache_access_refines_caching_disk_access(
        pre_cache,
        post_cache,
        disk,
        expanded_aus,
        reads,
        writes,
    );
    ownership_projection_forget_refines(
        post_cache,
        disk,
        expanded_aus,
        forgotten,
    );
    assert(final_cd == adapter_caching_disk_i(
        post_cache,
        disk,
        expanded_aus - forgotten,
    ));
    assert(disk_extend_for_alloc(
        pre_cd,
        expanded,
        allocs,
    ));
    assert(CachingDisk::State::next(
        expanded,
        accessed,
        CachingDisk::Label::Access{reads, writes},
    ));
    assert(CachingDisk::State::next(
        accessed,
        final_cd,
        CachingDisk::Label::Forget{aus: forgotten},
    ));
    let witness = DiskAccessWitness {
        expanded,
        accessed,
    };
    assert(exists |candidate: DiskAccessWitness| {
        &&& #[trigger] disk_extend_for_alloc(
            pre_cd,
            candidate.expanded,
            allocs,
        )
        &&& CachingDisk::State::next(
            candidate.expanded,
            candidate.accessed,
            CachingDisk::Label::Access{reads, writes},
        )
        &&& CachingDisk::State::next(
            candidate.accessed,
            final_cd,
            CachingDisk::Label::Forget{aus: forgotten},
        )
    }) by {
        assert(disk_extend_for_alloc(
            pre_cd,
            witness.expanded,
            allocs,
        ));
        assert(CachingDisk::State::next(
            witness.expanded,
            witness.accessed,
            CachingDisk::Label::Access{reads, writes},
        ));
        assert(CachingDisk::State::next(
            witness.accessed,
            final_cd,
            CachingDisk::Label::Forget{aus: forgotten},
        ));
    }
    assert(disk_access_for_alloc(
        pre_cd,
        final_cd,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
    )) by {
        reveal(disk_access_for_alloc);
    }
}

pub open spec fn init_shared_facts(
    src: UnifiedCacheBranchBetreeSource,
) -> bool {
    &&& src.cache.inv()
    &&& src.disk.inv()
    &&& src.disk.content.contains_key(spec_superblock_addr())
    &&& abstract_superblock_raw_wf(
        src.disk.content[spec_superblock_addr()],
    )
    &&& src.persistent_superblock_image_i()
        == empty_abstract_superblock_image()
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
        init_shared_facts(
            unified_cache_branch_betree_source(model),
        ),
    ensures
        inv(unified_cache_branch_betree_source(model)),
        unified_cache_branch_betree_source(model)
            .branch_projection_aus() =~= Set::<AU>::empty(),
        CrashAwareCachingDiskBranchBetree::State::init(
            unified_cache_branch_betree_i(
                unified_cache_branch_betree_source(model),
            ),
        ),
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
            let src =
                unified_cache_branch_betree_source(model);
            let dst = unified_cache_branch_betree_i(src);
            reveal(init_shared_facts);
            reveal(UnifiedCacheBranchBetreeSource::control_wf);
            reveal(UnifiedCacheBranchBetreeSource::
                persistent_superblock_image_i);
            reveal(UnifiedCacheBranchBetreeSource::
                persistent_metadata_i);
            assert(src.control
                == AtomicBranchBetreeControl::empty());
            assert(src.persistent_metadata_i()
                == CachingDiskBranchBetreeMetadata::empty());
            let empty_tree = LinkedBetree {
                root: Option::None,
                dv:
                    BetreeDiskView { entries: Map::empty() },
                buffer_dv: BufferDisk::<BranchNode>::empty_disk(),
            };
            assert(crate::implementation::
                CachingDiskBranchBetreeRefinement_v::
                    tight_betree_candidate(
                        Option::None,
                        to_betree_nodes(src.disk.content),
                        empty_tree,
                    )) by {
                reveal(crate::implementation::
                    CachingDiskBranchBetreeRefinement_v::
                        tight_betree_candidate);
                reveal(LinkedBetree::valid_ranking);
                reveal(crate::betree::LinkedBetree_v::
                    DiskView::valid_ranking);
                reveal(crate::betree::LinkedBetree_v::
                    DiskView::wf);
                reveal(LinkedBetree::acyclic);
                reveal(LinkedBetree::has_root);
                reveal(LinkedBetree::reachable_betree_addrs);
                reveal(LinkedBetree::
                    reachable_betree_addrs_using_ranking);
                assert(empty_tree.valid_ranking(
                    Map::<Address, nat>::empty(),
                ));
            }
            assert(tight_betree_exists(
                src.persistent_metadata_i().root,
                to_betree_nodes(src.disk.content),
            )) by {
                reveal(tight_betree_exists);
            }
            crate::implementation::
                CachingDiskBranchBetreeRefinement_v::
                    tight_betree_unique(
                        Option::None,
                        to_betree_nodes(src.disk.content),
                        src.persistent_tight_betree_i(),
                        empty_tree,
                    );
            assert(src.persistent_tight_betree_i()
                == empty_tree);
            assert(src.canonical_persistent_aus_i()
                =~= Set::<AU>::empty()) by {
                reveal(UnifiedCacheBranchBetreeSource::
                    canonical_persistent_aus_i);
                reveal(UnifiedCacheBranchBetreeSource::
                    persistent_branch_roots_i);
                reveal(UnifiedCacheBranchBetreeSource::
                    persistent_branch_summary_i);
                reveal(LinkedBetree::transitive_likes);
                reveal(LinkedBetree::tree_likes);
                reveal(LinkedBetree::buffer_likes);
                reveal(LinkedBetree::reachable_buffer_addrs);
                reveal(LinkedBetree::reachable_buffer);
                assert(empty_tree.transitive_likes()
                    == (
                        Multiset::<Address>::empty(),
                        Multiset::<Address>::empty(),
                    ));
                crate::allocation_layer::Likes_v::
                    to_au_likes_empty();
                let likes = empty_tree.transitive_likes();
                assert(to_au_likes(likes.0)
                    == Multiset::<AU>::empty());
                assert(to_au_likes(likes.1)
                    == Multiset::<AU>::empty());
                assert(to_au_likes(likes.0).dom()
                    =~= Set::<AU>::empty());
                assert(to_au_likes(likes.1).dom()
                    =~= Set::<AU>::empty());
                let branch_disk = empty_tree.buffer_dv;
                assert(src.persistent_branch_roots_i()
                    =~= Set::<Address>::empty());
                branch_disk.build_branch_domain(
                    Set::<Address>::empty(),
                );
                assert(branch_disk.build_branch_summary(
                    Set::<Address>::empty(),
                ) =~= Map::<AU, Summary>::empty()) by {
                    assert_maps_equal!(
                        branch_disk.build_branch_summary(
                            Set::<Address>::empty(),
                        ),
                        Map::<AU, Summary>::empty(),
                        au => {
                            if branch_disk.build_branch_summary(
                                Set::<Address>::empty(),
                            ).contains_key(au) {
                                assert(false);
                            }
                        }
                    );
                }
                assert(src.persistent_branch_summary_i()
                    == Map::<AU, Summary>::empty());
                assert(summary_aus(
                    Map::<AU, Summary>::empty(),
                ) =~= Set::<AU>::empty()) by {
                    reveal(summary_aus);
                    assert(Map::<AU, Summary>::empty().values()
                        =~= Set::<Summary>::empty()) by {
                        assert forall |summary: Summary|
                            !Map::<AU, Summary>::empty()
                                .values().contains(summary) by {
                            assert(!exists |au: AU|
                                Map::<AU, Summary>::empty()
                                    .contains_key(au)
                                && Map::<AU, Summary>::empty()[au]
                                    == summary);
                        }
                    }
                    reveal(crate::betree::Utils_v::
                        union_set_of_sets);
                }
            }
            assert(src.persistent_branch_image_i()
                == CachingDiskBranchBetreeImage::empty()) by {
                assert_maps_equal!(
                    src.persistent_branch_image_i().persistent,
                    Map::<Address, RawPage>::empty(),
                    addr => {}
                );
            }
            empty_image_valid();
            assert(src.branch_projection_aus()
                =~= Set::<AU>::empty());
            caching_disk_i_inv_from_clean_cache_coupling(
                src.cache,
                src.disk,
                src.branch_projection_aus(),
            );
            assert(src.branch_caching_disk_i().inv());
            assert(src.branch_caching_disk_i().cache
                == Map::<Address, RawPage>::empty());
            assert(src.branch_caching_disk_i().persistent
                == Map::<Address, RawPage>::empty());
            assert(src.branch_caching_disk_i().visible()
                == src.persistent_branch_image_i()
                    .disk().visible()) by {
                reveal(CachingDisk::State::visible);
                reveal(CachingDisk::State::visible_cache);
            }
            reveal(UnifiedCacheBranchBetreeSource::
                ephemeral_branch_i);
            reveal(UnifiedCacheBranchBetreeSource::
                prepared_branch_image_i);
            reveal(UnifiedCacheBranchBetreeSource::i);
            assert(dst.persistent
                == CachingDiskBranchBetreeImage::empty());
            assert(dst.ephemeral is Unknown);
            assert(dst.frozen is None);
            assert(dst.prepared is None);
            assert(CrashAwareCachingDiskBranchBetree::State::
                initialize(dst)) by {
                reveal(CrashAwareCachingDiskBranchBetree::State::
                    initialize);
            }
            CrashAwareCachingDiskBranchBetree::show::initialize(
                dst,
            );
            dst.init_refines();
            reveal(UnifiedCacheBranchBetreeSource::inv);
            assert(src.inv());
        }
        UnifiedCacheBetreeSystem::Config::
            dummy_to_use_type_params(_) => {
            assert(false);
        }
    }
}

pub proof fn load_ephemeral_refines(
    pre: UnifiedCacheBranchBetreeSource,
    post: UnifiedCacheBranchBetreeSource,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        !pre.control.loading,
        !pre.control.metadata_loaded,
        post.branch == pre.branch,
        post.cache == pre.cache,
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.sync_phase == pre.sync_phase,
        post.control == (AtomicBranchBetreeControl {
            recovery: BetreeMetadataRecoveryCore::start(
                pre.control.metadata,
            ),
            loading: true,
            ..pre.control
        }),
    ensures
        CrashAwareCachingDiskBranchBetree::State::next(
            unified_cache_branch_betree_i(pre),
            unified_cache_branch_betree_i(post),
            CrashAwareCachingDiskBranchBetree::Label::LoadEphemeral,
        ),
        inv(post),
{
    let src = unified_cache_branch_betree_i(pre);
    let dst = unified_cache_branch_betree_i(post);
    let initial_disk = pre.branch_caching_disk_i();

    reveal(UnifiedCacheBranchBetreeSource::ephemeral_branch_i);
    reveal(BetreeMetadataRecovery::from_core);
    reveal(BetreeMetadataRecoveryCore::start);
    assert(pre.persistent_metadata_i()
        == post.persistent_metadata_i());
    assert(pre.persistent_tight_betree_i()
        == post.persistent_tight_betree_i());
    assert(pre.canonical_persistent_aus_i()
        =~= post.canonical_persistent_aus_i());
    assert(pre.persistent_branch_image_i()
        == post.persistent_branch_image_i());
    assert(src.persistent.metadata == pre.control.metadata);
    assert(pre.branch_projection_aus()
        =~= post.branch_projection_aus());
    assert(pre.branch_caching_disk_i()
        == post.branch_caching_disk_i());

    assert(src.ephemeral is Unknown);
    assert(dst.ephemeral is Loading);
    assert(initial_disk.persistent
        == src.persistent.persistent);
    assert(initial_disk.visible()
        == src.persistent.disk().visible());
    assert(dst.ephemeral->recovery
        == BetreeMetadataRecovery::from_core(
            initial_disk,
            BetreeMetadataRecoveryCore::start(
                src.persistent.metadata,
            ),
        ));
    assert(CrashAwareCachingDiskBranchBetree::State::
        load_ephemeral(
            src,
            dst,
            CrashAwareCachingDiskBranchBetree::Label::LoadEphemeral,
            initial_disk,
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            load_ephemeral);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::next_by(
        src,
        dst,
        CrashAwareCachingDiskBranchBetree::Label::LoadEphemeral,
        CrashAwareCachingDiskBranchBetree::Step::load_ephemeral(
            initial_disk,
        ),
    )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    src.next_refines(
        dst,
        CrashAwareCachingDiskBranchBetree::Label::LoadEphemeral,
    );

    reveal(UnifiedCacheBranchBetreeSource::control_wf);
    reveal(UnifiedCacheBranchBetreeSource::inv);
    assert(post.control_wf());
    assert(post.i().refinement_inv());
    assert(post.inv());
}

pub open spec fn recovery_label_reads(
    lbl: BetreeMetadataRecoveryLabel,
) -> Map<Address, RawPage> {
    match lbl {
        BetreeMetadataRecoveryLabel::DiskInternal =>
            Map::empty(),
        BetreeMetadataRecoveryLabel::ReadBetree{reads, ..}
        | BetreeMetadataRecoveryLabel::ReadBranchRoot{
            reads, ..
        }
        | BetreeMetadataRecoveryLabel::ReadBranchAux{
            reads, ..
        } => reads,
    }
}

pub proof fn recover_metadata_refines(
    pre: UnifiedCacheBranchBetreeSource,
    post: UnifiedCacheBranchBetreeSource,
    recovery_op: BetreeMetadataRecoveryLabel,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        pre.control.loading,
        !pre.control.metadata_loaded,
        !(recovery_op is DiskInternal),
        post.branch == pre.branch,
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.sync_phase == pre.sync_phase,
        post.control == (AtomicBranchBetreeControl {
            recovery: post.control.recovery,
            ..pre.control
        }),
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access {
                reads: recovery_label_reads(recovery_op),
                writes: Map::empty(),
            },
        ),
        BetreeMetadataRecoveryCore::next(
            pre.control.recovery,
            post.control.recovery,
            recovery_op,
        ),
    ensures
        CrashAwareCachingDiskBranchBetree::State::next(
            unified_cache_branch_betree_i(pre),
            unified_cache_branch_betree_i(post),
            CrashAwareCachingDiskBranchBetree::Label::
                RecoverMetadata{recovery_op},
        ),
        inv(post),
{
    let reads = recovery_label_reads(recovery_op);
    let empty_writes = Map::<Address, RawPage>::empty();
    let cache_lbl = Cache::Label::Access {
        reads,
        writes: empty_writes,
    };
    let src = unified_cache_branch_betree_i(pre);
    let dst = unified_cache_branch_betree_i(post);
    let image = src.persistent;
    let old_recovery = src.ephemeral->recovery;
    let new_recovery = dst.ephemeral->recovery;
    let aus = pre.branch_projection_aus();

    reveal(UnifiedCacheBranchBetreeSource::ephemeral_branch_i);
    reveal(BetreeMetadataRecovery::from_core);
    assert(src.ephemeral is Loading);
    assert(dst.ephemeral is Loading);
    assert(old_recovery.core() == pre.control.recovery) by {
        reveal(BetreeMetadataRecovery::core);
    }
    assert(new_recovery.core() == post.control.recovery) by {
        reveal(BetreeMetadataRecovery::core);
    }
    assert(old_recovery.refinement_inv(image));
    recovery_frontier_pending_reads_persistent(
        old_recovery,
        image,
    );

    assert(reads.dom() <= image.persistent.dom()) by {
        match recovery_op {
            BetreeMetadataRecoveryLabel::DiskInternal => {
                assert(false);
            }
            BetreeMetadataRecoveryLabel::ReadBetree{
                addr,
                reads: op_reads,
            } => {
                assert(reads == op_reads);
                assert(pre.control.recovery
                    .pending_betree.contains(addr));
                assert(op_reads.dom() == set![addr]);
                assert(image.persistent.contains_key(addr));
            }
            BetreeMetadataRecoveryLabel::ReadBranchRoot{
                root,
                reads: op_reads,
            } => {
                assert(reads == op_reads);
                assert(pre.control.recovery
                    .pending_branch_roots.contains(root));
                assert(op_reads.dom() == set![root]);
                assert(image.persistent.contains_key(root));
            }
            BetreeMetadataRecoveryLabel::ReadBranchAux{
                root,
                reads: op_reads,
            } => {
                let aux =
                    pre.control.recovery.pending_branch_aux[root];
                assert(reads == op_reads);
                assert(pre.control.recovery
                    .pending_branch_aux.contains_key(root));
                assert(op_reads.dom() == set![aux]);
                assert(image.persistent.contains_key(aux));
            }
        }
    }
    assert(image.persistent.dom()
        <= addresses_in_aus(aus)) by {
        assert(aus =~= pre.canonical_persistent_aus_i());
    }
    assert(reads.dom() <= addresses_in_aus(aus));

    cache_access_reads_in_project_cache_by_addrs(
        pre.cache,
        post.cache,
        addresses_in_aus(aus),
        reads,
        empty_writes,
    );
    assert(reads <= pre.branch_caching_disk_i().cache);
    assert(pre.branch_caching_disk_i().cache
        .union_prefer_right(empty_writes)
        == pre.branch_caching_disk_i().cache) by {
        assert_maps_equal!(
            pre.branch_caching_disk_i().cache
                .union_prefer_right(empty_writes),
            pre.branch_caching_disk_i().cache,
            addr => {}
        );
    }
    let empty_status = crate::implementation::CachingDisk_v::
        status_map(
            empty_writes.dom(),
            crate::implementation::CachingDisk_v::
                PageStatus::Dirty,
        );
    assert(empty_status
        == Map::<Address,
            crate::implementation::CachingDisk_v::PageStatus>::
            empty()) by {
        assert_maps_equal!(
            empty_status,
            Map::<Address,
                crate::implementation::CachingDisk_v::PageStatus>::
                empty(),
            addr => {}
        );
    }
    assert(pre.branch_caching_disk_i().status
        .union_prefer_right(empty_status)
        == pre.branch_caching_disk_i().status) by {
        assert_maps_equal!(
            pre.branch_caching_disk_i().status
                .union_prefer_right(empty_status),
            pre.branch_caching_disk_i().status,
            addr => {}
        );
    }
    assert(CachingDisk::State::access(
        pre.branch_caching_disk_i(),
        pre.branch_caching_disk_i(),
        CachingDisk::Label::Access{
            reads,
            writes: empty_writes,
        },
    )) by {
        reveal(CachingDisk::State::access);
    }
    assert(CachingDisk::State::next_by(
        pre.branch_caching_disk_i(),
        pre.branch_caching_disk_i(),
        CachingDisk::Label::Access{
            reads,
            writes: empty_writes,
        },
        CachingDisk::Step::access(),
    )) by {
        reveal(CachingDisk::State::next_by);
    }
    reveal(CachingDisk::State::next);

    Cache::State::inv_next(pre.cache, post.cache, cache_lbl);
    projected_cache_read_only_access_unchanged(
        pre.cache,
        post.cache,
        aus,
        reads,
    );
    assert(post.branch_projection_aus() =~= aus);
    assert(project_persistent(post.disk, aus)
        == project_persistent(pre.disk, aus));
    caching_disk_i_equal_from_raw_projection_agreement(
        post.cache,
        pre.cache,
        post.disk,
        pre.disk,
        aus,
    );
    assert(post.branch_caching_disk_i()
        == pre.branch_caching_disk_i());

    assert(BetreeMetadataRecovery::next(
        old_recovery,
        new_recovery,
        recovery_op,
    )) by {
        match recovery_op {
            BetreeMetadataRecoveryLabel::DiskInternal => {
                assert(false);
            }
            BetreeMetadataRecoveryLabel::ReadBetree{..}
            | BetreeMetadataRecoveryLabel::ReadBranchRoot{..}
            | BetreeMetadataRecoveryLabel::ReadBranchAux{..} => {
                reveal(BetreeMetadataRecovery::next);
                reveal(BetreeMetadataRecoveryCore::next);
            }
        }
    }
    let target_lbl =
        CrashAwareCachingDiskBranchBetree::Label::
            RecoverMetadata{recovery_op};
    assert(CrashAwareCachingDiskBranchBetree::State::
        recover_metadata(
            src,
            dst,
            target_lbl,
            new_recovery,
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            recover_metadata);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBranchBetree::Step::
            recover_metadata(new_recovery),
    )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    src.next_refines(dst, target_lbl);

    reveal(UnifiedCacheBranchBetreeSource::control_wf);
    reveal(UnifiedCacheBranchBetreeSource::inv);
    assert(post.control_wf());
    assert(post.i().refinement_inv());
    assert(post.inv());
}

pub proof fn persistent_image_witness_aus_match_from_disk(
    src: UnifiedCacheBranchBetreeSource,
    image: CachingDiskBranchBetreeImage,
)
    requires
        image.valid(),
        image.metadata == src.persistent_metadata_i(),
        image.persistent <= src.disk.content,
        tight_betree_exists(
            src.persistent_metadata_i().root,
            to_betree_nodes(src.disk.content),
        ),
    ensures ({
        let witness = image.recovery_witness();
        witness.betree_aus.dom()
            + witness.branch_aus.dom()
            + summary_aus(witness.branch_summary)
            == src.canonical_persistent_aus_i()
    }),
{
    let witness = image.recovery_witness();
    let witness_tree =
        crate::implementation::
            CachingDiskBranchBetreeRefinement_v::
                initial_tight_tree(witness.initial_betree);
    let source_tree = src.persistent_tight_betree_i();

    image.recovery_witness_valid();
    recovery_witness_branch_facts(image);
    reveal(crate::implementation::
        CrashAwareCachingDiskBranchBetreeRefinement_v::
            RecoveredCachingDiskBranchBetreeMetadata::valid_for);
    reveal(crate::implementation::
        CachingDiskBranchBetreeRefinement_v::
            initial_refinement_witness_valid);
    reveal(crate::allocation_layer::
        AllocationBranchBetree_v::
            AllocationBranchBetree::State::initialize);
    reveal(crate::implementation::
        CachingDiskBranchBetreeRefinement_v::
            tight_betree_candidate);
    let image_tree_entries =
        to_betree_nodes(image.disk().visible());
    let bounded_witness_entries =
        image_tree_entries.restrict(
            addresses_in_aus(witness.betree_aus.dom()),
        );
    assert(witness_tree.dv.entries
        <= bounded_witness_entries);
    assert(bounded_witness_entries <= image_tree_entries);
    vstd::map_lib::lemma_submap_of_trans(
        witness_tree.dv.entries,
        bounded_witness_entries,
        image_tree_entries,
    );
    assert(image_tree_entries
        <= to_betree_nodes(src.disk.content)) by {
        assert forall |addr: Address|
            #[trigger] image_tree_entries.contains_key(addr)
            implies {
                &&& to_betree_nodes(src.disk.content)
                    .contains_key(addr)
                &&& image_tree_entries[addr]
                    == to_betree_nodes(src.disk.content)[addr]
            } by {
            assert(image.persistent.contains_key(addr));
            assert(src.disk.content.contains_key(addr));
            assert(image.persistent[addr]
                == src.disk.content[addr]);
        }
    }
    vstd::map_lib::lemma_submap_of_trans(
        witness_tree.dv.entries,
        image_tree_entries,
        to_betree_nodes(src.disk.content),
    );
    assert(crate::implementation::
        CachingDiskBranchBetreeRefinement_v::
            tight_betree_candidate(
                src.persistent_metadata_i().root,
                to_betree_nodes(src.disk.content),
                witness_tree,
            )) by {
    }
    crate::implementation::
        CachingDiskBranchBetreeRefinement_v::
            tight_betree_unique(
                src.persistent_metadata_i().root,
                to_betree_nodes(src.disk.content),
                witness_tree,
                source_tree,
            );
    assert(witness_tree == source_tree);
    let witness_full_tree = witness.initial_betree.linked;
    assert(witness_full_tree.acyclic());
    crate::implementation::
        CrashAwareCachingDiskBranchBetreeRefinement_v::
            same_betree_root_disk_same_transitive_likes(
                witness_tree,
                witness_full_tree,
            );
    assert(witness.betree_aus
        == to_au_likes(source_tree.transitive_likes().0));
    assert(witness.branch_aus
        == to_au_likes(source_tree.transitive_likes().1));

    let roots = source_tree.reachable_buffer_addrs();
    let witness_buffer = witness_full_tree.buffer_dv;
    let source_buffer = BufferDisk {
        entries: to_branch_nodes(src.disk.content),
    };
    assert(witness_buffer.entries <= source_buffer.entries) by {
        let image_branch_entries =
            to_branch_nodes(image.disk().visible());
        assert(witness_buffer.entries
            <= image_branch_entries);
        assert(image_branch_entries
            <= source_buffer.entries) by {
            assert forall |addr: Address|
                #[trigger] image_branch_entries
                    .contains_key(addr)
                implies {
                    &&& source_buffer.entries
                        .contains_key(addr)
                    &&& image_branch_entries[addr]
                        == source_buffer.entries[addr]
                } by {
                assert(image.persistent.contains_key(addr));
                assert(src.disk.content.contains_key(addr));
                assert(image.persistent[addr]
                    == src.disk.content[addr]);
            }
        }
        vstd::map_lib::lemma_submap_of_trans(
            witness_buffer.entries,
            image_branch_entries,
            source_buffer.entries,
        );
    }
    assert(witness.branch_summary
        == witness_buffer.build_branch_summary(roots));
    assert(src.persistent_branch_summary_i()
        == source_buffer.build_branch_summary(roots));
    assert(set_addrs_disjoint_aus(roots));
    assert(witness_buffer.sealed_branch_roots(roots));
    witness_buffer.build_branch_domain(roots);
    source_buffer.build_branch_domain(roots);
    assert(witness.branch_summary.dom()
        =~= src.persistent_branch_summary_i().dom());
    assert(witness.branch_summary
        == src.persistent_branch_summary_i()) by {
        assert_maps_equal!(
            witness.branch_summary,
            src.persistent_branch_summary_i(),
            au => {
                if witness.branch_summary.contains_key(au) {
                    let root = witness_buffer
                        .build_branch_summary_get_addr(
                            roots,
                            au,
                        );
                    witness_buffer.build_branch_summary_contains(
                        roots,
                        root,
                    );
                    source_buffer.build_branch_summary_contains(
                        roots,
                        root,
                    );
                    let witness_branch =
                        witness_buffer.get_branch(root);
                    let source_branch =
                        source_buffer.get_branch(root);
                    witness_buffer.sealed_branch_roots_contains(
                        roots,
                        root,
                    );
                    assert(witness_branch.valid_sealed_branch());
                    assert(witness_branch.has_root());
                    assert(witness_buffer.entries
                        .contains_key(root));
                    assert(source_buffer.entries
                        .contains_key(root));
                    assert(witness_buffer.entries[root]
                        == source_buffer.entries[root]);
                    assert(witness_branch.root()
                        == source_branch.root());
                    if witness_branch.root() is Index {
                        let aux = witness_branch.root()
                            .arrow_Index_aux_ptr().unwrap();
                        assert(witness_branch.sealed_root());
                        assert(witness_buffer.entries
                            .contains_key(aux));
                        assert(source_buffer.entries
                            .contains_key(aux));
                        assert(witness_buffer.entries[aux]
                            =~= source_buffer.entries[aux]);
                        assert(witness_buffer.entries[aux]
                            == source_buffer.entries[aux]);
                    }
                    reveal(crate::betree::LinkedBranch_v::
                        LinkedBranch::get_summary);
                    assert(witness_branch.get_summary()
                        == source_branch.get_summary());
                }
                if src.persistent_branch_summary_i()
                    .contains_key(au)
                {
                    assert(witness.branch_summary
                        .contains_key(au));
                    let root = source_buffer
                        .build_branch_summary_get_addr(
                            roots,
                            au,
                        );
                    source_buffer.build_branch_summary_contains(
                        roots,
                        root,
                    );
                    witness_buffer.build_branch_summary_contains(
                        roots,
                        root,
                    );
                }
            }
        );
    }
    reveal(UnifiedCacheBranchBetreeSource::
        canonical_persistent_aus_i);
}

pub proof fn persistent_image_witness_aus_match(
    src: UnifiedCacheBranchBetreeSource,
)
    requires inv(src)
    ensures ({
        let witness =
            src.persistent_branch_image_i().recovery_witness();
        witness.betree_aus.dom()
            + witness.branch_aus.dom()
            + summary_aus(witness.branch_summary)
            == src.canonical_persistent_aus_i()
    }),
{
    let image = src.persistent_branch_image_i();
    persistent_image_witness_aus_match_from_disk(
        src,
        image,
    );
}

pub proof fn post_crash_reconstructs_persistent_image(
    post: UnifiedCacheBranchBetreeSource,
    image: CachingDiskBranchBetreeImage,
)
    requires
        !post.control.metadata_loaded,
        post.cache.inv(),
        filled_cache_pages(post.cache).is_empty(),
        post.disk.inv(),
        image.valid(),
        image.metadata == post.persistent_metadata_i(),
        image.persistent
            == post.disk.content.restrict(
                addresses_in_aus(
                    image.load().betree.durable_aus(),
                ),
            ),
    ensures
        tight_betree_exists(
            post.persistent_metadata_i().root,
            to_betree_nodes(post.disk.content),
        ),
        post.canonical_persistent_aus_i()
            == image.load().betree.durable_aus(),
        post.persistent_branch_image_i() == image,
        post.branch_caching_disk_i() == image.disk(),
        post.branch_caching_disk_i().inv(),
        post.branch_caching_disk_i().visible()
            == image.disk().visible(),
{
    let witness = image.recovery_witness();
    let durable_aus =
        image.load().betree.durable_aus();
    assert(image.persistent <= post.disk.content);
    post.valid_image_implies_tight_betree_exists(image);
    persistent_image_witness_aus_match_from_disk(
        post,
        image,
    );
    reveal(CachingDiskBranchBetreeImage::load);
    reveal(CachingDiskBranchBetreeImage::cached_betree);
    reveal(CachedBranchBetree::State::durable_aus);
    assert(durable_aus
        == witness.betree_aus.dom()
            + witness.branch_aus.dom()
            + summary_aus(witness.branch_summary));
    assert(post.canonical_persistent_aus_i()
        == durable_aus);

    reveal(UnifiedCacheBranchBetreeSource::
        persistent_branch_image_i);
    assert(post.persistent_branch_image_i() == image);
    reveal(UnifiedCacheBranchBetreeSource::
        branch_projection_aus);
    assert(post.branch_projection_aus() == durable_aus);
    assert(project_persistent(post.disk, durable_aus)
        == image.persistent);
    assert(project_cache_pages(post.cache, durable_aus)
        == Map::<Address, RawPage>::empty()) by {
        assert_maps_equal!(
            project_cache_pages(post.cache, durable_aus),
            Map::<Address, RawPage>::empty(),
            addr => {
                if project_cache_pages(
                    post.cache,
                    durable_aus,
                ).contains_key(addr)
                {
                    assert(filled_cache_pages(post.cache)
                        .contains_key(addr));
                    assert(false);
                }
            }
        );
    }
    assert(project_cache_status(post.cache, durable_aus)
        == Map::<Address,
            crate::implementation::CachingDisk_v::PageStatus>::
            empty()) by {
        assert_maps_equal!(
            project_cache_status(post.cache, durable_aus),
            Map::<Address,
                crate::implementation::CachingDisk_v::
                    PageStatus>::empty(),
            addr => {
                if project_cache_status(
                    post.cache,
                    durable_aus,
                ).contains_key(addr)
                {
                    assert(filled_cache_status(post.cache)
                        .contains_key(addr));
                    assert(filled_cache_pages(post.cache)
                        .contains_key(addr));
                    assert(false);
                }
            }
        );
    }
    reveal(UnifiedCacheBranchBetreeSource::
        branch_caching_disk_i);
    reveal(CachingDiskBranchBetreeImage::disk);
    assert(post.branch_caching_disk_i() == image.disk());
    assert(post.branch_caching_disk_i().inv());
}

pub proof fn load_metadata_refines(
    pre: UnifiedCacheBranchBetreeSource,
    post: UnifiedCacheBranchBetreeSource,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        pre.control.loading,
        !pre.control.metadata_loaded,
        pre.control.recovery.complete(),
        post.cache == pre.cache,
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.sync_phase == pre.sync_phase,
        post.branch == pre.control.recovery.loaded_betree(
            pre.control.metadata,
        ),
        post.control == (AtomicBranchBetreeControl {
            persistent_aus: post.branch.durable_aus(),
            loading: false,
            metadata_loaded: true,
            ..pre.control
        }),
    ensures
        CrashAwareCachingDiskBranchBetree::State::next(
            unified_cache_branch_betree_i(pre),
            unified_cache_branch_betree_i(post),
            CrashAwareCachingDiskBranchBetree::Label::LoadMetadata,
        ),
        post.control.metadata_loaded,
        post.branch_projection_aus()
            =~= pre.branch_projection_aus(),
        inv(post),
{
    let src = unified_cache_branch_betree_i(pre);
    let dst = unified_cache_branch_betree_i(post);
    let image = src.persistent;
    let recovery = src.ephemeral->recovery;
    let recovered =
        crate::implementation::
            CrashAwareCachingDiskBranchBetreeRefinement_v::
                RecoveredCachingDiskBranchBetreeMetadata {
            betree_aus: recovery.betree_aus(image),
            branch_aus: recovery.branch_aus(image),
            branch_summary: recovery.branch_summary,
            initial_betree: recovery.initial_betree(image),
        };
    let witness = image.recovery_witness();

    reveal(UnifiedCacheBranchBetreeSource::ephemeral_branch_i);
    reveal(BetreeMetadataRecovery::from_core);
    assert(src.ephemeral is Loading);
    assert(recovery.core() == pre.control.recovery) by {
        reveal(BetreeMetadataRecovery::core);
    }
    assert(recovery.refinement_inv(image));
    assert(recovery.complete()) by {
        reveal(BetreeMetadataRecovery::complete);
        reveal(BetreeMetadataRecoveryCore::complete);
    }
    recovery_core_loaded_betree_matches(recovery, image);
    recovery_complete_metadata_matches_image(recovery, image);
    persistent_image_witness_aus_match(pre);
    assert(recovered == witness);

    reveal(BetreeMetadataRecovery::loaded_state);
    reveal(CachingDiskBranchBetreeImage::cached_betree);
    reveal(BetreeMetadataRecoveryCore::loaded_betree);
    assert(post.branch == recovery.loaded_state(image).betree);
    assert(post.branch.betree_aus == witness.betree_aus);
    assert(post.branch.branch_aus == witness.branch_aus);
    assert(post.branch.branch_summary
        == witness.branch_summary);
    assert(post.branch.compactors.len() == 0);
    assert(post.branch.wip_branches.len() == 0);
    assert(post.branch.owned_aus()
        == post.branch.durable_aus()) by {
        reveal(crate::implementation::CachedBranchBetree_v::
            CachedBranchBetree::State::owned_aus);
        reveal(crate::implementation::CachedBranchBetree_v::
            CachedBranchBetree::State::durable_aus);
        reveal(crate::implementation::CachedBranchBetree_v::
            cached_branch_alloc_aus);
    }
    assert(post.branch.durable_aus()
        == pre.canonical_persistent_aus_i()) by {
        reveal(crate::implementation::CachedBranchBetree_v::
            CachedBranchBetree::State::durable_aus);
    }
    assert(pre.control.frozen is None);
    assert(post.control.frozen is None);
    assert(post.branch_projection_aus()
        =~= pre.branch_projection_aus());
    crate::implementation::
        CachingDiskAdapterRefinement_v::
            caching_disk_i_equal_by_aus_ext(
                post.cache,
                post.disk,
                post.branch_projection_aus(),
                pre.branch_projection_aus(),
            );
    assert(post.branch_caching_disk_i()
        == pre.branch_caching_disk_i());
    assert(dst.ephemeral is Known);
    assert(dst.ephemeral->v
        == recovery.loaded_state(image));
    assert(dst.ephemeral->persistent_aus
        == recovery.loaded_state(image).betree.durable_aus());

    assert(CrashAwareCachingDiskBranchBetree::State::
        load_metadata(
            src,
            dst,
            CrashAwareCachingDiskBranchBetree::Label::LoadMetadata,
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            load_metadata);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::next_by(
        src,
        dst,
        CrashAwareCachingDiskBranchBetree::Label::LoadMetadata,
        CrashAwareCachingDiskBranchBetree::Step::load_metadata(),
    )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    src.next_refines(
        dst,
        CrashAwareCachingDiskBranchBetree::Label::LoadMetadata,
    );

    reveal(UnifiedCacheBranchBetreeSource::control_wf);
    reveal(UnifiedCacheBranchBetreeSource::inv);
    assert(post.control_wf());
    assert(post.i().refinement_inv());
    assert(post.inv());
}

proof fn page_access_betree_read_valid(
    pre: Cache::State,
    post: Cache::State,
    access: PageAccess,
    addr: Address,
)
    requires
        access.wf(),
        Cache::State::next(
            pre,
            post,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        access.betree_reads.contains_key(addr),
    ensures
        pre.valid_read(addr, access.betree_reads[addr]),
{
    assert(!access.branch_reads.contains_key(addr));
    assert(access.reads().contains_key(addr));
    assert(access.reads()[addr]
        == access.betree_reads[addr]);
    Cache::State::access_read_valid(
        pre,
        post,
        access.reads(),
        access.writes(),
        addr,
    );
}

proof fn page_access_branch_read_valid(
    pre: Cache::State,
    post: Cache::State,
    access: PageAccess,
    addr: Address,
)
    requires
        access.wf(),
        Cache::State::next(
            pre,
            post,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        access.branch_reads.contains_key(addr),
    ensures
        pre.valid_read(addr, access.branch_reads[addr]),
{
    assert(access.reads().contains_key(addr));
    assert(access.reads()[addr]
        == access.branch_reads[addr]);
    Cache::State::access_read_valid(
        pre,
        post,
        access.reads(),
        access.writes(),
        addr,
    );
}

proof fn cache_access_drop_reads(
    pre: Cache::State,
    post: Cache::State,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        Cache::State::next(
            pre,
            post,
            Cache::Label::Access{reads, writes},
        ),
    ensures
        Cache::State::next(
            pre,
            post,
            Cache::Label::Access {
                reads: Map::empty(),
                writes,
            },
        ),
{
    let source_lbl = Cache::Label::Access{reads, writes};
    let target_lbl = Cache::Label::Access {
        reads: Map::<Address, RawPage>::empty(),
        writes,
    };
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    assert(Cache::State::next_by(
        pre,
        post,
        source_lbl,
        Cache::Step::access(),
    ));
    reveal(Cache::State::access);
    assert(Cache::State::access(pre, post, source_lbl));
    assert(Cache::State::access(pre, post, target_lbl));
    assert(Cache::State::next_by(
        pre,
        post,
        target_lbl,
        Cache::Step::access(),
    ));
}

proof fn cache_access_subreads(
    pre: Cache::State,
    post: Cache::State,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    kept_reads: Map<Address, RawPage>,
)
    requires
        Cache::State::next(
            pre,
            post,
            Cache::Label::Access{reads, writes},
        ),
        kept_reads <= reads,
    ensures
        Cache::State::next(
            pre,
            post,
            Cache::Label::Access {
                reads: kept_reads,
                writes,
            },
        ),
{
    let source_lbl = Cache::Label::Access{reads, writes};
    let target_lbl = Cache::Label::Access {
        reads: kept_reads,
        writes,
    };
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    assert(Cache::State::next_by(
        pre,
        post,
        source_lbl,
        Cache::Step::access(),
    ));
    reveal(Cache::State::access);
    assert(Cache::State::access(pre, post, source_lbl));
    assert forall |addr: Address|
        #[trigger] kept_reads.contains_key(addr)
        implies pre.valid_read(addr, kept_reads[addr])
    by {
        assert(reads.contains_key(addr));
        Cache::State::access_read_valid(
            pre,
            post,
            reads,
            writes,
            addr,
        );
        assert(kept_reads[addr] == reads[addr]);
    }
    assert(Cache::State::access(pre, post, target_lbl));
    assert(Cache::State::next_by(
        pre,
        post,
        target_lbl,
        Cache::Step::access(),
    ));
}

proof fn betree_receipt_needed_addr_in_projection(
    src: UnifiedCacheBranchBetreeSource,
    post_cache: Cache::State,
    access: PageAccess,
    linked: LinkedBetree<BranchNode>,
    receipt: LoadedBetreePath,
    addr: Address,
)
    requires
        inv(src),
        src.control.metadata_loaded,
        access.wf(),
        Cache::State::next(
            src.cache,
            post_cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        linked.acyclic(),
        linked.dv == src.known_branch_i().linked_i().dv,
        linked.dv.entries
            <= to_betree_nodes(
                src.known_branch_i().disk.visible(),
            ),
        receipt.valid_for(
            linked.root,
            to_betree_nodes(access.betree_reads),
        ),
        receipt.needed_addrs().contains(addr),
    ensures
        addresses_in_aus(
            src.branch_projection_aus(),
        ).contains(addr),
    decreases receipt.depth(),
{
    let component = src.known_branch_i();
    let root = linked.root.unwrap();
    let root_reads =
        access.betree_reads.restrict(set![root]);

    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(src.i().ephemeral is Known);
    assert(component.refinement_inv());
    assert(component.i().inv());
    assert(component.i().betree.linked.dv
        == linked.dv);
    assert(addrs_closed(
        linked.dv.entries.dom(),
        component.betree.betree_aus.dom(),
    ));
    assert(linked.dv.entries.contains_key(root));
    assert(component.betree.betree_aus.dom()
        .contains(root.au));
    reveal(UnifiedCacheBranchBetreeSource::
        branch_projection_aus);
    reveal(CachedBranchBetree::State::owned_aus);
    assert(src.branch_projection_aus()
        .contains(root.au));
    assert(addresses_in_aus(
        src.branch_projection_aus(),
    ).contains(root));

    assert(receipt.needed_addrs().contains(root)) by {
        assert(receipt.lines[0].addr == receipt.root);
    }
    assert(to_betree_nodes(
        access.betree_reads,
    ).contains_key(root));
    assert(access.betree_reads.contains_key(root));
    page_access_betree_read_valid(
        src.cache,
        post_cache,
        access,
        root,
    );
    assert forall |read_addr: Address|
        #[trigger] root_reads.contains_key(read_addr)
        implies src.cache.valid_read(
            read_addr,
            root_reads[read_addr],
        )
    by {
        assert(read_addr == root);
    };
    assert(root_reads.dom()
        <= addresses_in_aus(
            src.branch_projection_aus(),
        ));
    valid_reads_in_project_cache_by_addrs(
        src.cache,
        addresses_in_aus(src.branch_projection_aus()),
        root_reads,
    );
    assert(root_reads <= component.disk.cache) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_caching_disk_i);
        reveal(UnifiedCacheBranchBetreeSource::
            known_branch_i);
        reveal(crate::implementation::
            CachingDiskAdapterRefinement_v::
                project_cache_pages_by_addrs);
        reveal(project_cache_pages);
    }
    assert(to_betree_nodes(
        component.disk.visible(),
    ).contains_key(root));
    assert(component.disk.visible().contains_key(root));
    betree_read_node_matches_visible(
        component.disk,
        root_reads,
        root,
    );
    assert(to_betree_nodes(root_reads)[root]
        == to_betree_nodes(access.betree_reads)[root]);
    assert(receipt.lines[0].node
        == linked.dv.entries[root]);

    if addr != root {
        assert(receipt.depth() > 0) by {
            if receipt.depth() == 0 {
                assert(receipt.lines.len() == 1);
                let i = choose |i: int|
                    0 <= i < receipt.lines.len()
                        && receipt.lines[i].addr == addr;
                assert(i == 0);
                assert(receipt.lines[0].addr == root);
            }
        }
        let tail = receipt.tail();
        let child = linked.child_for_key(receipt.key);
        loaded_betree_path_wf_child(receipt, 0);
        assert(linked.root()
            == receipt.lines[0].node);
        assert(child.root == Some(tail.root));
        let ranking = linked.the_ranking();
        assert(linked.valid_ranking(ranking));
        assert(child.valid_ranking(ranking)) by {
            let child_idx =
                linked.root().pivots.route(receipt.key)
                    as nat;
            linked.root().pivots.route_lemma(
                receipt.key,
            );
            assert(linked.root().valid_child_index(
                child_idx,
            ));
            assert(linked.dv.node_children_respects_rank(
                ranking,
                root,
            ));
            assert(ranking.contains_key(tail.root));
        }
        assert(child.acyclic());
        loaded_betree_path_tail_valid(
            receipt,
            to_betree_nodes(access.betree_reads),
        );
        assert(tail.valid_for(
            child.root,
            to_betree_nodes(access.betree_reads),
        ));
        assert(tail.needed_addrs().contains(addr)) by {
            let i = choose |i: int|
                0 <= i < receipt.lines.len()
                    && receipt.lines[i].addr == addr;
            assert(i > 0);
            assert(tail.lines[i - 1]
                == receipt.lines[i]);
        }
        betree_receipt_needed_addr_in_projection(
            src,
            post_cache,
            access,
            child,
            tail,
            addr,
        );
    }
}

proof fn project_betree_path_reads(
    src: UnifiedCacheBranchBetreeSource,
    post_cache: Cache::State,
    access: PageAccess,
    path: LoadedBetreePath,
)
    requires
        inv(src),
        src.control.metadata_loaded,
        access.wf(),
        Cache::State::next(
            src.cache,
            post_cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        path.valid_for(
            src.branch.root,
            to_betree_nodes(access.betree_reads),
        ),
    ensures ({
        let owned_addrs =
            addresses_in_aus(src.branch_projection_aus());
        let tight_reads =
            access.betree_reads.restrict(owned_addrs);
        &&& tight_reads <= src.known_branch_i().disk.cache
        &&& src.known_branch_i().linked_i().dv.entries
            <= to_betree_nodes(
                src.known_branch_i().disk.visible(),
            )
        &&& path.valid_for(
            src.known_branch_i().linked_i().root,
            to_betree_nodes(tight_reads),
        )
    }),
{
    let component = src.known_branch_i();
    let linked = component.linked_i();
    let owned_addrs =
        addresses_in_aus(src.branch_projection_aus());
    let tight_reads =
        access.betree_reads.restrict(owned_addrs);

    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(src.i().ephemeral is Known);
    assert(component.refinement_inv());
    component.linked_i_is_tight_candidate();
    component.linked_i_tight_tree_facts();
    assert(linked.acyclic());
    assert(linked.dv.entries
        <= to_betree_nodes(component.disk.visible())) by {
        assert(linked.dv.entries
            <= component.visible_betree_entries());
        assert(component.visible_betree_entries()
            <= to_betree_nodes(component.disk.visible())) by {
            assert forall |addr: Address|
                #[trigger] component.visible_betree_entries()
                    .contains_key(addr)
                implies {
                    &&& to_betree_nodes(
                        component.disk.visible(),
                    ).contains_key(addr)
                    &&& component.visible_betree_entries()[addr]
                        == to_betree_nodes(
                            component.disk.visible(),
                        )[addr]
                }
            by {
                reveal(CachingDiskBranchBetree::State::
                    visible_betree_entries);
            }
        }
        vstd::map_lib::lemma_submap_of_trans(
            linked.dv.entries,
            component.visible_betree_entries(),
            to_betree_nodes(component.disk.visible()),
        );
    }

    assert forall |addr: Address|
        #[trigger] tight_reads.contains_key(addr)
        implies src.cache.valid_read(
            addr,
            tight_reads[addr],
        )
    by {
        page_access_betree_read_valid(
            src.cache,
            post_cache,
            access,
            addr,
        );
    }
    valid_reads_in_project_cache_by_addrs(
        src.cache,
        owned_addrs,
        tight_reads,
    );
    assert(tight_reads <= component.disk.cache) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_caching_disk_i);
        reveal(UnifiedCacheBranchBetreeSource::
            known_branch_i);
        reveal(crate::implementation::
            CachingDiskAdapterRefinement_v::
                project_cache_pages_by_addrs);
        reveal(project_cache_pages);
    }
    assert(path.valid_for(
        linked.root,
        to_betree_nodes(tight_reads),
    )) by {
        assert(path.needed_addrs()
            <= to_betree_nodes(tight_reads).dom()) by {
            assert forall |addr: Address|
                #[trigger] path.needed_addrs().contains(addr)
                implies to_betree_nodes(tight_reads)
                    .contains_key(addr)
            by {
                betree_receipt_needed_addr_in_projection(
                    src,
                    post_cache,
                    access,
                    linked,
                    path,
                    addr,
                );
                assert(tight_reads.contains_key(addr));
            }
        }
        assert forall |i: int| 0 <= i < path.lines.len()
            implies {
                &&& to_betree_nodes(tight_reads)
                    .contains_key(path.lines[i].addr)
                &&& #[trigger] to_betree_nodes(tight_reads)[
                    path.lines[i].addr
                ] == path.lines[i].node
            }
        by {
            let addr = path.lines[i].addr;
            assert(path.needed_addrs().contains(addr));
            betree_receipt_needed_addr_in_projection(
                src,
                post_cache,
                access,
                linked,
                path,
                addr,
            );
            assert(tight_reads.contains_key(addr));
            assert(tight_reads[addr]
                == access.betree_reads[addr]);
            assert(to_betree_nodes(tight_reads)[addr]
                == to_betree_nodes(
                    access.betree_reads,
                )[addr]);
        }
    }
}

pub open spec fn betree_path_with_child_addrs(
    path: LoadedBetreePath,
    child_idx: nat,
) -> Set<Address>
    recommends
        path.lines.len() > 0,
        path.target().node.valid_child_index(child_idx),
        path.target().node.children[child_idx as int] is Some,
{
    path.needed_addrs()
        + set![path.child_addr(child_idx)]
}

proof fn project_betree_path_with_child_reads(
    src: UnifiedCacheBranchBetreeSource,
    post_cache: Cache::State,
    access: PageAccess,
    path: LoadedBetreePath,
    child_idx: nat,
)
    requires
        inv(src),
        src.control.metadata_loaded,
        access.wf(),
        Cache::State::next(
            src.cache,
            post_cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        path.valid_for(
            src.branch.root,
            to_betree_nodes(access.betree_reads),
        ),
        path.target().node.valid_child_index(child_idx),
        path.target().node.children[child_idx as int] is Some,
        access.betree_reads.contains_key(
            path.child_addr(child_idx),
        ),
    ensures ({
        let required = access.betree_reads.restrict(
            betree_path_with_child_addrs(path, child_idx),
        );
        &&& required <= src.known_branch_i().disk.cache
        &&& path.valid_for(
            src.known_branch_i().linked_i().root,
            to_betree_nodes(required),
        )
        &&& required.contains_key(path.child_addr(child_idx))
        &&& to_betree_nodes(required)[
            path.child_addr(child_idx)
        ] == to_betree_nodes(access.betree_reads)[
            path.child_addr(child_idx)
        ]
    }),
{
    let component = src.known_branch_i();
    let linked = component.linked_i();
    let owned_addrs =
        addresses_in_aus(src.branch_projection_aus());
    let owned_reads =
        access.betree_reads.restrict(owned_addrs);
    let child_addr = path.child_addr(child_idx);
    let required_addrs =
        betree_path_with_child_addrs(path, child_idx);
    let required =
        access.betree_reads.restrict(required_addrs);

    project_betree_path_reads(
        src,
        post_cache,
        access,
        path,
    );
    assert(path.valid_for(
        linked.root,
        to_betree_nodes(owned_reads),
    ));
    loaded_betree_path_matches_linked(
        component.disk,
        linked,
        owned_reads,
        path,
        path.depth(),
    );
    let semantic_path = crate::betree::LinkedBetree_v::Path {
        linked,
        key: path.key,
        depth: path.depth(),
    };
    assert(semantic_path.valid());
    assert(semantic_path.target().root()
        == path.target().node);
    assert(semantic_path.target().dv.entries
        == linked.dv.entries);
    assert(linked.dv.entries.contains_key(child_addr)) by {
        assert(semantic_path.target().root()
            .children[child_idx as int]
            == Some(child_addr));
        assert(semantic_path.target().dv
            .is_nondangling_ptr(Some(child_addr)));
    }
    assert(component.i().inv());
    assert(addrs_closed(
        linked.dv.entries.dom(),
        component.betree.betree_aus.dom(),
    ));
    assert(component.betree.betree_aus.dom()
        .contains(child_addr.au));
    reveal(UnifiedCacheBranchBetreeSource::
        branch_projection_aus);
    reveal(CachedBranchBetree::State::owned_aus);
    assert(src.branch_projection_aus()
        .contains(child_addr.au));
    assert(owned_addrs.contains(child_addr));

    assert forall |addr: Address|
        #[trigger] required.contains_key(addr)
        implies {
            &&& owned_addrs.contains(addr)
            &&& src.cache.valid_read(
                addr,
                required[addr],
            )
        }
    by {
        if addr == child_addr {
            assert(access.betree_reads.contains_key(addr));
        } else {
            assert(path.needed_addrs().contains(addr));
            betree_receipt_needed_addr_in_projection(
                src,
                post_cache,
                access,
                linked,
                path,
                addr,
            );
        }
        page_access_betree_read_valid(
            src.cache,
            post_cache,
            access,
            addr,
        );
    }
    assert(required.dom() <= owned_addrs);
    valid_reads_in_project_cache_by_addrs(
        src.cache,
        owned_addrs,
        required,
    );
    assert(required <= component.disk.cache) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_caching_disk_i);
        reveal(UnifiedCacheBranchBetreeSource::
            known_branch_i);
        reveal(crate::implementation::
            CachingDiskAdapterRefinement_v::
                project_cache_pages_by_addrs);
        reveal(project_cache_pages);
    }
    assert(path.valid_for(
        linked.root,
        to_betree_nodes(required),
    )) by {
        assert(path.needed_addrs()
            <= to_betree_nodes(required).dom()) by {
            assert forall |addr: Address|
                #[trigger] path.needed_addrs().contains(addr)
                implies required.contains_key(addr)
            by {
                assert(required_addrs.contains(addr));
                assert(access.betree_reads.contains_key(addr));
            }
        }
        assert forall |i: int| 0 <= i < path.lines.len()
            implies {
                &&& to_betree_nodes(required)
                    .contains_key(path.lines[i].addr)
                &&& #[trigger] to_betree_nodes(required)[
                    path.lines[i].addr
                ] == path.lines[i].node
            }
        by {
            let addr = path.lines[i].addr;
            assert(path.needed_addrs().contains(addr));
            assert(required.contains_key(addr));
            assert(required[addr]
                == access.betree_reads[addr]);
            assert(to_betree_nodes(required)[addr]
                == to_betree_nodes(
                    access.betree_reads,
                )[addr]);
        }
    }
    assert(required.contains_key(child_addr));
    assert(required[child_addr]
        == access.betree_reads[child_addr]);
}

proof fn finite_set_to_multiset_dom<A>(set: Set<A>)
    requires
        set.finite(),
    ensures
        set.to_multiset().dom() == set,
    decreases set.len(),
{
    reveal(Set::to_multiset);
    if set.len() == 0 {
        set.lemma_len0_is_empty();
    } else {
        let elem = set.choose();
        finite_set_to_multiset_dom(set.remove(elem));
        assert(set
            == set.remove(elem).insert(elem)) by {
            assert forall |candidate: A|
                #[trigger] set.contains(candidate)
                <==> set.remove(elem).insert(elem)
                    .contains(candidate)
            by {
            }
        }
    }
}

proof fn summary_aus_restrict_subset(
    summaries: Map<AU, Summary>,
    keys: Set<AU>,
)
    requires
        summaries.dom().finite(),
    ensures
        summary_aus(summaries.restrict(keys))
            <= summary_aus(summaries),
{
    vstd::map_lib::lemma_values_finite(summaries);
    crate::betree::Utils_v::lemma_subset_finite(
        summaries.dom(),
        summaries.restrict(keys).dom(),
    );
    vstd::map_lib::lemma_values_finite(
        summaries.restrict(keys),
    );
    assert forall |au: AU|
        #[trigger] summary_aus(
            summaries.restrict(keys),
        ).contains(au)
        implies summary_aus(summaries).contains(au)
    by {
        let summary =
            crate::betree::Utils_v::
                lemma_union_set_of_sets_contains(
                    summaries.restrict(keys).values(),
                    au,
                );
        assert(summaries.values().contains(summary));
        crate::betree::Utils_v::
            lemma_union_set_of_sets_subset(
                summaries.values(),
                summary,
            );
    }
}

proof fn split_owned_aus_effect(
    pre: UnifiedCacheBranchBetreeSource,
    post_component: CachingDiskBranchBetree::State,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    path: LoadedBetreePath,
    request: SplitRequest,
    new_addrs: SplitAddrs,
    path_addrs: PathAddrs,
    betree_reads:
        Map<Address, crate::betree::LinkedBetree_v::BetreeNode>,
    betree_writes:
        Map<Address, crate::betree::LinkedBetree_v::BetreeNode>,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        post_component.refinement_inv(),
        CachedBranchBetree::State::split(
            pre.branch,
            post_component.betree,
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
            path,
            request,
            new_addrs,
            path_addrs,
            betree_reads,
            betree_writes,
        ),
    ensures
        post_component.betree.owned_aus()
            == (pre.branch.owned_aus() + allocs) - deallocs,
        deallocs <= pre.branch.owned_aus(),
{
    reveal(CachedBranchBetree::State::split);
    reveal(CachedBranchBetree::State::owned_aus);
    let discarded =
        path_discard_likes(path).insert(
            path.child_addr(request.get_child_idx()),
        );
    let added = added_path_likes(new_addrs, path_addrs);
    let new_betree_aus =
        pre.branch.betree_aus
            .sub(to_au_likes(discarded))
            .add(to_au_likes(added));
    let pre_owned = pre.branch.owned_aus();
    let post_owned = post_component.betree.owned_aus();

    reveal(added_path_likes);
    path_addrs.to_multiset_ensures();
    assert(new_addrs.repr()
        == set![
            new_addrs.left,
            new_addrs.right,
            new_addrs.parent,
        ]);
    assert(new_addrs.repr().finite());
    finite_set_to_multiset_dom(new_addrs.repr());
    assert(added
        == new_addrs.repr().to_multiset()
            .add(path_addrs.to_multiset()));
    assert forall |addr: Address|
        #[trigger] added.dom().contains(addr)
        <==> (new_addrs.repr()
            + path_addrs.to_set()).contains(addr)
    by {
    }
    assert(added.dom()
        =~= new_addrs.repr() + path_addrs.to_set());
    crate::allocation_layer::Likes_v::
        to_au_likes_domain(added);
    assert(added.dom()
        =~= new_addrs.repr() + path_addrs.to_set());
    assert(to_au_likes(added).dom() == allocs);
    assert(allocs <= new_betree_aus.dom());
    assert(new_betree_aus.dom()
        <= pre.branch.betree_aus.dom() + allocs);
    assert(deallocs
        == pre.branch.betree_aus.dom()
            - new_betree_aus.dom());
    assert(new_betree_aus.dom()
        == (pre.branch.betree_aus.dom() + allocs)
            - deallocs) by {
        assert forall |au: AU|
            #[trigger] new_betree_aus.dom().contains(au)
            <==> ((pre.branch.betree_aus.dom() + allocs)
                - deallocs).contains(au)
        by {
        }
    }

    let pre_i = pre.known_branch_i().i();
    let post_i = post_component.i();
    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(pre.i().ephemeral is Known);
    assert(pre.known_branch_i().refinement_inv());
    assert(pre_i.inv());
    assert(post_i.inv());
    pre.known_branch_i().wip_alloc_aus_agree();
    post_component.wip_alloc_aus_agree();
    pre_i.inv_branch_summary_ensures();
    post_i.inv_branch_summary_ensures();
    assert(pre.branch.branch_aus.dom()
        <= summary_aus(pre.branch.branch_summary));
    assert(post_component.betree.branch_aus.dom()
        <= summary_aus(
            post_component.betree.branch_summary,
        ));
    assert(post_component.betree.branch_summary
        == pre.branch.branch_summary);
    assert(post_component.betree.wip_branches
        == pre.branch.wip_branches);

    let pre_betree_aus = pre.branch.betree_aus.dom();
    let post_betree_aus =
        post_component.betree.betree_aus.dom();
    let sealed_aus =
        summary_aus(pre.branch.branch_summary);
    let wip_aus =
        cached_branch_alloc_aus(pre.branch.wip_branches);
    assert(pre_owned
        == pre_betree_aus + sealed_aus + wip_aus) by {
        assert forall |au: AU|
            #[trigger] pre_owned.contains(au)
            <==> (pre_betree_aus + sealed_aus
                + wip_aus).contains(au)
        by {
        }
    }
    assert(post_owned
        == post_betree_aus + sealed_aus + wip_aus) by {
        assert forall |au: AU|
            #[trigger] post_owned.contains(au)
            <==> (post_betree_aus + sealed_aus
                + wip_aus).contains(au)
        by {
        }
    }
    assert(deallocs <= pre_betree_aus);
    assert(deallocs <= pre_owned);
    assert(pre_betree_aus.disjoint(sealed_aus));
    assert(pre_betree_aus.disjoint(wip_aus));
    assert(post_betree_aus.disjoint(sealed_aus));
    assert(post_betree_aus.disjoint(wip_aus));
    assert(allocs <= post_betree_aus);
    assert(post_owned
        == (pre_owned + allocs) - deallocs) by {
        assert forall |au: AU|
            #[trigger] post_owned.contains(au)
            <==> ((pre_owned + allocs) - deallocs)
                .contains(au)
        by {
            assert(post_betree_aus
                == (pre_betree_aus + allocs)
                    - deallocs);
        }
    }
}

proof fn flush_owned_aus_effect(
    pre: UnifiedCacheBranchBetreeSource,
    post_component: CachingDiskBranchBetree::State,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    path: LoadedBetreePath,
    child_idx: nat,
    buffer_gc: nat,
    new_addrs: TwoAddrs,
    path_addrs: PathAddrs,
    betree_reads:
        Map<Address, crate::betree::LinkedBetree_v::BetreeNode>,
    betree_writes:
        Map<Address, crate::betree::LinkedBetree_v::BetreeNode>,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        post_component.refinement_inv(),
        CachedBranchBetree::State::flush(
            pre.branch,
            post_component.betree,
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
            path,
            child_idx,
            buffer_gc,
            new_addrs,
            path_addrs,
            betree_reads,
            betree_writes,
        ),
    ensures
        post_component.betree.owned_aus()
            == (pre.branch.owned_aus() + allocs) - deallocs,
        deallocs <= pre.branch.owned_aus(),
{
    reveal(CachedBranchBetree::State::flush);
    reveal(CachedBranchBetree::State::owned_aus);
    let child_addr = path.child_addr(child_idx);
    let discarded =
        path_discard_likes(path).insert(child_addr);
    let added = added_path_likes(new_addrs, path_addrs);
    let new_betree_aus =
        pre.branch.betree_aus
            .sub(to_au_likes(discarded))
            .add(to_au_likes(added));
    let target = path.target().node;
    let discarded_branches = target.buffers
        .slice(0, buffer_gc as int).addrs
        .to_multiset();
    let flushed_ofs =
        target.flushed.offsets[child_idx as int];
    let added_branches = target.buffers
        .slice(
            flushed_ofs as int,
            target.buffers.len() as int,
        ).addrs.to_multiset();
    let new_branch_aus =
        pre.branch.branch_aus
            .sub(to_au_likes(discarded_branches))
            .add(to_au_likes(added_branches));
    let branch_deallocs =
        pre.branch.branch_aus.dom()
            - new_branch_aus.dom()
            - crate::allocation_layer::
                AllocationBranchBetree_v::read_ref_aus(
                    pre.branch.compactors,
                );
    let deallocated_summary =
        pre.branch.branch_summary.restrict(
            branch_deallocs,
        );
    let tree_deallocs =
        pre.branch.betree_aus.dom()
            - new_betree_aus.dom();
    let summary_deallocs =
        summary_aus(deallocated_summary);
    let pre_summary_aus =
        summary_aus(pre.branch.branch_summary);
    let post_summary_aus =
        summary_aus(
            post_component.betree.branch_summary,
        );

    reveal(added_path_likes);
    path_addrs.to_multiset_ensures();
    assert(new_addrs.repr()
        == set![new_addrs.addr1, new_addrs.addr2]);
    assert(new_addrs.repr().finite());
    finite_set_to_multiset_dom(new_addrs.repr());
    assert(added
        == new_addrs.repr().to_multiset()
            .add(path_addrs.to_multiset()));
    assert forall |addr: Address|
        #[trigger] added.dom().contains(addr)
        <==> (new_addrs.repr()
            + path_addrs.to_set()).contains(addr)
    by {
    }
    assert(added.dom()
        =~= new_addrs.repr() + path_addrs.to_set());
    crate::allocation_layer::Likes_v::
        to_au_likes_domain(added);
    assert(to_au_likes(added).dom() == allocs);
    assert(allocs <= new_betree_aus.dom());
    assert(new_betree_aus.dom()
        <= pre.branch.betree_aus.dom() + allocs);
    assert(new_betree_aus.dom()
        == (pre.branch.betree_aus.dom() + allocs)
            - tree_deallocs) by {
        assert forall |au: AU|
            #[trigger] new_betree_aus.dom().contains(au)
            <==> ((pre.branch.betree_aus.dom()
                + allocs) - tree_deallocs)
                .contains(au)
        by {
        }
    }
    assert(deallocs
        == tree_deallocs + summary_deallocs);

    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(pre.i().ephemeral is Known);
    assert(pre.known_branch_i().refinement_inv());
    let pre_i = pre.known_branch_i().i();
    let post_i = post_component.i();
    assert(pre_i.inv());
    assert(post_i.inv());
    pre.known_branch_i().wip_alloc_aus_agree();
    post_component.wip_alloc_aus_agree();
    pre_i.inv_branch_summary_ensures();
    post_i.inv_branch_summary_ensures();
    let (_, branch_likes) =
        pre_i.betree.linked.transitive_likes();
    let branch_roots =
        branch_likes.dom()
            + CompactorInput::input_roots(
                pre_i.compactors,
            );
    pre.known_branch_i()
        .semantic_sealed_branch_disk()
        .build_branch_summary_finite(branch_roots);
    vstd::map_lib::lemma_values_finite(
        pre.branch.branch_summary,
    );
    summary_partition_disjoint(
        pre.branch.branch_summary,
        branch_deallocs,
    );
    assert(post_component.betree.branch_summary
        == pre.branch.branch_summary.remove_keys(
            branch_deallocs,
        ));
    assert(pre_summary_aus
        == post_summary_aus + summary_deallocs);
    assert(post_summary_aus.disjoint(
        summary_deallocs,
    ));

    let pre_betree_aus = pre.branch.betree_aus.dom();
    let post_betree_aus =
        post_component.betree.betree_aus.dom();
    let wip_aus =
        cached_branch_alloc_aus(pre.branch.wip_branches);
    let pre_owned = pre.branch.owned_aus();
    let post_owned = post_component.betree.owned_aus();
    assert(pre.branch.branch_aus.dom()
        <= pre_summary_aus);
    assert(post_component.betree.branch_aus.dom()
        <= post_summary_aus);
    assert(post_component.betree.wip_branches
        == pre.branch.wip_branches);
    assert(pre_owned
        == pre_betree_aus + pre_summary_aus
            + wip_aus) by {
        assert forall |au: AU|
            #[trigger] pre_owned.contains(au)
            <==> (pre_betree_aus + pre_summary_aus
                + wip_aus).contains(au)
        by {
        }
    }
    assert(post_owned
        == post_betree_aus + post_summary_aus
            + wip_aus) by {
        assert forall |au: AU|
            #[trigger] post_owned.contains(au)
            <==> (post_betree_aus
                + post_summary_aus
                + wip_aus).contains(au)
        by {
        }
    }
    assert(pre_betree_aus.disjoint(pre_summary_aus));
    assert(pre_betree_aus.disjoint(wip_aus));
    assert(pre_summary_aus.disjoint(wip_aus));
    assert(post_betree_aus.disjoint(
        post_summary_aus,
    ));
    assert(post_betree_aus.disjoint(wip_aus));
    assert(post_summary_aus.disjoint(wip_aus));
    assert(tree_deallocs <= pre_betree_aus);
    assert(summary_deallocs <= pre_summary_aus);
    assert(deallocs <= pre_owned);
    assert(post_owned
        == (pre_owned + allocs) - deallocs) by {
        assert forall |au: AU|
            #[trigger] post_owned.contains(au)
            <==> ((pre_owned + allocs) - deallocs)
                .contains(au)
        by {
            assert(post_betree_aus
                == (pre_betree_aus + allocs)
                    - tree_deallocs);
            assert(pre_summary_aus
                == post_summary_aus
                    + summary_deallocs);
        }
    }
}

proof fn compact_abort_owned_aus_effect(
    pre: UnifiedCacheBranchBetreeSource,
    post_component: CachingDiskBranchBetree::State,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    input_idx: int,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        post_component.refinement_inv(),
        CachedBranchBetree::State::compact_abort(
            pre.branch,
            post_component.betree,
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
            input_idx,
        ),
    ensures
        post_component.betree.owned_aus()
            == pre.branch.owned_aus() - deallocs,
        cached_branch_alloc_aus(
            post_component.betree.wip_branches,
        ) == cached_branch_alloc_aus(
            pre.branch.wip_branches,
        ) - deallocs,
        deallocs <= pre.branch.owned_aus(),
{
    reveal(CachedBranchBetree::State::compact_abort);
    reveal(CachedBranchBetree::State::owned_aus);
    let new_compactors =
        pre.branch.compactors.remove(input_idx);
    let released =
        crate::allocation_layer::
            AllocationBranchBetree_v::read_ref_aus(
                pre.branch.compactors,
            )
        - crate::allocation_layer::
            AllocationBranchBetree_v::read_ref_aus(
                new_compactors,
            );
    let branch_deallocs =
        released - pre.branch.branch_aus.dom();
    let deallocated_summary =
        pre.branch.branch_summary.restrict(
            branch_deallocs,
        );
    let pre_summary_aus =
        summary_aus(pre.branch.branch_summary);
    let post_summary_aus =
        summary_aus(
            post_component.betree.branch_summary,
        );

    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(pre.i().ephemeral is Known);
    assert(pre.known_branch_i().refinement_inv());
    let pre_i = pre.known_branch_i().i();
    let post_i = post_component.i();
    assert(pre_i.inv());
    assert(post_i.inv());
    pre.known_branch_i().wip_alloc_aus_agree();
    post_component.wip_alloc_aus_agree();
    pre_i.inv_branch_summary_ensures();
    post_i.inv_branch_summary_ensures();
    let (_, branch_likes) =
        pre_i.betree.linked.transitive_likes();
    let branch_roots =
        branch_likes.dom()
            + CompactorInput::input_roots(
                pre_i.compactors,
            );
    pre.known_branch_i()
        .semantic_sealed_branch_disk()
        .build_branch_summary_finite(branch_roots);
    vstd::map_lib::lemma_values_finite(
        pre.branch.branch_summary,
    );
    summary_partition_disjoint(
        pre.branch.branch_summary,
        branch_deallocs,
    );
    assert(allocs.is_empty());
    assert(deallocs
        == summary_aus(deallocated_summary));
    assert(post_component.betree.branch_summary
        == pre.branch.branch_summary.remove_keys(
            branch_deallocs,
        ));
    assert(pre_summary_aus
        == post_summary_aus + deallocs);
    assert(post_summary_aus.disjoint(deallocs));
    assert(deallocs <= pre_summary_aus);

    let betree_aus = pre.branch.betree_aus.dom();
    let wip_aus =
        cached_branch_alloc_aus(pre.branch.wip_branches);
    let pre_owned = pre.branch.owned_aus();
    let post_owned = post_component.betree.owned_aus();
    assert(post_component.betree.betree_aus
        == pre.branch.betree_aus);
    assert(post_component.betree.wip_branches
        == pre.branch.wip_branches);
    assert(pre.branch.branch_aus.dom()
        <= pre_summary_aus);
    assert(post_component.betree.branch_aus.dom()
        <= post_summary_aus);
    assert(pre_owned
        == betree_aus + pre_summary_aus
            + wip_aus) by {
        assert forall |au: AU|
            #[trigger] pre_owned.contains(au)
            <==> (betree_aus + pre_summary_aus
                + wip_aus).contains(au)
        by {
        }
    }
    assert(deallocs <= pre_owned);
    assert(post_owned
        == betree_aus + post_summary_aus
            + wip_aus) by {
        assert forall |au: AU|
            #[trigger] post_owned.contains(au)
            <==> (betree_aus + post_summary_aus
                + wip_aus).contains(au)
        by {
        }
    }
    assert(betree_aus.disjoint(pre_summary_aus));
    assert(betree_aus.disjoint(wip_aus));
    assert(pre_summary_aus.disjoint(wip_aus));
    assert(post_owned == pre_owned - deallocs) by {
        assert forall |au: AU|
            #[trigger] post_owned.contains(au)
            <==> (pre_owned - deallocs).contains(au)
        by {
        }
    }
}

proof fn flush_memtable_owned_aus_effect(
    pre: UnifiedCacheBranchBetreeSource,
    post_component: CachingDiskBranchBetree::State,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    branch_idx: int,
    new_root_addr: Address,
    betree_reads:
        Map<Address, crate::betree::LinkedBetree_v::BetreeNode>,
    betree_writes:
        Map<Address, crate::betree::LinkedBetree_v::BetreeNode>,
    branch_reads:
        Map<Address, crate::allocation_layer::
            AllocationBranch_v::BranchNode>,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        post_component.refinement_inv(),
        CachedBranchBetree::State::flush_memtable(
            pre.branch,
            post_component.betree,
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
            branch_idx,
            new_root_addr,
            betree_reads,
            betree_writes,
            branch_reads,
        ),
    ensures
        post_component.betree.owned_aus()
            == (pre.branch.owned_aus() + allocs) - deallocs,
        cached_branch_alloc_aus(
            post_component.betree.wip_branches,
        ) <= cached_branch_alloc_aus(
            pre.branch.wip_branches,
        ),
        deallocs <= pre.branch.owned_aus(),
{
    reveal(CachedBranchBetree::State::flush_memtable);
    reveal(CachedBranchBetree::State::owned_aus);
    let cached_branch =
        pre.branch.wip_branches[branch_idx];
    let branch_root =
        cached_branch.sealed_root().unwrap();
    let branch_owned =
        cached_branch.mini_allocator.all_aus();
    let old_root_likes = if pre.branch.root is Some {
        Multiset::singleton(pre.branch.root.unwrap())
    } else {
        Multiset::empty()
    };
    let new_betree_aus =
        pre.branch.betree_aus
            .sub(to_au_likes(old_root_likes))
            .insert(new_root_addr.au);
    let tree_deallocs =
        pre.branch.betree_aus.dom()
            - new_betree_aus.dom();

    assert(allocs == set![new_root_addr.au]);
    assert(allocs <= new_betree_aus.dom());
    assert(new_betree_aus.dom()
        <= pre.branch.betree_aus.dom() + allocs);
    assert(deallocs == tree_deallocs);
    assert(new_betree_aus.dom()
        == (pre.branch.betree_aus.dom() + allocs)
            - deallocs) by {
        assert forall |au: AU|
            #[trigger] new_betree_aus.dom().contains(au)
            <==> ((pre.branch.betree_aus.dom()
                + allocs) - deallocs).contains(au)
        by {
        }
    }

    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(pre.i().ephemeral is Known);
    assert(pre.known_branch_i().refinement_inv());
    let pre_component = pre.known_branch_i();
    let pre_i = pre_component.i();
    let post_i = post_component.i();
    assert(pre_i.inv());
    assert(post_i.inv());
    pre_component.wip_alloc_aus_agree();
    post_component.wip_alloc_aus_agree();
    pre_i.inv_branch_summary_ensures();
    post_i.inv_branch_summary_ensures();
    assert(pre_i.wip_branches_inv());
    assert(pre_i.wip_branches_disjoint());
    let model_branch =
        pre_i.wip_branches[branch_idx]
            .branch.unwrap();
    assert(pre_i.wip_branches[branch_idx]
        .mini_allocator
        == cached_branch.mini_allocator) by {
        reveal(CachingDiskBranchBetree::State::
            wip_branches_i);
        reveal(CachingDiskBranchBetree::State::
            wip_branch_i);
    }
    crate::allocation_layer::AllocationBranch_v::
        AllocationBranch::alloc_aus_ensures(
            pre_i.wip_branches,
            branch_idx,
        );
    assert(branch_owned
        <= pre_i.branch_allocator_aus());
    assert(pre_i.wip_branches[branch_idx].inv());
    assert(pre_i.wip_branches[branch_idx].sealed);
    assert(model_branch.valid_sealed_branch());
    assert(model_branch.get_summary()
        == branch_owned);
    assert(pre.branch.branch_summary.dom().finite()) by {
        let (_, branch_likes) =
            pre_i.betree.linked.transitive_likes();
        let roots =
            branch_likes.dom()
                + CompactorInput::input_roots(
                    pre_i.compactors,
                );
        pre_component.semantic_sealed_branch_disk()
            .build_branch_summary_finite(roots);
    }
    assert(!pre.branch.branch_summary.contains_key(
        model_branch.root.au,
    )) by {
        if pre.branch.branch_summary.contains_key(
            model_branch.root.au,
        ) {
            assert(pre.branch.branch_summary.dom()
                <= summary_aus(
                    pre.branch.branch_summary,
                ));
            assert(summary_aus(
                pre.branch.branch_summary,
            ).contains(model_branch.root.au));
            assert(branch_owned.contains(
                model_branch.root.au,
            ));
        }
    }
    assert(summary_aus(pre.branch.branch_summary)
        .disjoint(model_branch.get_summary())) by {
        assert(summary_aus(pre.branch.branch_summary)
            .disjoint(
                pre_i.branch_allocator_aus(),
            ));
    }
    branch_summary_insert_ensures(
        pre.branch.branch_summary,
        model_branch,
    );
    let pre_summary_aus =
        summary_aus(pre.branch.branch_summary);
    let post_summary_aus =
        summary_aus(
            post_component.betree.branch_summary,
        );
    assert(post_component.betree.branch_summary
        == pre.branch.branch_summary.insert(
            branch_root.au,
            branch_owned,
        ));
    assert(post_summary_aus
        == pre_summary_aus + branch_owned);

    assert forall |left: int, right: int|
        0 <= left < right
            < pre.branch.wip_branches.len()
        implies (#[trigger] pre.branch.wip_branches[left])
            .mini_allocator.all_aus().disjoint(
                (#[trigger] pre.branch.wip_branches[right])
                    .mini_allocator.all_aus(),
            )
    by {
        assert(pre_i.wip_branches[left]
            .mini_allocator
            == pre.branch.wip_branches[left]
                .mini_allocator);
        assert(pre_i.wip_branches[right]
            .mini_allocator
            == pre.branch.wip_branches[right]
                .mini_allocator);
    }
    cached_branch_alloc_aus_remove_exact(
        pre.branch.wip_branches,
        branch_idx,
    );
    let pre_wip_aus =
        cached_branch_alloc_aus(pre.branch.wip_branches);
    let post_wip_aus =
        cached_branch_alloc_aus(
            post_component.betree.wip_branches,
        );
    assert(post_component.betree.wip_branches
        == pre.branch.wip_branches.remove(
            branch_idx,
        ));
    assert(post_wip_aus
        == pre_wip_aus - branch_owned);

    let pre_betree_aus = pre.branch.betree_aus.dom();
    let post_betree_aus =
        post_component.betree.betree_aus.dom();
    let pre_owned = pre.branch.owned_aus();
    let post_owned = post_component.betree.owned_aus();
    assert(pre.branch.branch_aus.dom()
        <= pre_summary_aus);
    assert(post_component.betree.branch_aus.dom()
        <= post_summary_aus);
    assert(pre_owned
        == pre_betree_aus + pre_summary_aus
            + pre_wip_aus) by {
        assert forall |au: AU|
            #[trigger] pre_owned.contains(au)
            <==> (pre_betree_aus + pre_summary_aus
                + pre_wip_aus).contains(au)
        by {
        }
    }
    assert(post_owned
        == post_betree_aus + post_summary_aus
            + post_wip_aus) by {
        assert forall |au: AU|
            #[trigger] post_owned.contains(au)
            <==> (post_betree_aus
                + post_summary_aus
                + post_wip_aus).contains(au)
        by {
        }
    }
    assert(pre_betree_aus.disjoint(pre_summary_aus));
    assert(pre_betree_aus.disjoint(pre_wip_aus));
    assert(pre_summary_aus.disjoint(pre_wip_aus));
    assert(post_betree_aus.disjoint(
        post_summary_aus,
    ));
    assert(post_betree_aus.disjoint(post_wip_aus));
    assert(post_summary_aus.disjoint(post_wip_aus));
    assert(pre_i.branch_allocator_aus()
        == pre_wip_aus);
    assert(branch_owned <= pre_wip_aus);
    assert(deallocs <= pre_betree_aus);
    assert(deallocs <= pre_owned);
    assert(post_owned
        == (pre_owned + allocs) - deallocs) by {
        assert forall |au: AU|
            #[trigger] post_owned.contains(au)
            <==> ((pre_owned + allocs) - deallocs)
                .contains(au)
        by {
            assert(post_betree_aus
                == (pre_betree_aus + allocs)
                    - deallocs);
            assert(post_summary_aus
                == pre_summary_aus + branch_owned);
            assert(post_wip_aus
                == pre_wip_aus - branch_owned);
        }
    }
}

proof fn compact_complete_owned_aus_effect(
    pre: UnifiedCacheBranchBetreeSource,
    post_component: CachingDiskBranchBetree::State,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    input_idx: int,
    branch_idx: int,
    path: LoadedBetreePath,
    start: nat,
    end: nat,
    new_node_addr: Address,
    path_addrs: PathAddrs,
    betree_reads:
        Map<Address, crate::betree::LinkedBetree_v::BetreeNode>,
    betree_writes:
        Map<Address, crate::betree::LinkedBetree_v::BetreeNode>,
    branch_reads:
        Map<Address, crate::allocation_layer::
            AllocationBranch_v::BranchNode>,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        post_component.refinement_inv(),
        CachedBranchBetree::State::compact_complete(
            pre.branch,
            post_component.betree,
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
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
        ),
    ensures
        post_component.betree.owned_aus()
            == (pre.branch.owned_aus() + allocs)
                - deallocs,
        cached_branch_alloc_aus(
            post_component.betree.wip_branches,
        ) <= cached_branch_alloc_aus(
            pre.branch.wip_branches,
        ),
        deallocs <= pre.branch.owned_aus(),
{
    reveal(CachedBranchBetree::State::compact_complete);
    reveal(CachedBranchBetree::State::owned_aus);
    let cached_branch =
        pre.branch.wip_branches[branch_idx];
    let branch_root =
        cached_branch.sealed_root().unwrap();
    let branch_owned =
        cached_branch.mini_allocator.all_aus();
    let new_compactors =
        pre.branch.compactors.remove(input_idx);
    let discarded = path_discard_likes(path);
    let added =
        path_addrs.to_multiset().insert(new_node_addr);
    let new_betree_aus =
        pre.branch.betree_aus
            .sub(to_au_likes(discarded))
            .add(to_au_likes(added));
    let discarded_branches =
        pre.branch.compactors[input_idx]
            .input_buffers.addrs.to_multiset();
    let new_branch_aus =
        pre.branch.branch_aus
            .sub(to_au_likes(discarded_branches))
            .insert(branch_root.au);
    let branch_deallocs =
        pre.branch.branch_summary.dom()
            - new_branch_aus.dom()
            - read_ref_aus(new_compactors);
    let with_new_summary =
        pre.branch.branch_summary.insert(
            branch_root.au,
            cached_branch.summary(),
        );
    let deallocated_summary =
        pre.branch.branch_summary.restrict(
            branch_deallocs,
        );
    let tree_deallocs =
        pre.branch.betree_aus.dom()
            - new_betree_aus.dom();
    let summary_deallocs =
        summary_aus(deallocated_summary);
    let pre_summary_aus =
        summary_aus(pre.branch.branch_summary);
    let post_summary_aus =
        summary_aus(
            post_component.betree.branch_summary,
        );

    path_addrs.to_multiset_ensures();
    assert(added.dom()
        == path_addrs.to_set().insert(new_node_addr));
    crate::allocation_layer::Likes_v::
        to_au_likes_domain(added);
    crate::disk::GenericDisk_v::to_aus_singleton(
        new_node_addr,
    );
    crate::disk::GenericDisk_v::to_aus_additive(
        path_addrs.to_set(),
        set![new_node_addr],
    );
    assert(path_addrs.to_set().insert(new_node_addr)
        == path_addrs.to_set() + set![new_node_addr]);
    assert(to_au_likes(added).dom()
        == allocs) by {
        assert(to_au_likes(added).dom()
            == to_aus(added.dom()));
        assert(to_aus(added.dom())
            == to_aus(path_addrs.to_set())
                + set![new_node_addr.au]);
    }
    assert(allocs <= new_betree_aus.dom());
    assert(new_betree_aus.dom()
        <= pre.branch.betree_aus.dom() + allocs);
    assert(new_betree_aus.dom()
        == (pre.branch.betree_aus.dom() + allocs)
            - tree_deallocs) by {
        assert forall |au: AU|
            #[trigger] new_betree_aus.dom().contains(au)
            <==> ((pre.branch.betree_aus.dom()
                + allocs) - tree_deallocs).contains(au)
        by {
        }
    }
    assert(deallocs
        == tree_deallocs + summary_deallocs);

    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(pre.i().ephemeral is Known);
    let pre_component = pre.known_branch_i();
    assert(pre_component.refinement_inv());
    let pre_i = pre_component.i();
    let post_i = post_component.i();
    assert(pre_i.inv());
    assert(post_i.inv());
    pre_component.wip_alloc_aus_agree();
    post_component.wip_alloc_aus_agree();
    pre_i.inv_branch_summary_ensures();
    post_i.inv_branch_summary_ensures();
    assert(pre_i.wip_branches_inv());
    assert(pre_i.wip_branches_disjoint());
    let model_branch =
        pre_i.wip_branches[branch_idx]
            .branch.unwrap();
    assert(pre_i.wip_branches[branch_idx]
        .mini_allocator == cached_branch.mini_allocator)
    by {
        reveal(CachingDiskBranchBetree::State::
            wip_branches_i);
        reveal(CachingDiskBranchBetree::State::
            wip_branch_i);
    }
    crate::allocation_layer::AllocationBranch_v::
        AllocationBranch::alloc_aus_ensures(
            pre_i.wip_branches,
            branch_idx,
        );
    assert(pre_i.wip_branches[branch_idx].inv());
    assert(pre_i.wip_branches[branch_idx].sealed);
    assert(model_branch.valid_sealed_branch());
    assert(model_branch.root == branch_root);
    assert(model_branch.get_summary() == branch_owned);
    assert(cached_branch.summary() == branch_owned);
    assert(pre.branch.branch_summary.dom().finite()) by {
        let (_, branch_likes) =
            pre_i.betree.linked.transitive_likes();
        let roots =
            branch_likes.dom()
                + CompactorInput::input_roots(
                    pre_i.compactors,
                );
        pre_component.semantic_sealed_branch_disk()
            .build_branch_summary_finite(roots);
    }
    assert(!pre.branch.branch_summary.contains_key(
        branch_root.au,
    )) by {
        if pre.branch.branch_summary.contains_key(
            branch_root.au,
        ) {
            assert(pre.branch.branch_summary.dom()
                <= pre_summary_aus);
            assert(pre_summary_aus.contains(
                branch_root.au,
            ));
            assert(branch_owned.contains(
                branch_root.au,
            ));
            assert(pre_summary_aus.disjoint(
                pre_i.branch_allocator_aus(),
            ));
            assert(branch_owned
                <= pre_i.branch_allocator_aus());
        }
    }
    assert(pre_summary_aus.disjoint(branch_owned)) by {
        assert(pre_summary_aus.disjoint(
            pre_i.branch_allocator_aus(),
        ));
        assert(branch_owned
            <= pre_i.branch_allocator_aus());
    }
    branch_summary_insert_ensures(
        pre.branch.branch_summary,
        model_branch,
    );
    assert(summary_aus(with_new_summary)
        == pre_summary_aus + branch_owned);

    assert(!branch_deallocs.contains(branch_root.au)) by {
        assert(new_branch_aus.dom()
            .contains(branch_root.au));
    }
    assert(with_new_summary.restrict(branch_deallocs)
        == deallocated_summary) by {
        assert_maps_equal!(
            with_new_summary.restrict(branch_deallocs),
            deallocated_summary,
            au => {}
        );
    }
    vstd::map_lib::lemma_values_finite(with_new_summary);
    summary_aus_restrict_subset(
        pre.branch.branch_summary,
        branch_deallocs,
    );
    assert(summary_deallocs <= pre_summary_aus);
    summary_partition_disjoint(
        with_new_summary,
        branch_deallocs,
    );
    assert(post_component.betree.branch_summary
        == with_new_summary.remove_keys(
            branch_deallocs,
        ));
    assert(summary_aus(with_new_summary)
        == post_summary_aus + summary_deallocs);
    assert(post_summary_aus.disjoint(
        summary_deallocs,
    ));

    assert forall |left: int, right: int|
        0 <= left < right
            < pre.branch.wip_branches.len()
        implies (#[trigger] pre.branch.wip_branches[left])
            .mini_allocator.all_aus().disjoint(
                (#[trigger] pre.branch.wip_branches[right])
                    .mini_allocator.all_aus(),
            )
    by {
        assert(pre_i.wip_branches[left]
            .mini_allocator
            == pre.branch.wip_branches[left]
                .mini_allocator);
        assert(pre_i.wip_branches[right]
            .mini_allocator
            == pre.branch.wip_branches[right]
                .mini_allocator);
    }
    cached_branch_alloc_aus_remove_exact(
        pre.branch.wip_branches,
        branch_idx,
    );
    let pre_wip_aus =
        cached_branch_alloc_aus(pre.branch.wip_branches);
    let post_wip_aus =
        cached_branch_alloc_aus(
            post_component.betree.wip_branches,
        );
    assert(post_component.betree.wip_branches
        == pre.branch.wip_branches.remove(
            branch_idx,
        ));
    assert(post_wip_aus
        == pre_wip_aus - branch_owned);

    let pre_betree_aus = pre.branch.betree_aus.dom();
    let post_betree_aus =
        post_component.betree.betree_aus.dom();
    let pre_owned = pre.branch.owned_aus();
    let post_owned = post_component.betree.owned_aus();
    assert(pre.branch.branch_aus.dom()
        <= pre_summary_aus);
    assert(post_component.betree.branch_aus.dom()
        <= post_summary_aus);
    assert(pre_owned
        == pre_betree_aus + pre_summary_aus
            + pre_wip_aus) by {
        assert forall |au: AU|
            #[trigger] pre_owned.contains(au)
            <==> (pre_betree_aus + pre_summary_aus
                + pre_wip_aus).contains(au)
        by {
        }
    }
    assert(post_owned
        == post_betree_aus + post_summary_aus
            + post_wip_aus) by {
        assert forall |au: AU|
            #[trigger] post_owned.contains(au)
            <==> (post_betree_aus + post_summary_aus
                + post_wip_aus).contains(au)
        by {
        }
    }
    assert(pre_betree_aus.disjoint(pre_summary_aus));
    assert(pre_betree_aus.disjoint(pre_wip_aus));
    assert(pre_summary_aus.disjoint(pre_wip_aus));
    assert(post_betree_aus.disjoint(post_summary_aus));
    assert(post_betree_aus.disjoint(post_wip_aus));
    assert(post_summary_aus.disjoint(post_wip_aus));
    assert(branch_owned <= pre_wip_aus);
    assert(tree_deallocs <= pre_betree_aus);
    assert(deallocs
        <= pre_betree_aus + pre_summary_aus);
    assert(deallocs <= pre_owned);
    assert(pre_owned.disjoint(allocs)) by {
        reveal(CachedBranchBetree::State::is_fresh);
    }
    assert(deallocs.disjoint(allocs));
    assert(post_betree_aus
        == (pre_betree_aus - tree_deallocs)
            + allocs) by {
        assert forall |au: AU|
            #[trigger] post_betree_aus.contains(au)
            <==> ((pre_betree_aus - tree_deallocs)
                + allocs).contains(au)
        by {
            assert(pre_betree_aus.disjoint(allocs));
        }
    }
    assert(post_summary_aus
        == (pre_summary_aus - summary_deallocs)
            + branch_owned) by {
        assert forall |au: AU|
            #[trigger] post_summary_aus.contains(au)
            <==> ((pre_summary_aus
                - summary_deallocs)
                + branch_owned).contains(au)
        by {
            assert(pre_summary_aus.disjoint(branch_owned));
            assert(summary_deallocs <= pre_summary_aus);
            assert(post_summary_aus.disjoint(
                summary_deallocs,
            ));
            if post_summary_aus.contains(au) {
                assert((post_summary_aus
                    + summary_deallocs).contains(au));
                assert((pre_summary_aus
                    + branch_owned).contains(au));
                assert(!summary_deallocs.contains(au));
            }
            if ((pre_summary_aus - summary_deallocs)
                + branch_owned).contains(au)
            {
                assert((pre_summary_aus
                    + branch_owned).contains(au));
                assert((post_summary_aus
                    + summary_deallocs).contains(au));
                if branch_owned.contains(au) {
                    assert(!summary_deallocs.contains(au));
                } else {
                    assert(pre_summary_aus.contains(au));
                    assert(!summary_deallocs.contains(au));
                }
                assert(post_summary_aus.contains(au));
            }
        }
    }
    assert((pre_wip_aus - branch_owned)
        + branch_owned == pre_wip_aus) by {
        assert forall |au: AU|
            #[trigger] ((pre_wip_aus - branch_owned)
                + branch_owned).contains(au)
            <==> pre_wip_aus.contains(au)
        by {
        }
    }
    assert(post_owned
        == (pre_owned + allocs) - deallocs) by {
        assert forall |au: AU|
            #[trigger] post_owned.contains(au)
            <==> ((pre_owned + allocs) - deallocs)
                .contains(au)
        by {
            assert(post_betree_aus
                == (pre_betree_aus + allocs)
                    - tree_deallocs);
            assert(pre_summary_aus + branch_owned
                == post_summary_aus
                    + summary_deallocs);
            assert(post_wip_aus
                == pre_wip_aus - branch_owned);
        }
    }
}

proof fn branch_build_owned_aus_effect(
    pre: UnifiedCacheBranchBetreeSource,
    post_component: CachingDiskBranchBetree::State,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    idx: int,
    post_branch: CachedAllocationBranch,
    event: BranchBuildEvent,
    access: PageAccess,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        post_component.refinement_inv(),
        CachedBranchBetree::State::branch_build(
            pre.branch,
            post_component.betree,
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
            idx,
            post_branch,
            event.cached_event(access),
        ),
    ensures
        post_component.betree.owned_aus()
            == pre.branch.owned_aus() - deallocs,
        cached_branch_alloc_aus(
            post_component.betree.wip_branches,
        ) == cached_branch_alloc_aus(
            pre.branch.wip_branches,
        ) - deallocs,
        deallocs <= pre.branch.owned_aus(),
{
    reveal(CachedBranchBetree::State::branch_build);
    reveal(CachedBranchBetree::State::owned_aus);
    let pre_target = pre.branch.wip_branches[idx];
    let cached_event = event.cached_event(access);
    assert(allocs.is_empty()) by {
        reveal(CachedAllocationBranch::build_next);
        match event {
            BranchBuildEvent::Append{..} => {}
            BranchBuildEvent::Initialize{..} => {}
            BranchBuildEvent::Grow{..} => {}
            BranchBuildEvent::Split{..} => {}
            BranchBuildEvent::Seal{..} => {}
        }
    }
    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(pre.i().ephemeral is Known);
    assert(pre.known_branch_i().refinement_inv());
    let early_pre_i = pre.known_branch_i().i();
    assert(early_pre_i.inv());
    assert(early_pre_i.wip_branches_inv());
    assert(early_pre_i.wip_branches[idx]
        .mini_allocator == pre_target.mini_allocator) by {
        reveal(CachingDiskBranchBetree::State::
            wip_branches_i);
        reveal(CachingDiskBranchBetree::State::
            wip_branch_i);
    }
    assert(pre_target.mini_allocator.wf());
    cached_allocation_branch_build_all_aus_subset(
        pre_target,
        post_branch,
        cached_event,
        allocs,
        deallocs,
    );
    assert(post_branch.mini_allocator.all_aus()
        == pre_target.mini_allocator.all_aus()
            - deallocs);
    assert(deallocs
        <= pre_target.mini_allocator.all_aus()) by {
        reveal(CachedAllocationBranch::build_next);
        match event {
            BranchBuildEvent::Seal{..} => {
                assert(deallocs
                    == pre_target.mini_allocator
                        .removable_aus());
                assert forall |au: AU|
                    #[trigger] deallocs.contains(au)
                    implies pre_target.mini_allocator
                        .all_aus().contains(au)
                by {
                    reveal(crate::allocation_layer::
                        MiniAllocator_v::MiniAllocator::
                            removable_aus);
                    reveal(crate::allocation_layer::
                        MiniAllocator_v::MiniAllocator::
                            can_remove);
                }
            }
            _ => {
                assert(deallocs.is_empty());
            }
        }
    }

    let pre_i = pre.known_branch_i().i();
    let post_i = post_component.i();
    assert(pre_i.inv());
    assert(post_i.inv());
    pre.known_branch_i().wip_alloc_aus_agree();
    post_component.wip_alloc_aus_agree();
    assert(pre_i.wip_branches_disjoint());
    assert forall |left: int, right: int|
        0 <= left < right
            < pre.branch.wip_branches.len()
        implies (#[trigger] pre.branch.wip_branches[left])
            .mini_allocator.all_aus().disjoint(
                (#[trigger] pre.branch.wip_branches[right])
                    .mini_allocator.all_aus(),
            )
    by {
        assert(pre_i.wip_branches[left]
            .mini_allocator
            == pre.branch.wip_branches[left]
                .mini_allocator) by {
            reveal(CachingDiskBranchBetree::State::
                wip_branches_i);
            reveal(CachingDiskBranchBetree::State::
                wip_branch_i);
        }
        assert(pre_i.wip_branches[right]
            .mini_allocator
            == pre.branch.wip_branches[right]
                .mini_allocator) by {
            reveal(CachingDiskBranchBetree::State::
                wip_branches_i);
            reveal(CachingDiskBranchBetree::State::
                wip_branch_i);
        }
    }
    cached_branch_alloc_aus_update_remove_exact(
        pre.branch.wip_branches,
        idx,
        post_branch,
        deallocs,
    );
    let pre_wip_aus =
        cached_branch_alloc_aus(pre.branch.wip_branches);
    let post_wip_aus =
        cached_branch_alloc_aus(
            post_component.betree.wip_branches,
        );
    assert(post_component.betree.wip_branches
        == pre.branch.wip_branches.update(
            idx,
            post_branch,
        ));
    assert(post_wip_aus
        == pre_wip_aus - deallocs);

    pre_i.inv_branch_summary_ensures();
    post_i.inv_branch_summary_ensures();
    let betree_aus = pre.branch.betree_aus.dom();
    let sealed_aus =
        summary_aus(pre.branch.branch_summary);
    let pre_owned = pre.branch.owned_aus();
    let post_owned = post_component.betree.owned_aus();
    assert(post_component.betree.betree_aus
        == pre.branch.betree_aus);
    assert(post_component.betree.branch_summary
        == pre.branch.branch_summary);
    assert(pre.branch.branch_aus.dom()
        <= sealed_aus);
    assert(post_component.betree.branch_aus.dom()
        <= sealed_aus);
    assert(pre_owned
        == betree_aus + sealed_aus + pre_wip_aus) by {
        assert forall |au: AU|
            #[trigger] pre_owned.contains(au)
            <==> (betree_aus + sealed_aus
                + pre_wip_aus).contains(au)
        by {
        }
    }
    assert(post_owned
        == betree_aus + sealed_aus
            + post_wip_aus) by {
        assert forall |au: AU|
            #[trigger] post_owned.contains(au)
            <==> (betree_aus + sealed_aus
                + post_wip_aus).contains(au)
        by {
        }
    }
    assert(betree_aus.disjoint(sealed_aus));
    assert(betree_aus.disjoint(pre_wip_aus));
    assert(sealed_aus.disjoint(pre_wip_aus));
    assert(deallocs <= pre_wip_aus) by {
        assert(pre_target.mini_allocator.all_aus()
            <= pre_wip_aus) by {
            assert(pre_i.branch_allocator_aus()
                == pre_wip_aus);
            crate::allocation_layer::
                AllocationBranch_v::AllocationBranch::
                    alloc_aus_ensures(
                        pre_i.wip_branches,
                        idx,
                    );
            assert(pre_i.wip_branches[idx]
                .mini_allocator
                == pre_target.mini_allocator) by {
                reveal(CachingDiskBranchBetree::State::
                    wip_branches_i);
                reveal(CachingDiskBranchBetree::State::
                    wip_branch_i);
            }
        }
    }
    assert(post_owned == pre_owned - deallocs) by {
        assert forall |au: AU|
            #[trigger] post_owned.contains(au)
            <==> (pre_owned - deallocs).contains(au)
        by {
        }
    }
}

proof fn reclaimable_deallocs_subset_branch_projection(
    pre: UnifiedCacheBranchBetreeSource,
    deallocs: Set<AU>,
)
    requires
        pre.control.metadata_loaded,
        deallocs <= pre.branch.owned_aus(),
    ensures
        pre.control.reclaimable(deallocs)
            <= pre.branch_projection_aus(),
{
    reveal(AtomicBranchBetreeControl::reclaimable);
    reveal(UnifiedCacheBranchBetreeSource::
    branch_projection_aus);
}

proof fn wip_branch_addr_wf(
    allocation: AllocationBranch,
    addr: Address,
)
    requires
        allocation.inv(),
        allocation.branch is Some,
        !allocation.sealed,
        allocation.branch.unwrap().disk_view.entries
            .contains_key(addr),
    ensures
        addr.wf(),
{
    reveal(AllocationBranch::inv);
    assert(allocation.addrs_closed_under_mini_allocator());
    assert(allocation.mini_allocator.page_is_allocated(addr));
    reveal(crate::allocation_layer::MiniAllocator_v::
        MiniAllocator::page_is_allocated);
    assert(allocation.mini_allocator.wf());
    assert(allocation.mini_allocator.allocs
        .contains_key(addr.au));
    assert(allocation.mini_allocator.allocs[addr.au].wf());
}

proof fn linked_branch_child_inv_internal(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    child_idx: int,
)
    requires
        branch.inv_internal(ranking),
        branch.root().valid_child_index(child_idx),
    ensures
        branch.child_at_idx(child_idx)
            .inv_internal(ranking),
{
    assert(branch.child_at_idx(child_idx)
        .valid_ranking(ranking)) by {
        assert(branch.disk_view.valid_ranking(ranking));
        assert(ranking.contains_key(branch.root));
        assert(branch.disk_view.node_children_respects_rank(
            ranking,
            branch.root,
        ));
        assert(ranking.contains_key(
            branch.root()->children[child_idx],
        ));
    }
    assert(branch.child_at_idx(child_idx)
        .keys_strictly_sorted_internal(ranking));
    assert(branch.child_at_idx(child_idx)
        .all_keys_in_range_internal(ranking));
}

proof fn branch_receipt_needed_addr_in_projection_internal(
    src: UnifiedCacheBranchBetreeSource,
    post_cache: Cache::State,
    access: PageAccess,
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    receipt: LoadedPathReceipt,
    addr: Address,
)
    requires
        inv(src),
        src.control.metadata_loaded,
        access.wf(),
        Cache::State::next(
            src.cache,
            post_cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        branch.inv_internal(ranking),
        branch.disk_view.entries
            == src.known_branch_i().linked_i()
                .buffer_dv.entries,
        branch.disk_view.entries
            <= to_branch_nodes(
                src.known_branch_i().disk.visible(),
            ),
        receipt.valid_for(
            branch.root,
            to_branch_nodes(access.branch_reads),
        ),
        receipt.needed_addrs().contains(addr),
    ensures
        addresses_in_aus(
            src.branch_projection_aus(),
        ).contains(addr),
    decreases receipt.depth(),
{
    let component = src.known_branch_i();
    let root = branch.root;
    let root_reads =
        access.branch_reads.restrict(set![root]);

    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(src.i().ephemeral is Known);
    assert(component.refinement_inv());
    assert(component.i().inv());
    assert(component.i().betree.linked.buffer_dv.entries
        == branch.disk_view.entries);
    assert(addrs_closed(
        branch.disk_view.entries.dom(),
        summary_aus(component.betree.branch_summary),
    ));
    assert(branch.disk_view.entries.contains_key(root));
    assert(summary_aus(component.betree.branch_summary)
        .contains(root.au));
    reveal(UnifiedCacheBranchBetreeSource::
        branch_projection_aus);
    reveal(CachedBranchBetree::State::owned_aus);
    assert(src.branch_projection_aus()
        .contains(root.au));
    assert(addresses_in_aus(
        src.branch_projection_aus(),
    ).contains(root));

    assert(receipt.needed_addrs().contains(root)) by {
        assert(receipt.lines[0].addr == receipt.root);
    }
    assert(to_branch_nodes(
        access.branch_reads,
    ).contains_key(root));
    assert(access.branch_reads.contains_key(root));
    page_access_branch_read_valid(
        src.cache,
        post_cache,
        access,
        root,
    );
    assert forall |read_addr: Address|
        #[trigger] root_reads.contains_key(read_addr)
        implies src.cache.valid_read(
            read_addr,
            root_reads[read_addr],
        )
    by {
        assert(read_addr == root);
    };
    assert(root_reads.dom()
        <= addresses_in_aus(
            src.branch_projection_aus(),
        ));
    valid_reads_in_project_cache_by_addrs(
        src.cache,
        addresses_in_aus(src.branch_projection_aus()),
        root_reads,
    );
    assert(root_reads <= component.disk.cache) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_caching_disk_i);
        reveal(UnifiedCacheBranchBetreeSource::
            known_branch_i);
        reveal(crate::implementation::
            CachingDiskAdapterRefinement_v::
                project_cache_pages_by_addrs);
        reveal(project_cache_pages);
    }
    assert(to_branch_nodes(
        component.disk.visible(),
    ).contains_key(root));
    assert(component.disk.visible().contains_key(root));
    query_read_node_matches_visible(
        component.disk,
        root_reads,
        root,
    );
    assert(to_branch_nodes(root_reads)[root]
        == to_branch_nodes(access.branch_reads)[root]);
    assert(receipt.lines[0].node
        == branch.disk_view.entries[root]);
    assert(receipt.lines[0].node == branch.root());

    if addr != root {
        assert(receipt.depth() > 0) by {
            if receipt.depth() == 0 {
                assert(receipt.lines.len() == 1);
                let i = choose |i: int|
                    0 <= i < receipt.lines.len()
                        && receipt.lines[i].addr == addr;
                assert(i == 0);
                assert(receipt.lines[0].addr == root);
            }
        }
        assert(receipt.lines.len() > 1);
        assert(receipt.lines[0].node is Index);
        assert(branch.root() is Index);
        let child_idx =
            branch.root().route(receipt.key) + 1;
        LinkedBranchRefinement::lemma_route_ensures(
            branch.root(),
            receipt.key,
        );
        assert(branch.root().valid_child_index(child_idx));
        let child = branch.child_at_idx(child_idx);
        let tail = receipt.tail();
        receipt_valid_implies_tail_valid(
            receipt,
            to_branch_nodes(access.branch_reads),
        );
        assert(child.root == tail.root) by {
            assert(receipt.lines[0].node
                ->children[child_idx]
                == receipt.lines[1].addr);
            assert(branch.root()->children[child_idx]
                == receipt.lines[1].addr);
            assert(tail.root == receipt.lines[1].addr);
        }
        assert(tail.needed_addrs().contains(addr)) by {
            let i = choose |i: int|
                0 <= i < receipt.lines.len()
                    && receipt.lines[i].addr == addr;
            assert(i > 0);
            assert(tail.lines[i - 1]
                == receipt.lines[i]);
        }
        linked_branch_child_inv_internal(
            branch,
            ranking,
            child_idx,
        );
        branch_receipt_needed_addr_in_projection_internal(
            src,
            post_cache,
            access,
            child,
            ranking,
            tail,
            addr,
        );
    }
}

proof fn branch_receipt_needed_addr_in_projection(
    src: UnifiedCacheBranchBetreeSource,
    post_cache: Cache::State,
    access: PageAccess,
    branch: LinkedBranch<Summary>,
    receipt: LoadedPathReceipt,
    addr: Address,
)
    requires
        inv(src),
        src.control.metadata_loaded,
        access.wf(),
        Cache::State::next(
            src.cache,
            post_cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        branch.inv(),
        branch.disk_view.entries
            == src.known_branch_i().linked_i()
                .buffer_dv.entries,
        branch.disk_view.entries
            <= to_branch_nodes(
                src.known_branch_i().disk.visible(),
            ),
        receipt.valid_for(
            branch.root,
            to_branch_nodes(access.branch_reads),
        ),
        receipt.needed_addrs().contains(addr),
    ensures
        addresses_in_aus(
            src.branch_projection_aus(),
        ).contains(addr),
{
    branch_receipt_needed_addr_in_projection_internal(
        src,
        post_cache,
        access,
        branch,
        branch.the_ranking(),
        receipt,
        addr,
    );
}

proof fn wip_receipt_needed_addr_in_projection_internal(
    src: UnifiedCacheBranchBetreeSource,
    post_cache: Cache::State,
    access: PageAccess,
    branch_idx: int,
    allocation:
        crate::allocation_layer::AllocationBranch_v::
            AllocationBranch,
    full_branch: LinkedBranch<Summary>,
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    receipt: LoadedPathReceipt,
    addr: Address,
)
    requires
        inv(src),
        src.control.metadata_loaded,
        access.wf(),
        Cache::State::next(
            src.cache,
            post_cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        0 <= branch_idx
            < src.branch.wip_branches.len(),
        allocation
            == src.known_branch_i()
                .wip_branch_i(branch_idx),
        allocation.inv(),
        !allocation.sealed,
        allocation.branch is Some,
        full_branch == allocation.branch.unwrap(),
        branch.disk_view == full_branch.disk_view,
        branch.inv_internal(ranking),
        receipt.valid_for(
            branch.root,
            to_branch_nodes(access.branch_reads),
        ),
        receipt.needed_addrs().contains(addr),
    ensures
        addresses_in_aus(
            src.branch_projection_aus(),
        ).contains(addr),
        full_branch.disk_view.entries.contains_key(addr),
        full_branch.disk_view.entries[addr]
            == to_branch_nodes(access.branch_reads)[addr],
    decreases receipt.depth(),
{
    let component = src.known_branch_i();
    let root = branch.root;
    let root_reads =
        access.branch_reads.restrict(set![root]);
    let cached =
        src.branch.wip_branches[branch_idx];

    assert(allocation.addrs_closed_under_mini_allocator());
    assert(branch.disk_view.entries.contains_key(root));
    assert(allocation.mini_allocator
        .page_is_allocated(root));
    assert(allocation.mini_allocator.all_aus()
        .contains(root.au));
    assert(allocation.mini_allocator
        == cached.mini_allocator) by {
        reveal(CachingDiskBranchBetree::State::
            wip_branch_i);
    }
    reveal(UnifiedCacheBranchBetreeSource::
        branch_projection_aus);
    reveal(CachedBranchBetree::State::owned_aus);
    component.wip_alloc_aus_agree();
    crate::allocation_layer::AllocationBranch_v::
        AllocationBranch::alloc_aus_ensures(
            component.i().wip_branches,
            branch_idx,
        );
    assert(component.i().wip_branches[branch_idx]
        .mini_allocator == cached.mini_allocator) by {
        reveal(CachingDiskBranchBetree::State::
            wip_branches_i);
        reveal(CachingDiskBranchBetree::State::
            wip_branch_i);
    }
    assert(src.branch_projection_aus()
        .contains(root.au));
    assert(addresses_in_aus(
        src.branch_projection_aus(),
    ).contains(root));

    assert(receipt.needed_addrs().contains(root)) by {
        assert(receipt.lines[0].addr == receipt.root);
    }
    assert(to_branch_nodes(access.branch_reads)
        .contains_key(root));
    assert(access.branch_reads.contains_key(root));
    page_access_branch_read_valid(
        src.cache,
        post_cache,
        access,
        root,
    );
    assert forall |read_addr: Address|
        #[trigger] root_reads.contains_key(read_addr)
        implies src.cache.valid_read(
            read_addr,
            root_reads[read_addr],
        )
    by {
        assert(read_addr == root);
    }
    assert(root_reads.dom()
        <= addresses_in_aus(
            src.branch_projection_aus(),
        ));
    valid_reads_in_project_cache_by_addrs(
        src.cache,
        addresses_in_aus(src.branch_projection_aus()),
        root_reads,
    );
    assert(root_reads <= component.disk.cache) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_caching_disk_i);
        reveal(UnifiedCacheBranchBetreeSource::
            known_branch_i);
        reveal(crate::implementation::
            CachingDiskAdapterRefinement_v::
                project_cache_pages_by_addrs);
        reveal(project_cache_pages);
    }
    assert(branch.disk_view.entries
        <= to_branch_nodes(component.disk.visible())) by {
        reveal(CachingDiskBranchBetree::State::
            wip_branch_i);
        assert forall |node_addr: Address|
            #[trigger] branch.disk_view.entries
                .contains_key(node_addr)
            implies {
                &&& to_branch_nodes(
                    component.disk.visible(),
                ).contains_key(node_addr)
                &&& branch.disk_view.entries[node_addr]
                    == to_branch_nodes(
                        component.disk.visible(),
                    )[node_addr]
            }
        by {
        }
    }
    assert(to_branch_nodes(component.disk.visible())
        .contains_key(root));
    query_read_node_matches_visible(
        component.disk,
        root_reads,
        root,
    );
    assert(to_branch_nodes(root_reads)[root]
        == to_branch_nodes(access.branch_reads)[root]);
    assert(receipt.lines[0].node
        == branch.disk_view.entries[root]);
    assert(receipt.lines[0].node == branch.root());
    if addr == root {
        assert(full_branch.disk_view.entries
            .contains_key(addr));
        assert(full_branch.disk_view.entries[addr]
            == to_branch_nodes(
                access.branch_reads,
            )[addr]);
    }

    if addr != root {
        assert(receipt.depth() > 0) by {
            if receipt.depth() == 0 {
                assert(receipt.lines.len() == 1);
                let i = choose |i: int|
                    0 <= i < receipt.lines.len()
                        && receipt.lines[i].addr == addr;
                assert(i == 0);
                assert(receipt.lines[0].addr == root);
            }
        }
        assert(receipt.lines.len() > 1);
        assert(receipt.lines[0].node is Index);
        assert(branch.root() is Index);
        let child_idx =
            branch.root().route(receipt.key) + 1;
        LinkedBranchRefinement::lemma_route_ensures(
            branch.root(),
            receipt.key,
        );
        assert(branch.root().valid_child_index(child_idx));
        let child = branch.child_at_idx(child_idx);
        let tail = receipt.tail();
        receipt_valid_implies_tail_valid(
            receipt,
            to_branch_nodes(access.branch_reads),
        );
        assert(child.root == tail.root) by {
            assert(receipt.lines[0].node
                ->children[child_idx]
                == receipt.lines[1].addr);
            assert(branch.root()->children[child_idx]
                == receipt.lines[1].addr);
            assert(tail.root == receipt.lines[1].addr);
        }
        assert(tail.needed_addrs().contains(addr)) by {
            let i = choose |i: int|
                0 <= i < receipt.lines.len()
                    && receipt.lines[i].addr == addr;
            assert(i > 0);
            assert(tail.lines[i - 1]
                == receipt.lines[i]);
        }
        linked_branch_child_inv_internal(
            branch,
            ranking,
            child_idx,
        );
        wip_receipt_needed_addr_in_projection_internal(
            src,
            post_cache,
            access,
            branch_idx,
            allocation,
            full_branch,
            child,
            ranking,
            tail,
            addr,
        );
    }
}

proof fn wip_receipt_needed_addr_in_projection(
    src: UnifiedCacheBranchBetreeSource,
    post_cache: Cache::State,
    access: PageAccess,
    branch_idx: int,
    receipt: LoadedPathReceipt,
    addr: Address,
)
    requires
        inv(src),
        src.control.metadata_loaded,
        access.wf(),
        Cache::State::next(
            src.cache,
            post_cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        0 <= branch_idx
            < src.branch.wip_branches.len(),
        !src.branch.wip_branches[branch_idx].sealed,
        src.known_branch_i()
            .wip_branch_i(branch_idx).inv(),
        src.known_branch_i()
            .wip_branch_i(branch_idx).branch is Some,
        receipt.valid_for(
            src.known_branch_i()
                .wip_branch_i(branch_idx)
                .branch.unwrap().root,
            to_branch_nodes(access.branch_reads),
        ),
        receipt.needed_addrs().contains(addr),
    ensures
        addresses_in_aus(
            src.branch_projection_aus(),
        ).contains(addr),
        src.known_branch_i()
            .wip_branch_i(branch_idx)
            .branch.unwrap().disk_view.entries
            .contains_key(addr),
        src.known_branch_i()
            .wip_branch_i(branch_idx)
            .branch.unwrap().disk_view.entries[addr]
            == to_branch_nodes(access.branch_reads)[addr],
{
    let allocation =
        src.known_branch_i().wip_branch_i(branch_idx);
    let branch = allocation.branch.unwrap();
    wip_receipt_needed_addr_in_projection_internal(
        src,
        post_cache,
        access,
        branch_idx,
        allocation,
        branch,
        branch,
        branch.the_ranking(),
        receipt,
        addr,
    );
}

proof fn wip_receipt_valid_on_projection(
    src: UnifiedCacheBranchBetreeSource,
    post_cache: Cache::State,
    access: PageAccess,
    branch_idx: int,
    receipt: LoadedPathReceipt,
)
    requires
        inv(src),
        src.control.metadata_loaded,
        access.wf(),
        Cache::State::next(
            src.cache,
            post_cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        0 <= branch_idx
            < src.branch.wip_branches.len(),
        !src.branch.wip_branches[branch_idx].sealed,
        src.known_branch_i()
            .wip_branch_i(branch_idx).inv(),
        src.known_branch_i()
            .wip_branch_i(branch_idx).branch is Some,
        receipt.valid_for(
            src.known_branch_i()
                .wip_branch_i(branch_idx)
                .branch.unwrap().root,
            to_branch_nodes(access.branch_reads),
        ),
    ensures ({
        let tight_reads =
            access.branch_reads.restrict(
                addresses_in_aus(
                    src.branch_projection_aus(),
                ),
            );
        receipt.valid_for(
            src.known_branch_i()
                .wip_branch_i(branch_idx)
                .branch.unwrap().root,
            to_branch_nodes(tight_reads),
        )
    }),
{
    let allocation =
        src.known_branch_i().wip_branch_i(branch_idx);
    let tight_reads =
        access.branch_reads.restrict(
            addresses_in_aus(
                src.branch_projection_aus(),
            ),
        );
    assert(receipt.needed_addrs()
        <= to_branch_nodes(tight_reads).dom()) by {
        assert forall |addr: Address|
            #[trigger] receipt.needed_addrs()
                .contains(addr)
            implies tight_reads.contains_key(addr)
        by {
            wip_receipt_needed_addr_in_projection(
                src,
                post_cache,
                access,
                branch_idx,
                receipt,
                addr,
            );
            assert(access.branch_reads
                .contains_key(addr));
        }
    }
    assert forall |i: int|
        0 <= i < receipt.lines.len()
        implies {
            &&& to_branch_nodes(tight_reads)
                .contains_key(receipt.lines[i].addr)
            &&& #[trigger] to_branch_nodes(tight_reads)[
                receipt.lines[i].addr
            ] == receipt.lines[i].node
        }
    by {
        let addr = receipt.lines[i].addr;
        assert(receipt.needed_addrs().contains(addr));
        wip_receipt_needed_addr_in_projection(
            src,
            post_cache,
            access,
            branch_idx,
            receipt,
            addr,
        );
        assert(tight_reads.contains_key(addr));
        assert(tight_reads[addr]
            == access.branch_reads[addr]);
        assert(to_branch_nodes(tight_reads)[addr]
            == to_branch_nodes(
                access.branch_reads,
            )[addr]);
    }
}

proof fn wip_root_in_projection(
    src: UnifiedCacheBranchBetreeSource,
    branch_idx: int,
)
    requires
        inv(src),
        src.control.metadata_loaded,
        0 <= branch_idx
            < src.branch.wip_branches.len(),
        src.known_branch_i()
            .wip_branch_i(branch_idx).inv(),
        src.known_branch_i()
            .wip_branch_i(branch_idx).branch is Some,
    ensures ({
        let allocation =
            src.known_branch_i().wip_branch_i(branch_idx);
        addresses_in_aus(
            src.branch_projection_aus(),
        ).contains(allocation.branch.unwrap().root)
    }),
{
    let component = src.known_branch_i();
    let allocation = component.wip_branch_i(branch_idx);
    let cached = src.branch.wip_branches[branch_idx];
    let root = allocation.branch.unwrap().root;
    assert(allocation.mini_allocator
        == cached.mini_allocator) by {
        reveal(CachingDiskBranchBetree::State::
            wip_branch_i);
    }
    assert(allocation.branch.unwrap().disk_view.entries
        .contains_key(root));
    if allocation.sealed {
        assert(allocation.branch.unwrap()
            .get_summary()
            == allocation.mini_allocator.all_aus());
        assert(allocation.branch.unwrap()
            .get_summary().contains(root.au));
    } else {
        assert(allocation.addrs_closed_under_mini_allocator());
        assert(allocation.mini_allocator
            .page_is_allocated(root));
        assert(allocation.mini_allocator.all_aus()
            .contains(root.au));
    }
    component.wip_alloc_aus_agree();
    crate::allocation_layer::AllocationBranch_v::
        AllocationBranch::alloc_aus_ensures(
            component.i().wip_branches,
            branch_idx,
        );
    assert(component.i().wip_branches[branch_idx]
        .mini_allocator == cached.mini_allocator) by {
        reveal(CachingDiskBranchBetree::State::
            wip_branches_i);
        reveal(CachingDiskBranchBetree::State::
            wip_branch_i);
    }
    reveal(UnifiedCacheBranchBetreeSource::
        branch_projection_aus);
    reveal(CachedBranchBetree::State::owned_aus);
    assert(src.branch_projection_aus()
        .contains(root.au));
}

pub open spec fn projected_branch_build_access(
    src: UnifiedCacheBranchBetreeSource,
    access: PageAccess,
) -> PageAccess {
    PageAccess {
        betree_reads: Map::empty(),
        branch_reads: access.branch_reads.restrict(
            addresses_in_aus(src.branch_projection_aus()),
        ),
        betree_writes: Map::empty(),
        branch_writes: access.branch_writes,
    }
}

pub open spec fn branch_with_updated_wip(
    branch: CachedBranchBetree::State,
    idx: int,
    post_branch: CachedAllocationBranch,
) -> CachedBranchBetree::State {
    CachedBranchBetree::State {
        wip_branches: branch.wip_branches.update(
            idx,
            post_branch,
        ),
        ..branch
    }
}

pub open spec fn projected_compact_complete_access(
    src: UnifiedCacheBranchBetreeSource,
    access: PageAccess,
) -> PageAccess {
    let owned_addrs =
        addresses_in_aus(src.branch_projection_aus());
    PageAccess {
        betree_reads:
            access.betree_reads.restrict(owned_addrs),
        branch_reads:
            access.branch_reads.restrict(owned_addrs),
        betree_writes: access.betree_writes,
        branch_writes: access.branch_writes,
    }
}

proof fn branch_only_write_domains(access: PageAccess)
    requires
        access.only_branch(),
    ensures
        access.writes().dom()
            == access.loaded_branch_writes().dom(),
{
    assert_sets_equal!(
        access.writes().dom(),
        access.loaded_branch_writes().dom(),
        addr => {
            reveal(PageAccess::writes);
            reveal(PageAccess::only_branch);
            reveal(PageAccess::loaded_branch_writes);
            reveal(to_branch_nodes);
        }
    );
}

proof fn compact_complete_access_on_projection(
    pre: UnifiedCacheBranchBetreeSource,
    post_cache: Cache::State,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    input_idx: int,
    branch_idx: int,
    path: LoadedBetreePath,
    start: nat,
    end: nat,
    new_node_addr: Address,
    path_addrs: PathAddrs,
    access: PageAccess,
    post_branch: CachedBranchBetree::State,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        access.wf(),
        access.branch_writes.is_empty(),
        Cache::State::next(
            pre.cache,
            post_cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        CachedBranchBetree::State::compact_complete(
            pre.branch,
            post_branch,
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
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
    ensures ({
        let tight =
            projected_compact_complete_access(pre, access);
        &&& tight.wf()
        &&& tight.branch_writes.is_empty()
        &&& tight.reads() <= access.reads()
        &&& tight.writes() == access.writes()
        &&& tight.reads().dom()
            <= addresses_in_aus(
                pre.branch_projection_aus() + allocs,
            )
        &&& tight.writes().dom()
            <= addresses_in_aus(
                pre.branch_projection_aus() + allocs,
            )
        &&& tight.writes().dom()
            <= addresses_in_aus(allocs)
        &&& CachedBranchBetree::State::compact_complete(
            pre.branch,
            post_branch,
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
            input_idx,
            branch_idx,
            path,
            start,
            end,
            new_node_addr,
            path_addrs,
            tight.loaded_betree_reads(),
            tight.loaded_betree_writes(),
            tight.loaded_branch_reads(),
        )
    }),
{
    let component = pre.known_branch_i();
    let linked = component.linked_i();
    let owned_addrs =
        addresses_in_aus(pre.branch_projection_aus());
    let tight =
        projected_compact_complete_access(pre, access);
    let tight_betree_reads =
        access.betree_reads.restrict(owned_addrs);
    let tight_branch_reads =
        access.branch_reads.restrict(owned_addrs);
    let full_branch_reads =
        access.loaded_branch_reads();
    let tight_loaded_branch_reads =
        tight.loaded_branch_reads();

    reveal(CachedBranchBetree::State::compact_complete);
    assert(0 <= input_idx
        < pre.branch.compactors.len());
    assert(0 <= branch_idx
        < pre.branch.wip_branches.len());
    let cached_branch =
        pre.branch.wip_branches[branch_idx];
    assert(cached_branch.sealed);
    assert(cached_branch.sealed_root() is Some);
    let branch_root =
        cached_branch.sealed_root().unwrap();
    let branch_owned =
        cached_branch.mini_allocator.all_aus();
    let input_roots =
        pre.branch.compactors[input_idx]
            .input_buffers.addrs.to_set();
    let input_aus =
        summary_aus(
            pre.branch.branch_summary.restrict(
                to_aus(input_roots),
            ),
        );
    let full_input_reads =
        loaded_branch_reads_for_roots(
            input_roots,
            pre.branch.branch_summary,
            full_branch_reads,
        );
    let tight_input_reads =
        loaded_branch_reads_for_roots(
            input_roots,
            pre.branch.branch_summary,
            tight_loaded_branch_reads,
        );
    let full_output_reads =
        full_branch_reads.restrict(
            addresses_in_aus(branch_owned),
        );
    let tight_output_reads =
        tight_loaded_branch_reads.restrict(
            addresses_in_aus(branch_owned),
        );

    assert(tight.wf());
    assert(tight.branch_writes.is_empty());
    assert(tight.writes() == access.writes());
    assert(tight.loaded_betree_writes()
        == access.loaded_betree_writes());
    assert(tight_loaded_branch_reads
        == full_branch_reads.restrict(owned_addrs))
    by {
        assert_maps_equal!(
            tight_loaded_branch_reads,
            full_branch_reads.restrict(owned_addrs),
            addr => {
                reveal(to_branch_nodes);
            }
        );
    }
    assert(tight.reads() <= access.reads()) by {
        assert forall |addr: Address|
            #[trigger] tight.reads().contains_key(addr)
            implies {
                &&& access.reads().contains_key(addr)
                &&& tight.reads()[addr]
                    == access.reads()[addr]
            }
        by {
            if tight_branch_reads.contains_key(addr) {
                assert(access.branch_reads
                    .contains_key(addr));
                assert(!access.betree_reads
                    .contains_key(addr));
            } else {
                assert(tight_betree_reads
                    .contains_key(addr));
                assert(access.betree_reads
                    .contains_key(addr));
                assert(!access.branch_reads
                    .contains_key(addr));
            }
        }
    }
    assert(tight.reads().dom() <= owned_addrs);
    assert(tight.reads().dom()
        <= addresses_in_aus(
            pre.branch_projection_aus() + allocs,
        ));

    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(pre.i().ephemeral is Known);
    assert(component.refinement_inv());
    component.linked_i_is_tight_candidate();
    component.linked_i_tight_tree_facts();
    assert(linked.acyclic());
    assert(linked.dv.entries
        <= to_betree_nodes(component.disk.visible())) by {
        assert(linked.dv.entries
            <= component.visible_betree_entries());
        assert(component.visible_betree_entries()
            <= to_betree_nodes(component.disk.visible())) by {
            assert forall |addr: Address|
                #[trigger] component.visible_betree_entries()
                    .contains_key(addr)
                implies {
                    &&& to_betree_nodes(
                        component.disk.visible(),
                    ).contains_key(addr)
                    &&& component.visible_betree_entries()[
                        addr
                    ] == to_betree_nodes(
                        component.disk.visible(),
                    )[addr]
                }
            by {
                reveal(CachingDiskBranchBetree::State::
                    visible_betree_entries);
            }
        }
        vstd::map_lib::lemma_submap_of_trans(
            linked.dv.entries,
            component.visible_betree_entries(),
            to_betree_nodes(component.disk.visible()),
        );
    }
    assert(path.valid_for(
        linked.root,
        to_betree_nodes(tight_betree_reads),
    )) by {
        assert(path.valid_for(
            linked.root,
            to_betree_nodes(access.betree_reads),
        ));
        assert(path.needed_addrs()
            <= to_betree_nodes(tight_betree_reads).dom())
        by {
            assert forall |addr: Address|
                #[trigger] path.needed_addrs().contains(addr)
                implies to_betree_nodes(tight_betree_reads)
                    .dom().contains(addr)
            by {
                betree_receipt_needed_addr_in_projection(
                    pre,
                    post_cache,
                    access,
                    linked,
                    path,
                    addr,
                );
                assert(access.betree_reads
                    .contains_key(addr));
                assert(tight_betree_reads
                    .contains_key(addr));
            }
        }
        assert forall |i: int|
            0 <= i < path.lines.len()
            implies {
                &&& to_betree_nodes(tight_betree_reads)
                    .contains_key(path.lines[i].addr)
                &&& #[trigger] to_betree_nodes(
                    tight_betree_reads,
                )[path.lines[i].addr]
                    == path.lines[i].node
            }
        by {
            let addr = path.lines[i].addr;
            assert(path.needed_addrs().contains(addr));
            betree_receipt_needed_addr_in_projection(
                pre,
                post_cache,
                access,
                linked,
                path,
                addr,
            );
            assert(tight_betree_reads.contains_key(addr));
            assert(tight_betree_reads[addr]
                == access.betree_reads[addr]);
            assert(to_betree_nodes(tight_betree_reads)[addr]
                == to_betree_nodes(
                    access.betree_reads,
                )[addr]);
        }
    }

    assert(pre.branch.branch_summary.dom().finite()) by {
        let pre_i = component.i();
        assert(pre_i.inv());
        pre_i.inv_branch_summary_ensures();
        let (_, branch_likes) =
            pre_i.betree.linked.transitive_likes();
        assert(branch_likes.dom().finite());
        CompactorInput::input_roots_finite(
            pre_i.compactors,
        );
        let roots =
            branch_likes.dom()
                + CompactorInput::input_roots(
                    pre_i.compactors,
                );
        assert(roots.finite());
        component.semantic_sealed_branch_disk()
            .build_branch_summary_finite(roots);
    }
    summary_aus_restrict_subset(
        pre.branch.branch_summary,
        to_aus(input_roots),
    );
    reveal(UnifiedCacheBranchBetreeSource::
        branch_projection_aus);
    reveal(CachedBranchBetree::State::owned_aus);
    assert(input_aus
        <= pre.branch_projection_aus());
    component.wip_alloc_aus_agree();
    crate::allocation_layer::AllocationBranch_v::
        AllocationBranch::alloc_aus_ensures(
            component.i().wip_branches,
            branch_idx,
        );
    assert(component.i().wip_branches[branch_idx]
        .mini_allocator == cached_branch.mini_allocator)
    by {
        reveal(CachingDiskBranchBetree::State::
            wip_branches_i);
        reveal(CachingDiskBranchBetree::State::
            wip_branch_i);
    }
    assert(branch_owned
        <= pre.branch_projection_aus());
    assert(addresses_in_aus(input_aus)
        <= owned_addrs);
    assert(addresses_in_aus(branch_owned)
        <= owned_addrs);
    assert(tight_input_reads
        == full_input_reads) by {
        reveal(loaded_branch_reads_for_roots);
        assert_maps_equal!(
            tight_input_reads,
            full_input_reads,
            addr => {
                if addresses_in_aus(input_aus)
                    .contains(addr)
                {
                    assert(owned_addrs.contains(addr));
                }
            }
        );
    }
    assert(tight_output_reads
        == full_output_reads) by {
        assert_maps_equal!(
            tight_output_reads,
            full_output_reads,
            addr => {
                if addresses_in_aus(branch_owned)
                    .contains(addr)
                {
                    assert(owned_addrs.contains(addr));
                }
            }
        );
    }
    assert(valid_loaded_sealed_branches(
        input_roots,
        pre.branch.branch_summary,
        tight_input_reads,
    ));
    assert(valid_loaded_sealed_branch(
        branch_root,
        cached_branch.summary(),
        tight_output_reads,
    ));

    let new_addrs = TwoAddrs {
        addr1: new_node_addr,
        addr2: branch_root,
    };
    let replacement =
        compact_replacement(
            path,
            start,
            end,
            branch_root,
            new_addrs,
        );
    assert(replacement.dom() == set![new_node_addr]);
    substitute_writes_dom_subset(
        path,
        new_node_addr,
        replacement,
        path_addrs,
    );
    assert(tight.writes().dom()
        <= set![new_node_addr] + path_addrs.to_set());
    crate::disk::GenericDisk_v::to_aus_domain(
        path_addrs.to_set(),
    );
    assert(tight.writes().dom()
        <= addresses_in_aus(allocs)) by {
        assert forall |addr: Address|
            #[trigger] tight.writes().dom()
                .contains(addr)
            implies addresses_in_aus(allocs)
                .contains(addr)
        by {
            if addr == new_node_addr {
                assert(allocs.contains(
                    new_node_addr.au,
                ));
            } else {
                assert(path_addrs.to_set()
                    .contains(addr));
                assert(to_aus(path_addrs.to_set())
                    .contains(addr.au));
                assert(allocs.contains(addr.au));
            }
        }
    }
    assert(tight.writes().dom()
        <= addresses_in_aus(
            pre.branch_projection_aus() + allocs,
        ));

    assert(CachedBranchBetree::State::compact_complete(
        pre.branch,
        post_branch,
        CachedBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
        },
        input_idx,
        branch_idx,
        path,
        start,
        end,
        new_node_addr,
        path_addrs,
        tight.loaded_betree_reads(),
        tight.loaded_betree_writes(),
        tight.loaded_branch_reads(),
    )) by {
        reveal(CachedBranchBetree::State::compact_complete);
    }
}

proof fn branch_build_access_on_projection(
    pre: UnifiedCacheBranchBetreeSource,
    post_cache: Cache::State,
    idx: int,
    post_branch: CachedAllocationBranch,
    event: BranchBuildEvent,
    access: PageAccess,
    allocs: Set<AU>,
    deallocs: Set<AU>,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        access.only_branch(),
        Cache::State::next(
            pre.cache,
            post_cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        CachedBranchBetree::State::branch_build(
            pre.branch,
            branch_with_updated_wip(
                pre.branch,
                idx,
                post_branch,
            ),
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
            idx,
            post_branch,
            event.cached_event(access),
        ),
    ensures ({
        let tight =
            projected_branch_build_access(pre, access);
        &&& tight.wf()
        &&& tight.only_branch()
        &&& tight.reads()
            <= pre.known_branch_i().disk.cache
        &&& tight.reads().dom()
            <= addresses_in_aus(
                pre.branch_projection_aus(),
            )
        &&& tight.writes().dom()
            <= addresses_in_aus(
                pre.branch_projection_aus(),
            )
        &&& tight.writes().dom()
            <= addresses_in_aus(
                pre.branch.wip_branches[idx]
                    .mini_allocator.all_aus(),
            )
        &&& tight.writes().dom()
            <= Set::new(|addr: Address| addr.wf())
        &&& tight.reads() <= access.reads()
        &&& tight.writes() == access.writes()
        &&& CachedBranchBetree::State::branch_build(
            pre.branch,
            branch_with_updated_wip(
                pre.branch,
                idx,
                post_branch,
            ),
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
            idx,
            post_branch,
            event.cached_event(tight),
        )
    }),
{
    let tight =
        projected_branch_build_access(pre, access);
    let component = pre.known_branch_i();
    let pre_target = pre.branch.wip_branches[idx];
    let allocation = component.wip_branch_i(idx);
    let model_branch = allocation.branch.unwrap();
    let owned_addrs =
        addresses_in_aus(pre.branch_projection_aus());
    let tight_reads =
        access.branch_reads.restrict(owned_addrs);

    reveal(CachedBranchBetree::State::branch_build);
    reveal(CachedAllocationBranch::build_next);
    reveal(BranchBuildEvent::cached_event);
    reveal(branch_with_updated_wip);
    assert(CachedAllocationBranch::build_next(
        pre_target,
        post_branch,
        event.cached_event(access),
        allocs,
        deallocs,
    ));
    assert(0 <= idx < pre.branch.wip_branches.len());
    assert(!pre_target.sealed);
    assert(allocs.is_empty());
    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(pre.i().ephemeral is Known);
    assert(component.refinement_inv());
    assert(component.i().wip_branches_inv());
    assert(allocation == component.i().wip_branches[idx]);
    assert(allocation.inv());
    assert(!allocation.sealed);
    assert(allocation.mini_allocator
        == pre_target.mini_allocator) by {
        reveal(CachingDiskBranchBetree::State::
            wip_branch_i);
    }
    assert(allocation.branch is Some
        <==> pre_target.branch.root is Some) by {
        reveal(CachingDiskBranchBetree::State::
            wip_branch_i);
    }
    assert(tight.wf());
    assert(tight.only_branch());
    branch_only_write_domains(tight);
    assert(tight.reads() == tight_reads);
    assert(tight.writes() == access.writes());
    assert(tight.reads() <= access.reads());

    assert forall |addr: Address|
        #[trigger] tight_reads.contains_key(addr)
        implies pre.cache.valid_read(
            addr,
            tight_reads[addr],
        )
    by {
        page_access_branch_read_valid(
            pre.cache,
            post_cache,
            access,
            addr,
        );
    }
    valid_reads_in_project_cache_by_addrs(
        pre.cache,
        owned_addrs,
        tight_reads,
    );
    assert(tight_reads <= component.disk.cache) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_caching_disk_i);
        reveal(UnifiedCacheBranchBetreeSource::
            known_branch_i);
        reveal(crate::implementation::
            CachingDiskAdapterRefinement_v::
                project_cache_pages_by_addrs);
        reveal(project_cache_pages);
    }

    component.wip_alloc_aus_agree();
    crate::allocation_layer::AllocationBranch_v::
        AllocationBranch::alloc_aus_ensures(
            component.i().wip_branches,
            idx,
        );
    assert(component.i().wip_branches[idx]
        .mini_allocator == pre_target.mini_allocator) by {
        reveal(CachingDiskBranchBetree::State::
            wip_branches_i);
        reveal(CachingDiskBranchBetree::State::
            wip_branch_i);
    }
    reveal(UnifiedCacheBranchBetreeSource::
        branch_projection_aus);
    reveal(CachedBranchBetree::State::owned_aus);
    assert(pre_target.mini_allocator.all_aus()
        <= pre.branch_projection_aus());

    match event {
        BranchBuildEvent::Append{
            receipt,
            keys,
            msgs,
        } => {
            let source_event =
                CachedAllocationBranchEvent::Append {
                    receipt,
                    keys,
                    msgs,
                    read_nodes:
                        access.loaded_branch_reads(),
                    write_nodes:
                        access.loaded_branch_writes(),
                };
            assert(event.cached_event(access)
                == source_event);
            assert(CachedAllocationBranch::build_next(
                pre_target,
                post_branch,
                source_event,
                allocs,
                deallocs,
            ));
            assert(source_event is Append);
            let source_label = CachedBranch::Label::Append {
                mini_allocator: pre_target.mini_allocator,
                receipt,
                keys,
                msgs,
                read_nodes: access.loaded_branch_reads(),
                write_nodes: access.loaded_branch_writes(),
            };
            assert(CachedBranch::State::next(
                pre_target.branch,
                post_branch.branch,
                source_label,
            )) by {
                reveal(CachedAllocationBranch::build_next);
            }
            reveal(CachedBranch::State::next);
            reveal(CachedBranch::State::next_by);
            let source_step = choose |step: CachedBranch::Step|
                CachedBranch::State::next_by(
                    pre_target.branch,
                    post_branch.branch,
                    source_label,
                    step,
                );
            match source_step {
                CachedBranch::Step::append_step() => {
                    reveal(CachedBranch::State::append_step);
                }
                _ => {
                    assert(false);
                }
            }
            assert(pre_target.branch.can_append(
                pre_target.mini_allocator,
                receipt,
                keys,
                msgs,
                access.loaded_branch_reads(),
                access.loaded_branch_writes(),
            ));
            assert(allocation.branch is Some);
            assert(receipt.valid_for(
                model_branch.root,
                to_branch_nodes(access.branch_reads),
            )) by {
                assert(model_branch.root
                    == pre_target.branch.root.unwrap()) by {
                    reveal(CachingDiskBranchBetree::State::
                        wip_branch_i);
                }
            }
            wip_receipt_valid_on_projection(
                pre,
                post_cache,
                access,
                idx,
                receipt,
            );
            let target = receipt.target().addr;
            wip_receipt_needed_addr_in_projection(
                pre,
                post_cache,
                access,
                idx,
                receipt,
                target,
            );
            wip_branch_addr_wf(allocation, target);
            assert(tight.loaded_branch_writes().dom()
                == set![target]);
            assert(allocation.addrs_closed_under_mini_allocator());
            assert(allocation.mini_allocator
                .page_is_allocated(target));
            assert(pre_target.mini_allocator.all_aus()
                .contains(target.au));
            assert(tight.writes().dom()
                <= addresses_in_aus(
                    pre_target.mini_allocator.all_aus(),
                ));
            assert(tight.writes().dom()
                <= owned_addrs);
            assert(tight.writes().dom()
                <= Set::new(|addr: Address| addr.wf())) by {
                assert forall |addr: Address|
                    #[trigger] tight.writes().dom()
                        .contains(addr)
                    implies addr.wf()
                by {
                    assert(addr == target);
                }
            }
            assert(pre_target.branch.can_append(
                pre_target.mini_allocator,
                receipt,
                keys,
                msgs,
                tight.loaded_branch_reads(),
                tight.loaded_branch_writes(),
            )) by {
                reveal(CachedBranch::State::can_append);
                reveal(crate::implementation::
                    CachedBranch_v::loaded_append_ready);
            }
            let tight_event =
                CachedAllocationBranchEvent::Append {
                    receipt,
                    keys,
                    msgs,
                    read_nodes:
                        tight.loaded_branch_reads(),
                    write_nodes:
                        tight.loaded_branch_writes(),
                };
            assert(event.cached_event(tight)
                == tight_event);
            assert(CachedBranch::State::next(
                pre_target.branch,
                post_branch.branch,
                CachedBranch::Label::Append {
                    mini_allocator:
                        pre_target.mini_allocator,
                    receipt,
                    keys,
                    msgs,
                    read_nodes:
                        tight.loaded_branch_reads(),
                    write_nodes:
                        tight.loaded_branch_writes(),
                },
            )) by {
                assert(CachedBranch::State::next_by(
                    pre_target.branch,
                    post_branch.branch,
                    CachedBranch::Label::Append {
                        mini_allocator:
                            pre_target.mini_allocator,
                        receipt,
                        keys,
                        msgs,
                        read_nodes:
                            tight.loaded_branch_reads(),
                        write_nodes:
                            tight.loaded_branch_writes(),
                    },
                    CachedBranch::Step::append_step(),
                )) by {
                    reveal(CachedBranch::State::next_by);
                    reveal(CachedBranch::State::append_step);
                }
                reveal(CachedBranch::State::next);
            }
            assert(CachedAllocationBranch::build_next(
                pre_target,
                post_branch,
                tight_event,
                allocs,
                deallocs,
            )) by {
                reveal(CachedAllocationBranch::build_next);
            }
            assert(CachedBranchBetree::State::branch_build(
                pre.branch,
                branch_with_updated_wip(
                    pre.branch,
                    idx,
                    post_branch,
                ),
                CachedBranchBetree::Label::InternalAlloc {
                    allocs,
                    deallocs,
                },
                idx,
                post_branch,
                event.cached_event(tight),
            )) by {
                reveal(CachedBranchBetree::State::
                    branch_build);
                reveal(CachedAllocationBranch::
                    build_next);
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                reveal(CachedBranch::State::append_step);
                reveal(CachedBranch::State::can_append);
                reveal(crate::implementation::
                    CachedBranch_v::loaded_append_ready);
            }
        }
        BranchBuildEvent::Initialize{
            init_root,
            keys,
            msgs,
        } => {
            let source_event =
                CachedAllocationBranchEvent::Initialize {
                    init_root,
                    keys,
                    msgs,
                    write_nodes:
                        access.loaded_branch_writes(),
                };
            assert(event.cached_event(access)
                == source_event);
            assert(CachedAllocationBranch::build_next(
                pre_target,
                post_branch,
                source_event,
                allocs,
                deallocs,
            ));
            assert(source_event is Initialize);
            let source_label = CachedBranch::Label::Initialize {
                mini_allocator: pre_target.mini_allocator,
                init_root,
                keys,
                msgs,
                write_nodes: access.loaded_branch_writes(),
            };
            assert(CachedBranch::State::next(
                pre_target.branch,
                post_branch.branch,
                source_label,
            )) by {
                reveal(CachedAllocationBranch::build_next);
            }
            reveal(CachedBranch::State::next);
            reveal(CachedBranch::State::next_by);
            let source_step = choose |step: CachedBranch::Step|
                CachedBranch::State::next_by(
                    pre_target.branch,
                    post_branch.branch,
                    source_label,
                    step,
                );
            match source_step {
                CachedBranch::Step::initialize_branch() => {
                    reveal(CachedBranch::State::initialize_branch);
                }
                _ => {
                    assert(false);
                }
            }
            assert(pre_target.branch.can_initialize(
                pre_target.mini_allocator,
                init_root,
                keys,
                msgs,
                access.loaded_branch_writes(),
            ));
            assert(pre_target.mini_allocator
                .can_allocate(init_root));
            assert(init_root.wf()) by {
                reveal(crate::allocation_layer::
                    MiniAllocator_v::MiniAllocator::
                        can_allocate);
                reveal(crate::allocation_layer::
                    MiniAllocator_v::PageAllocator::
                        is_free_addr);
            }
            assert(pre_target.mini_allocator.all_aus()
                .contains(init_root.au));
            assert(tight.loaded_branch_writes().dom()
                == set![init_root]);
            assert(tight.writes().dom()
                <= addresses_in_aus(
                    pre_target.mini_allocator.all_aus(),
                ));
            assert(tight.writes().dom()
                <= owned_addrs);
            assert(tight.writes().dom()
                <= Set::new(|addr: Address| addr.wf())) by {
                assert forall |addr: Address|
                    #[trigger] tight.writes().dom()
                        .contains(addr)
                    implies addr.wf()
                by {
                    assert(addr == init_root);
                }
            }
            assert(event.cached_event(tight)
                == event.cached_event(access));
        }
        BranchBuildEvent::Grow{new_root_addr} => {
            let source_event =
                CachedAllocationBranchEvent::Grow {
                    new_root_addr,
                    read_nodes:
                        access.loaded_branch_reads(),
                    write_nodes:
                        access.loaded_branch_writes(),
                };
            assert(event.cached_event(access)
                == source_event);
            assert(CachedAllocationBranch::build_next(
                pre_target,
                post_branch,
                source_event,
                allocs,
                deallocs,
            ));
            assert(source_event is Grow);
            let source_label = CachedBranch::Label::Grow {
                mini_allocator: pre_target.mini_allocator,
                new_root_addr,
                read_nodes: access.loaded_branch_reads(),
                write_nodes: access.loaded_branch_writes(),
            };
            assert(CachedBranch::State::next(
                pre_target.branch,
                post_branch.branch,
                source_label,
            )) by {
                reveal(CachedAllocationBranch::build_next);
            }
            reveal(CachedBranch::State::next);
            reveal(CachedBranch::State::next_by);
            let source_step = choose |step: CachedBranch::Step|
                CachedBranch::State::next_by(
                    pre_target.branch,
                    post_branch.branch,
                    source_label,
                    step,
                );
            match source_step {
                CachedBranch::Step::grow_step() => {
                    reveal(CachedBranch::State::grow_step);
                }
                _ => {
                    assert(false);
                }
            }
            assert(pre_target.branch.can_grow(
                pre_target.mini_allocator,
                new_root_addr,
                access.loaded_branch_reads(),
                access.loaded_branch_writes(),
            ));
            assert(allocation.branch is Some);
            let root = model_branch.root;
            wip_root_in_projection(pre, idx);
            assert(pre_target.branch.root
                == Some(root)) by {
                reveal(CachingDiskBranchBetree::State::
                    wip_branch_i);
            }
            assert(access.branch_reads.contains_key(root));
            assert(tight_reads.contains_key(root));
            assert(tight_reads[root]
                == access.branch_reads[root]);
            assert(pre_target.mini_allocator
                .can_allocate(new_root_addr));
            assert(new_root_addr.wf()) by {
                reveal(crate::allocation_layer::
                    MiniAllocator_v::MiniAllocator::
                        can_allocate);
                reveal(crate::allocation_layer::
                    MiniAllocator_v::PageAllocator::
                        is_free_addr);
            }
            assert(pre_target.mini_allocator.all_aus()
                .contains(new_root_addr.au));
            assert(tight.loaded_branch_writes().dom()
                == set![new_root_addr]);
            assert(tight.writes().dom()
                <= addresses_in_aus(
                    pre_target.mini_allocator.all_aus(),
                ));
            assert(tight.writes().dom()
                <= owned_addrs);
            assert(tight.writes().dom()
                <= Set::new(|addr: Address| addr.wf())) by {
                assert forall |addr: Address|
                    #[trigger] tight.writes().dom()
                        .contains(addr)
                    implies addr.wf()
                by {
                    assert(addr == new_root_addr);
                }
            }
            assert(crate::implementation::
                CachedBranch_v::loaded_line_wf(
                    tight.loaded_branch_reads(),
                    root,
                ));
            assert(pre_target.branch.can_grow(
                pre_target.mini_allocator,
                new_root_addr,
                tight.loaded_branch_reads(),
                tight.loaded_branch_writes(),
            )) by {
                reveal(CachedBranch::State::can_grow);
            }
            let tight_event =
                CachedAllocationBranchEvent::Grow {
                    new_root_addr,
                    read_nodes:
                        tight.loaded_branch_reads(),
                    write_nodes:
                        tight.loaded_branch_writes(),
                };
            assert(event.cached_event(tight)
                == tight_event);
            assert(CachedBranch::State::next(
                pre_target.branch,
                post_branch.branch,
                CachedBranch::Label::Grow {
                    mini_allocator:
                        pre_target.mini_allocator,
                    new_root_addr,
                    read_nodes:
                        tight.loaded_branch_reads(),
                    write_nodes:
                        tight.loaded_branch_writes(),
                },
            )) by {
                assert(CachedBranch::State::next_by(
                    pre_target.branch,
                    post_branch.branch,
                    CachedBranch::Label::Grow {
                        mini_allocator:
                            pre_target.mini_allocator,
                        new_root_addr,
                        read_nodes:
                            tight.loaded_branch_reads(),
                        write_nodes:
                            tight.loaded_branch_writes(),
                    },
                    CachedBranch::Step::grow_step(),
                )) by {
                    reveal(CachedBranch::State::next_by);
                    reveal(CachedBranch::State::grow_step);
                }
                reveal(CachedBranch::State::next);
            }
            assert(CachedAllocationBranch::build_next(
                pre_target,
                post_branch,
                tight_event,
                allocs,
                deallocs,
            )) by {
                reveal(CachedAllocationBranch::build_next);
            }
            assert(CachedBranchBetree::State::branch_build(
                pre.branch,
                branch_with_updated_wip(
                    pre.branch,
                    idx,
                    post_branch,
                ),
                CachedBranchBetree::Label::InternalAlloc {
                    allocs,
                    deallocs,
                },
                idx,
                post_branch,
                event.cached_event(tight),
            )) by {
                reveal(CachedBranchBetree::State::
                    branch_build);
                reveal(CachedAllocationBranch::
                    build_next);
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                reveal(CachedBranch::State::grow_step);
                reveal(CachedBranch::State::can_grow);
                reveal(crate::implementation::
                    CachedBranch_v::loaded_line_wf);
            }
        }
        BranchBuildEvent::Split{
            new_child_addr,
            receipt,
            split_arg,
        } => {
            let source_event =
                CachedAllocationBranchEvent::Split {
                    new_child_addr,
                    receipt,
                    split_arg,
                    read_nodes:
                        access.loaded_branch_reads(),
                    write_nodes:
                        access.loaded_branch_writes(),
                };
            assert(event.cached_event(access)
                == source_event);
            assert(CachedAllocationBranch::build_next(
                pre_target,
                post_branch,
                source_event,
                allocs,
                deallocs,
            ));
            assert(source_event is Split);
            let source_label = CachedBranch::Label::Split {
                mini_allocator: pre_target.mini_allocator,
                new_child_addr,
                receipt,
                split_arg,
                read_nodes: access.loaded_branch_reads(),
                write_nodes: access.loaded_branch_writes(),
            };
            assert(CachedBranch::State::next(
                pre_target.branch,
                post_branch.branch,
                source_label,
            )) by {
                reveal(CachedAllocationBranch::build_next);
            }
            reveal(CachedBranch::State::next);
            reveal(CachedBranch::State::next_by);
            let source_step = choose |step: CachedBranch::Step|
                CachedBranch::State::next_by(
                    pre_target.branch,
                    post_branch.branch,
                    source_label,
                    step,
                );
            match source_step {
                CachedBranch::Step::split_step() => {
                    reveal(CachedBranch::State::split_step);
                }
                _ => {
                    assert(false);
                }
            }
            assert(pre_target.branch.can_split(
                pre_target.mini_allocator,
                new_child_addr,
                receipt,
                split_arg,
                access.loaded_branch_reads(),
                access.loaded_branch_writes(),
            ));
            assert(allocation.branch is Some);
            assert(receipt.valid_for(
                model_branch.root,
                to_branch_nodes(access.branch_reads),
            )) by {
                assert(model_branch.root
                    == pre_target.branch.root.unwrap()) by {
                    reveal(CachingDiskBranchBetree::State::
                        wip_branch_i);
                }
            }
            wip_receipt_valid_on_projection(
                pre,
                post_cache,
                access,
                idx,
                receipt,
            );
            let parent_addr = receipt.target().addr;
            wip_receipt_needed_addr_in_projection(
                pre,
                post_cache,
                access,
                idx,
                receipt,
                parent_addr,
            );
            wip_branch_addr_wf(allocation, parent_addr);
            let child_addr = receipt.child_addr();
            assert(model_branch.disk_view.entries[
                parent_addr
            ] == receipt.target().node);
            assert(model_branch.disk_view.entries
                .contains_key(child_addr)) by {
                let parent = receipt.target().node;
                let child_idx =
                    parent.route(receipt.key) + 1;
                assert(receipt.target().wf());
                assert(parent.wf());
                broadcast use LinkedBranchRefinement::
                    lemma_route_ensures;
                assert(parent.valid_child_index(
                    child_idx,
                ));
                assert(parent->children[child_idx]
                    == child_addr);
                assert(model_branch.disk_view
                    .no_dangling_address());
                assert(model_branch.disk_view
                    .node_has_valid_child_address(parent));
                assert(model_branch.disk_view
                    .valid_address(child_addr));
            }
            assert(allocation.addrs_closed_under_mini_allocator());
            assert(allocation.mini_allocator
                .page_is_allocated(child_addr));
            wip_branch_addr_wf(allocation, child_addr);
            assert(pre_target.mini_allocator.all_aus()
                .contains(child_addr.au));
            assert(owned_addrs.contains(child_addr));
            assert(access.branch_reads
                .contains_key(child_addr));
            assert(tight_reads.contains_key(child_addr));
            assert(tight_reads[child_addr]
                == access.branch_reads[child_addr]);
            assert(crate::implementation::
                CachedBranch_v::loaded_line_wf(
                    tight.loaded_branch_reads(),
                    child_addr,
                )) by {
                reveal(crate::implementation::
                    CachedBranch_v::loaded_line_wf);
            }
            assert(pre_target.mini_allocator
                .can_allocate(new_child_addr));
            assert(new_child_addr.wf()) by {
                reveal(crate::allocation_layer::
                    MiniAllocator_v::MiniAllocator::
                        can_allocate);
                reveal(crate::allocation_layer::
                    MiniAllocator_v::PageAllocator::
                        is_free_addr);
            }
            assert(pre_target.mini_allocator.all_aus()
                .contains(new_child_addr.au));
            assert(allocation.mini_allocator
                .page_is_allocated(parent_addr));
            assert(pre_target.mini_allocator.all_aus()
                .contains(parent_addr.au));
            assert(tight.loaded_branch_writes().dom()
                == set![
                    parent_addr,
                    child_addr,
                    new_child_addr,
                ]);
            assert(tight.writes().dom()
                <= addresses_in_aus(
                    pre_target.mini_allocator.all_aus(),
                ));
            assert(tight.writes().dom()
                <= owned_addrs);
            assert(tight.writes().dom()
                <= Set::new(|addr: Address| addr.wf())) by {
                assert forall |addr: Address|
                    #[trigger] tight.writes().dom()
                        .contains(addr)
                    implies addr.wf()
                by {
                    assert(addr == parent_addr
                        || addr == child_addr
                        || addr == new_child_addr);
                }
            }
            assert(pre_target.branch.can_split(
                pre_target.mini_allocator,
                new_child_addr,
                receipt,
                split_arg,
                tight.loaded_branch_reads(),
                tight.loaded_branch_writes(),
            )) by {
                reveal(CachedBranch::State::can_split);
                reveal(crate::implementation::
                    CachedBranch_v::loaded_split_ready);
                reveal(crate::implementation::
                    CachedBranch_v::loaded_split_write_nodes);
            }
            let tight_event =
                CachedAllocationBranchEvent::Split {
                    new_child_addr,
                    receipt,
                    split_arg,
                    read_nodes:
                        tight.loaded_branch_reads(),
                    write_nodes:
                        tight.loaded_branch_writes(),
                };
            assert(event.cached_event(tight)
                == tight_event);
            assert(CachedBranch::State::next(
                pre_target.branch,
                post_branch.branch,
                CachedBranch::Label::Split {
                    mini_allocator:
                        pre_target.mini_allocator,
                    new_child_addr,
                    receipt,
                    split_arg,
                    read_nodes:
                        tight.loaded_branch_reads(),
                    write_nodes:
                        tight.loaded_branch_writes(),
                },
            )) by {
                assert(CachedBranch::State::next_by(
                    pre_target.branch,
                    post_branch.branch,
                    CachedBranch::Label::Split {
                        mini_allocator:
                            pre_target.mini_allocator,
                        new_child_addr,
                        receipt,
                        split_arg,
                        read_nodes:
                            tight.loaded_branch_reads(),
                        write_nodes:
                            tight.loaded_branch_writes(),
                    },
                    CachedBranch::Step::split_step(),
                )) by {
                    reveal(CachedBranch::State::next_by);
                    reveal(CachedBranch::State::split_step);
                }
                reveal(CachedBranch::State::next);
            }
            assert(CachedAllocationBranch::build_next(
                pre_target,
                post_branch,
                tight_event,
                allocs,
                deallocs,
            )) by {
                reveal(CachedAllocationBranch::build_next);
            }
            assert(CachedBranchBetree::State::branch_build(
                pre.branch,
                branch_with_updated_wip(
                    pre.branch,
                    idx,
                    post_branch,
                ),
                CachedBranchBetree::Label::InternalAlloc {
                    allocs,
                    deallocs,
                },
                idx,
                post_branch,
                event.cached_event(tight),
            )) by {
                reveal(CachedBranchBetree::State::
                    branch_build);
                reveal(CachedAllocationBranch::
                    build_next);
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                reveal(CachedBranch::State::split_step);
                reveal(CachedBranch::State::can_split);
                reveal(crate::implementation::
                    CachedBranch_v::loaded_split_ready);
            }
        }
        BranchBuildEvent::Seal{aux_ptr} => {
            let source_event =
                CachedAllocationBranchEvent::Seal {
                    aux_ptr,
                    read_nodes:
                        access.loaded_branch_reads(),
                    write_nodes:
                        access.loaded_branch_writes(),
                };
            assert(event.cached_event(access)
                == source_event);
            assert(CachedAllocationBranch::build_next(
                pre_target,
                post_branch,
                source_event,
                allocs,
                deallocs,
            ));
            assert(source_event is Seal);
            let source_label = CachedBranch::Label::Seal {
                mini_allocator: pre_target.mini_allocator,
                aux_ptr,
                read_nodes: access.loaded_branch_reads(),
                write_nodes: access.loaded_branch_writes(),
            };
            assert(CachedBranch::State::next(
                pre_target.branch,
                post_branch.branch,
                source_label,
            )) by {
                reveal(CachedAllocationBranch::build_next);
            }
            reveal(CachedBranch::State::next);
            reveal(CachedBranch::State::next_by);
            let source_step = choose |step: CachedBranch::Step|
                CachedBranch::State::next_by(
                    pre_target.branch,
                    post_branch.branch,
                    source_label,
                    step,
                );
            match source_step {
                CachedBranch::Step::seal_step() => {
                    reveal(CachedBranch::State::seal_step);
                }
                _ => {
                    assert(false);
                }
            }
            assert(pre_target.branch.can_seal(
                pre_target.mini_allocator,
                aux_ptr,
                access.loaded_branch_reads(),
                access.loaded_branch_writes(),
            ));
            assert(allocation.branch is Some);
            let root = model_branch.root;
            wip_root_in_projection(pre, idx);
            assert(model_branch.disk_view.entries
                .contains_key(root));
            wip_branch_addr_wf(allocation, root);
            assert(pre_target.branch.root
                == Some(root)) by {
                reveal(CachingDiskBranchBetree::State::
                    wip_branch_i);
            }
            assert(access.branch_reads.contains_key(root));
            assert(tight_reads.contains_key(root));
            assert(tight_reads[root]
                == access.branch_reads[root]);
            if aux_ptr is Some {
                assert(pre_target.mini_allocator
                    .can_allocate(aux_ptr.unwrap()));
                assert(aux_ptr.unwrap().wf()) by {
                    reveal(crate::allocation_layer::
                        MiniAllocator_v::MiniAllocator::
                            can_allocate);
                    reveal(crate::allocation_layer::
                        MiniAllocator_v::PageAllocator::
                            is_free_addr);
                }
                assert(pre_target.mini_allocator
                    .all_aus().contains(
                        aux_ptr.unwrap().au,
                    ));
                assert(tight.loaded_branch_writes().dom()
                    == set![root, aux_ptr.unwrap()]);
                assert(allocation.mini_allocator
                    .page_is_allocated(root));
                assert(pre_target.mini_allocator.all_aus()
                    .contains(root.au));
            } else {
                assert(tight.loaded_branch_writes()
                    .is_empty());
            }
            assert(tight.writes().dom()
                <= addresses_in_aus(
                    pre_target.mini_allocator.all_aus(),
                ));
            assert(tight.writes().dom()
                <= owned_addrs);
            assert(tight.writes().dom()
                <= Set::new(|addr: Address| addr.wf())) by {
                assert forall |addr: Address|
                    #[trigger] tight.writes().dom()
                        .contains(addr)
                    implies addr.wf()
                by {
                    if aux_ptr is Some {
                        assert(addr == root
                            || addr == aux_ptr.unwrap());
                    } else {
                        assert(false);
                    }
                }
            }
            assert(crate::implementation::
                CachedBranch_v::loaded_line_wf(
                    tight.loaded_branch_reads(),
                    root,
                ));
            assert(pre_target.branch.can_seal(
                pre_target.mini_allocator,
                aux_ptr,
                tight.loaded_branch_reads(),
                tight.loaded_branch_writes(),
            )) by {
                reveal(CachedBranch::State::can_seal);
                reveal(crate::implementation::
                    CachedBranch_v::loaded_seal_write_nodes);
            }
            let tight_event =
                CachedAllocationBranchEvent::Seal {
                    aux_ptr,
                    read_nodes:
                        tight.loaded_branch_reads(),
                    write_nodes:
                        tight.loaded_branch_writes(),
                };
            assert(event.cached_event(tight)
                == tight_event);
            assert(CachedBranch::State::next(
                pre_target.branch,
                post_branch.branch,
                CachedBranch::Label::Seal {
                    mini_allocator:
                        pre_target.mini_allocator,
                    aux_ptr,
                    read_nodes:
                        tight.loaded_branch_reads(),
                    write_nodes:
                        tight.loaded_branch_writes(),
                },
            )) by {
                assert(CachedBranch::State::next_by(
                    pre_target.branch,
                    post_branch.branch,
                    CachedBranch::Label::Seal {
                        mini_allocator:
                            pre_target.mini_allocator,
                        aux_ptr,
                        read_nodes:
                            tight.loaded_branch_reads(),
                        write_nodes:
                            tight.loaded_branch_writes(),
                    },
                    CachedBranch::Step::seal_step(),
                )) by {
                    reveal(CachedBranch::State::next_by);
                    reveal(CachedBranch::State::seal_step);
                }
                reveal(CachedBranch::State::next);
            }
            assert(CachedAllocationBranch::build_next(
                pre_target,
                post_branch,
                tight_event,
                allocs,
                deallocs,
            )) by {
                reveal(CachedAllocationBranch::build_next);
            }
            assert(CachedBranchBetree::State::branch_build(
                pre.branch,
                branch_with_updated_wip(
                    pre.branch,
                    idx,
                    post_branch,
                ),
                CachedBranchBetree::Label::InternalAlloc {
                    allocs,
                    deallocs,
                },
                idx,
                post_branch,
                event.cached_event(tight),
            )) by {
                reveal(CachedBranchBetree::State::
                    branch_build);
                reveal(CachedAllocationBranch::
                    build_next);
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                reveal(CachedBranch::State::seal_step);
                reveal(CachedBranch::State::can_seal);
                reveal(crate::implementation::
                    CachedBranch_v::loaded_line_wf);
            }
        }
    }
}

proof fn branch_receipts_valid_on_projection(
    src: UnifiedCacheBranchBetreeSource,
    post_cache: Cache::State,
    access: PageAccess,
    linked: LinkedBetree<BranchNode>,
    roots: crate::betree::LinkedSeq_v::LinkedSeq,
    start: nat,
    receipts: Seq<LoadedPathReceipt>,
    key: Key,
)
    requires
        inv(src),
        src.control.metadata_loaded,
        access.wf(),
        Cache::State::next(
            src.cache,
            post_cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        linked.buffer_dv.entries
            == src.known_branch_i().linked_i()
                .buffer_dv.entries,
        linked.buffer_dv.entries
            <= to_branch_nodes(
                src.known_branch_i().disk.visible(),
            ),
        linked.buffer_dv.valid_buffers(roots),
        linked.buffer_dv.sealed_branch_roots(
            roots.addrs.to_set(),
        ),
        branch_receipts_valid(
            roots,
            start,
            receipts,
            key,
            to_branch_nodes(access.branch_reads),
        ),
    ensures
        branch_receipts_valid(
            roots,
            start,
            receipts,
            key,
            to_branch_nodes(
                access.branch_reads.restrict(
                    addresses_in_aus(
                        src.branch_projection_aus(),
                    ),
                ),
            ),
        ),
{
    let owned_addrs =
        addresses_in_aus(src.branch_projection_aus());
    let tight_reads =
        access.branch_reads.restrict(owned_addrs);
    let loaded_reads = to_branch_nodes(access.branch_reads);
    let tight_loaded_reads = to_branch_nodes(tight_reads);

    assert forall |i: int|
        0 <= i < receipts.len()
        implies {
            let receipt = #[trigger] receipts[i];
            let root = roots[start as int + i];
            &&& receipt.key == key
            &&& receipt.valid_for(root, tight_loaded_reads)
            &&& receipt.target().node is Leaf
        }
    by {
        let receipt = receipts[i];
        let root_idx = start as int + i;
        let root = roots[root_idx];
        assert(root_idx < roots.len());
        assert(roots.addrs.to_set().contains(root));
        linked.buffer_dv.sealed_branch_roots_contains(
            roots.addrs.to_set(),
            root,
        );
        let branch = linked.buffer_dv.get_branch(root);
        assert(branch.valid_sealed_branch());
        assert(branch.inv());
        assert(branch.root == root);
        assert(branch.disk_view.entries
            == linked.buffer_dv.entries);
        assert(receipt.valid_for(root, loaded_reads));
        assert(receipt.valid_for(
            root,
            tight_loaded_reads,
        )) by {
            assert(receipt.needed_addrs()
                <= tight_loaded_reads.dom()) by {
                assert forall |addr: Address|
                    #[trigger] receipt.needed_addrs()
                        .contains(addr)
                    implies tight_loaded_reads.dom()
                        .contains(addr)
                by {
                    branch_receipt_needed_addr_in_projection(
                        src,
                        post_cache,
                        access,
                        branch,
                        receipt,
                        addr,
                    );
                    assert(owned_addrs.contains(addr));
                    assert(loaded_reads.contains_key(addr));
                    assert(access.branch_reads
                        .contains_key(addr));
                    assert(tight_reads.contains_key(addr));
                    assert(tight_loaded_reads
                        .contains_key(addr));
                }
            }
            assert forall |line_idx: int|
                0 <= line_idx < receipt.lines.len()
                implies {
                    &&& tight_loaded_reads.contains_key(
                        receipt.lines[line_idx].addr,
                    )
                    &&& #[trigger] tight_loaded_reads[
                        receipt.lines[line_idx].addr
                    ] == receipt.lines[line_idx].node
                }
            by {
                let addr = receipt.lines[line_idx].addr;
                assert(receipt.needed_addrs()
                    .contains(addr));
                branch_receipt_needed_addr_in_projection(
                    src,
                    post_cache,
                    access,
                    branch,
                    receipt,
                    addr,
                );
                assert(tight_reads.contains_key(addr));
                assert(tight_reads[addr]
                    == access.branch_reads[addr]);
                assert(tight_loaded_reads[addr]
                    == loaded_reads[addr]);
            }
        }
    }
}

pub proof fn query_refines(
    pre: UnifiedCacheBranchBetreeSource,
    post: UnifiedCacheBranchBetreeSource,
    end_lsn: LSN,
    key: Key,
    value: Value,
    receipt: LoadedBetreeQueryReceipt,
    access: PageAccess,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        post.branch == pre.branch,
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.sync_phase == pre.sync_phase,
        post.control == pre.control,
        access.wf(),
        access.read_only(),
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        CachedBranchBetree::State::query(
            pre.branch,
            pre.branch,
            CachedBranchBetree::Label::Query {
                end_lsn,
                key,
                value,
            },
            receipt,
            access.loaded_betree_reads(),
            access.loaded_branch_reads(),
        ),
    ensures
        CrashAwareCachingDiskBranchBetree::State::next(
            unified_cache_branch_betree_i(pre),
            unified_cache_branch_betree_i(post),
            CrashAwareCachingDiskBranchBetree::Label::Ephemeral {
                op: CachingDiskBranchBetree::Label::Query {
                    end_lsn,
                    key,
                    value,
                },
                deallocs: Set::empty(),
            },
        ),
        inv(post),
{
    let src = unified_cache_branch_betree_i(pre);
    let dst = unified_cache_branch_betree_i(post);
    let component_pre = pre.known_branch_i();
    let component_post = post.known_branch_i();
    let linked = component_pre.linked_i();
    let owned_addrs =
        addresses_in_aus(pre.branch_projection_aus());
    let tight_betree_reads =
        access.betree_reads.restrict(owned_addrs);
    let tight_branch_reads =
        access.branch_reads.restrict(owned_addrs);
    let tight_access = PageAccess {
        betree_reads: tight_betree_reads,
        branch_reads: tight_branch_reads,
        betree_writes: Map::empty(),
        branch_writes: Map::empty(),
    };
    let component_lbl =
        CachingDiskBranchBetree::Label::Query {
            end_lsn,
            key,
            value,
        };
    let target_lbl =
        CrashAwareCachingDiskBranchBetree::Label::
            Ephemeral {
                op: component_lbl,
                deallocs: Set::empty(),
            };

    reveal(CachedBranchBetree::State::query);
    assert(receipt.valid_for(
        pre.branch.root,
        key,
        to_betree_nodes(access.betree_reads),
        to_branch_nodes(access.branch_reads),
    ));
    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(src.ephemeral is Known);
    assert(component_pre.refinement_inv());
    component_pre.linked_i_is_tight_candidate();
    component_pre.linked_i_tight_tree_facts();
    assert(linked.acyclic());
    assert(linked.dv.entries
        <= to_betree_nodes(component_pre.disk.visible())) by {
        assert(linked.dv.entries
            <= component_pre.visible_betree_entries());
        assert(component_pre.visible_betree_entries()
            <= to_betree_nodes(component_pre.disk.visible())) by {
            assert forall |addr: Address|
                #[trigger] component_pre.visible_betree_entries()
                    .contains_key(addr)
                implies {
                    &&& to_betree_nodes(
                        component_pre.disk.visible(),
                    ).contains_key(addr)
                    &&& component_pre.visible_betree_entries()[addr]
                        == to_betree_nodes(
                            component_pre.disk.visible(),
                        )[addr]
                }
            by {
                reveal(CachingDiskBranchBetree::State::
                    visible_betree_entries);
            }
        }
        vstd::map_lib::lemma_submap_of_trans(
            linked.dv.entries,
            component_pre.visible_betree_entries(),
            to_betree_nodes(component_pre.disk.visible()),
        );
    }
    assert(linked.dv.entries.dom()
        == linked.reachable_betree_addrs());
    assert(linked.buffer_dv.entries
        <= to_branch_nodes(component_pre.disk.visible())) by {
        reveal(crate::implementation::
            CachingDiskBranchBetree_v::
                tight_sealed_branch_disk);
        reveal(crate::implementation::
            CachingDiskBranchBetree_v::
                visible_branch_disk);
    }

    assert forall |addr: Address|
        #[trigger] tight_betree_reads.contains_key(addr)
        implies pre.cache.valid_read(
            addr,
            tight_betree_reads[addr],
        )
    by {
        assert(access.betree_reads.contains_key(addr));
        page_access_betree_read_valid(
            pre.cache,
            post.cache,
            access,
            addr,
        );
    };
    valid_reads_in_project_cache_by_addrs(
        pre.cache,
        owned_addrs,
        tight_betree_reads,
    );
    assert(tight_betree_reads
        <= component_pre.disk.cache) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_caching_disk_i);
        reveal(UnifiedCacheBranchBetreeSource::
            known_branch_i);
        reveal(crate::implementation::
            CachingDiskAdapterRefinement_v::
                project_cache_pages_by_addrs);
        reveal(project_cache_pages);
    }
    assert forall |addr: Address|
        #[trigger] tight_branch_reads.contains_key(addr)
        implies pre.cache.valid_read(
            addr,
            tight_branch_reads[addr],
        )
    by {
        assert(access.branch_reads.contains_key(addr));
        page_access_branch_read_valid(
            pre.cache,
            post.cache,
            access,
            addr,
        );
    };
    valid_reads_in_project_cache_by_addrs(
        pre.cache,
        owned_addrs,
        tight_branch_reads,
    );
    assert(tight_branch_reads
        <= component_pre.disk.cache) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_caching_disk_i);
        reveal(UnifiedCacheBranchBetreeSource::
            known_branch_i);
        reveal(crate::implementation::
            CachingDiskAdapterRefinement_v::
                project_cache_pages_by_addrs);
        reveal(project_cache_pages);
    }

    assert(receipt.path.valid_for(
        linked.root,
        to_betree_nodes(tight_betree_reads),
    )) by {
        assert(receipt.path.valid_for(
            linked.root,
            to_betree_nodes(access.betree_reads),
        ));
        assert(receipt.path.needed_addrs()
            <= to_betree_nodes(tight_betree_reads).dom())
        by {
            assert forall |addr: Address|
                #[trigger] receipt.path.needed_addrs()
                    .contains(addr)
                implies to_betree_nodes(tight_betree_reads)
                    .dom().contains(addr)
            by {
                betree_receipt_needed_addr_in_projection(
                    pre,
                    post.cache,
                    access,
                    linked,
                    receipt.path,
                    addr,
                );
                assert(owned_addrs.contains(addr));
                assert(access.betree_reads
                    .contains_key(addr));
                assert(tight_betree_reads
                    .contains_key(addr));
            }
        }
        assert forall |i: int|
            0 <= i < receipt.path.lines.len()
            implies {
                &&& to_betree_nodes(tight_betree_reads)
                    .contains_key(
                        receipt.path.lines[i].addr,
                    )
                &&& #[trigger] to_betree_nodes(
                    tight_betree_reads,
                )[receipt.path.lines[i].addr]
                    == receipt.path.lines[i].node
            }
        by {
            let addr = receipt.path.lines[i].addr;
            assert(receipt.path.needed_addrs()
                .contains(addr));
            betree_receipt_needed_addr_in_projection(
                pre,
                post.cache,
                access,
                linked,
                receipt.path,
                addr,
            );
            assert(tight_betree_reads.contains_key(addr));
            assert(tight_betree_reads[addr]
                == access.betree_reads[addr]);
            assert(to_betree_nodes(tight_betree_reads)[addr]
                == to_betree_nodes(access.betree_reads)[addr]);
        }
    }

    let (_, branch_likes) = linked.transitive_likes();
    let compactor_roots =
        crate::allocation_layer::
            AllocationBranchBetree_v::
                CompactorInput::input_roots(
                    pre.branch.compactors,
                );
    linked.tree_likes_domain(linked.the_ranking());
    linked.buffer_likes_domain(
        linked.tree_likes(linked.the_ranking()),
    );
    assert(branch_likes.dom()
        == linked.reachable_buffer_addrs());
    assert(linked.buffer_dv.sealed_branch_roots(
        branch_likes.dom() + compactor_roots,
    ));

    assert forall |i: int|
        0 <= i < receipt.path.lines.len()
        implies {
            let node =
                (#[trigger] receipt.path.lines[i]).node;
            &&& linked.buffer_dv.valid_buffers(node.buffers)
            &&& linked.buffer_dv.sealed_branch_roots(
                node.buffers.addrs.to_set(),
            )
        }
    by {
        loaded_betree_path_matches_linked(
            component_pre.disk,
            linked,
            tight_betree_reads,
            receipt.path,
            i as nat,
        );
        let node = receipt.path.lines[i].node;
        let tree_addr = receipt.path.lines[i].addr;
        assert(linked.dv.entries.contains_key(tree_addr));
        assert(linked.reachable_betree_addrs()
            .contains(tree_addr));
        assert(linked.dv.entries[tree_addr] == node);
        assert forall |root: Address|
            #[trigger] node.buffers.addrs.to_set()
                .contains(root)
            implies linked.reachable_buffer_addrs()
                .contains(root)
        by {
            assert(node.buffers.contains(root));
            assert(linked.dv.entries[tree_addr]
                .buffers.contains(root));
            assert(linked.reachable_buffer(
                tree_addr,
                root,
            ));
        }
        assert(node.buffers.addrs.to_set()
            <= branch_likes.dom() + compactor_roots);
        linked.buffer_dv.sealed_branch_roots_subset(
            branch_likes.dom() + compactor_roots,
            node.buffers.addrs.to_set(),
        );
        assert(node.buffers.addrs.to_set()
            <= linked.buffer_dv.repr()) by {
            assert(node.buffers.addrs.to_set()
                <= linked.reachable_buffer_addrs());
            assert(linked.no_dangling_buffer_ptr());
        }
    }

    assert(receipt.valid_for(
        pre.branch.root,
        key,
        to_betree_nodes(tight_betree_reads),
        to_branch_nodes(tight_branch_reads),
    )) by {
        assert forall |i: int|
            0 <= i < receipt.path.lines.len()
            implies {
                let node =
                    (#[trigger] receipt.path.lines[i]).node;
                &&& branch_receipts_valid(
                    node.buffers,
                    node.flushed_ofs(key),
                    receipt.buffer_receipts[i],
                    key,
                    to_branch_nodes(tight_branch_reads),
                )
            }
        by {
            let node = receipt.path.lines[i].node;
            branch_receipts_valid_on_projection(
                pre,
                post.cache,
                access,
                linked,
                node.buffers,
                node.flushed_ofs(key),
                receipt.buffer_receipts[i],
                key,
            );
        }
    }

    assert(tight_access.wf());
    assert(tight_access.read_only());
    assert(tight_access.reads()
        <= component_pre.disk.cache) by {
        assert forall |addr: Address|
            #[trigger] tight_access.reads()
                .contains_key(addr)
            implies {
                &&& component_pre.disk.cache
                    .contains_key(addr)
                &&& tight_access.reads()[addr]
                    == component_pre.disk.cache[addr]
            }
        by {
            if tight_branch_reads.contains_key(addr) {
                assert(tight_access.reads()[addr]
                    == tight_branch_reads[addr]);
            } else {
                assert(tight_betree_reads.contains_key(addr));
                assert(tight_access.reads()[addr]
                    == tight_betree_reads[addr]);
            }
        }
    }
    assert(tight_access.writes().is_empty());
    assert(component_pre.disk.cache
        .union_prefer_right(tight_access.writes())
        == component_pre.disk.cache) by {
        assert_maps_equal!(
            component_pre.disk.cache
                .union_prefer_right(tight_access.writes()),
            component_pre.disk.cache,
            addr => {}
        );
    }
    assert(CachingDisk::State::access(
        component_pre.disk,
        component_pre.disk,
        CachingDisk::Label::Access {
            reads: tight_access.reads(),
            writes: tight_access.writes(),
        },
    )) by {
        reveal(CachingDisk::State::access);
        let empty_status = crate::implementation::
            CachingDisk_v::status_map(
                tight_access.writes().dom(),
                crate::implementation::CachingDisk_v::
                    PageStatus::Dirty,
            );
        assert(empty_status.is_empty());
        assert(component_pre.disk.status
            .union_prefer_right(empty_status)
            == component_pre.disk.status) by {
            assert_maps_equal!(
                component_pre.disk.status
                    .union_prefer_right(empty_status),
                component_pre.disk.status,
                addr => {}
            );
        }
    }
    assert(CachingDisk::State::next_by(
        component_pre.disk,
        component_pre.disk,
        CachingDisk::Label::Access {
            reads: tight_access.reads(),
            writes: tight_access.writes(),
        },
        CachingDisk::Step::access(),
    )) by {
        reveal(CachingDisk::State::next_by);
    }
    reveal(CachingDisk::State::next);

    assert(CachedBranchBetree::State::query(
        component_pre.betree,
        component_pre.betree,
        CachedBranchBetree::Label::Query {
            end_lsn,
            key,
            value,
        },
        receipt,
        tight_access.loaded_betree_reads(),
        tight_access.loaded_branch_reads(),
    )) by {
        reveal(CachedBranchBetree::State::query);
    }
    assert(CachingDiskBranchBetree::State::query(
        component_pre,
        component_pre,
        component_lbl,
        receipt,
        tight_access,
    )) by {
        reveal(CachingDiskBranchBetree::State::query);
    }
    assert(CachingDiskBranchBetree::State::next_by(
        component_pre,
        component_pre,
        component_lbl,
        CachingDiskBranchBetree::Step::query(
            receipt,
            tight_access,
        ),
    )) by {
        reveal(CachingDiskBranchBetree::State::next_by);
    }
    reveal(CachingDiskBranchBetree::State::next);

    Cache::State::inv_next(
        pre.cache,
        post.cache,
        Cache::Label::Access {
            reads: access.reads(),
            writes: access.writes(),
        },
    );
    assert(access.writes()
        == Map::<Address, RawPage>::empty()) by {
        assert(access.betree_writes.is_empty());
        assert(access.branch_writes.is_empty());
        assert_maps_equal!(
            access.writes(),
            Map::<Address, RawPage>::empty(),
            addr => {}
        );
    }
    assert(Cache::State::next(
        pre.cache,
        post.cache,
        Cache::Label::Access {
            reads: access.reads(),
            writes: Map::empty(),
        },
    ));
    projected_cache_read_only_access_unchanged(
        pre.cache,
        post.cache,
        pre.branch_projection_aus(),
        access.reads(),
    );
    assert(post.branch_projection_aus()
        =~= pre.branch_projection_aus());
    assert(project_persistent(
        post.disk,
        post.branch_projection_aus(),
    ) == project_persistent(
        pre.disk,
        pre.branch_projection_aus(),
    ));
    caching_disk_i_equal_from_raw_projection_agreement(
        post.cache,
        pre.cache,
        post.disk,
        pre.disk,
        post.branch_projection_aus(),
    );
    assert(component_post.disk == component_pre.disk);
    assert(component_post == component_pre);

    assert(dst.ephemeral is Known);
    assert(!(component_lbl is FreezeAs));
    assert(crate::implementation::
        CrashAwareCachingDiskBranchBetree_v::
            logical_allocs(component_lbl)
        =~= Set::<AU>::empty()) by {
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
    }
    assert(crate::implementation::
        CrashAwareCachingDiskBranchBetree_v::
            logical_deallocs(component_lbl)
        =~= Set::<AU>::empty()) by {
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs);
    }
    assert(crate::implementation::
        CrashAwareCachingDiskBranchBetree_v::
            logical_allocs(component_lbl).disjoint(
                crate::implementation::
                    CrashAwareCachingDiskBranchBetree_v::
                        protected_aus(
                            src.ephemeral->persistent_aus,
                            src.frozen,
                        ),
            ));
    assert(Set::<AU>::empty()
        == crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs(component_lbl)
            - crate::implementation::
                CrashAwareCachingDiskBranchBetree_v::
                    protected_aus(
                        src.ephemeral->persistent_aus,
                        src.frozen,
                    ));
    assert(CrashAwareCachingDiskBranchBetree::State::
        ephemeral_step(
            src,
            dst,
            target_lbl,
            component_post,
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            ephemeral_step);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                protected_aus);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBranchBetree::Step::
            ephemeral_step(component_post),
    )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    src.next_refines(dst, target_lbl);

    reveal(UnifiedCacheBranchBetreeSource::inv);
    assert(post.control_wf());
    assert(post.i().refinement_inv());
    assert(post.inv());
}

pub proof fn branch_begin_refines(
    pre: UnifiedCacheBranchBetreeSource,
    post: UnifiedCacheBranchBetreeSource,
    allocs: Set<AU>,
    deallocs: Set<AU>,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        post.cache == pre.cache,
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.sync_phase == pre.sync_phase,
        post.control == pre.control,
        CachedBranchBetree::State::branch_begin(
            pre.branch,
            post.branch,
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
        ),
    ensures
        CrashAwareCachingDiskBranchBetree::State::next(
            unified_cache_branch_betree_i(pre),
            unified_cache_branch_betree_i(post),
            CrashAwareCachingDiskBranchBetree::Label::
                Ephemeral {
                    op: CachingDiskBranchBetree::Label::
                        InternalAlloc {
                            allocs,
                            deallocs,
                            guard_aus:
                                pre.control.protected_aus(),
                        },
                    deallocs:
                        pre.control.reclaimable(deallocs),
                },
        ),
        post.branch_projection_aus()
            == (pre.branch_projection_aus() + allocs)
                - pre.control.reclaimable(deallocs),
        pre.control.reclaimable(deallocs)
            <= pre.branch_projection_aus(),
        cached_branch_alloc_aus(post.branch.wip_branches)
            == cached_branch_alloc_aus(
                pre.branch.wip_branches,
            ),
        inv(post),
{
    let src = pre.i();
    let dst = post.i();
    let component_pre = pre.known_branch_i();
    let component_post = post.known_branch_i();
    let component_lbl =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus: pre.control.protected_aus(),
        };
    let target_lbl =
        CrashAwareCachingDiskBranchBetree::Label::
            Ephemeral {
                op: component_lbl,
                deallocs:
                    pre.control.reclaimable(deallocs),
            };

    reveal(CachedBranchBetree::State::branch_begin);
    assert(allocs.is_empty());
    assert(deallocs.is_empty());
    assert(post.branch.betree_aus
        == pre.branch.betree_aus);
    assert(post.branch.branch_aus
        == pre.branch.branch_aus);
    assert(post.branch.branch_summary
        == pre.branch.branch_summary);
    assert(post.branch.compactors
        == pre.branch.compactors);
    assert(post.branch.wip_branches
        == pre.branch.wip_branches.push(
            crate::implementation::
                CachedBranchBetree_v::
                    CachedAllocationBranch::new(
                        Set::empty(),
                    ),
        ));
    assert(crate::implementation::
        CachedBranchBetree_v::
            cached_branch_alloc_aus(
                post.branch.wip_branches,
            )
        == crate::implementation::
            CachedBranchBetree_v::
                cached_branch_alloc_aus(
                    pre.branch.wip_branches,
                )) by {
        crate::implementation::
            CachedBranchBetree_v::
                cached_branch_alloc_aus_push_subset(
                    pre.branch.wip_branches,
                    crate::implementation::
                        CachedBranchBetree_v::
                            CachedAllocationBranch::new(
                                Set::empty(),
                            ),
                    Set::empty(),
                );
        assert forall |au: AU|
            #[trigger] crate::implementation::
                CachedBranchBetree_v::
                    cached_branch_alloc_aus(
                        pre.branch.wip_branches,
                    ).contains(au)
            implies crate::implementation::
                CachedBranchBetree_v::
                    cached_branch_alloc_aus(
                        post.branch.wip_branches,
                    ).contains(au)
        by {
            let idx = crate::implementation::
                CachedBranchBetree_v::
                    cached_branch_alloc_aus_contains(
                        pre.branch.wip_branches,
                        au,
                    );
            let sets = Seq::new(
                post.branch.wip_branches.len(),
                |i: int| post.branch.wip_branches[i]
                    .mini_allocator.all_aus(),
            );
            assert(sets[idx].contains(au));
            crate::betree::Utils_v::
                lemma_set_subset_of_union_seq_of_sets(
                    sets,
                    au,
                );
        }
    }
    assert(post.branch.owned_aus()
        == pre.branch.owned_aus()) by {
        reveal(CachedBranchBetree::State::owned_aus);
    }
    assert(post.branch_projection_aus()
        == pre.branch_projection_aus());
    assert(component_post.disk
        == component_pre.disk);

    assert(CachingDiskBranchBetree::State::branch_begin(
        component_pre,
        component_post,
        component_lbl,
        post.branch,
    )) by {
        reveal(CachingDiskBranchBetree::State::branch_begin);
    }
    assert(CachingDiskBranchBetree::State::next_by(
        component_pre,
        component_post,
        component_lbl,
        CachingDiskBranchBetree::Step::branch_begin(
            post.branch,
        ),
    )) by {
        reveal(CachingDiskBranchBetree::State::next_by);
    }
    reveal(CachingDiskBranchBetree::State::next);

    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(src.ephemeral->persistent_aus
        == dst.ephemeral->persistent_aus);
    assert(src.frozen == dst.frozen);
    assert(src.prepared == dst.prepared);
    assert(pre.control.protected_aus()
        == crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                protected_aus(
                    src.ephemeral->persistent_aus,
                    src.frozen,
                ));
    assert(pre.control.reclaimable(deallocs)
        == deallocs
            - crate::implementation::
                CrashAwareCachingDiskBranchBetree_v::
                    protected_aus(
                        src.ephemeral->persistent_aus,
                        src.frozen,
                    ));
    assert(CrashAwareCachingDiskBranchBetree::State::
        ephemeral_step(
            src,
            dst,
            target_lbl,
            component_post,
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            ephemeral_step);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_guard_aus);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBranchBetree::Step::
            ephemeral_step(component_post),
    )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    src.next_refines(dst, target_lbl);

    reveal(UnifiedCacheBranchBetreeSource::inv);
    assert(post.control_wf());
    assert(post.i().refinement_inv());
    assert(post.inv());
}

pub proof fn branch_fill_refines(
    pre: UnifiedCacheBranchBetreeSource,
    post: UnifiedCacheBranchBetreeSource,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    idx: int,
    post_branch: crate::implementation::
        CachedBranchBetree_v::CachedAllocationBranch,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        allocs.disjoint(pre.control.protected_aus()),
        clean_cache_disk_coupling_on_aus(
            pre.cache,
            pre.disk,
            pre.branch_projection_aus() + allocs,
        ),
        post.cache == pre.cache,
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.sync_phase == pre.sync_phase,
        post.control == pre.control,
        CachedBranchBetree::State::branch_build(
            pre.branch,
            post.branch,
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
            idx,
            post_branch,
            crate::implementation::
                CachedBranchBetree_v::
                    CachedAllocationBranchEvent::AllocFill{},
        ),
    ensures
        CrashAwareCachingDiskBranchBetree::State::next(
            pre.i(),
            post.i(),
            CrashAwareCachingDiskBranchBetree::Label::
                Ephemeral {
                    op: CachingDiskBranchBetree::Label::
                        InternalAlloc {
                            allocs,
                            deallocs,
                            guard_aus:
                                pre.control.protected_aus(),
                        },
                    deallocs:
                        pre.control.reclaimable(deallocs),
                },
        ),
        post.branch_projection_aus()
            == (pre.branch_projection_aus() + allocs)
                - pre.control.reclaimable(deallocs),
        pre.control.reclaimable(deallocs)
            <= pre.branch_projection_aus(),
        cached_branch_alloc_aus(post.branch.wip_branches)
            == cached_branch_alloc_aus(
                pre.branch.wip_branches,
            ) + allocs,
        inv(post),
{
    let src = pre.i();
    let dst = post.i();
    let component_pre = pre.known_branch_i();
    let component_post = post.known_branch_i();
    let component_lbl =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus: pre.control.protected_aus(),
        };
    let target_lbl =
        CrashAwareCachingDiskBranchBetree::Label::
            Ephemeral {
                op: component_lbl,
                deallocs:
                    pre.control.reclaimable(deallocs),
            };

    reveal(CachedBranchBetree::State::branch_build);
    reveal(crate::implementation::
        CachedBranchBetree_v::
            CachedAllocationBranch::build_next);
    assert(deallocs.is_empty());
    assert(0 <= idx < pre.branch.wip_branches.len());
    assert(post.branch.wip_branches
        == pre.branch.wip_branches.update(
            idx,
            post_branch,
        ));
    assert(post_branch
        == pre.branch.wip_branches[idx]
            .fill_aus(allocs));
    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(src.ephemeral is Known);
    assert(component_pre.refinement_inv());
    assert(component_pre.i().inv());
    assert(component_pre.i().wip_branches[idx]
        .mini_allocator
        == pre.branch.wip_branches[idx]
            .mini_allocator) by {
        reveal(CachingDiskBranchBetree::State::wip_branches_i);
        reveal(CachingDiskBranchBetree::State::wip_branch_i);
    }
    assert(component_pre.i().wip_branches[idx].inv());
    assert(pre.branch.wip_branches[idx]
        .mini_allocator.wf());
    crate::implementation::AllocationBranchStack_v::
        mini_allocator_add_aus_preserves_all_aus(
            pre.branch.wip_branches[idx]
                .mini_allocator,
            allocs,
        );
    assert(post_branch.mini_allocator.all_aus()
        == pre.branch.wip_branches[idx]
            .mini_allocator.all_aus() + allocs);

    let pre_wip_aus = crate::implementation::
        CachedBranchBetree_v::cached_branch_alloc_aus(
            pre.branch.wip_branches,
        );
    let post_wip_aus = crate::implementation::
        CachedBranchBetree_v::cached_branch_alloc_aus(
            post.branch.wip_branches,
        );
    crate::implementation::CachedBranchBetree_v::
        cached_branch_alloc_aus_update_subset(
            pre.branch.wip_branches,
            idx,
            post_branch,
            allocs,
        );
    assert(post_wip_aus == pre_wip_aus + allocs) by {
        assert forall |au: AU|
            #[trigger] (pre_wip_aus + allocs)
                .contains(au)
            implies post_wip_aus.contains(au)
        by {
            let updated_sets = Seq::new(
                post.branch.wip_branches.len(),
                |i: int| post.branch.wip_branches[i]
                    .mini_allocator.all_aus(),
            );
            if allocs.contains(au) {
                assert(updated_sets[idx].contains(au));
                crate::betree::Utils_v::
                    lemma_set_subset_of_union_seq_of_sets(
                        updated_sets,
                        au,
                    );
            } else {
                let source_idx = crate::implementation::
                    CachedBranchBetree_v::
                        cached_branch_alloc_aus_contains(
                            pre.branch.wip_branches,
                            au,
                        );
                if source_idx == idx {
                    assert(updated_sets[idx].contains(au));
                } else {
                    assert(post.branch.wip_branches[source_idx]
                        == pre.branch.wip_branches[source_idx]);
                    assert(updated_sets[source_idx]
                        .contains(au));
                }
                crate::betree::Utils_v::
                    lemma_set_subset_of_union_seq_of_sets(
                        updated_sets,
                        au,
                    );
            }
        }
    }
    assert(post.branch.owned_aus()
        == pre.branch.owned_aus() + allocs) by {
        reveal(CachedBranchBetree::State::owned_aus);
    }
    assert(post.branch_projection_aus()
        == pre.branch_projection_aus() + allocs) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_projection_aus);
    }
    projected_disk_extend_for_alloc(
        pre.cache,
        pre.disk,
        pre.branch_projection_aus(),
        allocs,
    );
    assert(disk_extend_for_alloc(
        component_pre.disk,
        component_post.disk,
        allocs,
    ));

    assert(CachingDiskBranchBetree::State::branch_fill(
        component_pre,
        component_post,
        component_lbl,
        post.branch,
        component_post.disk,
        idx,
        post_branch,
    )) by {
        reveal(CachingDiskBranchBetree::State::branch_fill);
    }
    assert(CachingDiskBranchBetree::State::next_by(
        component_pre,
        component_post,
        component_lbl,
        CachingDiskBranchBetree::Step::branch_fill(
            post.branch,
            component_post.disk,
            idx,
            post_branch,
        ),
    )) by {
        reveal(CachingDiskBranchBetree::State::next_by);
    }
    reveal(CachingDiskBranchBetree::State::next);

    assert(dst.ephemeral is Known);
    assert(src.ephemeral->persistent_aus
        == dst.ephemeral->persistent_aus);
    assert(src.frozen == dst.frozen);
    assert(src.prepared == dst.prepared) by {
        reveal(UnifiedCacheBranchBetreeSource::
            prepared_branch_image_i);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                CachingDiskBranchBetreeImage::
                    materialized_from_persistent);
    }
    assert(pre.control.protected_aus()
        == crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                protected_aus(
                    src.ephemeral->persistent_aus,
                    src.frozen,
                ));
    assert(pre.control.reclaimable(deallocs)
        == deallocs
            - crate::implementation::
                CrashAwareCachingDiskBranchBetree_v::
                    protected_aus(
                        src.ephemeral->persistent_aus,
                        src.frozen,
                    ));
    assert(CrashAwareCachingDiskBranchBetree::State::
        ephemeral_step(
            src,
            dst,
            target_lbl,
            component_post,
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            ephemeral_step);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_guard_aus);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBranchBetree::Step::
            ephemeral_step(component_post),
    )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    src.next_refines(dst, target_lbl);

    reveal(UnifiedCacheBranchBetreeSource::inv);
    assert(post.control_wf());
    assert(post.i().refinement_inv());
    assert(post.inv());
}

pub proof fn branch_build_refines(
    pre: UnifiedCacheBranchBetreeSource,
    post: UnifiedCacheBranchBetreeSource,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    idx: int,
    post_branch: CachedAllocationBranch,
    event: BranchBuildEvent,
    access: PageAccess,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        allocs.disjoint(pre.control.protected_aus()),
        clean_cache_disk_coupling_on_aus(
            pre.cache,
            pre.disk,
            pre.branch_projection_aus() + allocs,
        ),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.sync_phase == pre.sync_phase,
        post.control == pre.control,
        access.only_branch(),
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        CachedBranchBetree::State::branch_build(
            pre.branch,
            post.branch,
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
            idx,
            post_branch,
            event.cached_event(access),
        ),
    ensures
        CrashAwareCachingDiskBranchBetree::State::next(
            pre.i(),
            post.i(),
            CrashAwareCachingDiskBranchBetree::Label::
                Ephemeral {
                    op: CachingDiskBranchBetree::Label::
                        InternalAlloc {
                            allocs,
                            deallocs,
                            guard_aus:
                                pre.control.protected_aus(),
                        },
                    deallocs:
                        pre.control.reclaimable(deallocs),
                },
        ),
        post.branch_projection_aus()
            == (pre.branch_projection_aus() + allocs)
                - pre.control.reclaimable(deallocs),
        pre.control.reclaimable(deallocs)
            <= pre.branch_projection_aus(),
        access.writes().dom()
            <= addresses_in_aus(
                pre.branch_projection_aus() + allocs,
            ),
        access.writes().dom()
            <= addresses_in_aus(
                pre.branch.wip_branches[idx]
                    .mini_allocator.all_aus(),
            ),
        cached_branch_alloc_aus(post.branch.wip_branches)
            <= cached_branch_alloc_aus(
                pre.branch.wip_branches,
            ),
        access.writes().dom()
            <= Set::new(|addr: Address| addr.wf()),
        inv(post),
{
    let src = pre.i();
    let dst = post.i();
    let component_pre = pre.known_branch_i();
    let guard = pre.control.protected_aus();
    let reclaimed =
        pre.control.reclaimable(deallocs);
    let tight =
        projected_branch_build_access(pre, access);
    let expected_aus =
        (pre.branch_projection_aus() + allocs)
            - reclaimed;
    let candidate_post =
        CachingDiskBranchBetree::State {
            betree: post.branch,
            disk: adapter_caching_disk_i(
                post.cache,
                post.disk,
                expected_aus,
            ),
        };
    let component_lbl =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus: guard,
        };
    let target_lbl =
        CrashAwareCachingDiskBranchBetree::Label::
            Ephemeral {
                op: component_lbl,
                deallocs: reclaimed,
            };

    branch_build_access_on_projection(
        pre,
        post.cache,
        idx,
        post_branch,
        event,
        access,
        allocs,
        deallocs,
    );
    cache_access_subreads(
        pre.cache,
        post.cache,
        access.reads(),
        access.writes(),
        tight.reads(),
    );
    assert(Cache::State::next(
        pre.cache,
        post.cache,
        Cache::Label::Access {
            reads: tight.reads(),
            writes: tight.writes(),
        },
    ));
    assert(tight.reads().dom()
        <= addresses_in_aus(
            pre.branch_projection_aus() + allocs,
        ));
    assert(tight.writes().dom()
        <= addresses_in_aus(
            pre.branch_projection_aus() + allocs,
        ));
    assert(expected_aus
        == (pre.branch_projection_aus() + allocs)
            - (deallocs - guard)) by {
        reveal(AtomicBranchBetreeControl::reclaimable);
    }
    projected_disk_access_for_alloc(
        pre.cache,
        post.cache,
        pre.disk,
        pre.branch_projection_aus(),
        expected_aus,
        allocs,
        deallocs,
        guard,
        tight.reads(),
        tight.writes(),
    );
    assert(disk_access_for_alloc(
        component_pre.disk,
        candidate_post.disk,
        allocs,
        deallocs,
        guard,
        tight.reads(),
        tight.writes(),
    ));
    assert(CachingDiskBranchBetree::State::branch_build(
        component_pre,
        candidate_post,
        component_lbl,
        post.branch,
        candidate_post.disk,
        idx,
        post_branch,
        event,
        tight,
    )) by {
        reveal(CachingDiskBranchBetree::State::branch_build);
    }
    assert(CachingDiskBranchBetree::State::next_by(
        component_pre,
        candidate_post,
        component_lbl,
        CachingDiskBranchBetree::Step::branch_build(
            post.branch,
            candidate_post.disk,
            idx,
            post_branch,
            event,
            tight,
        ),
    )) by {
        reveal(CachingDiskBranchBetree::State::next_by);
    }
    reveal(CachingDiskBranchBetree::State::next);
    CachingDiskBranchBetree::State::next_refines(
        component_pre,
        candidate_post,
        component_lbl,
    );
    branch_build_owned_aus_effect(
        pre,
        candidate_post,
        allocs,
        deallocs,
        idx,
        post_branch,
        event,
        tight,
    );
    assert(candidate_post.betree == post.branch);
    assert(cached_branch_alloc_aus(
        candidate_post.betree.wip_branches,
    ) == cached_branch_alloc_aus(
        pre.branch.wip_branches,
    ) - deallocs);
    assert(cached_branch_alloc_aus(
        post.branch.wip_branches,
    ) == cached_branch_alloc_aus(
        pre.branch.wip_branches,
    ) - deallocs);
    assert(cached_branch_alloc_aus(
        post.branch.wip_branches,
    ) <= cached_branch_alloc_aus(
        pre.branch.wip_branches,
    ));

    assert(post.branch_projection_aus()
        == expected_aus) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_projection_aus);
        reveal(AtomicBranchBetreeControl::
            protected_aus);
        reveal(AtomicBranchBetreeControl::
            reclaimable);
        assert forall |au: AU|
            #[trigger] post.branch_projection_aus()
                .contains(au)
            <==> expected_aus.contains(au)
        by {
        }
    }
    crate::implementation::
        CachingDiskAdapterRefinement_v::
            caching_disk_i_equal_by_aus_ext(
                post.cache,
                post.disk,
                post.branch_projection_aus(),
                expected_aus,
            );
    let component_post = post.known_branch_i();
    assert(component_post == candidate_post);
    assert(CachingDiskBranchBetree::State::next(
        component_pre,
        component_post,
        component_lbl,
    ));

    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(src.ephemeral->persistent_aus
        == dst.ephemeral->persistent_aus);
    assert(src.frozen == dst.frozen);
    assert(src.prepared == dst.prepared) by {
        reveal(UnifiedCacheBranchBetreeSource::
            prepared_branch_image_i);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                CachingDiskBranchBetreeImage::
                    materialized_from_persistent);
    }
    assert(guard
        == crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                protected_aus(
                    src.ephemeral->persistent_aus,
                    src.frozen,
                ));
    assert(CrashAwareCachingDiskBranchBetree::State::
        ephemeral_step(
            src,
            dst,
            target_lbl,
            component_post,
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            ephemeral_step);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_guard_aus);
        reveal(AtomicBranchBetreeControl::reclaimable);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::
        next_by(
            src,
            dst,
            target_lbl,
            CrashAwareCachingDiskBranchBetree::Step::
                ephemeral_step(component_post),
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    src.next_refines(dst, target_lbl);

    Cache::State::inv_next(
        pre.cache,
        post.cache,
        Cache::Label::Access {
            reads: access.reads(),
            writes: access.writes(),
        },
    );
    reveal(UnifiedCacheBranchBetreeSource::inv);
    assert(post.control_wf());
    assert(post.i().refinement_inv());
    assert(post.inv());
}

pub proof fn internal_noop_refines(
    pre: UnifiedCacheBranchBetreeSource,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        CachedBranchBetree::State::internal_noop(
            pre.branch,
            pre.branch,
            CachedBranchBetree::Label::Internal,
        ),
    ensures
        CrashAwareCachingDiskBranchBetree::State::next(
            pre.i(),
            pre.i(),
            CrashAwareCachingDiskBranchBetree::Label::
                Ephemeral {
                    op: CachingDiskBranchBetree::Label::Internal,
                    deallocs: Set::empty(),
                },
        ),
{
    let src = pre.i();
    let component = pre.known_branch_i();
    let component_lbl =
        CachingDiskBranchBetree::Label::Internal;
    let target_lbl =
        CrashAwareCachingDiskBranchBetree::Label::
            Ephemeral {
                op: component_lbl,
                deallocs: Set::empty(),
            };

    assert(CachingDiskBranchBetree::State::internal_noop(
        component,
        component,
        component_lbl,
    )) by {
        reveal(CachingDiskBranchBetree::State::internal_noop);
    }
    assert(CachingDiskBranchBetree::State::next_by(
        component,
        component,
        component_lbl,
        CachingDiskBranchBetree::Step::internal_noop(),
    )) by {
        reveal(CachingDiskBranchBetree::State::next_by);
    }
    reveal(CachingDiskBranchBetree::State::next);

    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(src.ephemeral is Known);
    assert(crate::implementation::
        CrashAwareCachingDiskBranchBetree_v::
            logical_deallocs(component_lbl)
        =~= Set::<AU>::empty()) by {
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs);
    }
    assert(Set::<AU>::empty()
        == crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs(component_lbl)
            - crate::implementation::
                CrashAwareCachingDiskBranchBetree_v::
                    protected_aus(
                        src.ephemeral->persistent_aus,
                        src.frozen,
                    ));
    assert(CrashAwareCachingDiskBranchBetree::State::
        ephemeral_step(
            src,
            src,
            target_lbl,
            component,
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            ephemeral_step);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::next_by(
        src,
        src,
        target_lbl,
        CrashAwareCachingDiskBranchBetree::Step::
            ephemeral_step(component),
    )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
}

pub proof fn branch_abort_refines(
    pre: UnifiedCacheBranchBetreeSource,
    post: UnifiedCacheBranchBetreeSource,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    idx: int,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        allocs.disjoint(pre.control.protected_aus()),
        post.cache == pre.cache,
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.sync_phase == pre.sync_phase,
        post.control == pre.control,
        CachedBranchBetree::State::branch_abort(
            pre.branch,
            post.branch,
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
            idx,
        ),
    ensures
        CrashAwareCachingDiskBranchBetree::State::next(
            pre.i(),
            post.i(),
            CrashAwareCachingDiskBranchBetree::Label::
                Ephemeral {
                    op: CachingDiskBranchBetree::Label::
                        InternalAlloc {
                            allocs,
                            deallocs,
                            guard_aus:
                                pre.control.protected_aus(),
                        },
                    deallocs:
                        pre.control.reclaimable(deallocs),
                },
        ),
        post.branch_projection_aus()
            == (pre.branch_projection_aus() + allocs)
                - pre.control.reclaimable(deallocs),
        pre.control.reclaimable(deallocs)
            <= pre.branch_projection_aus(),
        cached_branch_alloc_aus(post.branch.wip_branches)
            == cached_branch_alloc_aus(
                pre.branch.wip_branches,
            ) - deallocs,
        inv(post),
{
    let src = pre.i();
    let dst = post.i();
    let component_pre = pre.known_branch_i();
    let component_post = post.known_branch_i();
    let guard = pre.control.protected_aus();
    let reclaimed = deallocs - guard;
    let component_lbl =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus: guard,
        };
    let target_lbl =
        CrashAwareCachingDiskBranchBetree::Label::
            Ephemeral {
                op: component_lbl,
                deallocs: reclaimed,
            };

    reveal(CachedBranchBetree::State::branch_abort);
    assert(allocs.is_empty());
    assert(0 <= idx < pre.branch.wip_branches.len());
    assert(deallocs
        == pre.branch.wip_branches[idx]
            .mini_allocator.all_aus());
    assert(post.branch.wip_branches
        == pre.branch.wip_branches.remove(idx));
    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(src.ephemeral is Known);
    assert(component_pre.refinement_inv());
    assert(component_pre.i().inv());
    assert(component_pre.i().wip_branches_disjoint());

    let pre_wip_aus = crate::implementation::
        CachedBranchBetree_v::cached_branch_alloc_aus(
            pre.branch.wip_branches,
        );
    let post_wip_aus = crate::implementation::
        CachedBranchBetree_v::cached_branch_alloc_aus(
            post.branch.wip_branches,
        );
    crate::implementation::CachedBranchBetree_v::
        cached_branch_alloc_aus_remove_subset(
            pre.branch.wip_branches,
            idx,
        );
    assert(post_wip_aus == pre_wip_aus - deallocs) by {
        assert forall |au: AU|
            #[trigger] post_wip_aus.contains(au)
            implies !deallocs.contains(au)
        by {
            let post_idx = crate::implementation::
                CachedBranchBetree_v::
                    cached_branch_alloc_aus_contains(
                        post.branch.wip_branches,
                        au,
                    );
            let source_idx = if post_idx < idx {
                post_idx
            } else {
                post_idx + 1
            };
            assert(source_idx != idx);
            assert(pre.branch.wip_branches[source_idx]
                == post.branch.wip_branches[post_idx]);
            assert(component_pre.i().wip_branches[source_idx]
                .mini_allocator.all_aus().contains(au)) by {
                reveal(CachingDiskBranchBetree::State::
                    wip_branches_i);
                reveal(CachingDiskBranchBetree::State::
                    wip_branch_i);
            }
            assert(component_pre.i().wip_branches[idx]
                .mini_allocator.all_aus()
                == deallocs) by {
                reveal(CachingDiskBranchBetree::State::
                    wip_branches_i);
                reveal(CachingDiskBranchBetree::State::
                    wip_branch_i);
            }
        }
        assert forall |au: AU|
            #[trigger] (pre_wip_aus - deallocs)
                .contains(au)
            implies post_wip_aus.contains(au)
        by {
            let source_idx = crate::implementation::
                CachedBranchBetree_v::
                    cached_branch_alloc_aus_contains(
                        pre.branch.wip_branches,
                        au,
                    );
            assert(source_idx != idx);
            let post_idx = if source_idx < idx {
                source_idx
            } else {
                source_idx - 1
            };
            assert(0 <= post_idx
                < post.branch.wip_branches.len());
            assert(post.branch.wip_branches[post_idx]
                == pre.branch.wip_branches[source_idx]);
            let sets = Seq::new(
                post.branch.wip_branches.len(),
                |i: int| post.branch.wip_branches[i]
                    .mini_allocator.all_aus(),
            );
            assert(sets[post_idx].contains(au));
            crate::betree::Utils_v::
                lemma_set_subset_of_union_seq_of_sets(
                    sets,
                    au,
                );
        }
    }
    component_pre.wip_alloc_aus_agree();
    crate::allocation_layer::AllocationBranch_v::
        AllocationBranch::alloc_aus_ensures(
            component_pre.i().wip_branches,
            idx,
        );
    assert(deallocs
        <= component_pre.i().branch_allocator_aus()) by {
        assert(component_pre.i().wip_branches[idx]
            .mini_allocator.all_aus() == deallocs) by {
            reveal(CachingDiskBranchBetree::State::
                wip_branches_i);
            reveal(CachingDiskBranchBetree::State::
                wip_branch_i);
        }
    }
    component_pre.i().inv_branch_summary_ensures();
    assert(post.branch.owned_aus()
        == pre.branch.owned_aus() - deallocs) by {
        reveal(CachedBranchBetree::State::owned_aus);
        assert(component_pre.i().betree_aus.dom()
            .disjoint(deallocs));
        assert(summary_aus(
            component_pre.i().branch_summary,
        ).disjoint(deallocs));
        assert(component_pre.i().branch_aus.dom()
            <= summary_aus(
                component_pre.i().branch_summary,
            ));
        assert(component_pre.i().branch_aus.dom()
            .disjoint(deallocs));
    }
    assert(post.branch_projection_aus()
        == pre.branch_projection_aus() - reclaimed) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_projection_aus);
        assert forall |au: AU|
            #[trigger] post.branch_projection_aus()
                .contains(au)
            <==> (pre.branch_projection_aus()
                - reclaimed).contains(au)
        by {
        }
    }
    ownership_projection_forget_refines(
        pre.cache,
        pre.disk,
        pre.branch_projection_aus(),
        reclaimed,
    );
    assert(CachingDisk::State::next(
        component_pre.disk,
        component_post.disk,
        CachingDisk::Label::Forget{aus: reclaimed},
    ));

    assert(CachingDiskBranchBetree::State::branch_abort(
        component_pre,
        component_post,
        component_lbl,
        post.branch,
        component_post.disk,
        idx,
    )) by {
        reveal(CachingDiskBranchBetree::State::branch_abort);
    }
    assert(CachingDiskBranchBetree::State::next_by(
        component_pre,
        component_post,
        component_lbl,
        CachingDiskBranchBetree::Step::branch_abort(
            post.branch,
            component_post.disk,
            idx,
        ),
    )) by {
        reveal(CachingDiskBranchBetree::State::next_by);
    }
    reveal(CachingDiskBranchBetree::State::next);

    assert(dst.ephemeral is Known);
    assert(src.ephemeral->persistent_aus
        == dst.ephemeral->persistent_aus);
    assert(src.frozen == dst.frozen);
    assert(src.prepared == dst.prepared) by {
        reveal(UnifiedCacheBranchBetreeSource::
            prepared_branch_image_i);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                CachingDiskBranchBetreeImage::
                    materialized_from_persistent);
    }
    assert(guard
        == crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                protected_aus(
                    src.ephemeral->persistent_aus,
                    src.frozen,
                ));
    assert(CrashAwareCachingDiskBranchBetree::State::
        ephemeral_step(
            src,
            dst,
            target_lbl,
            component_post,
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            ephemeral_step);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_guard_aus);
        reveal(AtomicBranchBetreeControl::reclaimable);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBranchBetree::Step::
            ephemeral_step(component_post),
    )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    src.next_refines(dst, target_lbl);

    reveal(UnifiedCacheBranchBetreeSource::inv);
    assert(post.control_wf());
    assert(post.i().refinement_inv());
    assert(post.inv());
}

pub proof fn flush_memtable_refines(
    pre: UnifiedCacheBranchBetreeSource,
    post: UnifiedCacheBranchBetreeSource,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    branch_idx: int,
    new_root_addr: Address,
    access: PageAccess,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        allocs.disjoint(pre.control.protected_aus()),
        clean_cache_disk_coupling_on_aus(
            pre.cache,
            pre.disk,
            pre.branch_projection_aus() + allocs,
        ),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.sync_phase == pre.sync_phase,
        post.control == pre.control,
        access.wf(),
        access.branch_writes.is_empty(),
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        CachedBranchBetree::State::flush_memtable(
            pre.branch,
            post.branch,
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
            branch_idx,
            new_root_addr,
            access.loaded_betree_reads(),
            access.loaded_betree_writes(),
            access.loaded_branch_reads(),
        ),
    ensures
        CrashAwareCachingDiskBranchBetree::State::next(
            pre.i(),
            post.i(),
            CrashAwareCachingDiskBranchBetree::Label::
                Ephemeral {
                    op: CachingDiskBranchBetree::Label::
                        InternalAlloc {
                            allocs,
                            deallocs,
                            guard_aus:
                                pre.control.protected_aus(),
                        },
                    deallocs:
                        pre.control.reclaimable(deallocs),
                },
        ),
        post.branch_projection_aus()
            == (pre.branch_projection_aus() + allocs)
                - pre.control.reclaimable(deallocs),
        pre.control.reclaimable(deallocs)
            <= pre.branch_projection_aus(),
        access.writes().dom()
            <= addresses_in_aus(
                pre.branch_projection_aus() + allocs,
            ),
        access.writes().dom()
            <= addresses_in_aus(allocs),
        cached_branch_alloc_aus(post.branch.wip_branches)
            <= cached_branch_alloc_aus(
                pre.branch.wip_branches,
            ),
        access.writes().dom()
            <= Set::new(|addr: Address| addr.wf()),
        inv(post),
{
    let src = pre.i();
    let dst = post.i();
    let component_pre = pre.known_branch_i();
    let guard = pre.control.protected_aus();
    let forgotten = deallocs - guard;
    let expected_aus =
        (pre.branch_projection_aus() + allocs)
            - forgotten;
    let candidate_post =
        CachingDiskBranchBetree::State {
            betree: post.branch,
            disk: adapter_caching_disk_i(
                post.cache,
                post.disk,
                expected_aus,
            ),
        };
    let cached_branch =
        pre.branch.wip_branches[branch_idx];
    let branch_root =
        cached_branch.sealed_root().unwrap();
    let branch_owned =
        cached_branch.mini_allocator.all_aus();
    let old_root_addrs = if pre.branch.root is Some {
        set![pre.branch.root.unwrap()]
    } else {
        Set::empty()
    };
    let tight_betree_reads =
        access.betree_reads.restrict(old_root_addrs);
    let tight_branch_reads =
        access.branch_reads.restrict(
            addresses_in_aus(branch_owned),
        );
    let tight_access = PageAccess {
        betree_reads: tight_betree_reads,
        branch_reads: tight_branch_reads,
        betree_writes: access.betree_writes,
        branch_writes: Map::empty(),
    };
    let component_lbl =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus: guard,
        };
    let target_lbl =
        CrashAwareCachingDiskBranchBetree::Label::
            Ephemeral {
                op: component_lbl,
                deallocs:
                    pre.control.reclaimable(deallocs),
            };

    reveal(CachedBranchBetree::State::flush_memtable);
    assert(0 <= branch_idx
        < pre.branch.wip_branches.len());
    assert(cached_branch.sealed);
    assert(cached_branch.sealed_root() is Some);
    assert(allocs == set![new_root_addr.au]);
    assert(access.loaded_betree_writes()
        == crate::implementation::
            CachedBranchBetree_v::
                flush_memtable_writes(
                    pre.branch.root,
                    branch_root,
                    new_root_addr,
                    access.loaded_betree_reads(),
                ));
    assert(access.loaded_betree_writes().dom()
        == set![new_root_addr]);
    assert(access.loaded_betree_writes().dom()
        == access.betree_writes.dom());
    assert(access.betree_writes.dom()
        == set![new_root_addr]);
    assert(tight_access.wf());
    assert(tight_access.branch_writes.is_empty());
    assert(tight_access.writes() == access.writes());
    assert(tight_access.loaded_betree_writes()
        == access.loaded_betree_writes());
    assert(tight_access.loaded_branch_reads()
        == access.loaded_branch_reads().restrict(
            addresses_in_aus(branch_owned),
        ));

    assert(branch_owned
        <= pre.branch_projection_aus()) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_projection_aus);
        reveal(CachedBranchBetree::State::owned_aus);
        pre.known_branch_i().wip_alloc_aus_agree();
        crate::allocation_layer::AllocationBranch_v::
            AllocationBranch::alloc_aus_ensures(
                pre.known_branch_i().i().wip_branches,
                branch_idx,
            );
        assert(pre.known_branch_i().i()
            .wip_branches[branch_idx].mini_allocator
            == cached_branch.mini_allocator) by {
            reveal(CachingDiskBranchBetree::State::
                wip_branches_i);
            reveal(CachingDiskBranchBetree::State::
                wip_branch_i);
        }
    }
    assert(tight_branch_reads.dom()
        <= addresses_in_aus(
            pre.branch_projection_aus(),
        ));

    if pre.branch.root is Some {
        let old_root = pre.branch.root.unwrap();
        assert(access.betree_reads.contains_key(
            old_root,
        ));
        reveal(UnifiedCacheBranchBetreeSource::
            ephemeral_branch_i);
        assert(src.ephemeral is Known);
        assert(component_pre.refinement_inv());
        component_pre.linked_i_is_tight_candidate();
        component_pre.linked_i_tight_tree_facts();
        assert(component_pre.linked_i().root
            == Some(old_root));
        assert(component_pre.linked_i().dv.entries
            .contains_key(old_root));
        assert(addrs_closed(
            component_pre.linked_i().dv.entries.dom(),
            pre.branch.betree_aus.dom(),
        ));
        assert(pre.branch.betree_aus.dom()
            .contains(old_root.au));
        reveal(UnifiedCacheBranchBetreeSource::
            branch_projection_aus);
        reveal(CachedBranchBetree::State::owned_aus);
        assert(pre.branch_projection_aus()
            .contains(old_root.au));
    }
    assert(tight_betree_reads.dom()
        <= addresses_in_aus(
            pre.branch_projection_aus(),
        ));
    assert(tight_access.reads().dom()
        <= addresses_in_aus(
            pre.branch_projection_aus(),
        ));
    assert(tight_access.writes().dom()
        <= addresses_in_aus(allocs));
    assert(tight_access.reads().dom()
        <= addresses_in_aus(
            pre.branch_projection_aus() + allocs,
        ));
    assert(tight_access.writes().dom()
        <= addresses_in_aus(
            pre.branch_projection_aus() + allocs,
        ));
    assert(tight_access.reads()
        <= access.reads()) by {
        assert forall |addr: Address|
            #[trigger] tight_access.reads()
                .contains_key(addr)
            implies {
                &&& access.reads().contains_key(addr)
                &&& tight_access.reads()[addr]
                    == access.reads()[addr]
            }
        by {
            if tight_betree_reads.contains_key(addr) {
                assert(!tight_branch_reads
                    .contains_key(addr));
                assert(access.betree_reads
                    .contains_key(addr));
                assert(!access.branch_reads
                    .contains_key(addr));
            } else {
                assert(tight_branch_reads
                    .contains_key(addr));
                assert(access.branch_reads
                    .contains_key(addr));
                assert(!access.betree_reads
                    .contains_key(addr));
            }
        }
    }
    cache_access_subreads(
        pre.cache,
        post.cache,
        access.reads(),
        access.writes(),
        tight_access.reads(),
    );
    assert(Cache::State::next(
        pre.cache,
        post.cache,
        Cache::Label::Access {
            reads: tight_access.reads(),
            writes: tight_access.writes(),
        },
    ));
    projected_disk_access_for_alloc(
        pre.cache,
        post.cache,
        pre.disk,
        pre.branch_projection_aus(),
        expected_aus,
        allocs,
        deallocs,
        guard,
        tight_access.reads(),
        tight_access.writes(),
    );
    assert(disk_access_for_alloc(
        component_pre.disk,
        candidate_post.disk,
        allocs,
        deallocs,
        guard,
        tight_access.reads(),
        tight_access.writes(),
    ));

    assert(crate::implementation::
        CachedBranchBetree_v::valid_loaded_sealed_branch(
            branch_root,
            cached_branch.summary(),
            access.loaded_branch_reads(),
        ));
    assert(tight_access.loaded_branch_reads()
        .restrict(addresses_in_aus(
            cached_branch.summary(),
        ))
        == access.loaded_branch_reads()
            .restrict(addresses_in_aus(
                cached_branch.summary(),
            ))) by {
        assert_maps_equal!(
            tight_access.loaded_branch_reads()
                .restrict(addresses_in_aus(
                    cached_branch.summary(),
                )),
            access.loaded_branch_reads()
                .restrict(addresses_in_aus(
                    cached_branch.summary(),
                )),
            addr => {}
        );
    }
    assert(crate::implementation::
        CachedBranchBetree_v::valid_loaded_sealed_branch(
            branch_root,
            cached_branch.summary(),
            tight_access.loaded_branch_reads(),
        )) by {
        reveal(crate::implementation::
            CachedBranchBetree_v::
                valid_loaded_sealed_branch);
    }
    assert(crate::implementation::
        CachedBranchBetree_v::loaded_sealed_branch(
            branch_root,
            tight_access.loaded_branch_reads().restrict(
                addresses_in_aus(
                    cached_branch.summary(),
                ),
            ),
        ).i().i() == pre.branch.memtable.buffer) by {
        assert(tight_access.loaded_branch_reads()
            .restrict(addresses_in_aus(
                cached_branch.summary(),
            ))
            == access.loaded_branch_reads()
                .restrict(addresses_in_aus(
                    cached_branch.summary(),
                )));
    }
    if pre.branch.root is Some {
        let old_root = pre.branch.root.unwrap();
        assert(tight_access.loaded_betree_reads()
            .contains_key(old_root));
        assert(tight_access.loaded_betree_reads()[
            old_root
        ] == access.loaded_betree_reads()[old_root]);
    }
    assert(CachedBranchBetree::State::flush_memtable(
        pre.branch,
        post.branch,
        CachedBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
        },
        branch_idx,
        new_root_addr,
        tight_access.loaded_betree_reads(),
        tight_access.loaded_betree_writes(),
        tight_access.loaded_branch_reads(),
    )) by {
        reveal(CachedBranchBetree::State::
            flush_memtable);
    }
    assert(CachingDiskBranchBetree::State::
        flush_memtable(
            component_pre,
            candidate_post,
            component_lbl,
            post.branch,
            candidate_post.disk,
            branch_idx,
            new_root_addr,
            tight_access,
        )) by {
        reveal(CachingDiskBranchBetree::State::
            flush_memtable);
    }
    assert(CachingDiskBranchBetree::State::next_by(
        component_pre,
        candidate_post,
        component_lbl,
        CachingDiskBranchBetree::Step::flush_memtable(
            post.branch,
            candidate_post.disk,
            branch_idx,
            new_root_addr,
            tight_access,
        ),
    )) by {
        reveal(CachingDiskBranchBetree::State::next_by);
    }
    reveal(CachingDiskBranchBetree::State::next);
    CachingDiskBranchBetree::State::next_refines(
        component_pre,
        candidate_post,
        component_lbl,
    );
    flush_memtable_owned_aus_effect(
        pre,
        candidate_post,
        allocs,
        deallocs,
        branch_idx,
        new_root_addr,
        tight_access.loaded_betree_reads(),
        tight_access.loaded_betree_writes(),
        tight_access.loaded_branch_reads(),
    );
    assert(candidate_post.betree == post.branch);
    assert(cached_branch_alloc_aus(
        candidate_post.betree.wip_branches,
    ) <= cached_branch_alloc_aus(
        pre.branch.wip_branches,
    ));
    assert(cached_branch_alloc_aus(
        post.branch.wip_branches,
    ) <= cached_branch_alloc_aus(
        pre.branch.wip_branches,
    ));

    assert(post.branch_projection_aus()
        == expected_aus) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_projection_aus);
        reveal(AtomicBranchBetreeControl::
            protected_aus);
        reveal(AtomicBranchBetreeControl::
            reclaimable);
        assert forall |au: AU|
            #[trigger] post.branch_projection_aus()
                .contains(au)
            <==> expected_aus.contains(au)
        by {
        }
    }
    crate::implementation::
        CachingDiskAdapterRefinement_v::
            caching_disk_i_equal_by_aus_ext(
                post.cache,
                post.disk,
                post.branch_projection_aus(),
                expected_aus,
            );
    let component_post = post.known_branch_i();
    assert(component_post == candidate_post);
    assert(CachingDiskBranchBetree::State::next(
        component_pre,
        component_post,
        component_lbl,
    ));

    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(src.ephemeral->persistent_aus
        == dst.ephemeral->persistent_aus);
    assert(src.frozen == dst.frozen);
    assert(src.prepared == dst.prepared) by {
        reveal(UnifiedCacheBranchBetreeSource::
            prepared_branch_image_i);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                CachingDiskBranchBetreeImage::
                    materialized_from_persistent);
        assert(allocs.disjoint(guard));
    }
    assert(guard
        == crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                protected_aus(
                    src.ephemeral->persistent_aus,
                    src.frozen,
                ));
    assert(CrashAwareCachingDiskBranchBetree::State::
        ephemeral_step(
            src,
            dst,
            target_lbl,
            component_post,
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            ephemeral_step);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_guard_aus);
        reveal(AtomicBranchBetreeControl::reclaimable);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::
        next_by(
            src,
            dst,
            target_lbl,
            CrashAwareCachingDiskBranchBetree::Step::
                ephemeral_step(component_post),
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    src.next_refines(dst, target_lbl);

    Cache::State::inv_next(
        pre.cache,
        post.cache,
        Cache::Label::Access {
            reads: access.reads(),
            writes: access.writes(),
        },
    );
    reveal(UnifiedCacheBranchBetreeSource::inv);
    assert(post.control_wf());
    assert(post.i().refinement_inv());
    assert(post.inv());
}

pub proof fn grow_refines(
    pre: UnifiedCacheBranchBetreeSource,
    post: UnifiedCacheBranchBetreeSource,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    new_root_addr: Address,
    access: PageAccess,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        allocs.disjoint(pre.control.protected_aus()),
        clean_cache_disk_coupling_on_aus(
            pre.cache,
            pre.disk,
            pre.branch_projection_aus() + allocs,
        ),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.sync_phase == pre.sync_phase,
        post.control == pre.control,
        access.only_betree(),
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        CachedBranchBetree::State::grow(
            pre.branch,
            post.branch,
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
            new_root_addr,
            access.loaded_betree_writes(),
        ),
    ensures
        CrashAwareCachingDiskBranchBetree::State::next(
            pre.i(),
            post.i(),
            CrashAwareCachingDiskBranchBetree::Label::
                Ephemeral {
                    op: CachingDiskBranchBetree::Label::
                        InternalAlloc {
                            allocs,
                            deallocs,
                            guard_aus:
                                pre.control.protected_aus(),
                        },
                    deallocs:
                        pre.control.reclaimable(deallocs),
                },
        ),
        post.branch_projection_aus()
            == (pre.branch_projection_aus() + allocs)
                - pre.control.reclaimable(deallocs),
        pre.control.reclaimable(deallocs)
            <= pre.branch_projection_aus(),
        access.writes().dom()
            <= addresses_in_aus(
                pre.branch_projection_aus() + allocs,
            ),
        access.writes().dom()
            <= addresses_in_aus(allocs),
        cached_branch_alloc_aus(post.branch.wip_branches)
            <= cached_branch_alloc_aus(
                pre.branch.wip_branches,
            ),
        access.writes().dom()
            <= Set::new(|addr: Address| addr.wf()),
        inv(post),
{
    let src = pre.i();
    let dst = post.i();
    let component_pre = pre.known_branch_i();
    let component_post = post.known_branch_i();
    let guard = pre.control.protected_aus();
    let component_lbl =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus: guard,
        };
    let target_lbl =
        CrashAwareCachingDiskBranchBetree::Label::
            Ephemeral {
                op: component_lbl,
                deallocs:
                    pre.control.reclaimable(deallocs),
            };
    let tight_access = PageAccess {
        betree_reads: Map::empty(),
        branch_reads: Map::empty(),
        betree_writes: access.betree_writes,
        branch_writes: Map::empty(),
    };

    reveal(CachedBranchBetree::State::grow);
    assert(allocs == set![new_root_addr.au]);
    assert(deallocs.is_empty());
    assert(post.branch.betree_aus
        == pre.branch.betree_aus.insert(
            new_root_addr.au,
        ));
    assert(post.branch.owned_aus()
        == pre.branch.owned_aus() + allocs) by {
        reveal(CachedBranchBetree::State::owned_aus);
    }
    assert(post.branch_projection_aus()
        == pre.branch_projection_aus() + allocs) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_projection_aus);
    }
    assert(access.branch_reads.is_empty());
    assert(access.branch_writes.is_empty());
    assert(tight_access.wf());
    assert(tight_access.only_betree());
    assert(tight_access.writes()
        == access.writes());
    assert(tight_access.loaded_betree_writes()
        == access.loaded_betree_writes());
    assert(tight_access.writes().dom()
        == set![new_root_addr]) by {
        assert(access.loaded_betree_writes()
            == crate::implementation::
                CachedBranchBetree_v::grow_writes(
                    pre.branch.root,
                    new_root_addr,
                ));
    }
    assert(tight_access.reads().is_empty());
    assert(tight_access.reads().dom()
        <= addresses_in_aus(
            pre.branch_projection_aus() + allocs,
        ));
    assert(tight_access.writes().dom()
        <= addresses_in_aus(
            pre.branch_projection_aus() + allocs,
        ));
    cache_access_subreads(
        pre.cache,
        post.cache,
        access.reads(),
        access.writes(),
        tight_access.reads(),
    );
    assert(Cache::State::next(
        pre.cache,
        post.cache,
        Cache::Label::Access {
            reads: tight_access.reads(),
            writes: tight_access.writes(),
        },
    )) by {
        assert(tight_access.reads()
            == Map::<Address, RawPage>::empty());
    }
    assert(post.branch_projection_aus()
        == (pre.branch_projection_aus() + allocs)
            - (deallocs - guard)) by {
        assert(deallocs.is_empty());
        assert forall |au: AU|
            #[trigger] post.branch_projection_aus()
                .contains(au)
            <==> ((pre.branch_projection_aus() + allocs)
                - (deallocs - guard)).contains(au)
        by {
        }
    }
    projected_disk_access_for_alloc(
        pre.cache,
        post.cache,
        pre.disk,
        pre.branch_projection_aus(),
        post.branch_projection_aus(),
        allocs,
        deallocs,
        guard,
        tight_access.reads(),
        tight_access.writes(),
    );
    assert(disk_access_for_alloc(
        component_pre.disk,
        component_post.disk,
        allocs,
        deallocs,
        guard,
        tight_access.reads(),
        tight_access.writes(),
    ));

    assert(CachedBranchBetree::State::grow(
        component_pre.betree,
        component_post.betree,
        CachedBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
        },
        new_root_addr,
        tight_access.loaded_betree_writes(),
    ));
    assert(CachingDiskBranchBetree::State::grow(
        component_pre,
        component_post,
        component_lbl,
        post.branch,
        component_post.disk,
        new_root_addr,
        tight_access,
    )) by {
        reveal(CachingDiskBranchBetree::State::grow);
    }
    assert(CachingDiskBranchBetree::State::next_by(
        component_pre,
        component_post,
        component_lbl,
        CachingDiskBranchBetree::Step::grow(
            post.branch,
            component_post.disk,
            new_root_addr,
            tight_access,
        ),
    )) by {
        reveal(CachingDiskBranchBetree::State::next_by);
    }
    reveal(CachingDiskBranchBetree::State::next);

    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(src.ephemeral->persistent_aus
        == dst.ephemeral->persistent_aus);
    assert(src.frozen == dst.frozen);
    assert(src.prepared == dst.prepared) by {
        reveal(UnifiedCacheBranchBetreeSource::
            prepared_branch_image_i);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                CachingDiskBranchBetreeImage::
                    materialized_from_persistent);
        assert(allocs.disjoint(guard));
    }
    assert(guard
        == crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                protected_aus(
                    src.ephemeral->persistent_aus,
                    src.frozen,
                ));
    assert(CrashAwareCachingDiskBranchBetree::State::
        ephemeral_step(
            src,
            dst,
            target_lbl,
            component_post,
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            ephemeral_step);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_guard_aus);
        reveal(AtomicBranchBetreeControl::reclaimable);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBranchBetree::Step::
            ephemeral_step(component_post),
    )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    src.next_refines(dst, target_lbl);

    Cache::State::inv_next(
        pre.cache,
        post.cache,
        Cache::Label::Access {
            reads: access.reads(),
            writes: access.writes(),
        },
    );
    reveal(UnifiedCacheBranchBetreeSource::inv);
    assert(post.control_wf());
    assert(post.i().refinement_inv());
    assert(post.inv());
}

pub proof fn split_refines(
    pre: UnifiedCacheBranchBetreeSource,
    post: UnifiedCacheBranchBetreeSource,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    path: LoadedBetreePath,
    request: SplitRequest,
    new_addrs: SplitAddrs,
    path_addrs: PathAddrs,
    access: PageAccess,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        allocs.disjoint(pre.control.protected_aus()),
        clean_cache_disk_coupling_on_aus(
            pre.cache,
            pre.disk,
            pre.branch_projection_aus() + allocs,
        ),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.sync_phase == pre.sync_phase,
        post.control == pre.control,
        access.only_betree(),
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        CachedBranchBetree::State::split(
            pre.branch,
            post.branch,
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
            path,
            request,
            new_addrs,
            path_addrs,
            access.loaded_betree_reads(),
            access.loaded_betree_writes(),
        ),
    ensures
        CrashAwareCachingDiskBranchBetree::State::next(
            pre.i(),
            post.i(),
            CrashAwareCachingDiskBranchBetree::Label::
                Ephemeral {
                    op: CachingDiskBranchBetree::Label::
                        InternalAlloc {
                            allocs,
                            deallocs,
                            guard_aus:
                                pre.control.protected_aus(),
                        },
                    deallocs:
                        pre.control.reclaimable(deallocs),
                },
        ),
        post.branch_projection_aus()
            == (pre.branch_projection_aus() + allocs)
                - pre.control.reclaimable(deallocs),
        pre.control.reclaimable(deallocs)
            <= pre.branch_projection_aus(),
        access.writes().dom()
            <= addresses_in_aus(
                pre.branch_projection_aus() + allocs,
            ),
        access.writes().dom()
            <= addresses_in_aus(allocs),
        access.writes().dom()
            <= Set::new(|addr: Address| addr.wf()),
        inv(post),
{
    let src = pre.i();
    let dst = post.i();
    let component_pre = pre.known_branch_i();
    let guard = pre.control.protected_aus();
    let forgotten = deallocs - guard;
    let expected_aus =
        (pre.branch_projection_aus() + allocs)
            - forgotten;
    let expected_disk = adapter_caching_disk_i(
        post.cache,
        post.disk,
        expected_aus,
    );
    let candidate_post =
        CachingDiskBranchBetree::State {
            betree: post.branch,
            disk: expected_disk,
        };
    let child_idx = request.get_child_idx();
    let required_addrs =
        betree_path_with_child_addrs(path, child_idx);
    let tight_reads =
        access.betree_reads.restrict(required_addrs);
    let tight_access = PageAccess {
        betree_reads: tight_reads,
        branch_reads: Map::empty(),
        betree_writes: access.betree_writes,
        branch_writes: Map::empty(),
    };
    let component_lbl =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus: guard,
        };
    let target_lbl =
        CrashAwareCachingDiskBranchBetree::Label::
            Ephemeral {
                op: component_lbl,
                deallocs: pre.control.reclaimable(
                    deallocs,
                ),
            };

    reveal(CachedBranchBetree::State::split);
    assert(path.target().node.valid_child_index(
        child_idx,
    ));
    assert(path.target().node.children[
        child_idx as int
    ] is Some);
    assert(access.betree_reads.contains_key(
        path.child_addr(child_idx),
    ));
    project_betree_path_with_child_reads(
        pre,
        post.cache,
        access,
        path,
        child_idx,
    );
    assert(tight_reads <= component_pre.disk.cache);
    assert(path.valid_for(
        component_pre.linked_i().root,
        to_betree_nodes(tight_reads),
    ));
    assert(tight_access.wf());
    assert(tight_access.only_betree());
    assert(tight_access.reads() == tight_reads);
    assert(tight_access.writes() == access.writes());
    assert(tight_access.loaded_betree_reads()
        == to_betree_nodes(tight_reads));
    assert(tight_access.loaded_betree_writes()
        == access.loaded_betree_writes());

    let replacement = split_replacement(
        path,
        to_betree_nodes(tight_reads),
        request,
        new_addrs,
    );
    assert(replacement.dom() == new_addrs.repr()) by {
        assert_maps_equal!(
            replacement,
            map![
                new_addrs.left => replacement[
                    new_addrs.left
                ],
                new_addrs.right => replacement[
                    new_addrs.right
                ],
                new_addrs.parent => replacement[
                    new_addrs.parent
                ],
            ],
            addr => {}
        );
    }
    substitute_writes_dom_subset(
        path,
        new_addrs.parent,
        replacement,
        path_addrs,
    );
    assert(tight_access.writes().dom()
        <= new_addrs.repr() + path_addrs.to_set());
    crate::disk::GenericDisk_v::to_aus_domain(
        new_addrs.repr() + path_addrs.to_set(),
    );
    assert(allocs
        == to_aus(
            new_addrs.repr() + path_addrs.to_set(),
        ));
    assert(tight_access.writes().dom()
        <= addresses_in_aus(allocs));
    assert(tight_reads.dom()
        <= addresses_in_aus(
            pre.branch_projection_aus(),
        )) by {
        assert(tight_reads <= component_pre.disk.cache);
        assert(component_pre.disk.cache.dom()
            <= addresses_in_aus(
                pre.branch_projection_aus(),
            )) by {
            reveal(UnifiedCacheBranchBetreeSource::
                branch_caching_disk_i);
            reveal(UnifiedCacheBranchBetreeSource::
                known_branch_i);
            reveal(crate::implementation::
                CachingDiskAdapterRefinement_v::
                    project_cache_pages_by_addrs);
            reveal(project_cache_pages);
        }
    }
    assert(tight_access.reads().dom()
        <= addresses_in_aus(
            pre.branch_projection_aus() + allocs,
        ));
    assert(tight_access.writes().dom()
        <= addresses_in_aus(
            pre.branch_projection_aus() + allocs,
        ));

    cache_access_subreads(
        pre.cache,
        post.cache,
        access.reads(),
        access.writes(),
        tight_access.reads(),
    );
    assert(Cache::State::next(
        pre.cache,
        post.cache,
        Cache::Label::Access {
            reads: tight_access.reads(),
            writes: tight_access.writes(),
        },
    )) by {
        assert(tight_access.reads()
            <= access.reads());
    }
    projected_disk_access_for_alloc(
        pre.cache,
        post.cache,
        pre.disk,
        pre.branch_projection_aus(),
        expected_aus,
        allocs,
        deallocs,
        guard,
        tight_access.reads(),
        tight_access.writes(),
    );
    assert(disk_access_for_alloc(
        component_pre.disk,
        candidate_post.disk,
        allocs,
        deallocs,
        guard,
        tight_access.reads(),
        tight_access.writes(),
    ));

    assert(CachedBranchBetree::State::split(
        pre.branch,
        post.branch,
        CachedBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
        },
        path,
        request,
        new_addrs,
        path_addrs,
        tight_access.loaded_betree_reads(),
        tight_access.loaded_betree_writes(),
    )) by {
        reveal(CachedBranchBetree::State::split);
        assert(tight_reads[
            path.child_addr(child_idx)
        ] == access.betree_reads[
            path.child_addr(child_idx)
        ]);
    }
    assert(CachingDiskBranchBetree::State::split(
        component_pre,
        candidate_post,
        component_lbl,
        post.branch,
        candidate_post.disk,
        path,
        request,
        new_addrs,
        path_addrs,
        tight_access,
    )) by {
        reveal(CachingDiskBranchBetree::State::split);
    }
    assert(CachingDiskBranchBetree::State::next_by(
        component_pre,
        candidate_post,
        component_lbl,
        CachingDiskBranchBetree::Step::split(
            post.branch,
            candidate_post.disk,
            path,
            request,
            new_addrs,
            path_addrs,
            tight_access,
        ),
    )) by {
        reveal(CachingDiskBranchBetree::State::next_by);
    }
    reveal(CachingDiskBranchBetree::State::next);
    CachingDiskBranchBetree::State::next_refines(
        component_pre,
        candidate_post,
        component_lbl,
    );
    split_owned_aus_effect(
        pre,
        candidate_post,
        allocs,
        deallocs,
        path,
        request,
        new_addrs,
        path_addrs,
        tight_access.loaded_betree_reads(),
        tight_access.loaded_betree_writes(),
    );

    assert(post.branch_projection_aus()
        == expected_aus) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_projection_aus);
        reveal(AtomicBranchBetreeControl::
            protected_aus);
        reveal(AtomicBranchBetreeControl::
            reclaimable);
        assert forall |au: AU|
            #[trigger] post.branch_projection_aus()
                .contains(au)
            <==> expected_aus.contains(au)
        by {
        }
    }
    crate::implementation::
        CachingDiskAdapterRefinement_v::
            caching_disk_i_equal_by_aus_ext(
                post.cache,
                post.disk,
                post.branch_projection_aus(),
                expected_aus,
            );
    let component_post = post.known_branch_i();
    assert(component_post == candidate_post);
    assert(CachingDiskBranchBetree::State::next(
        component_pre,
        component_post,
        component_lbl,
    ));

    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(src.ephemeral->persistent_aus
        == dst.ephemeral->persistent_aus);
    assert(src.frozen == dst.frozen);
    assert(src.prepared == dst.prepared) by {
        reveal(UnifiedCacheBranchBetreeSource::
            prepared_branch_image_i);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                CachingDiskBranchBetreeImage::
                    materialized_from_persistent);
        assert(allocs.disjoint(guard));
    }
    assert(guard
        == crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                protected_aus(
                    src.ephemeral->persistent_aus,
                    src.frozen,
                ));
    assert(CrashAwareCachingDiskBranchBetree::State::
        ephemeral_step(
            src,
            dst,
            target_lbl,
            component_post,
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            ephemeral_step);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_guard_aus);
        reveal(AtomicBranchBetreeControl::reclaimable);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::
        next_by(
            src,
            dst,
            target_lbl,
            CrashAwareCachingDiskBranchBetree::Step::
                ephemeral_step(component_post),
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    src.next_refines(dst, target_lbl);

    Cache::State::inv_next(
        pre.cache,
        post.cache,
        Cache::Label::Access {
            reads: access.reads(),
            writes: access.writes(),
        },
    );
    reveal(UnifiedCacheBranchBetreeSource::inv);
    assert(post.control_wf());
    assert(post.i().refinement_inv());
    assert(post.inv());
}

pub proof fn flush_refines(
    pre: UnifiedCacheBranchBetreeSource,
    post: UnifiedCacheBranchBetreeSource,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    path: LoadedBetreePath,
    child_idx: nat,
    buffer_gc: nat,
    new_addrs: TwoAddrs,
    path_addrs: PathAddrs,
    access: PageAccess,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        allocs.disjoint(pre.control.protected_aus()),
        clean_cache_disk_coupling_on_aus(
            pre.cache,
            pre.disk,
            pre.branch_projection_aus() + allocs,
        ),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.sync_phase == pre.sync_phase,
        post.control == pre.control,
        access.only_betree(),
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        CachedBranchBetree::State::flush(
            pre.branch,
            post.branch,
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
            path,
            child_idx,
            buffer_gc,
            new_addrs,
            path_addrs,
            access.loaded_betree_reads(),
            access.loaded_betree_writes(),
        ),
    ensures
        CrashAwareCachingDiskBranchBetree::State::next(
            pre.i(),
            post.i(),
            CrashAwareCachingDiskBranchBetree::Label::
                Ephemeral {
                    op: CachingDiskBranchBetree::Label::
                        InternalAlloc {
                            allocs,
                            deallocs,
                            guard_aus:
                                pre.control.protected_aus(),
                        },
                    deallocs:
                        pre.control.reclaimable(deallocs),
                },
        ),
        post.branch_projection_aus()
            == (pre.branch_projection_aus() + allocs)
                - pre.control.reclaimable(deallocs),
        pre.control.reclaimable(deallocs)
            <= pre.branch_projection_aus(),
        access.writes().dom()
            <= addresses_in_aus(
                pre.branch_projection_aus() + allocs,
            ),
        access.writes().dom()
            <= addresses_in_aus(allocs),
        access.writes().dom()
            <= Set::new(|addr: Address| addr.wf()),
        inv(post),
{
    let src = pre.i();
    let dst = post.i();
    let component_pre = pre.known_branch_i();
    let guard = pre.control.protected_aus();
    let forgotten = deallocs - guard;
    let expected_aus =
        (pre.branch_projection_aus() + allocs)
            - forgotten;
    let expected_disk = adapter_caching_disk_i(
        post.cache,
        post.disk,
        expected_aus,
    );
    let candidate_post =
        CachingDiskBranchBetree::State {
            betree: post.branch,
            disk: expected_disk,
        };
    let required_addrs =
        betree_path_with_child_addrs(path, child_idx);
    let tight_reads =
        access.betree_reads.restrict(required_addrs);
    let tight_access = PageAccess {
        betree_reads: tight_reads,
        branch_reads: Map::empty(),
        betree_writes: access.betree_writes,
        branch_writes: Map::empty(),
    };
    let component_lbl =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus: guard,
        };
    let target_lbl =
        CrashAwareCachingDiskBranchBetree::Label::
            Ephemeral {
                op: component_lbl,
                deallocs: pre.control.reclaimable(
                    deallocs,
                ),
            };

    reveal(CachedBranchBetree::State::flush);
    assert(path.target().node.valid_child_index(
        child_idx,
    ));
    assert(path.target().node.children[
        child_idx as int
    ] is Some);
    assert(access.betree_reads.contains_key(
        path.child_addr(child_idx),
    ));
    project_betree_path_with_child_reads(
        pre,
        post.cache,
        access,
        path,
        child_idx,
    );
    assert(tight_reads <= component_pre.disk.cache);
    assert(path.valid_for(
        component_pre.linked_i().root,
        to_betree_nodes(tight_reads),
    ));
    assert(tight_access.wf());
    assert(tight_access.only_betree());
    assert(tight_access.reads() == tight_reads);
    assert(tight_access.writes() == access.writes());
    assert(tight_access.loaded_betree_reads()
        == to_betree_nodes(tight_reads));
    assert(tight_access.loaded_betree_writes()
        == access.loaded_betree_writes());

    let replacement = flush_replacement(
        path,
        to_betree_nodes(tight_reads),
        child_idx,
        buffer_gc,
        new_addrs,
    );
    assert(replacement.dom() == new_addrs.repr()) by {
        assert_maps_equal!(
            replacement,
            map![
                new_addrs.addr1 => replacement[
                    new_addrs.addr1
                ],
                new_addrs.addr2 => replacement[
                    new_addrs.addr2
                ],
            ],
            addr => {}
        );
    }
    substitute_writes_dom_subset(
        path,
        new_addrs.addr1,
        replacement,
        path_addrs,
    );
    assert(tight_access.writes().dom()
        <= new_addrs.repr() + path_addrs.to_set());
    crate::disk::GenericDisk_v::to_aus_domain(
        new_addrs.repr() + path_addrs.to_set(),
    );
    assert(allocs
        == to_aus(
            new_addrs.repr() + path_addrs.to_set(),
        ));
    assert(tight_access.writes().dom()
        <= addresses_in_aus(allocs));
    assert(tight_reads.dom()
        <= addresses_in_aus(
            pre.branch_projection_aus(),
        )) by {
        assert(tight_reads <= component_pre.disk.cache);
        assert(component_pre.disk.cache.dom()
            <= addresses_in_aus(
                pre.branch_projection_aus(),
            )) by {
            reveal(UnifiedCacheBranchBetreeSource::
                branch_caching_disk_i);
            reveal(UnifiedCacheBranchBetreeSource::
                known_branch_i);
            reveal(crate::implementation::
                CachingDiskAdapterRefinement_v::
                    project_cache_pages_by_addrs);
            reveal(project_cache_pages);
        }
    }
    assert(tight_access.reads().dom()
        <= addresses_in_aus(
            pre.branch_projection_aus() + allocs,
        ));
    assert(tight_access.writes().dom()
        <= addresses_in_aus(
            pre.branch_projection_aus() + allocs,
        ));

    cache_access_subreads(
        pre.cache,
        post.cache,
        access.reads(),
        access.writes(),
        tight_access.reads(),
    );
    assert(Cache::State::next(
        pre.cache,
        post.cache,
        Cache::Label::Access {
            reads: tight_access.reads(),
            writes: tight_access.writes(),
        },
    )) by {
        assert(tight_access.reads()
            <= access.reads());
    }
    projected_disk_access_for_alloc(
        pre.cache,
        post.cache,
        pre.disk,
        pre.branch_projection_aus(),
        expected_aus,
        allocs,
        deallocs,
        guard,
        tight_access.reads(),
        tight_access.writes(),
    );
    assert(disk_access_for_alloc(
        component_pre.disk,
        candidate_post.disk,
        allocs,
        deallocs,
        guard,
        tight_access.reads(),
        tight_access.writes(),
    ));

    assert(CachedBranchBetree::State::flush(
        pre.branch,
        post.branch,
        CachedBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
        },
        path,
        child_idx,
        buffer_gc,
        new_addrs,
        path_addrs,
        tight_access.loaded_betree_reads(),
        tight_access.loaded_betree_writes(),
    )) by {
        reveal(CachedBranchBetree::State::flush);
        assert(tight_reads[
            path.child_addr(child_idx)
        ] == access.betree_reads[
            path.child_addr(child_idx)
        ]);
    }
    assert(CachingDiskBranchBetree::State::flush(
        component_pre,
        candidate_post,
        component_lbl,
        post.branch,
        candidate_post.disk,
        path,
        child_idx,
        buffer_gc,
        new_addrs,
        path_addrs,
        tight_access,
    )) by {
        reveal(CachingDiskBranchBetree::State::flush);
    }
    assert(CachingDiskBranchBetree::State::next_by(
        component_pre,
        candidate_post,
        component_lbl,
        CachingDiskBranchBetree::Step::flush(
            post.branch,
            candidate_post.disk,
            path,
            child_idx,
            buffer_gc,
            new_addrs,
            path_addrs,
            tight_access,
        ),
    )) by {
        reveal(CachingDiskBranchBetree::State::next_by);
    }
    reveal(CachingDiskBranchBetree::State::next);
    CachingDiskBranchBetree::State::next_refines(
        component_pre,
        candidate_post,
        component_lbl,
    );
    flush_owned_aus_effect(
        pre,
        candidate_post,
        allocs,
        deallocs,
        path,
        child_idx,
        buffer_gc,
        new_addrs,
        path_addrs,
        tight_access.loaded_betree_reads(),
        tight_access.loaded_betree_writes(),
    );

    assert(post.branch_projection_aus()
        == expected_aus) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_projection_aus);
        reveal(AtomicBranchBetreeControl::
            protected_aus);
        reveal(AtomicBranchBetreeControl::
            reclaimable);
        assert forall |au: AU|
            #[trigger] post.branch_projection_aus()
                .contains(au)
            <==> expected_aus.contains(au)
        by {
        }
    }
    crate::implementation::
        CachingDiskAdapterRefinement_v::
            caching_disk_i_equal_by_aus_ext(
                post.cache,
                post.disk,
                post.branch_projection_aus(),
                expected_aus,
            );
    let component_post = post.known_branch_i();
    assert(component_post == candidate_post);
    assert(CachingDiskBranchBetree::State::next(
        component_pre,
        component_post,
        component_lbl,
    ));

    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(src.ephemeral->persistent_aus
        == dst.ephemeral->persistent_aus);
    assert(src.frozen == dst.frozen);
    assert(src.prepared == dst.prepared) by {
        reveal(UnifiedCacheBranchBetreeSource::
            prepared_branch_image_i);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                CachingDiskBranchBetreeImage::
                    materialized_from_persistent);
        assert(allocs.disjoint(guard));
    }
    assert(guard
        == crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                protected_aus(
                    src.ephemeral->persistent_aus,
                    src.frozen,
                ));
    assert(CrashAwareCachingDiskBranchBetree::State::
        ephemeral_step(
            src,
            dst,
            target_lbl,
            component_post,
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            ephemeral_step);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_guard_aus);
        reveal(AtomicBranchBetreeControl::reclaimable);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::
        next_by(
            src,
            dst,
            target_lbl,
            CrashAwareCachingDiskBranchBetree::Step::
                ephemeral_step(component_post),
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    src.next_refines(dst, target_lbl);

    Cache::State::inv_next(
        pre.cache,
        post.cache,
        Cache::Label::Access {
            reads: access.reads(),
            writes: access.writes(),
        },
    );
    reveal(UnifiedCacheBranchBetreeSource::inv);
    assert(post.control_wf());
    assert(post.i().refinement_inv());
    assert(post.inv());
}

pub proof fn compact_begin_refines(
    pre: UnifiedCacheBranchBetreeSource,
    post: UnifiedCacheBranchBetreeSource,
    path: LoadedBetreePath,
    start: nat,
    end: nat,
    access: PageAccess,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.sync_phase == pre.sync_phase,
        post.control == pre.control,
        access.only_betree(),
        access.read_only(),
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        CachedBranchBetree::State::compact_begin(
            pre.branch,
            post.branch,
            CachedBranchBetree::Label::Internal,
            path,
            start,
            end,
            access.loaded_betree_reads(),
        ),
    ensures
        CrashAwareCachingDiskBranchBetree::State::next(
            pre.i(),
            post.i(),
            CrashAwareCachingDiskBranchBetree::Label::
                Ephemeral {
                    op: CachingDiskBranchBetree::Label::Internal,
                    deallocs: Set::empty(),
                },
        ),
        post.branch_projection_aus()
            == pre.branch_projection_aus(),
        inv(post),
{
    let src = pre.i();
    let dst = post.i();
    let component_pre = pre.known_branch_i();
    let component_post = post.known_branch_i();
    let linked = component_pre.linked_i();
    let owned_addrs =
        addresses_in_aus(pre.branch_projection_aus());
    let tight_reads =
        access.betree_reads.restrict(owned_addrs);
    let tight_access = PageAccess {
        betree_reads: tight_reads,
        branch_reads: Map::empty(),
        betree_writes: Map::empty(),
        branch_writes: Map::empty(),
    };
    let component_lbl =
        CachingDiskBranchBetree::Label::Internal;
    let target_lbl =
        CrashAwareCachingDiskBranchBetree::Label::
            Ephemeral {
                op: component_lbl,
                deallocs: Set::empty(),
            };

    reveal(CachedBranchBetree::State::compact_begin);
    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(src.ephemeral is Known);
    assert(component_pre.refinement_inv());
    component_pre.linked_i_is_tight_candidate();
    component_pre.linked_i_tight_tree_facts();
    assert(linked.acyclic());
    assert(linked.dv.entries
        <= to_betree_nodes(component_pre.disk.visible())) by {
        assert(linked.dv.entries
            <= component_pre.visible_betree_entries());
        assert(component_pre.visible_betree_entries()
            <= to_betree_nodes(
                component_pre.disk.visible(),
            )) by {
            assert forall |addr: Address|
                #[trigger] component_pre.visible_betree_entries()
                    .contains_key(addr)
                implies {
                    &&& to_betree_nodes(
                        component_pre.disk.visible(),
                    ).contains_key(addr)
                    &&& component_pre.visible_betree_entries()[addr]
                        == to_betree_nodes(
                            component_pre.disk.visible(),
                        )[addr]
                }
            by {
                reveal(CachingDiskBranchBetree::State::
                    visible_betree_entries);
            }
        }
        vstd::map_lib::lemma_submap_of_trans(
            linked.dv.entries,
            component_pre.visible_betree_entries(),
            to_betree_nodes(component_pre.disk.visible()),
        );
    }

    assert forall |addr: Address|
        #[trigger] tight_reads.contains_key(addr)
        implies pre.cache.valid_read(
            addr,
            tight_reads[addr],
        )
    by {
        page_access_betree_read_valid(
            pre.cache,
            post.cache,
            access,
            addr,
        );
    }
    valid_reads_in_project_cache_by_addrs(
        pre.cache,
        owned_addrs,
        tight_reads,
    );
    assert(tight_reads <= component_pre.disk.cache) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_caching_disk_i);
        reveal(UnifiedCacheBranchBetreeSource::
            known_branch_i);
        reveal(crate::implementation::
            CachingDiskAdapterRefinement_v::
                project_cache_pages_by_addrs);
        reveal(project_cache_pages);
    }
    assert(path.valid_for(
        linked.root,
        to_betree_nodes(tight_reads),
    )) by {
        assert(path.valid_for(
            linked.root,
            to_betree_nodes(access.betree_reads),
        ));
        assert(path.needed_addrs()
            <= to_betree_nodes(tight_reads).dom()) by {
            assert forall |addr: Address|
                #[trigger] path.needed_addrs().contains(addr)
                implies to_betree_nodes(tight_reads)
                    .contains_key(addr)
            by {
                betree_receipt_needed_addr_in_projection(
                    pre,
                    post.cache,
                    access,
                    linked,
                    path,
                    addr,
                );
                assert(tight_reads.contains_key(addr));
            }
        }
        assert forall |i: int| 0 <= i < path.lines.len()
            implies {
                &&& to_betree_nodes(tight_reads)
                    .contains_key(path.lines[i].addr)
                &&& #[trigger] to_betree_nodes(tight_reads)[
                    path.lines[i].addr
                ] == path.lines[i].node
            }
        by {
            let addr = path.lines[i].addr;
            assert(path.needed_addrs().contains(addr));
            betree_receipt_needed_addr_in_projection(
                pre,
                post.cache,
                access,
                linked,
                path,
                addr,
            );
            assert(tight_reads.contains_key(addr));
            assert(tight_reads[addr]
                == access.betree_reads[addr]);
            assert(to_betree_nodes(tight_reads)[addr]
                == to_betree_nodes(
                    access.betree_reads,
                )[addr]);
        }
    }
    assert(tight_access.wf());
    assert(tight_access.only_betree());
    assert(tight_access.read_only());
    assert(tight_access.reads()
        == tight_reads);
    assert(tight_access.reads()
        <= component_pre.disk.cache);
    assert(tight_access.writes().is_empty());
    assert(CachingDisk::State::access(
        component_pre.disk,
        component_pre.disk,
        CachingDisk::Label::Access {
            reads: tight_access.reads(),
            writes: tight_access.writes(),
        },
    )) by {
        reveal(CachingDisk::State::access);
        assert(component_pre.disk.cache
            .union_prefer_right(tight_access.writes())
            == component_pre.disk.cache) by {
            assert_maps_equal!(
                component_pre.disk.cache
                    .union_prefer_right(
                        tight_access.writes(),
                    ),
                component_pre.disk.cache,
                addr => {}
            );
        }
        let empty_status = crate::implementation::
            CachingDisk_v::status_map(
                tight_access.writes().dom(),
                crate::implementation::CachingDisk_v::
                    PageStatus::Dirty,
            );
        assert(empty_status.is_empty());
        assert(component_pre.disk.status
            .union_prefer_right(empty_status)
            == component_pre.disk.status) by {
            assert_maps_equal!(
                component_pre.disk.status
                    .union_prefer_right(empty_status),
                component_pre.disk.status,
                addr => {}
            );
        }
    }
    assert(CachingDisk::State::next_by(
        component_pre.disk,
        component_pre.disk,
        CachingDisk::Label::Access {
            reads: tight_access.reads(),
            writes: tight_access.writes(),
        },
        CachingDisk::Step::access(),
    )) by {
        reveal(CachingDisk::State::next_by);
    }
    reveal(CachingDisk::State::next);

    assert(CachedBranchBetree::State::compact_begin(
        component_pre.betree,
        component_post.betree,
        CachedBranchBetree::Label::Internal,
        path,
        start,
        end,
        tight_access.loaded_betree_reads(),
    )) by {
        reveal(CachedBranchBetree::State::compact_begin);
    }
    assert(post.branch.owned_aus()
        == pre.branch.owned_aus()) by {
        reveal(CachedBranchBetree::State::owned_aus);
    }
    assert(post.branch_projection_aus()
        == pre.branch_projection_aus());
    assert(access.writes()
        == Map::<Address, RawPage>::empty()) by {
        assert_maps_equal!(
            access.writes(),
            Map::<Address, RawPage>::empty(),
            addr => {}
        );
    }
    assert(Cache::State::next(
        pre.cache,
        post.cache,
        Cache::Label::Access {
            reads: access.reads(),
            writes: Map::empty(),
        },
    ));
    Cache::State::access_read_only_is_noop(
        pre.cache,
        post.cache,
        access.reads(),
    );
    assert(post.cache == pre.cache);
    assert(component_post.disk == component_pre.disk);
    assert(CachingDiskBranchBetree::State::compact_begin(
        component_pre,
        component_post,
        component_lbl,
        post.branch,
        path,
        start,
        end,
        tight_access,
    )) by {
        reveal(CachingDiskBranchBetree::State::compact_begin);
    }
    assert(CachingDiskBranchBetree::State::next_by(
        component_pre,
        component_post,
        component_lbl,
        CachingDiskBranchBetree::Step::compact_begin(
            post.branch,
            path,
            start,
            end,
            tight_access,
        ),
    )) by {
        reveal(CachingDiskBranchBetree::State::next_by);
    }
    reveal(CachingDiskBranchBetree::State::next);

    assert(dst.ephemeral is Known);
    assert(src.ephemeral->persistent_aus
        == dst.ephemeral->persistent_aus);
    assert(src.frozen == dst.frozen);
    assert(src.prepared == dst.prepared) by {
        reveal(UnifiedCacheBranchBetreeSource::
            prepared_branch_image_i);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                CachingDiskBranchBetreeImage::
                    materialized_from_persistent);
    }
    assert(crate::implementation::
        CrashAwareCachingDiskBranchBetree_v::
            logical_deallocs(component_lbl)
        =~= Set::<AU>::empty()) by {
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs);
    }
    assert(Set::<AU>::empty()
        == crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs(component_lbl)
            - crate::implementation::
                CrashAwareCachingDiskBranchBetree_v::
                    protected_aus(
                        src.ephemeral->persistent_aus,
                        src.frozen,
                    ));
    assert(CrashAwareCachingDiskBranchBetree::State::
        ephemeral_step(
            src,
            dst,
            target_lbl,
            component_post,
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            ephemeral_step);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBranchBetree::Step::
            ephemeral_step(component_post),
    )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    src.next_refines(dst, target_lbl);

    reveal(UnifiedCacheBranchBetreeSource::inv);
    assert(post.control_wf());
    assert(post.i().refinement_inv());
    assert(post.inv());
}

pub proof fn compact_abort_refines(
    pre: UnifiedCacheBranchBetreeSource,
    post: UnifiedCacheBranchBetreeSource,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    input_idx: int,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        allocs.disjoint(pre.control.protected_aus()),
        post.cache == pre.cache,
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.sync_phase == pre.sync_phase,
        post.control == pre.control,
        CachedBranchBetree::State::compact_abort(
            pre.branch,
            post.branch,
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
            input_idx,
        ),
    ensures
        CrashAwareCachingDiskBranchBetree::State::next(
            pre.i(),
            post.i(),
            CrashAwareCachingDiskBranchBetree::Label::
                Ephemeral {
                    op: CachingDiskBranchBetree::Label::
                        InternalAlloc {
                            allocs,
                            deallocs,
                            guard_aus:
                                pre.control.protected_aus(),
                        },
                    deallocs:
                        pre.control.reclaimable(deallocs),
                },
        ),
        post.branch_projection_aus()
            == (pre.branch_projection_aus() + allocs)
                - pre.control.reclaimable(deallocs),
        pre.control.reclaimable(deallocs)
            <= pre.branch_projection_aus(),
        inv(post),
{
    let src = pre.i();
    let dst = post.i();
    let component_pre = pre.known_branch_i();
    let guard = pre.control.protected_aus();
    let reclaimed =
        pre.control.reclaimable(deallocs);
    let expected_aus =
        pre.branch_projection_aus() - reclaimed;
    let candidate_post =
        CachingDiskBranchBetree::State {
            betree: post.branch,
            disk: adapter_caching_disk_i(
                post.cache,
                post.disk,
                expected_aus,
            ),
        };
    let component_lbl =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus: guard,
        };
    let target_lbl =
        CrashAwareCachingDiskBranchBetree::Label::
            Ephemeral {
                op: component_lbl,
                deallocs: reclaimed,
            };

    reveal(CachedBranchBetree::State::compact_abort);
    assert(allocs.is_empty());
    ownership_projection_forget_refines(
        pre.cache,
        pre.disk,
        pre.branch_projection_aus(),
        reclaimed,
    );
    assert(CachingDisk::State::next(
        component_pre.disk,
        candidate_post.disk,
        CachingDisk::Label::Forget{
            aus: reclaimed,
        },
    ));
    assert(CachingDiskBranchBetree::State::
        compact_abort(
            component_pre,
            candidate_post,
            component_lbl,
            post.branch,
            candidate_post.disk,
            input_idx,
        )) by {
        reveal(CachingDiskBranchBetree::State::
            compact_abort);
        reveal(AtomicBranchBetreeControl::
            reclaimable);
    }
    assert(CachingDiskBranchBetree::State::next_by(
        component_pre,
        candidate_post,
        component_lbl,
        CachingDiskBranchBetree::Step::compact_abort(
            post.branch,
            candidate_post.disk,
            input_idx,
        ),
    )) by {
        reveal(CachingDiskBranchBetree::State::next_by);
    }
    reveal(CachingDiskBranchBetree::State::next);
    CachingDiskBranchBetree::State::next_refines(
        component_pre,
        candidate_post,
        component_lbl,
    );
    compact_abort_owned_aus_effect(
        pre,
        candidate_post,
        allocs,
        deallocs,
        input_idx,
    );

    assert(post.branch_projection_aus()
        == expected_aus) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_projection_aus);
        reveal(AtomicBranchBetreeControl::
            protected_aus);
        reveal(AtomicBranchBetreeControl::
            reclaimable);
        assert forall |au: AU|
            #[trigger] post.branch_projection_aus()
                .contains(au)
            <==> expected_aus.contains(au)
        by {
        }
    }
    crate::implementation::
        CachingDiskAdapterRefinement_v::
            caching_disk_i_equal_by_aus_ext(
                post.cache,
                post.disk,
                post.branch_projection_aus(),
                expected_aus,
            );
    let component_post = post.known_branch_i();
    assert(component_post == candidate_post);
    assert(CachingDiskBranchBetree::State::next(
        component_pre,
        component_post,
        component_lbl,
    ));

    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(src.ephemeral->persistent_aus
        == dst.ephemeral->persistent_aus);
    assert(src.frozen == dst.frozen);
    assert(src.prepared == dst.prepared) by {
        reveal(UnifiedCacheBranchBetreeSource::
            prepared_branch_image_i);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                CachingDiskBranchBetreeImage::
                    materialized_from_persistent);
    }
    assert(guard
        == crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                protected_aus(
                    src.ephemeral->persistent_aus,
                    src.frozen,
                ));
    assert(CrashAwareCachingDiskBranchBetree::State::
        ephemeral_step(
            src,
            dst,
            target_lbl,
            component_post,
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            ephemeral_step);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_guard_aus);
        reveal(AtomicBranchBetreeControl::reclaimable);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::
        next_by(
            src,
            dst,
            target_lbl,
            CrashAwareCachingDiskBranchBetree::Step::
                ephemeral_step(component_post),
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    src.next_refines(dst, target_lbl);

    reveal(UnifiedCacheBranchBetreeSource::inv);
    assert(post.control_wf());
    assert(post.i().refinement_inv());
    assert(post.inv());
}

pub proof fn compact_complete_refines(
    pre: UnifiedCacheBranchBetreeSource,
    post: UnifiedCacheBranchBetreeSource,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    input_idx: int,
    branch_idx: int,
    path: LoadedBetreePath,
    start: nat,
    end: nat,
    new_node_addr: Address,
    path_addrs: PathAddrs,
    access: PageAccess,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        allocs.disjoint(pre.control.protected_aus()),
        clean_cache_disk_coupling_on_aus(
            pre.cache,
            pre.disk,
            pre.branch_projection_aus() + allocs,
        ),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.sync_phase == pre.sync_phase,
        post.control == pre.control,
        access.wf(),
        access.branch_writes.is_empty(),
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        CachedBranchBetree::State::compact_complete(
            pre.branch,
            post.branch,
            CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
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
        CrashAwareCachingDiskBranchBetree::State::next(
            pre.i(),
            post.i(),
            CrashAwareCachingDiskBranchBetree::Label::
                Ephemeral {
                    op: CachingDiskBranchBetree::Label::
                        InternalAlloc {
                            allocs,
                            deallocs,
                            guard_aus:
                                pre.control.protected_aus(),
                        },
                    deallocs:
                        pre.control.reclaimable(deallocs),
                },
        ),
        post.branch_projection_aus()
            == (pre.branch_projection_aus() + allocs)
                - pre.control.reclaimable(deallocs),
        pre.control.reclaimable(deallocs)
            <= pre.branch_projection_aus(),
        access.writes().dom()
            <= addresses_in_aus(
                pre.branch_projection_aus() + allocs,
            ),
        access.writes().dom()
            <= addresses_in_aus(allocs),
        cached_branch_alloc_aus(post.branch.wip_branches)
            <= cached_branch_alloc_aus(
                pre.branch.wip_branches,
            ),
        access.writes().dom()
            <= Set::new(|addr: Address| addr.wf()),
        inv(post),
{
    let src = pre.i();
    let dst = post.i();
    let component_pre = pre.known_branch_i();
    let guard = pre.control.protected_aus();
    let reclaimed =
        pre.control.reclaimable(deallocs);
    let tight =
        projected_compact_complete_access(pre, access);
    let expected_aus =
        (pre.branch_projection_aus() + allocs)
            - reclaimed;
    let candidate_post =
        CachingDiskBranchBetree::State {
            betree: post.branch,
            disk: adapter_caching_disk_i(
                post.cache,
                post.disk,
                expected_aus,
            ),
        };
    let component_lbl =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus: guard,
        };
    let target_lbl =
        CrashAwareCachingDiskBranchBetree::Label::
            Ephemeral {
                op: component_lbl,
                deallocs: reclaimed,
            };

    compact_complete_access_on_projection(
        pre,
        post.cache,
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
        post.branch,
    );
    cache_access_subreads(
        pre.cache,
        post.cache,
        access.reads(),
        access.writes(),
        tight.reads(),
    );
    assert(Cache::State::next(
        pre.cache,
        post.cache,
        Cache::Label::Access {
            reads: tight.reads(),
            writes: tight.writes(),
        },
    ));
    assert(expected_aus
        == (pre.branch_projection_aus() + allocs)
            - (deallocs - guard)) by {
        reveal(AtomicBranchBetreeControl::reclaimable);
    }
    projected_disk_access_for_alloc(
        pre.cache,
        post.cache,
        pre.disk,
        pre.branch_projection_aus(),
        expected_aus,
        allocs,
        deallocs,
        guard,
        tight.reads(),
        tight.writes(),
    );
    assert(disk_access_for_alloc(
        component_pre.disk,
        candidate_post.disk,
        allocs,
        deallocs,
        guard,
        tight.reads(),
        tight.writes(),
    ));
    assert(CachingDiskBranchBetree::State::
        compact_complete(
            component_pre,
            candidate_post,
            component_lbl,
            post.branch,
            candidate_post.disk,
            input_idx,
            branch_idx,
            path,
            start,
            end,
            new_node_addr,
            path_addrs,
            tight,
        )) by {
        reveal(CachingDiskBranchBetree::State::
            compact_complete);
    }
    assert(CachingDiskBranchBetree::State::next_by(
        component_pre,
        candidate_post,
        component_lbl,
        CachingDiskBranchBetree::Step::compact_complete(
            post.branch,
            candidate_post.disk,
            input_idx,
            branch_idx,
            path,
            start,
            end,
            new_node_addr,
            path_addrs,
            tight,
        ),
    )) by {
        reveal(CachingDiskBranchBetree::State::next_by);
    }
    reveal(CachingDiskBranchBetree::State::next);
    CachingDiskBranchBetree::State::next_refines(
        component_pre,
        candidate_post,
        component_lbl,
    );
    compact_complete_owned_aus_effect(
        pre,
        candidate_post,
        allocs,
        deallocs,
        input_idx,
        branch_idx,
        path,
        start,
        end,
        new_node_addr,
        path_addrs,
        tight.loaded_betree_reads(),
        tight.loaded_betree_writes(),
        tight.loaded_branch_reads(),
    );
    assert(candidate_post.betree == post.branch);
    assert(cached_branch_alloc_aus(
        candidate_post.betree.wip_branches,
    ) <= cached_branch_alloc_aus(
        pre.branch.wip_branches,
    ));
    assert(cached_branch_alloc_aus(
        post.branch.wip_branches,
    ) <= cached_branch_alloc_aus(
        pre.branch.wip_branches,
    ));

    assert(post.branch_projection_aus()
        == expected_aus) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_projection_aus);
        reveal(AtomicBranchBetreeControl::
            protected_aus);
        reveal(AtomicBranchBetreeControl::
            reclaimable);
        assert forall |au: AU|
            #[trigger] post.branch_projection_aus()
                .contains(au)
            <==> expected_aus.contains(au)
        by {
        }
    }
    crate::implementation::
        CachingDiskAdapterRefinement_v::
            caching_disk_i_equal_by_aus_ext(
                post.cache,
                post.disk,
                post.branch_projection_aus(),
                expected_aus,
            );
    let component_post = post.known_branch_i();
    assert(component_post == candidate_post);
    assert(CachingDiskBranchBetree::State::next(
        component_pre,
        component_post,
        component_lbl,
    ));

    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(src.ephemeral->persistent_aus
        == dst.ephemeral->persistent_aus);
    assert(src.frozen == dst.frozen);
    assert(src.prepared == dst.prepared) by {
        reveal(UnifiedCacheBranchBetreeSource::
            prepared_branch_image_i);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                CachingDiskBranchBetreeImage::
                    materialized_from_persistent);
        assert(allocs.disjoint(guard));
    }
    assert(guard
        == crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                protected_aus(
                    src.ephemeral->persistent_aus,
                    src.frozen,
                ));
    assert(CrashAwareCachingDiskBranchBetree::State::
        ephemeral_step(
            src,
            dst,
            target_lbl,
            component_post,
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            ephemeral_step);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_guard_aus);
        reveal(AtomicBranchBetreeControl::reclaimable);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::
        next_by(
            src,
            dst,
            target_lbl,
            CrashAwareCachingDiskBranchBetree::Step::
                ephemeral_step(component_post),
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    src.next_refines(dst, target_lbl);

    Cache::State::inv_next(
        pre.cache,
        post.cache,
        Cache::Label::Access {
            reads: access.reads(),
            writes: access.writes(),
        },
    );
    reveal(UnifiedCacheBranchBetreeSource::inv);
    assert(post.control_wf());
    assert(post.i().refinement_inv());
    assert(post.inv());
}

pub proof fn store_commit_start_refines(
    pre: UnifiedCacheBranchBetreeSource,
    post: UnifiedCacheBranchBetreeSource,
    image: AbstractSuperblockImage,
    reads: Map<Address, RawPage>,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        pre.control.metadata_loaded,
        pre.control.frozen is None,
        pre.sync_phase is None,
        pre.branch.compactors.len() == 0,
        pre.branch.wip_branches.len() == 0,
        post.branch == pre.branch,
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.control == (AtomicBranchBetreeControl {
            frozen: Some(FrozenCachingDiskBranchBetree {
                metadata:
                    betree_metadata_from_superblock(image),
                aus: pre.branch.durable_aus(),
            }),
            ..pre.control
        }),
        post.sync_phase
            == (AtomicBetreeSyncPhase::Preparing{
                image,
                journal_ready: false,
                branch_ready: false,
            }),
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access {
                reads,
                writes: Map::empty(),
            },
        ),
        CachedBranchBetree::State::freeze_as(
            pre.branch,
            pre.branch,
            CachedBranchBetree::Label::FreezeAs {
                image: FrozenBranchBetree {
                    root:
                        betree_metadata_from_superblock(
                            image,
                        ).root,
                    seq_end:
                        betree_metadata_from_superblock(
                            image,
                        ).seq_end,
                },
            },
        ),
    ensures
        CrashAwareCachingDiskBranchBetree::State::next(
            pre.i(),
            post.i(),
            CrashAwareCachingDiskBranchBetree::Label::
                CommitStart {
                    image: FrozenBranchBetree {
                        root:
                            betree_metadata_from_superblock(
                                image,
                            ).root,
                        seq_end:
                            betree_metadata_from_superblock(
                                image,
                            ).seq_end,
                    },
                },
        ),
        post.branch_projection_aus()
            =~= pre.branch_projection_aus(),
        inv(post),
{
    let src = pre.i();
    let dst = post.i();
    let metadata =
        betree_metadata_from_superblock(image);
    let frozen_image = FrozenBranchBetree {
        root: metadata.root,
        seq_end: metadata.seq_end,
    };
    let frozen = FrozenCachingDiskBranchBetree {
        metadata,
        aus: pre.branch.durable_aus(),
    };
    let component_pre = pre.known_branch_i();
    let component_lbl =
        CachingDiskBranchBetree::Label::FreezeAs {
            image: frozen_image,
        };
    let target_lbl =
        CrashAwareCachingDiskBranchBetree::Label::
            CommitStart { image: frozen_image };

    Cache::State::inv_next(
        pre.cache,
        post.cache,
        Cache::Label::Access {
            reads,
            writes: Map::empty(),
        },
    );
    assert(pre.branch.durable_aus()
        <= pre.branch.owned_aus()) by {
        reveal(CachedBranchBetree::State::durable_aus);
        reveal(CachedBranchBetree::State::owned_aus);
    }
    assert(post.branch_projection_aus()
        =~= pre.branch_projection_aus()) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_projection_aus);
        reveal(UnifiedCacheBranchBetreeSource::
            frozen_aus_i);
    }
    projected_cache_read_only_access_unchanged(
        pre.cache,
        post.cache,
        pre.branch_projection_aus(),
        reads,
    );
    assert(project_persistent(
        post.disk,
        pre.branch_projection_aus(),
    ) == project_persistent(
        pre.disk,
        pre.branch_projection_aus(),
    ));
    caching_disk_i_equal_from_raw_projection_agreement(
        post.cache,
        pre.cache,
        post.disk,
        pre.disk,
        pre.branch_projection_aus(),
    );
    crate::implementation::
        CachingDiskAdapterRefinement_v::
            caching_disk_i_equal_by_aus_ext(
                post.cache,
                post.disk,
                post.branch_projection_aus(),
                pre.branch_projection_aus(),
            );
    let component_post = post.known_branch_i();
    assert(component_post == component_pre);

    assert(CachingDiskBranchBetree::State::freeze_as(
        component_pre,
        component_pre,
        component_lbl,
    )) by {
        reveal(CachingDiskBranchBetree::State::freeze_as);
    }
    assert(CachingDiskBranchBetree::State::next_by(
        component_pre,
        component_pre,
        component_lbl,
        CachingDiskBranchBetree::Step::freeze_as(),
    )) by {
        reveal(CachingDiskBranchBetree::State::next_by);
    }
    reveal(CachingDiskBranchBetree::State::next);

    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    reveal(UnifiedCacheBranchBetreeSource::
        prepared_branch_image_i);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(src.ephemeral == dst.ephemeral);
    assert(src.frozen is None);
    assert(src.prepared is None);
    assert(dst.frozen == Some(frozen));
    assert(dst.prepared is None);
    assert(src.persistent == dst.persistent);
    assert(src.persistent.metadata.seq_end
        <= frozen_image.seq_end) by {
        reveal(UnifiedCacheBranchBetreeSource::
            control_wf);
        reveal(UnifiedCacheBranchBetreeSource::
            persistent_metadata_i);
        reveal(CachedBranchBetree::State::freeze_as);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::
        commit_start(src, dst, target_lbl)) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            commit_start);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::
        next_by(
            src,
            dst,
            target_lbl,
            CrashAwareCachingDiskBranchBetree::Step::
                commit_start(),
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    src.next_refines(dst, target_lbl);

    reveal(UnifiedCacheBranchBetreeSource::inv);
    assert(post.control_wf());
    assert(post.i().refinement_inv());
    assert(post.inv());
}

pub proof fn store_commit_prepared_refines(
    pre: UnifiedCacheBranchBetreeSource,
    post: UnifiedCacheBranchBetreeSource,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        pre.control.frozen is Some,
        pre.sync_phase is Preparing,
        pre.sync_phase.journal_ready(),
        pre.sync_phase.branch_ready(),
        post.branch == pre.branch,
        post.disk.content == pre.disk.content,
        post.disk.inv(),
        post.persistent_image == pre.persistent_image,
        post.control == pre.control,
        post.sync_phase is SuperblockWriteIssued,
        post.cache == pre.cache,
        forall |slot: crate::implementation::Cache_v::Slot|
            #[trigger] pre.cache.entries.contains_key(slot)
            && pre.cache.entries[slot] is Filled
            && pre.control.frozen.unwrap().aus.contains(
                pre.cache.entries[slot].get_addr().au,
            )
            ==> pre.cache.status_map[slot] is Clean,
    ensures
        CrashAwareCachingDiskBranchBetree::State::next(
            pre.i(),
            post.i(),
            CrashAwareCachingDiskBranchBetree::Label::
                CommitPrepared,
        ),
        post.branch_projection_aus()
            =~= pre.branch_projection_aus(),
        forall |slot: crate::implementation::Cache_v::Slot|
            #[trigger] post.cache.entries.contains_key(slot)
            && post.cache.entries[slot] is Filled
            && pre.control.frozen.unwrap().aus.contains(
                post.cache.entries[slot].get_addr().au,
            )
            ==> post.cache.status_map[slot] is Clean,
        inv(post),
{
    let src = pre.i();
    let dst = post.i();
    let frozen = pre.control.frozen.unwrap();
    let component = pre.known_branch_i();
    let target_lbl =
        CrashAwareCachingDiskBranchBetree::Label::
            CommitPrepared;

    assert(post.cache == pre.cache);
    assert(post.branch_projection_aus()
        =~= pre.branch_projection_aus()) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_projection_aus);
        reveal(UnifiedCacheBranchBetreeSource::
            frozen_aus_i);
    }
    assert(project_persistent(
        post.disk,
        pre.branch_projection_aus(),
    ) == project_persistent(
        pre.disk,
        pre.branch_projection_aus(),
    )) by {
        reveal(project_persistent);
        assert_maps_equal!(
            project_persistent(
                post.disk,
                pre.branch_projection_aus(),
            ),
            project_persistent(
                pre.disk,
                pre.branch_projection_aus(),
            ),
            addr => {}
        );
    }
    caching_disk_i_equal_from_raw_projection_agreement(
        post.cache,
        pre.cache,
        post.disk,
        pre.disk,
        pre.branch_projection_aus(),
    );
    crate::implementation::
        CachingDiskAdapterRefinement_v::
            caching_disk_i_equal_by_aus_ext(
                post.cache,
                post.disk,
                post.branch_projection_aus(),
                pre.branch_projection_aus(),
            );
    assert(post.known_branch_i() == component);

    assert(component.disk.aus_clean_or_evictable(
        frozen.aus,
    )) by {
        pre.cache.build_lookup_map_ensures();
        assert forall |addr: Address|
            #[trigger] component.disk.cache.contains_key(addr)
            && frozen.aus.contains(addr.au)
            implies {
                &&& component.disk.status.contains_key(addr)
                &&& component.disk.status[addr]
                    == PageStatus::Clean
            }
        by {
            reveal(UnifiedCacheBranchBetreeSource::
                branch_caching_disk_i);
            reveal(adapter_caching_disk_i);
            reveal(project_cache_pages);
            reveal(project_cache_status);
            reveal(filled_cache_pages);
            reveal(filled_cache_status);
            assert(filled_cache_pages(pre.cache)
                .contains_key(addr));
            assert(crate::implementation::
                CachingDiskAdapterRefinement_v::
                    cache_filled_addr(pre.cache, addr));
            let slot = pre.cache.lookup_map[addr];
            assert(pre.cache.entries.contains_key(slot));
            assert(pre.cache.entries[slot] is Filled);
            assert(pre.cache.entries[slot].get_addr() == addr);
            assert(pre.cache.status_map[slot] is Clean);
            reveal(cache_status_i);
        }
        component.disk.
            aus_clean_or_evictable_from_forall(
                frozen.aus,
            );
    }
    component.disk.
        aus_clean_or_evictable_implies_persistent_visible_agree(
            frozen.aus,
        );
    let prepared =
        CachingDiskBranchBetreeImage::
            materialized_from_persistent(
                component,
                frozen,
            );
    assert(prepared
        == CachingDiskBranchBetreeImage::
            materialized_from_visible(
                component,
                frozen,
            )) by {
        assert_maps_equal!(
            prepared.persistent,
            CachingDiskBranchBetreeImage::
                materialized_from_visible(
                    component,
                    frozen,
                ).persistent,
            addr => {}
        );
    }

    reveal(UnifiedCacheBranchBetreeSource::
        ephemeral_branch_i);
    reveal(UnifiedCacheBranchBetreeSource::
        prepared_branch_image_i);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(src.ephemeral == dst.ephemeral);
    assert(src.persistent == dst.persistent);
    assert(src.frozen == Some(frozen));
    assert(dst.frozen == src.frozen);
    assert(src.prepared is None);
    assert(dst.prepared == Some(prepared));
    assert(prepared.valid()) by {
        assert(src.refinement_inv());
        assert(src.frozen_image().valid());
    }
    assert(CrashAwareCachingDiskBranchBetree::State::
        commit_prepared(
            src,
            dst,
            target_lbl,
            prepared,
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            commit_prepared);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::
        next_by(
            src,
            dst,
            target_lbl,
            CrashAwareCachingDiskBranchBetree::Step::
                commit_prepared(prepared),
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    src.next_refines(dst, target_lbl);

    post.cache.build_lookup_map_ensures();
    assert forall |slot:
        crate::implementation::Cache_v::Slot|
        #[trigger] post.cache.entries.contains_key(slot)
        && post.cache.entries[slot] is Filled
        && pre.control.frozen.unwrap().aus.contains(
            post.cache.entries[slot].get_addr().au,
        )
        implies post.cache.status_map[slot] is Clean
    by {
        let addr = post.cache.entries[slot].get_addr();
        assert(post.cache.lookup_map.contains_key(addr));
        assert(post.cache.lookup_map[addr] == slot);
        assert(pre.cache.lookup_map.contains_key(addr));
        assert(pre.cache.lookup_map[addr] == slot);
        assert(pre.cache.status_map[slot] is Clean);
    }

    reveal(UnifiedCacheBranchBetreeSource::inv);
    assert(post.control_wf());
    assert(post.i().refinement_inv());
    assert(post.inv());
}

pub proof fn store_commit_complete_refines(
    pre: UnifiedCacheBranchBetreeSource,
    post: UnifiedCacheBranchBetreeSource,
    image: AbstractSuperblockImage,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        pre.control.frozen is Some,
        pre.sync_phase is SuperblockWriteIssued,
        post.branch == pre.branch,
        post.cache == pre.cache,
        post.disk.content == pre.disk.content,
        post.disk.inv(),
        post.persistent_image == Some(image),
        image.wf(),
        betree_metadata_from_superblock(image)
            == pre.control.frozen.unwrap().metadata,
        post.control == (AtomicBranchBetreeControl {
            metadata:
                pre.control.frozen.unwrap().metadata,
            persistent_aus:
                pre.control.frozen.unwrap().aus,
            frozen: None,
            ..pre.control
        }),
        post.sync_phase is None,
    ensures
        CrashAwareCachingDiskBranchBetree::State::next(
            pre.i(),
            post.i(),
            CrashAwareCachingDiskBranchBetree::Label::
                CommitComplete {
                    deallocs:
                        pre.control.persistent_aus
                            - pre.control.frozen.unwrap().aus
                            - pre.branch.owned_aus(),
                },
        ),
        post.branch_projection_aus()
            =~= pre.branch_projection_aus()
                .difference(
                    pre.control.persistent_aus
                        - pre.control.frozen.unwrap().aus
                        - pre.branch.owned_aus(),
                ),
        pre.control.persistent_aus
                - pre.control.frozen.unwrap().aus
                - pre.branch.owned_aus()
            <= pre.branch_projection_aus(),
        inv(post),
{
    let src = pre.i();
    let dst = post.i();
    let current = pre.known_branch_i();
    let candidate = post.known_branch_i();
    let frozen = pre.control.frozen.unwrap();
    let persistent_aus = pre.control.persistent_aus;
    let guard_aus =
        frozen.aus + pre.branch.owned_aus();
    let deallocs =
        persistent_aus - frozen.aus
            - pre.branch.owned_aus();
    let pre_aus = pre.branch_projection_aus();
    let post_aus = post.branch_projection_aus();
    let target_lbl =
        CrashAwareCachingDiskBranchBetree::Label::
            CommitComplete { deallocs };

    assert(deallocs
        =~= persistent_aus - guard_aus);
    assert(pre_aus
        =~= pre.branch.owned_aus()
            + persistent_aus + frozen.aus) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_projection_aus);
        reveal(UnifiedCacheBranchBetreeSource::
            frozen_aus_i);
    }
    assert(post_aus
        =~= pre.branch.owned_aus() + frozen.aus) by {
        reveal(UnifiedCacheBranchBetreeSource::
            branch_projection_aus);
        reveal(UnifiedCacheBranchBetreeSource::
            frozen_aus_i);
    }
    assert(pre_aus - deallocs =~= post_aus) by {
        assert forall |au: AU|
            #[trigger] (pre_aus - deallocs).contains(au)
                <==> post_aus.contains(au)
        by {
        }
    }

    ownership_projection_forget_refines(
        pre.cache,
        pre.disk,
        pre_aus,
        deallocs,
    );
    caching_disk_i_equal_from_raw_projection_agreement(
        post.cache,
        pre.cache,
        post.disk,
        pre.disk,
        post_aus,
    );
    crate::implementation::
        CachingDiskAdapterRefinement_v::
            caching_disk_i_equal_by_aus_ext(
                pre.cache,
                pre.disk,
                pre_aus - deallocs,
                post_aus,
            );
    assert(CachingDisk::State::next(
        current.disk,
        candidate.disk,
        CachingDisk::Label::Forget {
            aus: deallocs,
        },
    ));
    assert(candidate.betree == current.betree);
    assert(reclaim_guarded_aus(
        current,
        candidate,
        persistent_aus,
        guard_aus,
    )) by {
        reveal(reclaim_guarded_aus);
    }
    reclaim_guarded_aus_preserves_inv(
        current,
        candidate,
        persistent_aus,
        guard_aus,
    );

    let prepared =
        CachingDiskBranchBetreeImage::
            materialized_from_persistent(
                current,
                frozen,
            );
    reveal(UnifiedCacheBranchBetreeSource::
        persistent_branch_image_i);
    reveal(UnifiedCacheBranchBetreeSource::
        prepared_branch_image_i);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(src.frozen == Some(frozen));
    assert(src.prepared == Some(prepared));
    assert(dst.frozen is None);
    assert(dst.prepared is None);
    assert(dst.ephemeral->persistent_aus
        == frozen.aus);
    assert(dst.ephemeral->v == candidate);
    assert(dst.persistent == prepared) by {
        reveal(CachingDiskBranchBetreeImage::
            materialized_from_persistent);
        assert_maps_equal!(
            dst.persistent.persistent,
            prepared.persistent,
            addr => {
                if dst.persistent.persistent
                    .contains_key(addr)
                {
                    assert(addresses_in_aus(frozen.aus)
                        .contains(addr));
                    assert(pre_aus.contains(addr.au));
                    assert(current.disk.persistent
                        .contains_key(addr));
                }
                if prepared.persistent
                    .contains_key(addr)
                {
                    assert(addresses_in_aus(frozen.aus)
                        .contains(addr));
                    assert(pre_aus.contains(addr.au));
                    assert(post.disk.content
                        .contains_key(addr));
                }
            }
        );
    }
    assert(CrashAwareCachingDiskBranchBetree::State::
        commit_complete(
            src,
            dst,
            target_lbl,
            candidate,
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            commit_complete);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::
        next_by(
            src,
            dst,
            target_lbl,
            CrashAwareCachingDiskBranchBetree::Step::
                commit_complete(candidate),
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    src.next_refines(dst, target_lbl);

    assert(prepared.valid()) by {
        assert(src.refinement_inv());
        assert(src.prepared.unwrap().valid());
    }
    prepared.recovery_witness_valid();
    let witness = prepared.recovery_witness();
    let tree = initial_tight_tree(
        witness.initial_betree,
    );
    reveal(crate::implementation::
        CrashAwareCachingDiskBranchBetreeRefinement_v::
            RecoveredCachingDiskBranchBetreeMetadata::
                valid_for);
    reveal(initial_refinement_witness_valid);
    reveal(tight_betree_candidate);
    assert(prepared.persistent
        <= post.disk.content) by {
        assert forall |addr: Address|
            #[trigger] prepared.persistent
                .contains_key(addr)
            implies {
                &&& post.disk.content.contains_key(addr)
                &&& prepared.persistent[addr]
                    == post.disk.content[addr]
            }
        by {
            assert(dst.persistent.persistent
                .contains_key(addr));
        }
    }
    assert(tree.dv.entries
        <= to_betree_nodes(post.disk.content)) by {
        assert forall |addr: Address|
            #[trigger] tree.dv.entries
                .contains_key(addr)
            implies {
                &&& to_betree_nodes(post.disk.content)
                    .contains_key(addr)
                &&& tree.dv.entries[addr]
                    == to_betree_nodes(
                        post.disk.content,
                    )[addr]
            }
        by {
            assert(prepared.disk().visible()
                == prepared.persistent) by {
                reveal(CachingDiskBranchBetreeImage::disk);
                reveal(CachingDisk::State::visible);
                reveal(CachingDisk::State::visible_cache);
            }
            let bounded = to_betree_nodes(
                prepared.disk().visible(),
            ).restrict(addresses_in_aus(
                witness.betree_aus.dom(),
            ));
            assert(tree.dv.entries <= bounded);
            assert(bounded.contains_key(addr));
            assert(to_betree_nodes(
                prepared.disk().visible(),
            ).contains_key(addr));
            assert(prepared.disk().visible()
                .contains_key(addr));
            assert(prepared.persistent.contains_key(addr));
            assert(post.disk.content.contains_key(addr));
            assert(prepared.persistent[addr]
                == post.disk.content[addr]);
        }
    }
    assert(tight_betree_candidate(
        post.persistent_metadata_i().root,
        to_betree_nodes(post.disk.content),
        tree,
    ));
    assert(tight_betree_exists(
        post.persistent_metadata_i().root,
        to_betree_nodes(post.disk.content),
    )) by {
        reveal(tight_betree_exists);
    }

    reveal(UnifiedCacheBranchBetreeSource::inv);
    reveal(UnifiedCacheBranchBetreeSource::control_wf);
    assert(post.control_wf());
    assert(post.persistent_superblock_image_i()
        == image);
    assert(post.persistent_branch_image_i()
        == prepared);
    assert(post.branch_caching_disk_i().inv());
    assert(post.i().refinement_inv());
    assert(post.inv());
}

pub proof fn put_refines(
    pre: UnifiedCacheBranchBetreeSource,
    post: UnifiedCacheBranchBetreeSource,
    puts: crate::abstract_system::MsgHistory_v::MsgHistory,
)
    requires
        inv(pre),
        pre.control.metadata_loaded,
        post.cache == pre.cache,
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.sync_phase == pre.sync_phase,
        post.control == pre.control,
        CachedBranchBetree::State::put(
            pre.branch,
            post.branch,
            CachedBranchBetree::Label::Put{puts},
        ),
    ensures
        CrashAwareCachingDiskBranchBetree::State::next(
            unified_cache_branch_betree_i(pre),
            unified_cache_branch_betree_i(post),
            CrashAwareCachingDiskBranchBetree::Label::Ephemeral {
                op: CachingDiskBranchBetree::Label::Put{puts},
                deallocs: Set::empty(),
            },
        ),
        inv(post),
{
    let src = unified_cache_branch_betree_i(pre);
    let dst = unified_cache_branch_betree_i(post);
    let cpre = pre.known_branch_i();
    let cpost = post.known_branch_i();
    let component_lbl =
        CachingDiskBranchBetree::Label::Put{puts};
    let target_lbl =
        CrashAwareCachingDiskBranchBetree::Label::Ephemeral {
            op: component_lbl,
            deallocs: Set::empty(),
        };

    reveal(CachedBranchBetree::State::put);
    assert(post.branch.root == pre.branch.root);
    assert(post.branch.betree_aus == pre.branch.betree_aus);
    assert(post.branch.branch_aus == pre.branch.branch_aus);
    assert(post.branch.branch_summary
        == pre.branch.branch_summary);
    assert(post.branch.compactors == pre.branch.compactors);
    assert(post.branch.wip_branches
        == pre.branch.wip_branches);
    assert(post.branch.owned_aus()
        == pre.branch.owned_aus());
    assert(post.branch_projection_aus()
        =~= pre.branch_projection_aus());
    crate::implementation::
        CachingDiskAdapterRefinement_v::
            caching_disk_i_equal_by_aus_ext(
                post.cache,
                post.disk,
                post.branch_projection_aus(),
                pre.branch_projection_aus(),
            );
    assert(post.branch_caching_disk_i()
        == pre.branch_caching_disk_i());

    assert(CachingDiskBranchBetree::State::put(
        cpre,
        cpost,
        component_lbl,
        post.branch,
    )) by {
        reveal(CachingDiskBranchBetree::State::put);
    }
    assert(CachingDiskBranchBetree::State::next_by(
        cpre,
        cpost,
        component_lbl,
        CachingDiskBranchBetree::Step::put(post.branch),
    )) by {
        reveal(CachingDiskBranchBetree::State::next_by);
    }
    reveal(CachingDiskBranchBetree::State::next);

    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(crate::implementation::
        CrashAwareCachingDiskBranchBetree_v::
            logical_deallocs(component_lbl)
        =~= Set::<AU>::empty()) by {
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs);
    }
    assert(Set::<AU>::empty()
        - crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                protected_aus(
                    src.ephemeral->persistent_aus,
                    src.frozen,
                )
        =~= Set::<AU>::empty());
    assert(CrashAwareCachingDiskBranchBetree::State::
        ephemeral_step(
            src,
            dst,
            target_lbl,
            cpost,
        )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::
            ephemeral_step);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_deallocs);
    }
    assert(CrashAwareCachingDiskBranchBetree::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBranchBetree::Step::
            ephemeral_step(cpost),
    )) by {
        reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
    }
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    src.next_refines(dst, target_lbl);

    reveal(UnifiedCacheBranchBetreeSource::inv);
    pre.branch.memtable.apply_puts_end(puts);
    assert(pre.branch.memtable.seq_end
        <= post.branch.memtable.seq_end);
    assert(post.i().refinement_inv());
    assert(post.inv());
}

} // verus!
