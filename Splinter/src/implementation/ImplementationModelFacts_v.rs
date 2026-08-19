// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

// Narrow runtime certificates derived from the trusted SystemModel invariant.
// The executable coordinator consumes these contracts without opening the
// refinement stack itself.

#![allow(unused_imports)]
#![allow(unused_variables)]

use vstd::prelude::*;
use vstd::assert_maps_equal;

use crate::allocation_layer::BranchTypes_v::Summary;
use crate::disk::GenericDisk_v::{
    Address, AU, set_addrs_disjoint_aus, to_aus,
};
use crate::implementation::BetreeQueryImpl_v::cached_betree_query_valid;
use crate::implementation::BranchBetreeImpl_v::{
    compactor_owned_input_aus, compactor_views,
};
use crate::implementation::CachingDiskAdapterRefinement_v::{
    cache_filled_addr, cache_filled_page, filled_cache_pages,
    project_cache_pages, projectable_entry_in_caching_disk_i,
};
use crate::implementation::CachingDiskJournal_v::CachingDiskJournal;
use crate::implementation::CachingDisk_v::addresses_in_aus;
use crate::implementation::FracCacheImpl_v::CACHE_SIZE_RECS;
use crate::implementation::Implementation_v::*;
use crate::implementation::JournalImpl_v::{
    cache_agrees_with_raw_disk_on_domain, journal_disk_load_index_inv,
};
use crate::implementation::JournalTypes_v::to_journal_records;
use crate::implementation::UnifiedCacheBetreeRefinementProof_v::
    UnifiedCacheBetreeRefinementProof;
use crate::implementation::UnifiedCacheBetreeProgramModel_v::
    UnifiedCacheBetreeProgramModel;
use crate::implementation::UnifiedCacheBetreeSystemRefinement_v as
    UnifiedCacheBetreeSystemRefinement;
use crate::implementation::UnifiedCacheBranchBetreeRefinement_v as
    UnifiedCacheBranchBetreeRefinement;
use crate::implementation::UnifiedCacheJournalRefinement_v as
    UnifiedCacheJournalRefinement;
use crate::journal::LinkedJournal_v::DiskView;
use crate::betree::LinkedBranch_v::LinkedBranch;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::spec::AsyncDisk_t::{RawPage, DiskResponse};
use crate::implementation::AbstractSuperblock_v::abstract_superblock_raw_wf;
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::ID;
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::trusted::KVStoreTrait_t::{
    open_system_invariant_disk_response,
    open_system_invariant_disk_response_singleton,
};
use crate::trusted::RefinementObligation_t::RefinementObligation;

verus! {

impl Implementation {
    pub proof fn sync_write_response_certificate(
        &self,
        id: ID,
        token: Tracked<DiskRespShard>,
    )
        requires
            self.inv(),
            self.sync_phase is SuperblockWriteIssued,
            self.outstanding_requests@.contains_key(id),
            self.outstanding_requests@[id] is SuperblockWrite,
            token@.instance_id() == self.instance_id(),
            token@.multiset() == crate::implementation::
                MultisetMapRelation_v::multiset_map_singleton(
                    id,
                    DiskResponse::WriteResp {},
                ),
        ensures
            self.recovery_phase is ReadyForUserOperation,
            self.state().journal.journal == self.journal@,
            self.state().journal.loaded_index_aus()
                == self.journal@.status.unwrap().lsn_au_index.values(),
            self.journal.index_aus_bounded(self.disk_au_count),
            self.branch_owned_aus_bounded(),
            self.au_pool@.disjoint(self.state().journal.owned_aus()),
            self.au_pool@.disjoint(
                self.branch.control_i().persistent_aus,
            ),
            self.state().journal.owned_aus().disjoint(
                self.branch.control_i().persistent_aus,
            ),
            !self.state().journal.owned_aus().contains(
                spec_superblock_addr().au,
            ),
    {
        self.model_alignment_facts();
        let system_model =
            open_system_invariant_disk_response_singleton::<
                UnifiedCacheBetreeProgramModel,
                UnifiedCacheBetreeRefinementProof,
            >(
                self.model,
                token,
                id,
                DiskResponse::WriteResp {},
            );
        assert(UnifiedCacheBetreeSystemRefinement::refinement_inv(
            system_model,
        ));
        assert(system_model.program == self.model@.value());
        assert(system_model.program.state.sync_phase
            is SuperblockWriteIssued);
        UnifiedCacheBetreeSystemRefinement::
            active_sync_implies_client_ready(system_model);
        UnifiedCacheBetreeSystemRefinement::
            client_ready_component_facts(system_model);
        UnifiedCacheBetreeSystemRefinement::
            ready_free_aus_disjoint_journal_owned(system_model);
        UnifiedCacheBetreeSystemRefinement::
            ready_free_aus_disjoint_branch_projection(system_model);
        UnifiedCacheBetreeSystemRefinement::
            journal_branch_projections_disjoint(system_model);
        UnifiedCacheBetreeSystemRefinement::
            ready_journal_owned_aus_exclude_superblock(system_model);
        UnifiedCacheBetreeSystemRefinement::branch_source_inv(system_model);
        UnifiedCacheBetreeSystemRefinement::
            inv_implies_journal_source_inv(system_model);
        let branch_source = UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(system_model);
        let journal_source = UnifiedCacheBetreeSystemRefinement::
            unified_cache_betree_journal_source(system_model);
        assert(self.state().free_aus =~= self.au_pool@);
        assert(self.state().branch == self.branch@);
        assert(branch_source.control == self.branch.control_i());
        assert(branch_source.inv());
        assert(branch_source.control.metadata_loaded);
        UnifiedCacheBranchBetreeRefinement::
            persistent_aus_within_branch_projection(branch_source);
        assert(journal_source.journal == self.state().journal);
        assert(journal_source.inv());
        assert(journal_source.journal.ready());
        assert(journal_source.journal_projection_aus()
            == self.state().journal.owned_aus());
        assert(self.recovery_phase is ReadyForUserOperation);
        assert(self.journal.index_ready());
        self.journal.view_ensures();
        assert(self.state().journal.loaded_index_aus()
            == self.journal@.status.unwrap().lsn_au_index.values());
    }

    pub proof fn recovery_superblock_response_certificate(
        &self,
        id: ID,
        response: DiskResponse,
        token: Tracked<DiskRespShard>,
    )
        requires
            self.inv(),
            self.recovery_phase is FetchingSuperblock,
            self.state().recovery_state is AwaitingSuperblock,
            token@.instance_id() == self.instance_id(),
            token@.multiset() == crate::implementation::
                MultisetMapRelation_v::multiset_map_singleton(id, response),
        ensures
            response is ReadResp,
            abstract_superblock_raw_wf(response->data),
    {
        self.model_alignment_facts();
        let system_model =
            open_system_invariant_disk_response_singleton::<
                UnifiedCacheBetreeProgramModel,
                UnifiedCacheBetreeRefinementProof,
            >(
                self.model,
                token,
                id,
                response,
            );
        assert(UnifiedCacheBetreeRefinementProof::inv(system_model));
        assert(system_model.program == self.model@.value());
        assert(UnifiedCacheBetreeSystemRefinement::refinement_inv(
            system_model,
        ));
        assert(system_model.disk.responses.contains_key(id));
        assert(system_model.disk.responses[id] == response);
        UnifiedCacheBetreeSystemRefinement::
            recovery_superblock_response_facts(
                system_model,
                id,
                response,
            );
    }

    pub proof fn ready_journal_sync_metadata_facts(&self)
        requires
            self.inv(),
            self.recovery_phase is ReadyForUserOperation,
        ensures
            self.state().journal.persistent_seq_end
                <= self.state().branch.betree.memtable.seq_end,
            self.state().branch.control.metadata.seq_end
                == self.state().journal.journal.snapshot.boundary_lsn,
            self.persistent_journal_seq_end as nat
                <= self.branch@.betree.memtable.seq_end,
            self.branch.control.metadata.seq_end as nat
                == self.journal@.snapshot.boundary_lsn,
    {
        self.model_alignment_facts();
        let tracked empty_disk_responses: Tracked<DiskRespShard> =
            Tracked(DiskRespShard::empty(self.instance_id()));
        let model = open_system_invariant_disk_response::<
            UnifiedCacheBetreeProgramModel,
            UnifiedCacheBetreeRefinementProof,
        >(self.model, empty_disk_responses);
        assert(model.program == self.model@.value());
        assert(UnifiedCacheBetreeSystemRefinement::refinement_inv(model));
        UnifiedCacheBetreeSystemRefinement::
            ready_journal_sync_metadata_facts(model);
        assert(self.state().branch == self.branch@);
        assert(self.state().journal.journal == self.journal@);
        assert(self.state().journal.persistent_seq_end
            == self.persistent_journal_seq_end as nat);
        self.journal.view_snapshot_ensures();
    }

    pub proof fn ready_journal_owned_aus_exclude_superblock(&self)
        requires
            self.inv(),
            self.recovery_phase is ReadyForUserOperation,
        ensures
            forall |au: AU|
                #[trigger] self.journal@.status.unwrap()
                    .lsn_au_index.values().contains(au)
                ==> au != spec_superblock_addr().au,
    {
        self.model_alignment_facts();
        let tracked empty_disk_responses: Tracked<DiskRespShard> =
            Tracked(DiskRespShard::empty(self.instance_id()));
        let model = open_system_invariant_disk_response::<
            UnifiedCacheBetreeProgramModel,
            UnifiedCacheBetreeRefinementProof,
        >(self.model, empty_disk_responses);
        assert(model.program == self.model@.value());
        assert(UnifiedCacheBetreeSystemRefinement::refinement_inv(model));
        UnifiedCacheBetreeSystemRefinement::
            ready_journal_owned_aus_exclude_superblock(model);
        self.journal.view_ensures();
        assert(self.state().journal.ready());
        assert(self.state().journal.loaded_index_aus()
            == self.journal@.status.unwrap().lsn_au_index.values());
        assert(self.state().journal.loaded_index_aus()
            <= self.state().journal.owned_aus());
    }

    pub proof fn ready_journal_cache_certificate(&self)
        requires
            self.inv(),
            self.recovery_phase is ReadyForUserOperation,
        ensures self.cache@.inv(),
    {
        self.model_alignment_facts();
        let tracked empty_disk_responses: Tracked<DiskRespShard> =
            Tracked(DiskRespShard::empty(self.instance_id()));
        let model = open_system_invariant_disk_response::<
            UnifiedCacheBetreeProgramModel,
            UnifiedCacheBetreeRefinementProof,
        >(self.model, empty_disk_responses);
        let journal_source = UnifiedCacheBetreeSystemRefinement::
            unified_cache_betree_journal_source(model);
        assert(model.program == self.model@.value());
        assert(UnifiedCacheBetreeSystemRefinement::refinement_inv(model));
        UnifiedCacheBetreeSystemRefinement::inv_implies_journal_source_inv(
            model,
        );
        assert(UnifiedCacheJournalRefinement::inv(journal_source));
        assert(journal_source.inv());
        assert(journal_source.cache == self.cache@);
    }

    pub proof fn ready_query_cache_certificate(&self)
        requires
            self.inv(),
            self.recovery_phase is ReadyForUserOperation,
        ensures
            self.branch.query_cache_inv(self.cache@),
            self.branch.root is Some ==>
                self.branch.ownership.betree.active_aus().contains(
                    self.branch.root.unwrap()@.au,
                ),
            !addresses_in_aus(
                self.branch.ownership.betree.active_aus()
                    + self.branch.ownership.branches.active_summary_aus(),
            ).contains(spec_superblock_addr()),
    {
        self.model_alignment_facts();
        let tracked empty_disk_responses: Tracked<DiskRespShard> =
            Tracked(DiskRespShard::empty(self.instance_id()));
        let model = open_system_invariant_disk_response::<
            UnifiedCacheBetreeProgramModel,
            UnifiedCacheBetreeRefinementProof,
        >(self.model, empty_disk_responses);
        assert(model.program == self.model@.value());
        assert(UnifiedCacheBetreeSystemRefinement::refinement_inv(model));
        assert(model.program.state.client_ready());
        UnifiedCacheBetreeSystemRefinement::
            client_ready_component_facts(model);
        UnifiedCacheBetreeSystemRefinement::ready_branch_query_cache_inv(
            model,
            CACHE_SIZE_RECS as nat,
            CACHE_SIZE_RECS as nat,
        );
        self.branch.ownership.betree.view_domain_matches_active();
        self.branch.ownership.branches.active_summary_projection();
        UnifiedCacheBetreeSystemRefinement::
            branch_projection_excludes_superblock(model);
        let branch_source = UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(model);
        assert(model.program.state.branch.control.metadata_loaded);
        assert(model.program.state.branch.betree.owned_aus()
            <= branch_source.branch_projection_aus());
        assert(!branch_source.branch_projection_aus()
            .contains(spec_superblock_addr().au));
        assert(self.state().branch == self.branch@);
        assert(self.state().cache == self.cache@);
        assert(self.state().branch.betree == self.branch.betree_i());
        assert((self.branch.ownership.betree.active_aus()
            + self.branch.ownership.branches.active_summary_aus())
            <= self.state().branch.betree.owned_aus());
        if self.branch.root is Some {
            let key = Key(0);
            assert(cached_betree_query_valid(
                self.cache@,
                self.branch.root.unwrap()@,
                key,
                CACHE_SIZE_RECS as nat,
                CACHE_SIZE_RECS as nat,
                self.branch.ownership.betree.active_aus(),
                self.branch.ownership.branches.active_summary_map(),
                self.branch.ownership.branches.active_summary_aus(),
            ));
        }
    }

    pub proof fn ready_compaction_sources_certificate(
        &self,
        input_idx: usize,
    ) -> (sources: Seq<LinkedBranch<Summary>>)
        requires
            self.inv(),
            self.recovery_phase is ReadyForUserOperation,
            input_idx < self.branch.compactors.len(),
            self.branch.compactors@[input_idx as int].merge is None,
        ensures
            set_addrs_disjoint_aus(
                Parsedview::<Seq<Address>>::parsedv(
                    &self.branch.compactors@[input_idx as int]
                        .input_buffers,
                ).to_set(),
            ),
            ({
                let compactor =
                    self.branch.compactors@[input_idx as int];
                let selected_input_aus = compactor_owned_input_aus(
                    compactor,
                    self.branch.ownership.branches.active_summary_map(),
                );
                &&& sources.len() == compactor.input_buffers@.len()
                &&& forall |i: int| 0 <= i < sources.len() ==> {
                    let source = #[trigger] sources[i];
                    &&& source.valid_sealed_branch()
                    &&& source.tight_disk_view_with_summary()
                    &&& source.root == compactor.input_buffers@[i]@
                    &&& source.get_summary() <= selected_input_aus
                    &&& self.branch.ownership.branches
                        .active_summary_map().contains_key(source.root.au)
                    &&& source.get_summary()
                        == self.branch.ownership.branches
                            .active_summary_map()[source.root.au]
                    &&& crate::implementation::BranchScanCursorImpl_v::
                        cached_branch_scan_valid(self.cache@, source)
                }
                &&& forall |left: int, right: int, addr: Address|
                    0 <= left < sources.len()
                    && 0 <= right < sources.len()
                    && #[trigger] sources[left].disk_view.entries
                        .contains_key(addr)
                    && #[trigger] sources[right].disk_view.entries
                        .contains_key(addr)
                    ==> sources[left].disk_view.entries[addr]
                        == sources[right].disk_view.entries[addr]
                &&& forall |left: int, right: int|
                    0 <= left < sources.len()
                    && 0 <= right < sources.len()
                    && #[trigger] sources[left].root
                        == #[trigger] sources[right].root
                    ==> sources[left] == sources[right]
            }),
    {
        self.model_alignment_facts();
        let tracked empty_disk_responses: Tracked<DiskRespShard> =
            Tracked(DiskRespShard::empty(self.instance_id()));
        let model = open_system_invariant_disk_response::<
            UnifiedCacheBetreeProgramModel,
            UnifiedCacheBetreeRefinementProof,
        >(self.model, empty_disk_responses);
        assert(model.program == self.model@.value());
        assert(UnifiedCacheBetreeSystemRefinement::refinement_inv(model));
        UnifiedCacheBetreeSystemRefinement::branch_source_inv(model);
        let source = UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(model);
        assert(UnifiedCacheBranchBetreeRefinement::inv(source));
        assert(source.control.metadata_loaded);
        assert(source.branch == self.branch.betree_i());
        assert(source.cache == self.cache@);
        assert(source.branch.compactors == compactor_views(
            self.branch.compactors@,
        ));
        UnifiedCacheBranchBetreeRefinement::
            ready_compaction_sources_exist(source, input_idx as int);
        let sources = choose |sources: Seq<LinkedBranch<Summary>>| {
            let compactor = source.branch.compactors[input_idx as int];
            let roots = compactor.input_buffers.addrs;
            let selected_input_aus = crate::allocation_layer::
                AllocationBranchBetree_v::summary_aus(
                    source.branch.branch_summary.restrict(
                        to_aus(roots.to_set()),
                    ),
                );
            &&& #[trigger] sources.len() == roots.len()
            &&& forall |i: int| 0 <= i < sources.len() ==> {
                let branch = #[trigger] sources[i];
                &&& branch.valid_sealed_branch()
                &&& branch.tight_disk_view_with_summary()
                &&& branch.root == roots[i]
                &&& branch.get_summary() <= selected_input_aus
                &&& source.branch.branch_summary
                    .contains_key(branch.root.au)
                &&& branch.get_summary()
                    == source.branch.branch_summary[branch.root.au]
                &&& crate::implementation::BranchScanCursorImpl_v::
                    cached_branch_scan_valid(source.cache, branch)
            }
            &&& forall |left: int, right: int, addr: Address|
                0 <= left < sources.len()
                && 0 <= right < sources.len()
                && #[trigger] sources[left].disk_view.entries
                    .contains_key(addr)
                && #[trigger] sources[right].disk_view.entries
                    .contains_key(addr)
                ==> sources[left].disk_view.entries[addr]
                    == sources[right].disk_view.entries[addr]
            &&& forall |left: int, right: int|
                0 <= left < sources.len()
                && 0 <= right < sources.len()
                && #[trigger] sources[left].root
                    == #[trigger] sources[right].root
                ==> sources[left] == sources[right]
        };
        assert(self.branch.compactors@[input_idx as int]@
            == source.branch.compactors[input_idx as int]);
        assert(Parsedview::<Seq<Address>>::parsedv(
            &self.branch.compactors@[input_idx as int].input_buffers,
        ) == source.branch.compactors[input_idx as int]
            .input_buffers.addrs);
        assert(set_addrs_disjoint_aus(
            source.branch.compactors[input_idx as int]
                .input_buffers.addrs.to_set(),
        ));
        assert(self.branch.ownership.branches.active_summary_map()
            == source.branch.branch_summary);
        sources
    }

    pub proof fn ready_branch_allocation_certificate(&self)
        requires
            self.inv(),
            self.recovery_phase is ReadyForUserOperation,
        ensures
            self.au_pool@.disjoint(self.branch.betree_i().owned_aus()),
            self.au_pool@.disjoint(
                self.branch.control_i().protected_aus(),
            ),
            self.branch.betree_i().owned_aus().disjoint(
                self.journal.owned_aus(),
            ),
    {
        self.model_alignment_facts();
        let tracked empty_disk_responses: Tracked<DiskRespShard> =
            Tracked(DiskRespShard::empty(self.instance_id()));
        let model = open_system_invariant_disk_response::<
            UnifiedCacheBetreeProgramModel,
            UnifiedCacheBetreeRefinementProof,
        >(self.model, empty_disk_responses);
        assert(model.program == self.model@.value());
        assert(UnifiedCacheBetreeSystemRefinement::refinement_inv(model));
        assert(model.program.state.client_ready());
        UnifiedCacheBetreeSystemRefinement::
            client_ready_component_facts(model);
        assert(UnifiedCacheBetreeSystemRefinement::
            unified_cache_betree_allocation_inv(model));
        UnifiedCacheBetreeSystemRefinement::
            ready_free_aus_disjoint_branch_projection(model);
        let source = UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(model);
        let journal_source = UnifiedCacheBetreeSystemRefinement::
            unified_cache_betree_journal_source(model);
        assert(source.control.metadata_loaded);
        assert(source.branch == self.branch.betree_i());
        assert(source.control == self.branch.control_i());
        assert(journal_source.journal == self.state().journal);
        self.journal.view_ensures();
        assert(self.journal.index_ready());
        assert(self.journal@.status is Some);
        assert(self.state().journal.ready());
        assert(journal_source.journal.ready());
        assert(journal_source.journal_projection_aus()
            == journal_source.journal.owned_aus());
        assert(journal_source.journal.owned_aus()
            == self.state().journal.owned_aus());
        assert(model.program.state.free_aus.disjoint(
            source.branch_projection_aus(),
        ));
        assert(source.branch_projection_aus()
            == source.branch.owned_aus()
                + source.control.persistent_aus
                + source.frozen_aus_i());
        assert(self.state().branch == self.branch@);
        assert(self.state().free_aus =~= self.au_pool@);
        assert(self.branch.betree_i().owned_aus()
            <= source.branch_projection_aus());
        assert(self.journal.owned_aus()
            <= journal_source.journal_projection_aus()) by {
            self.journal.journal_alloc.all_aus_match();
            assert(self.journal.owned_aus()
                == self.journal.journal_alloc.i().all_aus());
            assert(self.state().journal.mini_allocator
                == self.journal.journal_alloc.i());
            assert(self.state().journal.mini_allocator.all_aus()
                <= self.state().journal.owned_aus());
        }
        UnifiedCacheBetreeSystemRefinement::
            journal_branch_projections_disjoint(model);
        assert(journal_source.journal_projection_aus().disjoint(
            source.branch_projection_aus(),
        ));
        assert(self.branch.betree_i().owned_aus().disjoint(
            self.journal.owned_aus(),
        )) by {
            assert forall |au: AU| #[trigger]
                self.branch.betree_i().owned_aus().contains(au)
                implies !self.journal.owned_aus().contains(au) by {
                assert(source.branch_projection_aus().contains(au));
            }
        }
        assert(self.branch.control_i().protected_aus()
            <= source.branch_projection_aus()) by {
            assert(self.branch.frozen_i() is Some ==> {
                self.branch.frozen_i().unwrap().aus
                    <= source.branch_projection_aus()
            });
        }
    }

    pub proof fn frozen_branch_aus_exclude_superblock(&self)
        requires
            self.inv(),
            self.recovery_phase is ReadyForUserOperation,
            self.branch.control.frozen_metadata is Some,
        ensures
            forall |au: AU|
                #[trigger] self.branch.ownership.frozen_aus().contains(au)
                ==> au != spec_superblock_addr().au,
    {
        self.model_alignment_facts();
        let tracked empty_disk_responses: Tracked<DiskRespShard> =
            Tracked(DiskRespShard::empty(self.instance_id()));
        let model = open_system_invariant_disk_response::<
            UnifiedCacheBetreeProgramModel,
            UnifiedCacheBetreeRefinementProof,
        >(self.model, empty_disk_responses);
        assert(model.program == self.model@.value());
        assert(UnifiedCacheBetreeSystemRefinement::refinement_inv(model));
        UnifiedCacheBetreeSystemRefinement::
            branch_projection_excludes_superblock(model);
        let source = UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(model);
        assert(source.control == self.branch.control_i());
        assert(source.control.frozen is Some);
        assert(source.control.frozen.unwrap().aus
            == self.branch.ownership.frozen_aus());
        assert(source.control.frozen.unwrap().aus
            <= source.branch_projection_aus());
        assert(!source.branch_projection_aus().contains(
            spec_superblock_addr().au,
        ));
    }

    pub proof fn branch_recovery_semantic_certificate(
        self,
    ) -> (out: (
        crate::implementation::CrashAwareCachingDiskBranchBetree_v::
            BetreeMetadataRecovery,
        crate::implementation::CrashAwareCachingDiskBranchBetree_v::
            CachingDiskBranchBetreeImage,
    ))
        requires
            self.inv(),
            self.recovery_phase is LoadingBranch,
            self.branch.control.loading,
        ensures
            self.branch.recovery@ == out.0.core(),
            self.branch.control.metadata@ == out.1.metadata,
            out.0.refinement_inv(out.1),
    {
        self.model_alignment_facts();
        let tracked empty_disk_responses: Tracked<DiskRespShard> =
            Tracked(DiskRespShard::empty(self.instance_id()));
        let model = open_system_invariant_disk_response::<
            UnifiedCacheBetreeProgramModel,
            UnifiedCacheBetreeRefinementProof,
        >(self.model, empty_disk_responses);
        UnifiedCacheBetreeSystemRefinement::
            loading_branch_recovery_facts(model);
        let source = UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(model);
        let recovery = crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                BetreeMetadataRecovery::from_core(
                    source.branch_caching_disk_i(),
                    model.program.state.branch.control.recovery,
                );
        let image = source.persistent_branch_image_i();
        assert(model.program == self.model@.value());
        assert(model.program.state.branch == self.branch@);
        assert(self.branch.recovery@
            == model.program.state.branch.control.recovery);
        assert(self.branch.control.metadata@
            == model.program.state.branch.control.metadata);
        (recovery, image)
    }

    pub proof fn journal_recovery_raw_disk(
        self,
    ) -> (journal_raw_disk: Map<Address, RawPage>)
        requires
            self.inv(),
            !(self.state().recovery_state is Begin),
            !(self.state().recovery_state is AwaitingSuperblock),
        ensures
            cache_agrees_with_raw_disk_on_domain(
                self.cache@,
                journal_raw_disk,
            ),
            self.journal@.status is None
                && self.journal@.snapshot.freshest_rec() is Some
                ==> journal_disk_load_index_inv(
                    DiskView {
                        boundary_lsn:
                            self.journal@.snapshot.boundary_lsn,
                        entries: to_journal_records(journal_raw_disk),
                    },
                    self.journal@.snapshot.freshest_rec(),
                    self.journal@.snapshot.first(),
                ),
    {
        self.model_alignment_facts();
        let tracked empty_disk_responses: Tracked<DiskRespShard> =
            Tracked(DiskRespShard::empty(self.instance_id()));
        let model = open_system_invariant_disk_response::<
            UnifiedCacheBetreeProgramModel,
            UnifiedCacheBetreeRefinementProof,
        >(self.model, empty_disk_responses);
        let journal_source = UnifiedCacheBetreeSystemRefinement::
            unified_cache_betree_journal_source(model);
        let journal_cdj = journal_source.journal_caching_disk_state_i();
        let journal_raw_disk = journal_cdj.disk.visible().restrict(
            journal_cdj.journal_tj().disk_view.entries.dom(),
        );

        assert(UnifiedCacheBetreeRefinementProof::inv(model));
        assert(model.program == self.model@.value());
        assert(UnifiedCacheBetreeSystemRefinement::refinement_inv(model));
        UnifiedCacheBetreeSystemRefinement::
            post_superblock_journal_source_inv(model);
        assert(UnifiedCacheJournalRefinement::inv(journal_source));
        assert(journal_source.inv());
        assert(journal_source.semantic_inv());
        assert(journal_source.superblock_loaded());
        assert(journal_source.i().refinement_inv());
        assert(journal_source.i().ephemeral is Known);
        assert(journal_source.i().ephemeral->v == journal_cdj);
        assert(journal_cdj.refinement_inv());
        assert(journal_cdj.semantic_inv());
        reveal(CachingDiskJournal::State::allocation_view_semantic_inv);
        assert(journal_cdj.inv());
        assert(journal_cdj.journal == self.journal@);

        journal_cdj.disk.visible_submap_readable();
        journal_cdj.journal_disk_view().path_build_tight_is_sub_disk(
            journal_cdj.journal_tj().freshest_rec,
        );
        assert(to_journal_records(journal_raw_disk)
            == journal_cdj.journal_tj().disk_view.entries) by {
            assert_maps_equal!(
                to_journal_records(journal_raw_disk),
                journal_cdj.journal_tj().disk_view.entries,
                addr => {
                    if to_journal_records(journal_raw_disk)
                        .contains_key(addr)
                    {
                        assert(journal_raw_disk.contains_key(addr));
                        assert(journal_cdj.journal_tj().disk_view
                            .entries.contains_key(addr));
                        assert(journal_cdj.journal_disk_view().entries
                            .contains_key(addr));
                        assert(journal_cdj.disk.visible()
                            .contains_key(addr));
                        assert(journal_cdj.journal_tj().disk_view
                            .is_sub_disk(journal_cdj.journal_disk_view()));
                        assert(journal_raw_disk[addr]
                            == journal_cdj.disk.visible()[addr]);
                    }
                    if journal_cdj.journal_tj().disk_view.entries
                        .contains_key(addr)
                    {
                        assert(journal_cdj.journal_disk_view().entries
                            .contains_key(addr));
                        assert(journal_cdj.disk.visible()
                            .contains_key(addr));
                        assert(journal_cdj.journal_tj().disk_view
                            .is_sub_disk(journal_cdj.journal_disk_view()));
                        assert(journal_raw_disk.contains_key(addr));
                        assert(journal_raw_disk[addr]
                            == journal_cdj.disk.visible()[addr]);
                    }
                }
            );
        }

        assert(cache_agrees_with_raw_disk_on_domain(
            self.cache@,
            journal_raw_disk,
        )) by {
            assert forall |addr: Address, data: RawPage|
                #[trigger] self.cache@.valid_read(addr, data)
                && journal_raw_disk.contains_key(addr)
                implies journal_raw_disk[addr] == data by {
                let aus = journal_source.journal_projection_aus();
                assert(journal_cdj.journal_tj().disk_view.entries
                    .contains_key(addr));
                assert(journal_cdj.journal_disk_view().entries
                    .contains_key(addr));
                assert(journal_cdj.disk.visible().contains_key(addr));
                if journal_cdj.disk.visible_cache().contains_key(addr) {
                    assert(journal_cdj.disk.cache.contains_key(addr));
                } else {
                    assert(journal_cdj.disk.persistent.contains_key(addr));
                    if journal_cdj.disk.cache.contains_key(addr) {
                        assert(journal_cdj.disk.status.contains_key(addr));
                        assert(journal_cdj.disk.status[addr]
                            == crate::implementation::CachingDisk_v::
                                PageStatus::Clean);
                    }
                }
                assert(addresses_in_aus(aus).contains(addr)) by {
                    if journal_cdj.disk.cache.contains_key(addr) {
                        assert(project_cache_pages(
                            journal_source.cache,
                            aus,
                        ).contains_key(addr));
                    } else {
                        assert(journal_cdj.disk.persistent
                            .contains_key(addr));
                    }
                }
                assert(cache_filled_addr(journal_source.cache, addr)) by {
                    assert(journal_source.cache == self.cache@);
                    journal_source.cache.build_lookup_map_ensures();
                    assert(journal_source.cache.build_lookup_map_props(
                        journal_source.cache.lookup_map,
                    ));
                    assert(journal_source.cache.lookup_map
                        .contains_key(addr));
                }
                assert(filled_cache_pages(journal_source.cache)
                    .contains_key(addr));
                assert(cache_filled_page(journal_source.cache, addr)
                    == data) by {
                    assert(journal_source.cache == self.cache@);
                }
                assert(project_cache_pages(journal_source.cache, aus)
                    .contains_key(addr));
                projectable_entry_in_caching_disk_i(
                    journal_source.cache,
                    journal_source.disk,
                    aus,
                    addr,
                );
                assert(journal_cdj.disk.cache.contains_key(addr));
                assert(journal_cdj.disk.cache[addr] == data);
                journal_cdj.disk.visible_submap_readable();
                assert(journal_cdj.disk.readable().contains_key(addr));
                assert(journal_cdj.disk.readable()[addr]
                    == journal_cdj.disk.visible()[addr]);
            }
        }

        if self.journal@.status is None
            && self.journal@.snapshot.freshest_rec() is Some
        {
            let image = journal_cdj.backing_journal_image();
            assert(journal_cdj.journal.status is None);
            assert(journal_cdj.unloaded_backing_image_valid());
            assert(image.valid_image());
            image.valid_image_implies_tight_valid_image();
            assert(image.tj.disk_view == journal_cdj.journal_disk_view());
            assert(image.tj.freshest_rec
                == self.journal@.snapshot.freshest_rec());
            assert(image.first == self.journal@.snapshot.first());
            assert(image.tight_tj() == journal_cdj.journal_tj());
            assert(journal_cdj.journal_tj().disk_view
                .pointer_is_upstream(
                    journal_cdj.journal_tj().freshest_rec,
                    self.journal@.snapshot.first(),
                ));
            journal_cdj.journal_disk_view().path_build_tight_idempotent(
                journal_cdj.journal_tj().freshest_rec,
            );
            assert(journal_cdj.journal_tj().disk_view.path_build_tight(
                journal_cdj.journal_tj().freshest_rec,
            ) == journal_cdj.journal_tj().disk_view);
        }
        journal_raw_disk
    }
}

} // verus!
