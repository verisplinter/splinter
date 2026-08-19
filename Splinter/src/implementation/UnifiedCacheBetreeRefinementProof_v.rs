// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

// Auditor refinement obligation for the executable unified-cache Betree
// program model. Executable orchestration lives in Implementation_v.rs.

#![allow(unused_imports)]

use vstd::prelude::*;

use crate::implementation::CrashAwareCachingDiskBetreeSystemRefinement_v as
    CrashAwareCachingDiskBetreeSystemRefinement;
use crate::implementation::UnifiedCacheBetreeProgramModel_v::
    UnifiedCacheBetreeProgramModel;
use crate::implementation::UnifiedCacheBetreeSystemRefinement_v as
    UnifiedCacheBetreeSystemRefinement;
use crate::spec::MapSpec_t::CrashTolerantAsyncMap;
use crate::trusted::RefinementObligation_t::RefinementObligation;
use crate::trusted::SystemModel_t::SystemModel;

verus! {

pub struct UnifiedCacheBetreeRefinementProof;

impl RefinementObligation<UnifiedCacheBetreeProgramModel>
    for UnifiedCacheBetreeRefinementProof
{
    open spec fn inv(
        model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    ) -> bool {
        UnifiedCacheBetreeSystemRefinement::refinement_inv(model)
    }

    open spec fn i(
        model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    ) -> CrashTolerantAsyncMap::State {
        CrashAwareCachingDiskBetreeSystemRefinement::
            caching_disk_betree_system_ctam_i(
                UnifiedCacheBetreeSystemRefinement::
                    unified_cache_betree_system_i(model),
            )
    }

    open spec fn i_lbl(
        pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
        post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
        lbl: SystemModel::Label,
    ) -> CrashTolerantAsyncMap::Label {
        CrashAwareCachingDiskBetreeSystemRefinement::
            caching_disk_betree_system_lbl_i(
                UnifiedCacheBetreeSystemRefinement::
                    unified_cache_betree_system_i_lbl(pre, post, lbl),
            )
    }

    proof fn i_lbl_valid(
        pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
        post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
        lbl: SystemModel::Label,
        ctam_lbl: CrashTolerantAsyncMap::Label,
    ) {
    }

    proof fn init_refines(
        model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    ) {
        UnifiedCacheBetreeSystemRefinement::init_refines(model);
        CrashAwareCachingDiskBetreeSystemRefinement::init_refines_ctam(
            UnifiedCacheBetreeSystemRefinement::
                unified_cache_betree_system_i(model),
        );
        assert(CrashTolerantAsyncMap::State::init(Self::i(model)));
        reveal(CrashTolerantAsyncMap::State::init);
        reveal(CrashTolerantAsyncMap::State::init_by);

        let config = choose |config|
            CrashTolerantAsyncMap::State::init_by(Self::i(model), config);
        match config {
            CrashTolerantAsyncMap::Config::initialize() => {
                assert(CrashTolerantAsyncMap::State::initialize(
                    Self::i(model),
                ));
            },
            CrashTolerantAsyncMap::Config::dummy_to_use_type_params(_) => {
                assert(false);
            },
        }
    }

    proof fn next_refines(
        pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
        post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
        lbl: SystemModel::Label,
    ) {
        UnifiedCacheBetreeSystemRefinement::next_refines(pre, post, lbl);
        CrashAwareCachingDiskBetreeSystemRefinement::next_refines_ctam(
            UnifiedCacheBetreeSystemRefinement::
                unified_cache_betree_system_i(pre),
            UnifiedCacheBetreeSystemRefinement::
                unified_cache_betree_system_i(post),
            UnifiedCacheBetreeSystemRefinement::
                unified_cache_betree_system_i_lbl(pre, post, lbl),
        );
    }
}

} // verus!
