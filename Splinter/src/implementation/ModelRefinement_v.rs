// ModelRefinement_v.rs — Thin adapter satisfying RefinementObligation<ConcreteProgramModel>
// by composing BracketRefinement (SM1→SM2) and ModelRefinementTwo (SM2→CTAM).
//
// Also provides:
// - multiset_to_set (used by ModelRefinementTwo_v)
// - Cache::State extensions (used by JournalCoordinationRefinement_v)
// - Delegation methods on SystemModel::State<CPM> (used by Implementation_v)

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::prelude::*;

use vstd::multiset::Multiset;
use crate::spec::AsyncDisk_t::{Address, AsyncDisk, DiskRequest, DiskResponse, RawPage};
use crate::spec::MapSpec_t::{AsyncMap, CrashTolerantAsyncMap, ID, MapSpec, SyncReqId};
use crate::trusted::SystemModel_t::SystemModel;
use crate::trusted::RefinementObligation_t::RefinementObligation;
use crate::trusted::ProgramModelTrait_t::{DiskLabel, ProgramModelTrait, ProgramUserOp};
use crate::implementation::Cache_v::{Cache, Slot};
use crate::implementation::ConcreteProgramModel_v::ConcreteProgramModel;
use crate::implementation::SystemModelTwo_v::SystemModelTwo;
use crate::implementation::ModelRefinementTwo_v::{sm2_i, sm2_i_lbl, next_refines_ctam};
use crate::implementation::BracketRefinement_v;

verus!{

// ================================================================
// Shared helpers
// ================================================================

// TODO: put into vstd/multiset_lib.rs
pub open spec fn multiset_to_set<V>(m: Multiset<V>) -> Set<V> {
    Set::new(|v| m.contains(v))
}

// ================================================================
// Cache extensions (used by JournalCoordinationRefinement_v)
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
// Delegation methods on SystemModel::State<CPM> for Implementation_v.rs
// ================================================================

impl SystemModel::State<ConcreteProgramModel> {
    pub open spec fn outstanding_reqs_consistent(self) -> bool
    {
        SystemModelTwo::State::from_system_model(self).outstanding_reqs_consistent()
    }

    pub open spec fn awaiting_sb_response_is_disk_content(self) -> bool
    {
        SystemModelTwo::State::from_system_model(self).awaiting_sb_response_is_disk_content()
    }

    pub open spec fn persistent_sb_disk_inv(self) -> bool
    {
        SystemModelTwo::State::from_system_model(self).persistent_sb_disk_inv()
    }

    pub open spec fn journal_pages_parsable(self) -> bool
    {
        SystemModelTwo::State::from_system_model(self).journal_pages_parsable()
    }

    pub open spec fn cache_reads_agree_with_disk(self) -> bool
    {
        SystemModelTwo::State::from_system_model(self).cache_reads_agree_with_disk()
    }

    pub open spec fn persistent_journal_structure(self) -> bool
    {
        SystemModelTwo::State::from_system_model(self).persistent_journal_structure()
    }
}

// ================================================================
// RefinementObligation adapter: composes BracketRefinement + ModelRefinementTwo
// ================================================================

pub struct RefinementProof{}

impl RefinementObligation<ConcreteProgramModel> for RefinementProof {

    open spec fn inv(model: SystemModel::State<ConcreteProgramModel>) -> bool
    {
        SystemModelTwo::State::from_system_model(model).inv()
    }

    closed spec fn i(model: SystemModel::State<ConcreteProgramModel>) -> (mapspec: CrashTolerantAsyncMap::State)
    {
        sm2_i(SystemModelTwo::State::from_system_model(model))
    }

    // i_lbl defined directly on SM1 labels (no SM2 delegation needed).
    // Structurally isomorphic to sm2_i_lbl but operates on SystemModel::Label.
    closed spec fn i_lbl(pre: SystemModel::State<ConcreteProgramModel>, post: SystemModel::State<ConcreteProgramModel>, lbl: SystemModel::Label) -> (ctam_lbl: CrashTolerantAsyncMap::Label)
    {
        match lbl {
            SystemModel::Label::AcceptRequest{req} => {
                CrashTolerantAsyncMap::Label::OperateOp{
                    base_op: AsyncMap::Label::RequestOp { req }
                }
            },
            SystemModel::Label::DeliverReply{reply} => {
                CrashTolerantAsyncMap::Label::OperateOp{
                    base_op: AsyncMap::Label::ReplyOp { reply }
                }
            },
            SystemModel::Label::ProgramUIOp{op} => {
            match op {
                ProgramUserOp::Execute{req, reply} =>
                    CrashTolerantAsyncMap::Label::OperateOp{
                        base_op: AsyncMap::Label::ExecuteOp  { req, reply },
                    },
                ProgramUserOp::AcceptSyncRequest{ sync_req_id } =>
                    CrashTolerantAsyncMap::Label::ReqSyncOp{ sync_req_id },
                ProgramUserOp::DeliverSyncReply{ sync_req_id } =>
                    CrashTolerantAsyncMap::Label::ReplySyncOp{ sync_req_id },
            }},
            SystemModel::Label::ProgramDiskOp{ info } =>
                CrashTolerantAsyncMap::Label::Noop{},
            SystemModel::Label::ProgramInternal =>
                CrashTolerantAsyncMap::Label::Noop{},
            SystemModel::Label::DiskInternal => {
                let sm2_pre = SystemModelTwo::State::from_system_model(pre);
                let sm2_post = SystemModelTwo::State::from_system_model(post);
                if sm2_pre.sb_landed(sm2_post) {
                    CrashTolerantAsyncMap::Label::SyncOp{}
                } else {
                    CrashTolerantAsyncMap::Label::Noop{}
                }
            },
            SystemModel::Label::Crash =>
                CrashTolerantAsyncMap::Label::CrashOp{},
            _ =>
                CrashTolerantAsyncMap::Label::Noop{},
        }
    }

    proof fn i_lbl_valid(pre: SystemModel::State<ConcreteProgramModel>, post: SystemModel::State<ConcreteProgramModel>, lbl: SystemModel::Label, ctam_lbl: CrashTolerantAsyncMap::Label)
    {
        assert( ctam_lbl == Self::i_lbl(pre, post, lbl) );
        assert( lbl.label_correspondence(ctam_lbl) );
    }

    proof fn init_refines(pre: SystemModel::State<ConcreteProgramModel>)
    {
        assume(false); // TODO: delegate to sm2_init_refines
    }

    proof fn next_refines(pre: SystemModel::State<ConcreteProgramModel>, post: SystemModel::State<ConcreteProgramModel>, lbl: SystemModel::Label)
    {
        // Step 1: BracketRefinement — SM1 step induces SM2 step
        SystemModelTwo::State::next_refines(pre, post, lbl);

        // Step 2: ModelRefinementTwo — SM2 step refines CTAM step
        let sm2_pre = SystemModelTwo::State::from_system_model(pre);
        let sm2_post = SystemModelTwo::State::from_system_model(post);
        let sm2_lbl = SystemModelTwo::State::i_lbl(lbl);

        next_refines_ctam(sm2_pre, sm2_post, sm2_lbl);
    }
}

}
