// BracketRefinement: Proves that SystemModel<ConcreteProgramModel> refines
// SystemModelTwo via the trivial bracket rearrangement.
//
// The isomorphism is: SystemModelTwo::from_system_model(sm).
// The same state, different nesting of fields.

#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::multiset::Multiset;

use crate::spec::AsyncDisk_t::*;
use crate::spec::MapSpec_t::{ID, SyncReqId, Request, Reply};
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::abstract_system::AbstractCrashAwareMap_v::AbstractCrashAwareMap;
use crate::trusted::ProgramModelTrait_t::{DiskLabel, DiskModel, ProgramDiskInfo, ProgramLabel, ProgramModelTrait, ProgramUserOp};
use crate::trusted::SystemModel_t::SystemModel;
use crate::implementation::ConcreteProgramModel_v::ConcreteProgramModel;
use crate::implementation::ConcreteJournal_v::ConcreteJournal;
use crate::implementation::SystemModelTwo_v::SystemModelTwo;
use crate::implementation::AtomicState_v::{AtomicState, RecoveryState, InflightInfo, ProgramEvent};
use crate::implementation::MultisetMapRelation_v::multiset_to_map;

verus!{

impl SystemModelTwo::State {
    /// The interpretation: map a SystemModel label to a SystemModelTwo label (trivially isomorphic)
    pub open spec fn i_lbl(lbl: SystemModel::Label) -> SystemModelTwo::Label
    {
        match lbl {
            SystemModel::Label::AcceptRequest{req} => SystemModelTwo::Label::AcceptRequest{req},
            SystemModel::Label::DeliverReply{reply} => SystemModelTwo::Label::DeliverReply{reply},
            SystemModel::Label::AcceptSyncRequest{sync_req_id} => SystemModelTwo::Label::AcceptSyncRequest{sync_req_id},
            SystemModel::Label::DeliverSyncReply{sync_req_id} => SystemModelTwo::Label::DeliverSyncReply{sync_req_id},
            SystemModel::Label::ProgramUIOp{op} => SystemModelTwo::Label::ProgramUIOp{op},
            SystemModel::Label::ProgramDiskOp{info} => SystemModelTwo::Label::ProgramDiskOp{info},
            SystemModel::Label::ProgramInternal => SystemModelTwo::Label::ProgramInternal,
            SystemModel::Label::DiskInternal => SystemModelTwo::Label::DiskInternal,
            SystemModel::Label::Crash => SystemModelTwo::Label::Crash,
            SystemModel::Label::Noop => SystemModelTwo::Label::Noop,
        }
    }

    /// Round-trip: from_system_model preserves to_atomic
    proof fn from_system_model_atomic(sm: SystemModel::State<ConcreteProgramModel>)
        ensures Self::from_system_model(sm).to_atomic() == sm.program.state
    {
    }

    /// The bracket refinement: every SystemModel step induces a SystemModelTwo step.
    pub proof fn next_refines(
        pre: SystemModel::State<ConcreteProgramModel>,
        post: SystemModel::State<ConcreteProgramModel>,
        lbl: SystemModel::Label,
    )
        requires
            SystemModel::State::next(pre, post, lbl),
        ensures
            SystemModelTwo::State::next(
                Self::from_system_model(pre),
                Self::from_system_model(post),
                Self::i_lbl(lbl)),
    {
        reveal(SystemModel::State::next);
        reveal(SystemModel::State::next_by);
        reveal(SystemModelTwo::State::next);
        reveal(SystemModelTwo::State::next_by);

        let sm2_pre = Self::from_system_model(pre);
        let sm2_post = Self::from_system_model(post);
        let sm2_lbl = Self::i_lbl(lbl);

        let step = choose |step| SystemModel::State::next_by(pre, post, lbl, step);

        match step {
            SystemModel::Step::accept_request() => {
                assert(SystemModelTwo::State::next_by(sm2_pre, sm2_post, sm2_lbl,
                    SystemModelTwo::Step::accept_request()));
            },
            SystemModel::Step::deliver_reply() => {
                assert(SystemModelTwo::State::next_by(sm2_pre, sm2_post, sm2_lbl,
                    SystemModelTwo::Step::deliver_reply()));
            },
            SystemModel::Step::program_execute(new_program) => {
                let pe = choose |pe: ProgramEvent|
                    AtomicState::execute_transition(pre.program.state, post.program.state,
                        lbl->op->req, lbl->op->reply, pe);
                assert(SystemModelTwo::State::next_by(sm2_pre, sm2_post, sm2_lbl,
                    SystemModelTwo::Step::program_execute(sm2_post.concrete_journal, sm2_post.store)));
            },
            SystemModel::Step::accept_sync_request() => {
                assert(SystemModelTwo::State::next_by(sm2_pre, sm2_post, sm2_lbl,
                    SystemModelTwo::Step::accept_sync_request()));
            },
            SystemModel::Step::program_accept_sync_request(new_program) => {
                assert(SystemModelTwo::State::next_by(sm2_pre, sm2_post, sm2_lbl,
                    SystemModelTwo::Step::program_accept_sync_request(sm2_post.sync_req_map)));
            },
            SystemModel::Step::program_deliver_sync_reply(new_program) => {
                assert(SystemModelTwo::State::next_by(sm2_pre, sm2_post, sm2_lbl,
                    SystemModelTwo::Step::program_deliver_sync_reply(sm2_post.sync_req_map)));
            },
            SystemModel::Step::deliver_sync_reply() => {
                assert(SystemModelTwo::State::next_by(sm2_pre, sm2_post, sm2_lbl,
                    SystemModelTwo::Step::deliver_sync_reply()));
            },
            SystemModel::Step::program_disk(new_program, new_disk) => {
                Self::from_system_model_atomic(pre);
                Self::from_system_model_atomic(post);
                // Bridge through valid_disk_transition (workaround for disk_transition trigger)
                assert(ConcreteProgramModel::valid_disk_transition(pre.program, post.program, lbl->info));
                assert(SystemModelTwo::State::next_by(sm2_pre, sm2_post, sm2_lbl,
                    SystemModelTwo::Step::program_disk(
                        sm2_post.concrete_journal,
                        sm2_post.outstanding_cache_reqs,
                        sm2_post.recovery_state,
                        sm2_post.store,
                        sm2_post.persistent_store_ptr,
                        sm2_post.prepared_store_ptr,
                        sm2_post.prepared_store_lsn,
                        sm2_post.sync_req_map)));
            },
            SystemModel::Step::program_internal(new_program) => {
                assert(SystemModelTwo::State::next_by(sm2_pre, sm2_post, sm2_lbl,
                    SystemModelTwo::Step::program_internal(
                        sm2_post.concrete_journal,
                        sm2_post.outstanding_cache_reqs,
                        sm2_post.recovery_state,
                        sm2_post.store,
                        sm2_post.persistent_store_ptr,
                        sm2_post.prepared_store_ptr,
                        sm2_post.prepared_store_lsn)));
            },
            SystemModel::Step::disk_internal(new_disk) => {
                assert(SystemModelTwo::State::next_by(sm2_pre, sm2_post, sm2_lbl,
                    SystemModelTwo::Step::disk_internal(post.disk)));
            },
            SystemModel::Step::crash(new_program, new_disk) => {
                assert(SystemModelTwo::State::next_by(sm2_pre, sm2_post, sm2_lbl,
                    SystemModelTwo::Step::crash(sm2_post.concrete_journal, post.disk, sm2_post.store)));
            },
            SystemModel::Step::noop() => {
                assert(SystemModelTwo::State::next_by(sm2_pre, sm2_post, sm2_lbl,
                    SystemModelTwo::Step::noop()));
            },
            _ => { }  // dummy_to_use_type_params
        }
    }
}

}
