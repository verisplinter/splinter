use builtin_macros::*;
use builtin::*;
use vstd::prelude::arbitrary;
use vstd::prelude::ValueToken;
use vstd::prelude::ElementToken;

use vstd::tokens::InstanceId;
use crate::trusted::ProgramModelTrait_t::*;
use crate::trusted::RefinementObligation_t::*;
use crate::trusted::ClientAPI_t::*;
use crate::trusted::KVStoreTokenized_t::*;
use crate::trusted::SystemModel_t::*;
use crate::spec::MapSpec_t::*;
use crate::spec::AsyncDisk_t::*;
use crate::implementation::MultisetMapRelation_v::multiset_map_singleton;

verus!{

// Auditor contracts for the program impl 
pub trait KVStoreTrait : Sized{

    type ProgramModel: ProgramModelTrait;
    type Proof: RefinementObligation<Self::ProgramModel>;

    spec fn wf_init(self) -> bool;

    // NOTE: this must return the instance of the KVStoreTokenized, not enforced yet
    spec fn instance_id(self) -> InstanceId;

    fn new() -> (out: Self)
        ensures out.wf_init()
    ;

    fn kvstore_main(&mut self, api: ClientAPI<Self::ProgramModel>)
        requires 
            old(self).wf_init(),
            old(self).instance_id() == api.instance_id()
    ;

    // TODO: someday add an ensures that the disk model "after this runs" abstracts to an initial state.
    fn kvstore_mkfs(&mut self, api: ClientAPI<Self::ProgramModel>)
        requires 
            old(self).wf_init(),
            old(self).instance_id() == api.instance_id()
    ;
}

// Auditor promise
// This should only be true for the specific RefinementObligation!
// Here I'm also narrowly specializing to a particular set of available tokens.
pub proof fn open_system_invariant_disk_response<ProgramModel: ProgramModelTrait, Proof: RefinementObligation<ProgramModel>>(
    model_token: Tracked<KVStoreTokenized::model<ProgramModel>>,
    disk_responses_token: Tracked<KVStoreTokenized::disk_responses_multiset<ProgramModel>>,
    ) -> (model: SystemModel::State<ProgramModel>)
ensures
    Proof::inv(model),
    model.program == model_token@.value(),
    forall |id,disk_response| #[trigger] disk_responses_token@.multiset().contains((id, disk_response))
        ==> (model.disk.responses.dom().contains(id) && model.disk.responses[id] == disk_response),
{
    assume(false);
    arbitrary()
}

// The generic version handles multiple simultaneous responses in a single shard, but the ClientAPI
// only ever supplies one at a time.
pub proof fn open_system_invariant_disk_response_singleton<ProgramModel: ProgramModelTrait, Proof: RefinementObligation<ProgramModel>>(
    model_token: Tracked<KVStoreTokenized::model<ProgramModel>>,
    disk_responses_token: Tracked<KVStoreTokenized::disk_responses_multiset<ProgramModel>>,
    id: ID,
    disk_response: DiskResponse,
    ) -> (model: SystemModel::State<ProgramModel>)
requires
    disk_responses_token@.multiset() == multiset_map_singleton(id, disk_response)
ensures
    Proof::inv(model),
    model.program == model_token@.value(),
    model.disk.responses.dom().contains(id),
    model.disk.responses[id] == disk_response,
{
    assert( disk_responses_token@.multiset().contains((id, disk_response)) );
    open_system_invariant_disk_response::<ProgramModel, Proof>(model_token, disk_responses_token)
}

pub proof fn open_system_invariant_user_request<ProgramModel: ProgramModelTrait, Proof: RefinementObligation<ProgramModel>>(
    model_token: Tracked<KVStoreTokenized::model<ProgramModel>>,
    user_request_token: Tracked<KVStoreTokenized::requests<ProgramModel>>,
    ) -> (model: SystemModel::State<ProgramModel>)
ensures
    Proof::inv(model),
    model.program == model_token@.value(),
    model.sync_requests.dom().contains(user_request_token@.element().id),
{
    assume(false);
    arbitrary()
}


}
