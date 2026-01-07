// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
//use vstd::prelude_macros::*;
use vstd::pervasive::*;
use vstd::prelude::*;
use vstd::modes::*;
use vstd::tokens::InstanceId;
// use vstd::hash_map::*;
use vstd::std_specs::hash::*;

use crate::trusted::ClientAPI_t::*;
use crate::trusted::ReqReply_t::*;
use crate::trusted::KVStoreTrait_t::*;
use crate::trusted::KVStoreTokenized_t::*;
use crate::trusted::ProgramModelTrait_t::*;
use crate::abstract_system::StampedMap_v::LSN;

use crate::spec::MapSpec_t::{ID, MapSpec, PersistentState};
use crate::spec::TotalKMMap_t::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
// use crate::spec::FloatingSeq_t::*;
// use crate::abstract_system::StampedMap_v;
use crate::abstract_system::StampedMap_v::{StampedMap};
use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::abstract_system::MsgHistory_v::KeyedMessage;
// use crate::abstract_system::AbstractCrashAwareSystemRefinement_v;
use crate::abstract_system::AbstractJournal_v::AbstractJournal;
use crate::abstract_system::AbstractMap_v::AbstractMap;
use crate::abstract_system::AbstractCrashAwareMap_v::AbstractCrashAwareMap;
use crate::disk::GenericDisk_v::Pointer;

use crate::implementation::ModelRefinement_v::*;
use crate::implementation::ConcreteProgramModel_v::*;
use crate::implementation::AtomicState_v::*;
use crate::implementation::MultisetMapRelation_v::*;
use crate::implementation::VecMap_v::*;
use crate::implementation::JournalTypes_v::{ILsn};
use crate::implementation::JournalModel_v::lsn_addr_index_discard_up_to;
use crate::implementation::JournalImpl_v::*;
use crate::implementation::SuperblockTypes_v;
use crate::implementation::SuperblockTypes_v::*;
use crate::implementation::CachedJournal_v::CachedJournal;
use crate::implementation::CachedJournal_v;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::WF_v::WF;
// use crate::marshalling::UniformSized_v::UniformSized;
use crate::implementation::OverflowFiction_v::*;
use crate::abstract_system::AbstractCrashAwareMap_v;
use crate::implementation::CacheImpl_v::CacheImpl;

#[allow(unused_imports)]
use vstd::multiset::*;
#[allow(unused_imports)]
use vstd::tokens::*;
#[allow(unused_imports)]
use crate::spec::AsyncDisk_t::*;
use crate::spec::ImplDisk_t::*;
#[allow(unused_imports)]
use crate::implementation::DiskLayout_v::*;
use vstd::hash_map::HashMapWithView;

verus!{

broadcast use JournalImpl::view_ensures;

pub closed spec fn good_req(instance_id: InstanceId, req: Request, req_shard: RequestShard) -> bool
{
    &&& req_shard.instance_id() == instance_id
    &&& req_shard.element() == req
}

// requests that can be satisfied when this superblock lands
// TODO(jonh): in sync_request: need to consume request shard to get
// atomic state; then just store atomic state ids here.
// That also suggests we will have version numbers handy, which will
// further simplify this data structure.
struct SyncRequestBuffer {
    satisfied_reqs: Vec<Request>,
    deferred_reqs: Vec<Request>,
}

impl SyncRequestBuffer {
    closed spec fn wf(self, instance_id: InstanceId) -> bool
    {
        &&& forall |r| #![auto] self.satisfied_reqs@.contains(r) ==> {
            &&& r.input is SyncInput
        }
        &&& forall |r| #![auto] self.deferred_reqs@.contains(r) ==> {
            &&& r.input is SyncInput
        }
    }

    fn new_empty() -> (out: Self)
    ensures
        !out.in_flight(),
        out.deferred_reqs@.len() == 0,
    {
        SyncRequestBuffer{ satisfied_reqs: vec![], deferred_reqs: vec![] }
    }

    closed spec fn in_flight(self) -> bool {
        &&& self.satisfied_reqs.len() > 0
    }

    fn exec_in_flight(&self) -> (out: bool)
    ensures self.in_flight() == out
    {
        &&& self.satisfied_reqs.len() > 0
    }
}

pub type ModelShard = KVStoreTokenized::model<ConcreteProgramModel>;

pub type RequestShard = KVStoreTokenized::requests<ConcreteProgramModel>;
pub type ReplyShard = KVStoreTokenized::replies<ConcreteProgramModel>;

pub type DiskRespShard = KVStoreTokenized::disk_responses_multiset<ConcreteProgramModel>;
pub type DiskReqShard = KVStoreTokenized::disk_requests_multiset<ConcreteProgramModel>;

// Truncate 
pub struct InFlight {
    // Together this is the implementation of a StampedMap
    new_boundary_lsn: ILsn,     // this will be the version of the new persistent map (when it lands)
    freshest_rec: Pointer,
    new_persistent_lsn: ILsn,   // this will be the seq_end of the persistent journal (when it lands)
    new_store: VecMap<Key, Value>,  // this will be the new persistent map
}

closed spec(checked) fn view_as_kmmap(store: VecMap<Key, Value>) -> TotalKMMap
{
    SuperblockTypes_v::map_to_kmmap(store@)
}

// TODO(jonh): delete
// proof fn vec_insert_is_kmmap_insert(old_store: Map<Key, Value>, new_store: Map<Key, Value>, key: Key, value: Value)
// requires
//     new_store == old_store.insert(key, value),
// ensures ASuperblock::map_to_kmmap(new_store) == ASuperblock::map_to_kmmap(old_store.insert(key, value))
// {
// }
// 
// proof fn insert_is_apply(old_kmmap: TotalKMMap, new_kmmap: TotalKMMap, key: Key, value: Value, lsn: LSN)
// requires
//     new_kmmap == old_kmmap.insert(key, Message::Define{value})
// ensures ({
//     let puts = MsgHistory::singleton_at(lsn, KeyedMessage{key, message: Message::Define{value}});
//     new_kmmap == puts.apply_to_stamped_map(StampedMap{value: old_kmmap, seq_end: lsn}).value
//     })
// {
// }
    

// TODO replace with defn from MsgHistory
closed spec(checked) fn map_plus_history(map: TotalKMMap, msg_history: MsgHistory) -> TotalKMMap
    recommends msg_history.wf()
{
    let stamped_map = StampedMap{value: map, seq_end: msg_history.seq_start};
    msg_history.apply_to_stamped_map(stamped_map).value
}

#[derive(Debug)]
enum RecoveryPhase {
    FetchingSuperblock, // not really needed since this phase is delineated by lexical scope
    ReadingJournalIndex,
    ApplyingJournalToRecoverEphemeralMap,
    ReadyForUserOperation,
}

impl RecoveryPhase {
    spec fn advances(self, old: Self) -> bool {
        match old {
            Self::FetchingSuperblock => { true },
            Self::ReadingJournalIndex => { !(self is FetchingSuperblock) },
            Self::ApplyingJournalToRecoverEphemeralMap => { self is ApplyingJournalToRecoverEphemeralMap || self is ReadyForUserOperation },
            Self::ReadyForUserOperation => { self is ReadyForUserOperation },
        }
    }
}

// This struct supplies KVStoreTrait, which has both the entry point to the implementation and the
// proof hooks to satisfy the refinement obligation trait.
pub struct Implementation {
    recovery_phase: RecoveryPhase,

    sync_counter: u64,

    store: VecMap<Key, Value>,
    store_lsn: u64,

    // starts at persistent_store.version, ends matching store
    journal: JournalImpl,
    
    cache: CacheImpl,

    // this is a truncate in flight, only set when a truncation is occuring
    in_flight: Option<InFlight>,

    // remember the actual persistent version on disk and
    // its journal info, so we can interpret to the floating versions.
    persistent_store: VecMap<Key, Value>,

    // token for the program model variable
    model: Tracked<ModelShard>, // 

    // we do not own a mutable reference to this
    instance: Tracked<KVStoreTokenized::Instance<ConcreteProgramModel>>,

    sync_requests: SyncRequestBuffer,

    outstanding_requests: HashMapWithView<ID, IDiskRequest>,
}

impl Implementation {
    // closed spec(checked) fn view_as_kmmap(self) -> TotalKMMap
    // {
    //     ASuperblock::map_to_kmmap(self.store@)
    // }

    // TODO delete this is nonsense now we have a real store
//     broadcast proof fn view_as_kmmap_ensures(self)
//         requires self.persistent_version() <= self.version(), self.journal.seq_start == 0
//         ensures #[trigger] self.view_as_kmmap() =~= MsgHistory::map_plus_history(StampedMap_v::empty(), self.journal@@).value
//     { 
//         assert(self.journal@@.discard_recent((self.journal@@.seq_end) as nat) =~= self.journal@@);
//     }

    // closed spec(checked) fn persistent_map_plus_history(self) -> TotalKMMap
    // {
    //     let sb = ISuperblock { journal: self.journal, store: self.persistent_store.v };
    //     sb@@.store.appv.kmmap
    // }

    // view as floating version should be maintained the same

    pub closed spec fn i(self) -> AtomicState {
        self.state()
    }

    closed spec fn state(&self) -> AtomicState
    {
        self.model@.value().state
    }

    closed spec fn version(&self) -> nat
    {
        self.journal.seq_end()
    }

    closed spec fn inv_recover(self) -> bool {
        &&& self.recovery_phase is FetchingSuperblock
        &&& self.model@.instance_id() == self.instance@.id()
        &&& self.in_flight is None
        &&& !self.sync_requests.in_flight()
        &&& self.sync_requests.deferred_reqs@.len() == 0
        &&& self.store.wf()
        &&& self.state().recovery_state is Begin
        &&& self.cache.inv()
    }

    closed spec fn inv_running(self) -> bool {
        let state = self.state();

        &&& self.store.wf()
        &&& self.journal.wf()
        // &&& self.model@.instance_id() == self.instance@.id() // TODO delete covered by inv

        &&& self.journal.index_ready()

        // physical state consistent with model
        &&& state.recovery_state is RecoveryComplete

        // model matches our interpretation of Implementation state struct
        &&& state.store == self.view_store()
        &&& state.journal == self.journal@

        // map and journal are at the same LSN
        &&& state.journal.seq_end() == state.ephemeral_map().seq_end
        // Probably also need contents to match...

        &&& self.state().wf()

        &&& state.in_flight is Some <==> self.sync_requests.in_flight()
        &&& state.in_flight is Some <==> self.in_flight is Some

        &&& (state.in_flight is Some ==> {
            &&& self.in_flight.unwrap().new_boundary_lsn <= state.journal.status.unwrap().unmarshalled_tail.seq_start
            })
        &&& (state.in_flight is Some ==> {

            // The in-flight version stays active so get_suffix doesn't choke on it when it's time
            // to handle the disk response
            let sync_version = state.in_flight.unwrap().journal_version;
            let new_persistent_map_version = self.in_flight.unwrap().new_boundary_lsn as nat;
            let new_persistent_map = self.in_flight.unwrap().new_store;
//TODO            let new_persistent_journal = self.journal@@.discard_recent(sync_version).discard_old(new_persistent_map_version);
//TODO            let new_ephemeral_journal = self.journal@@.discard_old(new_persistent_map_version);

//TODO            &&& state.history.is_active(sync_version as int)
            &&& self.journal.seq_start() <= new_persistent_map_version
            &&& new_persistent_map_version <= sync_version

            // this seems necessary for recovery???
//TODO            &&& state.history.get(sync_version as int).appv.kmmap 
//TODO                == map_plus_history(view_as_kmmap(new_persistent_map), new_persistent_journal)
//TODO            &&& view_as_kmmap(self.store) 
//TODO                == map_plus_history(view_as_kmmap(new_persistent_map), new_ephemeral_journal)

            // The in-flight 'satisfied requests' can indeed be satisfied by the in-flight version
            &&& self.sync_reqs_in_version(self.sync_requests.satisfied_reqs@, sync_version)
        })

        &&& self.sync_requests.wf(self.instance@.id())
        &&& self.sync_reqs_in_version(self.sync_requests.deferred_reqs@, self.version())
        &&& Self::sync_req_lists_mutually_unique(self.sync_requests.satisfied_reqs@, self.sync_requests.deferred_reqs@)
    }

    spec fn inv_reading_journal(self) -> bool
    {
        &&& self.state().recovery_state is SuperblockAvailable
        &&& self.journal.wf()
        &&& !self.journal.index_ready()
    }

    spec fn inv_applying_journal(self) -> bool
    {
        &&& self.state().recovery_state is JournalIndexComplete
        &&& self.journal.wf()
        &&& self.journal.index_ready()
    }

    closed spec fn inv(self) -> bool {
        &&& self.cache.inv()
        // from the physical phase field to stuff we know
        &&& self.recovery_phase is FetchingSuperblock ==> self.inv_recover()
        &&& self.recovery_phase is ReadingJournalIndex ==> self.inv_reading_journal()
        &&& self.recovery_phase is ApplyingJournalToRecoverEphemeralMap ==> self.inv_applying_journal()
        &&& self.recovery_phase is ReadyForUserOperation ==> self.inv_running()

        // working backward from stuff we know to infer physical phase (used when applying system
        // invs to infer current state)
        &&& self.in_flight is Some ==> self.recovery_phase is ReadyForUserOperation
        &&& self.model@.instance_id() == self.instance@.id()
    }

    // Recovery is complete -- journal index ready, map matches journal. We've established
    // invariants necessary to process user requsets.
    pub closed spec fn ready_for_user_operation(&self) -> bool
    {
        &&& self.recovery_phase is ReadyForUserOperation
    }

    pub closed spec fn i_persistent_store(self) -> StampedMap {
        StampedMap{value: view_as_kmmap(self.persistent_store), seq_end: self.journal.seq_start()}
    }

    pub closed spec fn i_ephemeral_store(self) -> AbstractCrashAwareMap_v::Ephemeral {
        // When is it Unknown? I guess based on the program counter being in recovery.
        AbstractCrashAwareMap_v::Ephemeral::Known{
            v: AbstractMap::State{
                stamped_map: StampedMap{value: view_as_kmmap(self.store), seq_end: self.journal.seq_end()}
            }
        }
    }

    pub closed spec fn i_inflight_store(self) -> Option<StampedMap> {
        match self.in_flight {
            None => None,
            Some(inflight) => {
                Some(StampedMap{value: view_as_kmmap(inflight.new_store), seq_end: inflight.new_boundary_lsn as nat})
            }
        }
    }

    pub open spec fn view_store(&self) -> AbstractCrashAwareMap::State
    {
        AbstractCrashAwareMap::State{
            persistent: self.i_persistent_store(),
            ephemeral: self.i_ephemeral_store(),
            in_flight: self.i_inflight_store(),
        }
    }

    pub closed spec fn good_req(self, req: Request, req_shard: RequestShard) -> bool
    {
        good_req(self.instance_id(), req, req_shard)
    }

    // `api` should really just be part of the state, and this property maintained in inv, except
    // that we have a construction order mess between constructing the instancea and model and then
    // getting an api from the trusted main. Probably should expose a builder pattern.
    pub closed spec fn inv_api(self, api: &ClientAPI<ConcreteProgramModel>) -> bool
    {
        &&& self.inv()
        &&& api.instance_id() == self.instance_id()
    }

    pub closed spec fn good_disk_response(self, id: ID, disk_response: IDiskResponse, response_shard: DiskRespShard) -> bool
    {
        &&& response_shard.instance_id() == self.instance_id()
        &&& response_shard.multiset() == multiset_map_singleton(id, disk_response@)
    }

    pub exec fn handle_noop(&mut self, req: Request, req_shard: Tracked<RequestShard>, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).good_req(req, req_shard@),
        req.input is NoopInput,
        old(self).ready_for_user_operation(),
    ensures
        self.inv_api(api),
        self.ready_for_user_operation(),
    {
        match req.input {
            Input::NoopInput => {
                let reply = Reply{output: Output::NoopOutput, id: req.id};

                let ghost pre_state = self.model@.value();
                let ghost post_state = self.model@.value(); // noop!

                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof { tracked_swap(self.model.borrow_mut(), &mut model); }

                proof {
                    let map_req = req.mapspec_req();
                    let map_reply = reply.mapspec_reply();
                    let ghost map_lbl = MapSpec::Label::Noop{input: map_req.input, output: map_reply.output};
//                     reveal(MapSpec::State::next);
//                     reveal(MapSpec::State::next_by);
                    // assert( MapSpec::State::next_by(post_state.state.history.last().appv, post_state.state.history.last().appv,
                    //         map_lbl, MapSpec::Step::noop())); // witness to step
                    // assert( post_state.state.history.get_prefix(pre_state.state.history.len()) == pre_state.state.history );  // extn
                    let program_event = ProgramEvent::NoOp{};
                    assert( AtomicState::execute_transition(pre_state.state, post_state.state, map_req, map_reply, program_event) );
                    assert( ConcreteProgramModel::next(pre_state, post_state,
                        ProgramLabel::UserIO{op: ProgramUserOp::Execute{req: map_req, reply: map_reply}}) );
                }

                let tracked new_reply_token = self.instance.borrow().execute_transition(
                    KVStoreTokenized::Label::ExecuteOp{req, reply},
                    post_state,
                    &mut model,
                    req_shard.get()
                );
                self.model = Tracked(model);

                api.send_reply(reply, Tracked(new_reply_token), true);
                assert( self.inv_api(api) );
            },
            _ => unreached(),
        }
    }

    pub exec fn handle_put(&mut self, req: Request, req_shard: Tracked<RequestShard>, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).good_req(req, req_shard@),
        old(self).ready_for_user_operation(),
        req.input is PutInput,
    ensures
        self.inv_api(api),
        self.ready_for_user_operation(),
    {
        let out = match req.input {
        Input::PutInput{key, value} => {
            let ghost pre_state = self.model@.value();
            let ghost keyed_msg = KeyedMessage{key, message: Message::Define{value}};

            self.journal.insert(key.clone(), value);
            self.store.insert(key.clone(), value);

            let reply = Reply{output: Output::PutOutput, id: req.id};
            let ghost post_state = ConcreteProgramModel{
                state: AtomicState{
                    journal: self.journal@,
                    store: self.view_store(),
                    ..pre_state.state
                }
            };

            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

            // Prove our physical states correspond to the model state machine step.
            proof {
                let map_req = req.mapspec_req();
                let map_reply = reply.mapspec_reply();
                let puts = MsgHistory::singleton_at(old(self).journal.seq_end(), keyed_msg);

                assert(view_as_kmmap(self.store) =~= view_as_kmmap(old(self).store).insert(key, Message::Define{value})); //extn

                // Need to unwind two instances of the recursive definition: one for the empty base
                // case and one for the single message we stuck in the history.
                reveal_with_fuel(MsgHistory::apply_to_stamped_map, 2);

                reveal(AbstractMap::State::next_by);
                reveal(AbstractMap::State::next);
                // step witness
                assert( AbstractMap::State::next_by(pre_state.state.store.ephemeral->v, post_state.state.store.ephemeral->v,
                        AbstractMap::Label::PutLabel{ puts }, AbstractMap::Step::put{}));

                reveal(AbstractCrashAwareMap::State::next_by);
                reveal(AbstractCrashAwareMap::State::next);
                // step witness
                assert( AbstractCrashAwareMap::State::next_by(pre_state.state.store, post_state.state.store,
                        AbstractCrashAwareMap::Label::PutRecordsLabel{records: puts},
                        AbstractCrashAwareMap::Step::put_records(post_state.state.store.ephemeral->v)) );

                reveal(CachedJournal::State::next_by);
                reveal(CachedJournal::State::next);
                // step witness
                assert( CachedJournal::State::next_by(pre_state.state.journal, post_state.state.journal,
                        CachedJournal::Label::Put{messages: puts},
                        CachedJournal::Step::put()) );

                assert( AtomicState::execute_put(pre_state.state, post_state.state, map_req, map_reply, puts) );
                assert( AtomicState::execute_transition(
                        pre_state.state, post_state.state, map_req, map_reply, ProgramEvent::Put{puts}) );
                assert( ConcreteProgramModel::next(pre_state, post_state,
                    ProgramLabel::UserIO{op: ProgramUserOp::Execute{req: map_req, reply: map_reply}}) );
            }

             let tracked new_reply_token = self.instance.borrow().execute_transition(
                KVStoreTokenized::Label::ExecuteOp{req, reply},
                post_state,
                &mut model,
                req_shard.get(),
            );
            self.model = Tracked(model);

            api.send_reply(reply, Tracked(new_reply_token), true);
        },
            _ => unreached(),
        };
    }

    proof fn system_inv_cannot_receive_write_response_during_recovery(self, disk_req_id: ID, i_disk_response: IDiskResponse, disk_response_token: Tracked<DiskRespShard>)
    requires
        self.i().recovery_state is AwaitingSuperblock,
        disk_response_token@.multiset() == multiset_map_singleton(disk_req_id, i_disk_response@),
        i_disk_response is WriteResp,
    ensures
        false,
    {
        open_system_invariant_disk_response::<ConcreteProgramModel, RefinementProof>(self.model, disk_response_token);
        multiset_map_singleton_ensures(disk_req_id, i_disk_response@);
        assert(disk_response_token@.multiset().contains((disk_req_id, i_disk_response@))); //trigger
        assume(false); // Not sure what broke here; where are we importing this contradicting invariant from?
    }

    pub exec fn handle_query(&mut self, req: Request, req_shard: Tracked<RequestShard>, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).good_req(req, req_shard@),
        req.input is QueryInput,
        old(self).ready_for_user_operation(),
    ensures
        self.inv_api(api),
        // allowed to do nothing in response
        self.ready_for_user_operation(),
    {
        match req.input {
        Input::QueryInput{key} => {
            let value = match self.store.get(&key) {
                Some(v) => *v,
                None => { Value(0) },
            };

            let ghost pre_state = self.model@.value();
            let ghost post_state = pre_state;

            let reply = Reply{output: Output::QueryOutput{value: value}, id: req.id};

            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

            // Prove our physical states correspond to the model state machine step.
            proof {
                let end_lsn = pre_state.state.ephemeral_map().seq_end;
                let map_req = req.mapspec_req();
                let map_reply = reply.mapspec_reply();

                reveal(AbstractMap::State::next_by);
                reveal(AbstractMap::State::next);
                // step witness
                assert( AbstractMap::State::next_by(pre_state.state.store.ephemeral->v, post_state.state.store.ephemeral->v,
                        AbstractMap::Label::QueryLabel{end_lsn, key, value}, AbstractMap::Step::query{}));
                
                reveal(AbstractCrashAwareMap::State::next_by);
                reveal(AbstractCrashAwareMap::State::next);
                // step witness
                assert( AbstractCrashAwareMap::State::next_by(pre_state.state.store, post_state.state.store,
                        AbstractCrashAwareMap::Label::QueryLabel{end_lsn, key, value},
                        AbstractCrashAwareMap::Step::query(post_state.state.store.ephemeral->v)) );

                assert( AtomicState::execute_query(pre_state.state, post_state.state, map_req, map_reply, end_lsn, key, value) );
                assert( AtomicState::execute_transition(
                        pre_state.state, post_state.state, map_req, map_reply, ProgramEvent::Query{end_lsn, key, value}) );
                assert( ConcreteProgramModel::next(pre_state, post_state,
                    ProgramLabel::UserIO{op: ProgramUserOp::Execute{req: map_req, reply: map_reply}}) );
            }

            let tracked new_reply_token = self.instance.borrow().execute_transition(
                KVStoreTokenized::Label::ExecuteOp{req, reply},
                post_state,
                &mut model,
                req_shard.get(),
            );
            self.model = Tracked(model);

            api.send_reply(reply, Tracked(new_reply_token), true);
        },
            _ => unreached(),
        }
    }

    pub exec fn handle_sync_request(&mut self, req: Request, req_shard: Tracked<RequestShard>, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).good_req(req, req_shard@),
        req.input is SyncInput,
        old(self).ready_for_user_operation(),
    ensures
        self.inv_api(api),
        self.ready_for_user_operation(),
    {
        let ghost old_satisfied_reqs = old(self).sync_requests.satisfied_reqs@;
        let ghost old_deferred_reqs = old(self).sync_requests.deferred_reqs@;
        assert({
            &&& forall |i| #![auto] 0 <= i < old_satisfied_reqs.len() ==> old_satisfied_reqs[i].id != req.id
            &&& forall |i| #![auto] 0 <= i < old_deferred_reqs.len() ==> old_deferred_reqs[i].id != req.id
        }) by {
            self.system_inv_sync_request_fresh_id(req, req_shard);
        }

        // Consume the shard to convert into model state
        let ghost pre_state = self.model@.value();
        let ghost version = pre_state.state.ephemeral_map().seq_end;
        let ghost post_state = ConcreteProgramModel {
            state: AtomicState{
                sync_req_map: pre_state.state.sync_req_map.insert(req.id, version),
                ..pre_state.state}
        };

        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof { tracked_swap(self.model.borrow_mut(), &mut model); }

        let tracked new_reply_token = self.instance.borrow().accept_sync_request(
            KVStoreTokenized::Label::RequestSyncOp{sync_req_id: req.id},
            post_state,
            &mut model,
            req_shard.get(),
        );
        self.model = Tracked(model);

        self.sync_requests.deferred_reqs.push(req);

        // trigger prior inv, element by element
        assert forall |r| #![auto] self.sync_requests.deferred_reqs@.contains(r) implies r.input is SyncInput by {
            if r != req { assert( old(self).sync_requests.deferred_reqs@.contains(r) ); }
        }

//         assert( self.inv_api(api) );
        self.maybe_launch_superblock(api);
    }

    pub exec fn maybe_launch_superblock(&mut self, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).ready_for_user_operation(),
    ensures
        self.inv_api(api),
        self.ready_for_user_operation(),
    {
        if self.sync_requests.deferred_reqs.len() == 0 {
            // nobody is waiting for a superblock send.
        } else if self.sync_requests.satisfied_reqs.len() == 0 {
            self.send_superblock(api);
        } else {
            // Someone is waiting to start a sync, but a superblock is already in-flight; we'll
            // consider this again when the disk response lands back here.
        }
    }

    exec fn send_superblock(&mut self, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).sync_requests.satisfied_reqs.len() == 0,
        old(self).sync_requests.deferred_reqs.len() > 0,
        old(self).ready_for_user_operation(),
    ensures
        self.inv_api(api),
        self.ready_for_user_operation(),
    {
//         proof { self.system_inv_implies_atomic_state_wf(); }
// 
//         assert( self.journal@@.wf() );
//         assert( self.journal@.wf() );
//         let version = self.journal.seq_end();
//         let ghost pre_sb = self.state().ephemeral_sb();
// 
//         assert(self.journal@@.discard_recent(version as nat) == self.journal@@);
// 
//         // sync/truncate policy
//         if self.sync_counter < 3 {
//             self.sync_counter = self.sync_counter + 1;
//         } else {
//             self.sync_counter = 1;
//         }
//         // persist map if the counter says so and if there's actually journal messages to apply
//         let sync_map = (self.sync_counter % 3) == 0 && self.journal.msg_history.len() > 0;
//         let ghost pre_sb = self.state().sync_sb(sync_map);
// 
//         let mut raw_page = Vec::new();
//         let mut tmp_store = VecMap::new();
//         let mut tmp_journal = JournalImpl::new();
// 
//         let mut sb;
//         if sync_map { // sync the ephemeral map with an empty journal
//             api.log("send_superblock: sync store and truncate the journal");
//             tmp_journal.seq_start = version;
//             std::mem::swap(&mut self.store, &mut tmp_store);
//     
//             sb = ISuperblock{
//                 journal: tmp_journal,
//                 store: tmp_store.v,
//             };
//             raw_page = DiskLayout::new().marshall(&sb);
// 
//             let ISuperblock{store: mut tmp_store_v, /*store: mut tmp_store,*/ ..} = sb;
//             tmp_store.v = tmp_store_v;
//             std::mem::swap(&mut self.store, &mut tmp_store);
//             assert( sb@@ == pre_sb );
// 
//             self.in_flight = Some(InFlight{
//                 new_boundary_lsn: version,
//                 new_store: self.store.clone(),
//             });
//         } else { // sync the ephemeral journal with the same persistent map
//             api.log("send_superblock: journal sync only");
//             std::mem::swap(&mut self.journal, &mut tmp_journal);
//             std::mem::swap(&mut self.persistent_store, &mut tmp_store);
// 
//             sb = ISuperblock{
//                 journal: tmp_journal,
//                 store: tmp_store.v,
//             };
//             raw_page = DiskLayout::new().marshall(&sb);
// 
//             let ISuperblock{journal: mut tmp_journal, store: mut tmp_store_v, ..} = sb;
//             std::mem::swap(&mut self.journal, &mut tmp_journal);
//             tmp_store.v = tmp_store_v;
//             std::mem::swap(&mut self.persistent_store, &mut tmp_store);
// 
// //             proof {
// //                 sb@.final_stamped_map_ensures();
// //             }
//             self.in_flight = Some(InFlight{
//                 new_boundary_lsn: self.journal.seq_start,
//                 new_store: self.persistent_store.clone(),
//             });
// 
//             assert(self.journal@@.discard_recent(version as nat).discard_old(self.journal.seq_start as nat) 
//                 == self.journal@@.discard_recent(version as nat)); // ext_eq
//         }
//         let ghost new_persistent_map = sb.store@;
// 
//         let req_id_perm = Tracked( api.send_disk_request_predict_id() );
//         let ghost disk_req_id = req_id_perm@;
//         let disk_request = IDiskRequest::WriteReq{to: superblock_addr(), data: raw_page};
//         let ghost disk_event = DiskEvent::ExecuteSyncBegin{req: disk_request@, req_id: disk_req_id, sync_map};
//         let ghost disk_reqs = multiset_map_singleton(disk_req_id, disk_request@);
//         let ghost info = ProgramDiskInfo{ reqs: disk_reqs, resps: Multiset::empty() };
// 
//         let ghost inflight_info = InflightInfo{
// //             new_persistent_map: ASuperblock::map_to_kmmap(new_persistent_map),
//             new_persistent_map: arbitrary(),
//             journal_version: version as nat,
//             req_id: disk_req_id
//         };
//         let ghost post_state = ConcreteProgramModel {
//             state: AtomicState{
//                 in_flight: Some(inflight_info),
//                 ..old(self).state()}
//         };
// 
//         let tracked empty_disk_responses: DiskRespShard = DiskRespShard::empty(self.instance_id());
// 
//         let ghost lbl = KVStoreTokenized::Label::DiskOp{
//                 disk_request_tuples: disk_reqs,
//                 disk_response_tuples: empty_disk_responses.multiset(),
//             };
// 
//         let ghost info = ProgramDiskInfo{
//                 reqs: lbl->disk_request_tuples,
//                 resps: lbl->disk_response_tuples,
//             };
// 
//         proof {
//             assert( disk_reqs == Multiset::singleton(
//                 (disk_event.arrow_ExecuteSyncBegin_req_id(),
//                 disk_request@))
//             );   // extn
//             assert( DiskLayout::spec_new().spec_parse(disk_request@->data) == pre_sb );
//             assert( AtomicState::disk_transition(self.state(), post_state.state, disk_event, info.reqs, info.resps) );  // witness
//         }
// 
//         // // take the transition, get the token
//         let tracked mut model = KVStoreTokenized::model::arbitrary();
//         proof { tracked_swap(self.model.borrow_mut(), &mut model); }
//         let tracked new_reply_token = self.instance.borrow().disk_transitions(
//             lbl,
//             post_state,
//             &mut model,
//             empty_disk_responses,
//         );
//         self.model = Tracked(model);
//         std::mem::swap(&mut self.sync_requests.satisfied_reqs, &mut self.sync_requests.deferred_reqs);
// 
//         assert( new_reply_token.multiset() == multiset_map_singleton(req_id_perm@, disk_request@) );    // extn
//         api.send_disk_request(disk_request, req_id_perm, Tracked(new_reply_token));
    }

    exec fn deliver_inflight_replies(&mut self, ready_reqs: &mut Vec<Request>, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).sync_reqs_in_version(old(ready_reqs)@, old(self).state().persistent_journal_seq_end),
        // can't break in-flight inv because there aren't any satisfied_reqs during this call
        old(self).sync_requests.satisfied_reqs@.len()==0,
        Self::sync_req_lists_mutually_unique(old(ready_reqs)@, old(self).sync_requests.deferred_reqs@),
        old(self).ready_for_user_operation(),
    ensures
        self.inv_api(api),
        self.ready_for_user_operation(),
    {
        assert( ready_reqs@.take(ready_reqs@.len() as int) == ready_reqs@ ); // extn
        loop
        invariant
            self.inv_api(api),
            self.ready_for_user_operation(),
            self.sync_reqs_in_version(ready_reqs@, old(self).state().persistent_journal_seq_end),
            self.state().persistent_journal_seq_end == old(self).state().persistent_journal_seq_end,
            self.sync_requests.satisfied_reqs@.len()==0,
            ready_reqs@.len() <= old(ready_reqs)@.len(),
            old(self).sync_requests.deferred_reqs@ == self.sync_requests.deferred_reqs@,
            Self::sync_req_lists_mutually_unique(old(ready_reqs)@, old(self).sync_requests.deferred_reqs@),   // mutter mutter
            ready_reqs@ == old(ready_reqs)@.take(ready_reqs@.len() as int),
        decreases ready_reqs.len(),
        {
            match ready_reqs.pop()
            {
                Some(req) => {
                    assert( ready_reqs@ == old(ready_reqs)@.take(ready_reqs@.len() as int) );   // extn
                    self.send_sync_response(req, api)
                },
                None => break,
            }
        }
    }

    // Every request in reqs is a Sync request and is satisfiable by version_num
    closed spec fn sync_reqs_in_version(&self, reqs: Seq<Request>, version_num: LSN) -> bool
    {
        &&& forall |i| #![auto] 0<=i<reqs.len() ==> {
            &&& reqs[i].input is SyncInput
            &&& self.sync_req_in_version(reqs[i].id, version_num)
        }
        &&& forall |i,j| #![auto] 0 <= i < reqs.len() && 0 <= j < reqs.len() && i!=j ==> reqs[i].id != reqs[j].id
    }

    // sync req ID is in the sync_req map and is satisfiable by LSN version_num
    closed spec fn sync_req_in_version(&self, id: ID, version_num: LSN) -> bool
    {
        &&& self.state().sync_req_map.contains_key(id)
        &&& self.state().sync_req_map[id] <= version_num
    }

    closed spec fn sync_req_lists_mutually_unique(listi: Seq<Request>, listj: Seq<Request>) -> bool
    {
        forall |i:int, j:int| #![auto] 0 <= i < listi.len() && 0 <= j < listj.len() ==> listi[i].id != listj[j].id
    }

    closed spec fn no_matching_sync_req_id(self, id: ID) -> bool
    {
        &&& (forall |j| #![auto] 0<=j<self.sync_requests.satisfied_reqs@.len() ==> self.sync_requests.satisfied_reqs@[j].id!=id)
        &&& (forall |j| #![auto] 0<=j<self.sync_requests.deferred_reqs@.len() ==> self.sync_requests.deferred_reqs@[j].id!=id)
    }

    exec fn send_sync_response(&mut self, req: Request, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        req.input is SyncInput,
        old(self).sync_req_in_version(req.id, old(self).state().persistent_journal_seq_end),
        old(self).no_matching_sync_req_id(req.id),
        old(self).ready_for_user_operation(),
    ensures
        self.inv_api(api),
//         self.store == old(self).store,
//         self.sync_requests == old(self).sync_requests,
        (self.state() == AtomicState{
            sync_req_map: old(self).state().sync_req_map.remove(req.id),
            ..old(self).state()
        }),
        old(self).sync_requests.deferred_reqs@ == self.sync_requests.deferred_reqs@,
        self.ready_for_user_operation(),
    {
        // Convert the model state back into a shard
        let ghost pre_state = self.model@.value();
        
        let ghost post_state = ConcreteProgramModel {
            state: AtomicState{
                sync_req_map: pre_state.state.sync_req_map.remove(req.id),
                ..pre_state.state}
        };

        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof { tracked_swap(self.model.borrow_mut(), &mut model); }

        assert(ConcreteProgramModel::next(pre_state, post_state,
                ProgramLabel::UserIO{
                    op: ProgramUserOp::DeliverSyncReply{sync_req_id: req.id}
                }
                ));
        let tracked reply_shard = self.instance.borrow().deliver_sync_reply(
            KVStoreTokenized::Label::ReplySyncOp{sync_req_id: req.id},
            post_state,
            &mut model,
        );
        self.model = Tracked(model);

        let reply = Reply{output: Output::SyncOutput, id: req.id};

        api.send_reply(reply, Tracked(reply_shard), true);
    }

    pub exec fn handle_user_request(&mut self, req: Request, req_shard: Tracked<RequestShard>, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).good_req(req, req_shard@),
        old(self).ready_for_user_operation(),
    ensures
        self.inv_api(api),
        self.ready_for_user_operation(),
    {
        match req.input {
            Input::NoopInput => self.handle_noop(req, req_shard, api),
            Input::PutInput{..} => self.handle_put(req, req_shard, api),
            Input::QueryInput{..} => self.handle_query(req, req_shard, api),
            Input::SyncInput{} => self.handle_sync_request(req, req_shard, api),
            Input::SimulateCrash{} => (),
        }
    }

    proof fn system_inv_response_implies_in_flight(self, disk_req_id: ID, i_disk_response: IDiskResponse, disk_response_token: Tracked<DiskRespShard>)
    requires
        self.i().recovery_state is RecoveryComplete,
        disk_response_token@.multiset() == multiset_map_singleton(disk_req_id, i_disk_response@),
    ensures
        i_disk_response is WriteResp,   // when RecoveryComplete, we never read again
        self.i().in_flight is Some,
        self.i().in_flight->0.req_id == disk_req_id,
    {
        open_system_invariant_disk_response::<ConcreteProgramModel, RefinementProof>(self.model, disk_response_token);
        multiset_map_singleton_ensures(disk_req_id, i_disk_response@);
        assert(disk_response_token@.multiset().contains((disk_req_id, i_disk_response@))); //trigger
        assume( false ); // something broke in connection to ConcreteSystem<AtomicState>?
    }

    proof fn system_inv_implies_atomic_state_wf(self)
    ensures
        self.state().wf()
    {
        let tracked empty_disk_responses:Tracked<KVStoreTokenized::disk_responses_multiset<ConcreteProgramModel>>
            = Tracked(KVStoreTokenized::disk_responses_multiset::empty(self.instance_id()));
        open_system_invariant_disk_response::<ConcreteProgramModel, RefinementProof>(self.model, empty_disk_responses);
    }

    proof fn system_inv_sync_request_fresh_id(self, req: Request, req_shard: Tracked<RequestShard>)
    requires
        self.i().recovery_state is RecoveryComplete,
        // TODO req ~~ req_shard?
    ensures
        !self.state().sync_req_map.dom().contains(req.id)
    {
        let system_model = open_system_invariant_user_request::<ConcreteProgramModel, RefinementProof>(self.model, req_shard);
        if self.state().sync_req_map.dom().contains(req.id) {
            // by fresh_id
            // we can only learn this during an accept_request transition
            // assert( !system_model.state().sync_requests.contains(req.id) );
        }
        // multiset_map_singleton_ensures(disk_req_id, i_disk_response@);
        // assert(disk_response_token@.multiset().contains((disk_req_id, i_disk_response@))); //trigger
        assume( false );   // fresh id stuff
    }

    // A reply to a superblock read only ever occurs as the first operation after reboot; those get
    // handled in-line by the recover procedure.

    // In normal operations, we will see write acknowledgements to superblock commits.
    pub exec fn handle_disk_superblock_write_response(&mut self, id: ID, disk_response: IDiskResponse, response_shard: Tracked<DiskRespShard>,
        api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).good_disk_response(id, disk_response, response_shard@),
        response_shard@.multiset() == multiset_map_singleton(id, disk_response@),
    ensures
        self.inv_api(api),
        self.ready_for_user_operation(),
    {
        let mut ready_reqs = vec![];
        std::mem::swap(&mut self.sync_requests.satisfied_reqs, &mut ready_reqs);
//         (ready_reqs,self.sync_requests.satisfied_reqs) = (self.sync_requests.satisfied_reqs,ready_reqs);

        // TODO(jialin): why do these Noop requests have ids? :v/ Because ... we have to know which
        // Noop a reply is for? Obviously?

        let ghost pre_state = self.model@.value();
        let ghost new_persistent_version = pre_state.state.in_flight->0.journal_version;

        // Use existence of a response + system model invariant to learn that we must have
        // known in_flight true when we got here.
        assert( self.in_flight is Some
            && self.model@.value().state.journal.status is Some
            ) by {
            open_system_invariant_disk_response_singleton::<ConcreteProgramModel, RefinementProof>(self.model, response_shard, id, disk_response@);
            assume( false );    // TODO(JL+jonh): Another spot where we lost open-invariant properties
        }
        assert( self.recovery_phase is ReadyForUserOperation );

        let mut in_flight = None;
        std::mem::swap(&mut self.in_flight, &mut in_flight);
        if let Some(InFlight{new_boundary_lsn, freshest_rec, new_persistent_lsn, new_store}) = in_flight {
            if self.journal.exec_seq_start() != new_boundary_lsn { // a new map is persisted
                self.persistent_store = new_store;
//                 self.journal.truncate_to(new_boundary_lsn);
//                 assert(self.journal@@ == old(self).journal@@.discard_old(new_boundary_lsn as nat)); // ext_eq

                // proof {
                //     assert(view_as_kmmap(self.store) ==
                //         map_plus_history(view_as_kmmap(self.persistent_store), self.journal@@));
                // }
              } else {
                assert(self.journal.seq_start() == new_boundary_lsn);
                assert(SuperblockTypes_v::map_to_kmmap(self.persistent_store@) == SuperblockTypes_v::map_to_kmmap(self.persistent_store@));
            }

            let ghost new_lsn_addr_index =
                lsn_addr_index_discard_up_to(pre_state.state.journal.status.unwrap().lsn_addr_index, new_boundary_lsn as LSN);
            
            // Here's a commit_complete step of AbstractCrashAwareMap:
            let ghost post_store = AbstractCrashAwareMap::State{
                persistent: old(self).state().store.in_flight.unwrap(),
                in_flight: None,
                ..old(self).state().store
            };
            let ghost post_state = ConcreteProgramModel{ state: AtomicState{
                in_flight: None,
                journal: CachedJournal::State {
                    snapshot: CachedJournal_v::JournalSnapShot{
                        boundary_lsn: new_boundary_lsn as LSN,
                        freshest_rec: freshest_rec,
                    },
                    status: Some(CachedJournal_v::JournalStatus{
                        lsn_addr_index: new_lsn_addr_index,
                        ..pre_state.state.journal.status.unwrap()
                    }),
                    ..pre_state.state.journal
                },
                store: post_store,
                persistent_journal_seq_end: new_persistent_lsn as LSN,
                ..pre_state.state
            }};
//             assert( pre_state.state.journal.wf() );
//             assert( post_state.state.journal.seq_start() == new_boundary_lsn );
//             assert( post_state.state.journal.seq_end() == pre_state.state.journal.status.unwrap().unmarshalled_tail.seq_end );
//             assert( new_boundary_lsn == old(self).in_flight.unwrap().new_boundary_lsn );
//             assert( old(self).in_flight.unwrap().new_boundary_lsn
//                 <= old(self).state().journal.status.unwrap().unmarshalled_tail.seq_start );
//             assert( new_boundary_lsn <= pre_state.state.journal.status.unwrap().unmarshalled_tail.seq_start );
//             assert( post_state.state.journal.seq_start() <= post_state.state.journal.seq_end() );
//             assert( post_state.state.journal.wf() );

            proof {
                // Learn this before we yoink model out of self
                assert( self.i().recovery_state is RecoveryComplete );
                self.system_inv_response_implies_in_flight(id, disk_response, response_shard);
            }

            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

            proof {
                let info = ProgramDiskInfo{ reqs: Multiset::empty(), resps: response_shard@.multiset() };
                let discard_addrs =
                    pre_state.state.journal.status.unwrap().lsn_addr_index.values() - new_lsn_addr_index.values();
                let disk_event = DiskEvent::ExecuteSyncEnd{ discard_addrs };

                assert( response_shard@.multiset() == Multiset::singleton((pre_state.state.in_flight->Some_0.req_id, DiskResponse::WriteResp{})) );    // extn

                assert( post_state.state.store.in_flight is None);
                assert( post_state.state.in_flight is None );
                assert( post_state.state.store.in_flight is Some == post_state.state.in_flight is Some );
//                 assert( post_state.state.journal.seq_end() == post_state.state.persistent_map().seq_end );
                assume(false); // TODO(jonh) left off here
                assert( post_state.state.wf() );
                assert( AbstractCrashAwareMap::State::next(pre_state.state.store, post_state.state.store, AbstractCrashAwareMap::Label::CommitCompleteLabel{}) );
                assume(false);
                let journal_lbl = CachedJournal::Label::DiscardOld{
                    start_lsn: post_state.state.persistent_map().seq_end,
                    require_end: post_state.state.ephemeral_map().seq_end, // requires journal to still line up with ephemeral map, might not be needed
                    discard_addrs,
                };
                assert( CachedJournal::State::next(pre_state.state.journal, post_state.state.journal, journal_lbl) );
                assert( AtomicState::disk_transition(
                    pre_state.state, post_state.state, disk_event, info.reqs, info.resps) );    // witness
            }
        
            let tracked empty_disk_requests = DiskReqShard::empty(self.instance_id());
            let tracked new_reply_token = self.instance.borrow().disk_transitions(
                KVStoreTokenized::Label::DiskOp{
                    disk_request_tuples: empty_disk_requests.multiset(),
                    disk_response_tuples: response_shard@.multiset()},
                post_state,
                &mut model,
                response_shard.get(),
            );

            self.model = Tracked(model);

            assert(self.inv());
            self.deliver_inflight_replies(&mut ready_reqs, api);

            // maybe launch another superblock
            self.maybe_launch_superblock(api);
        } else {
            api.log("handle_disk_response: received non superblock related disk response");
            assert(false);
        }
    }

    // In normal operations, we will see write acknowledgements to cache IO.
    exec fn handle_disk_cache_response(&mut self, id: ID, disk_response: IDiskResponse, response_shard: Tracked<DiskRespShard>,
        api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).good_disk_response(id, disk_response, response_shard@),
        response_shard@.multiset() == multiset_map_singleton(id, disk_response@),
    ensures
        self.inv_api(api),
        self.recovery_phase.advances(old(self).recovery_phase),
    {
    }

    exec fn handle_disk_response(&mut self, id: ID, disk_response: IDiskResponse, response_shard: Tracked<DiskRespShard>,
        api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        !(old(self).recovery_phase is FetchingSuperblock),
        old(self).good_disk_response(id, disk_response, response_shard@),
        response_shard@.multiset() == multiset_map_singleton(id, disk_response@),
    ensures
        self.inv_api(api),
        self.recovery_phase.advances(old(self).recovery_phase),
    {
        match self.outstanding_requests.get(&id) {
            None => {
                assert(false) by {
                    // TODO apply a system invariant: every disk response matches an outstanding
                    // disk request
                    assume(false);
                }
            }
            Some(disk_request) => {
                if disk_request.exec_addr() == superblock_addr() {
                    self.handle_disk_superblock_write_response(id, disk_response, response_shard, api);
                } else {
                    self.handle_disk_cache_response(id, disk_response, response_shard, api);
                }
            }
        }
    }

    fn recover_fetch_superblock(&mut self, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv(),
        old(self).recovery_phase is FetchingSuperblock,
        old(self).instance_id() == old(api).instance_id(),
//         old(self).state().recovery_state is Begin,   // delete?
    ensures
        self.inv(),
        self.instance_id() == api.instance_id(),
        self.recovery_phase is ReadingJournalIndex,
    {
        api.log("issue superblock read");
        { // braces to scope variables used in this step
            let ghost pre_state = self.model@.value();
            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

            let disk_req = IDiskRequest::ReadReq{from: superblock_addr() };
            let tracked empty_disk_responses = MultisetToken::empty(self.instance_id());

            let ghost post_state = ConcreteProgramModel{state: AtomicState { recovery_state: RecoveryState::AwaitingSuperblock, ..pre_state.state }};

            let req_id_perm = Tracked( api.send_disk_request_predict_id() );

            let ghost disk_event = DiskEvent::InitiateRecovery{req_id: req_id_perm@};
            // let ghost disk_req_id = req_id_perm@;
            let ghost disk_response_tuples = Multiset::empty();
            let ghost disk_request_tuples = multiset_map_singleton(req_id_perm@, disk_req@);
            // proof { multiset_map_singleton_ensures(req_id_perm@, disk_req@); }
            proof {
                let info = ProgramDiskInfo{
                    reqs: disk_request_tuples,
                    resps: disk_response_tuples,
                };
                assert(AtomicState::disk_transition(
                    pre_state.state, post_state.state, disk_event, info.reqs, info.resps));
                assert(ConcreteProgramModel::valid_disk_transition(pre_state, post_state, info));
                assert(ConcreteProgramModel::next(pre_state, post_state, ProgramLabel::DiskIO{info}));
            }

            let tracked disk_request_tokens = self.instance.borrow().disk_transitions(
                KVStoreTokenized::Label::DiskOp{
                    disk_request_tuples,
                    disk_response_tuples,
                },
                post_state,
                &mut model,
                empty_disk_responses,
            );

            assert( model.value() == post_state );

            // this way of composition feels like it can be easily cheated?
            // if we really want to we can try to
            // let ghost disk_lbl = AsyncDisk::Label::DiskOps{
            //         requests: Map::empty().insert(req_id_perm@, disk_req@),
            //         responses: Map::empty()
            // };
            // assert( disk_lbl->responses == multiset_to_map(disk_response_tuples) ); // extn equality

            // this models external_diskop with the disk label
            let disk_req_id = api.send_disk_request(disk_req, req_id_perm, Tracked(disk_request_tokens));
            self.model = Tracked(model);
        }

        ////////////////////////////////////////
        assert( self.model@.value().state.recovery_state is AwaitingSuperblock );
        ////////////////////////////////////////
        api.log("await superblock response");
        { // braces to scope variables used in this step
            let ghost pre_state = self.model@.value();
            let disk_resp = IDiskRequest::ReadReq{from: superblock_addr() };
            let DiskResponseRecord{id: disk_req_id, disk_response: i_disk_response, token: disk_response_token}
                = api.blocking_receive_disk_response();

            let raw_page = match i_disk_response {
                IDiskResponse::ReadResp{data} => data,
                IDiskResponse::WriteResp{} => {
                    proof { self.system_inv_cannot_receive_write_response_during_recovery(disk_req_id, i_disk_response, disk_response_token); };
                    unreached()
                }
            };

            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

            let layout = DiskLayout::new();
            let superblock: ISuperblock = layout.parse(&raw_page);
            Self::debug_print(&superblock);

            assert( VecMap::unique_keys(superblock.store@) ) by {
                assume( false );    // get this from a system invariant about the superblock on the disk
            }
            self.persistent_store = VecMap::from_vec(superblock.store);

            self.journal = JournalImpl::new(superblock.journal_snapshot);

            let mut i = 0;
            // TODO: why do we need to clone here? Try removing.
            self.store = self.persistent_store.clone();
            // Disk invariant: store must have agreed with journal start
            // (before we begin advancing it during recovery).
            self.store_lsn = self.journal.exec_seq_start();

            // Compute the next ghost model and transition our token
            let ghost psb = DiskLayout::spec_new().spec_parse(raw_page@);
            let ghost post_state = ConcreteProgramModel{
                state: AtomicState {
                    recovery_state: RecoveryState::SuperblockAvailable,                    
                    journal: self.journal@,
                    store: AbstractCrashAwareMap::State{
                        persistent: psb.store,
                        ephemeral: AbstractCrashAwareMap_v::Ephemeral::Known {
                            v: AbstractMap::State { stamped_map: psb.store }
                        },
                        in_flight: None,
                    },
                    // TODO: don't we know the pj seqend right now?
                    persistent_journal_seq_end: arbitrary(),
                    in_flight: None,
                    sync_req_map: Map::empty(),
                    ..pre_state.state
                }
            };

            let ghost disk_response_tuples = multiset_map_singleton(disk_req_id, i_disk_response@);

            let ghost disk_event = DiskEvent::SuperblockRecovery{req_id: disk_req_id, raw_page: raw_page@};
            let ghost disk_request_tuples = Multiset::empty();

            proof {
                // Something about constructing a ProgramDiskInfo object is necessary to trigger a
                // pattern match in the disk_transitions preconditions below.
                let info = ProgramDiskInfo{
                    reqs: disk_request_tuples,
                    resps: disk_response_tuples,
                };
                assert(AtomicState::disk_transition(
                    pre_state.state, post_state.state, disk_event, info.reqs, info.resps)); // step witness
            }

            let tracked disk_request_tokens = self.instance.borrow().disk_transitions(
                KVStoreTokenized::Label::DiskOp{
                    disk_request_tuples,
                    disk_response_tuples,
                },
                post_state,
                &mut model,
                disk_response_token.get(),
            );
            self.model = Tracked(model);
        }

        api.log("recovery phase now ReadingJournalIndex");
        self.recovery_phase = RecoveryPhase::ReadingJournalIndex;

        assert( self.inv() );
    }

    fn recover_read_journal_index(&mut self, api: &mut ClientAPI<ConcreteProgramModel>) -> (progress: bool)
    requires
        old(self).inv_api(old(api)),
        old(self).recovery_phase is ReadingJournalIndex,
    ensures
        self.inv_api(api),
        self.recovery_phase is ReadingJournalIndex || self.recovery_phase is ApplyingJournalToRecoverEphemeralMap,
    {
        assert( self.journal.wf() );
        let (progress,ready) = self.journal.recover_index_step(&mut self.cache);
        if ready {
            self.recovery_phase = RecoveryPhase::ApplyingJournalToRecoverEphemeralMap;

            let ghost pre_state = self.i();
            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

            let ghost post_state = ConcreteProgramModel{
                state: AtomicState {
                    recovery_state: RecoveryState::JournalIndexComplete,
                    journal: self.journal@,
                    persistent_journal_seq_end: arbitrary(),
                    in_flight: None,
                    sync_req_map: Map::empty(),
                    ..pre_state
                }
            };

            proof {
                assert(AtomicState::internal_transitions(pre_state, post_state.state)) by {
                    // AtomicState internal transition is currently a "silly" noop; needs to expand
                    // to include journal internal
                    assume( false ); // TODO
                };
            }

            let tracked new_reply_token = self.instance.borrow().internal(
                KVStoreTokenized::Label::InternalOp{},
                post_state,
                &mut model,
            );
            self.model = Tracked(model);

            assert( self.i().recovery_state is JournalIndexComplete );
        }
        progress
    }

    fn recover_apply_journal_to_recover_ephemeral_map(&mut self, api: &mut ClientAPI<ConcreteProgramModel>) -> (progress: bool)
    requires
        old(self).inv_api(old(api)),
        old(self).recovery_phase is ApplyingJournalToRecoverEphemeralMap,
    ensures
        self.inv_api(api),
        self.recovery_phase is ReadyForUserOperation,
    {
        if self.store_lsn < self.journal.exec_seq_end() {
            Self::todo_placeholder();   // Go restore more blocks from journal
            // this branch may return progress false if we are waiting for
            // disk IO to fetch the next page.
        }
        {
            self.recovery_phase = RecoveryPhase::ReadyForUserOperation;

            let ghost pre_state = self.i();
            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

//             assert( model.value()@ == self.state() )@;
            assert( model.value() == ConcreteProgramModel { state: pre_state } );
            let ghost post_state = ConcreteProgramModel{
                state: AtomicState {
                    recovery_state: RecoveryState::RecoveryComplete,
                    journal: self.journal@,
                    persistent_journal_seq_end: arbitrary(),
                    in_flight: None,
                    sync_req_map: Map::empty(),
                    ..pre_state
                }
            };

            proof {
                assert(AtomicState::internal_transitions(pre_state, post_state.state)) by {
                    assume( false ); // TODO
                };
            }

            assert( ConcreteProgramModel::next(
                    ConcreteProgramModel { state: pre_state },
                    post_state,
                    ProgramLabel::Internal{}) );
//             assert( model.instance_id() == (self.instance@).id() );
            assert( model.value() == ConcreteProgramModel { state: pre_state } );
            let tracked new_reply_token = self.instance.borrow().internal(
                KVStoreTokenized::Label::InternalOp{},
                post_state,
                &mut model,
            );
            self.model = Tracked(model);

            assert( self.i().recovery_state is RecoveryComplete  );
            assert( self.inv_api(api) );
        }
        true
    }

    #[verifier::external_body]
    fn todo_placeholder()
        ensures false
    {
        panic!();
    }

    #[verifier::external_body]
    fn exec_mkfs(api: &mut ClientAPI<ConcreteProgramModel>)
    ensures api == old(api) // liiiies
    {
        let raw_page = DiskLayout::new().exec_mkfs();
//         Self::debug_print_raw_page(&raw_page);
        let disk_request = IDiskRequest::WriteReq{to: superblock_addr(), data: raw_page};
        let req_id_perm = Tracked( api.send_disk_request_predict_id() );
        let tracked new_reply_token = arbitrary();
        api.send_disk_request(disk_request, req_id_perm, Tracked(new_reply_token));

        // absorb the write response
        match api.blocking_receive_disk_response() {
            DiskResponseRecord{disk_response: IDiskResponse::WriteResp{..}, ..} => {
                api.log("mkfs acknowledged")
            }
            _ => { panic!(); }
        };
    }

    #[verifier::external_body]
    fn debug_print_raw_page(raw_page: &Vec<u8>)
    {
        println!("raw_page: {:?} (len {:?})", raw_page, raw_page.len());
    }

    #[verifier::external_body]
    fn debug_print<T: std::fmt::Debug>(t: &T)
    {
        println!("{:?}", t);
    }
}

impl KVStoreTrait for Implementation {
    type ProgramModel = ConcreteProgramModel;
    type Proof = RefinementProof;

    closed spec fn wf_init(self) -> bool {
        &&& self.inv_recover()
        &&& self.state().recovery_state is Begin
    }

    closed spec fn instance_id(self) -> InstanceId
    {
        self.instance@.id()
    }

    fn new() -> (out: Self)
        ensures out.wf_init()
    {
        let tracked (
            Tracked(instance),
            Tracked(model),         // non sharded model
            Tracked(requests),      // request perm map (multiset), empty
            Tracked(replies),       // reply perm map (multiset), empty
            Tracked(disk_requests),
            Tracked(disk_responses),
        ) = KVStoreTokenized::Instance::initialize(ConcreteProgramModel{state: AtomicState::init(0)});

        // TODO maybe another Option<> wrapper?
        let placeholder_snapshot = JournalSnapshot{
            boundary_lsn: 0, freshest_rec: None, };
        let selff = Implementation{
            recovery_phase: RecoveryPhase::FetchingSuperblock,
            sync_counter: 0,
            store: new_empty_vec_map(),
            store_lsn: 7,
            journal: JournalImpl::new(placeholder_snapshot),
            cache: CacheImpl::new(/*100*/),
            in_flight: None,
            persistent_store: new_empty_vec_map(),
            // persistent_version: 0,
            model: Tracked(model),
            instance: Tracked(instance),
            sync_requests: SyncRequestBuffer::new_empty(),
            outstanding_requests: HashMapWithView::new(),
        };
        selff
    }

    fn kvstore_mkfs(&mut self, mut api: ClientAPI<Self::ProgramModel>)
    {
        Self::exec_mkfs(&mut api);
    }

    #[verifier::exec_allows_no_decreases_clause]    // main loop doesn't terminate
    fn kvstore_main(&mut self, mut api: ClientAPI<Self::ProgramModel>)
    {
        api.log("knstore_main begins");
        self.recover_fetch_superblock(&mut api);

        let debug_print = true;
        loop
        invariant
            self.inv_api(&api),
            !(self.recovery_phase is FetchingSuperblock),
        {
            // "Progress" means some step changed the system state, so maybe another step occurring
            // right away would be productive, say because a queued work item is now runnable. If
            // no steps make progress, we're waiting on IO, so we may as well sleep a little
            // waiting for that IO to arrive.
            let mut progress = false;
            api.log("main loop");

            Self::debug_print(&self.recovery_phase);
            match api.receive_disk_response() {
                None => {},
                Some(rec) => {
                    progress = true;
                    self.handle_disk_response(rec.id, rec.disk_response, rec.token, &mut api);
                }
            }
            match self.recovery_phase {
                RecoveryPhase::FetchingSuperblock => {
                    assert(false);
                }
                RecoveryPhase::ReadingJournalIndex => {
                    progress = self.recover_read_journal_index(&mut api);
                }
                RecoveryPhase::ApplyingJournalToRecoverEphemeralMap => {
                    progress = self.recover_apply_journal_to_recover_ephemeral_map(&mut api);
                }
                RecoveryPhase::ReadyForUserOperation => {
                    match api.receive_request(debug_print) {
                        None => {},
                        Some(rec) => {
                            progress = true;
                            match rec.request.input {
                                Input::SimulateCrash => {
                                // End this main thread so the trusted main can restart us "after the
                                // crash" to exercise the recovery path.
                                return;
                                }
                                _ => {
                                    self.handle_user_request(rec.request, rec.token, &mut api);
                                }
                            }
                        }
                    }
                }
            }
            if !progress {
                api.log("sleeping");
                api.sleep_a_little();
            }
        }
    }
}

pub fn new_empty_vec_map() -> (out: VecMap<Key,Value>)
ensures
    out.wf(),
    out@.is_empty(),
{
    // verus/source/vstd/std_specs/hash.rs says this is the best we can do right now
    assume( obeys_key_model::<Key>() );
    VecMap::new()
}

// // Convert overflow into a liveness failure
// #[verifier::exec_allows_no_decreases_clause]
// pub fn increment(x: u64) -> (y: u64)
// ensures y == x + 1
// {
//     if x == u64::MAX { loop {} }
//     x + 1
// }

}
