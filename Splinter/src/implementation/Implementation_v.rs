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
use crate::implementation::Cache_v::Cache;

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
    // requests enter here
    buffered_reqs: Vec<Request>,
    
    // This field is meaningless if send_superblock doesn't have journal cleaning IO activity
    // outstanding (which is connected to a nonempty journal_cleaning_reqs). Make it an Option
    // and express this comment as an invariant?
    journal_cleaning_target_lsn: ILsn,

    // every sync req in this buffer has lsn <= journal_cleaning_target_lsn
    journal_cleaning_reqs: Vec<Request>,

    // reqs in here will be satisfied when in-flight superblock lands (their lsn <= in flight journal seq_end)
    superblocking_reqs: Vec<Request>,
}

impl SyncRequestBuffer {
    closed spec fn wf(self, instance_id: InstanceId) -> bool
    {
        &&& forall |r| #![auto] self.buffered_reqs@.contains(r) ==> {
            &&& r.input is SyncInput
        }
        &&& forall |r| #![auto] self.journal_cleaning_reqs@.contains(r) ==> {
            &&& r.input is SyncInput
        }
        &&& forall |r| #![auto] self.superblocking_reqs@.contains(r) ==> {
            &&& r.input is SyncInput
        }
    }

    fn new_empty() -> (out: Self)
    ensures
        !out.in_flight(),
        out.buffered_reqs@.len() == 0,
    {
        SyncRequestBuffer{
            buffered_reqs: vec![],
            journal_cleaning_target_lsn: 0,
            journal_cleaning_reqs: vec![],
            superblocking_reqs: vec![],
        }
    }

    closed spec fn in_flight(self) -> bool {
        &&& self.superblocking_reqs.len() > 0
    }

    fn exec_in_flight(&self) -> (out: bool)
    ensures self.in_flight() == out
    {
        &&& self.superblocking_reqs.len() > 0
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
    freshest_rec: Option<IAddress>,
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

enum SuperblockMotivation {
    PushMap,
    PushJournal,
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
        &&& self.sync_requests.buffered_reqs@.len() == 0
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
            &&& self.sync_reqs_in_version(self.sync_requests.superblocking_reqs@, sync_version)
        })

        &&& self.sync_requests.wf(self.instance@.id())
        &&& self.sync_reqs_in_version(self.sync_requests.buffered_reqs@, self.version())
        &&& self.sync_requests.journal_cleaning_target_lsn <= self.version()
        &&& self.sync_reqs_in_version(self.sync_requests.journal_cleaning_reqs@, self.sync_requests.journal_cleaning_target_lsn as nat)
        &&& Self::sync_req_lists_mutually_unique(self.sync_requests.superblocking_reqs@, self.sync_requests.buffered_reqs@)
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
        let ghost old_superblocking_reqs = old(self).sync_requests.superblocking_reqs@;
        let ghost old_buffered_reqs = old(self).sync_requests.buffered_reqs@;
        assert({
            &&& forall |i| #![auto] 0 <= i < old_superblocking_reqs.len() ==> old_superblocking_reqs[i].id != req.id
            &&& forall |i| #![auto] 0 <= i < old_buffered_reqs.len() ==> old_buffered_reqs[i].id != req.id
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

        self.sync_requests.buffered_reqs.push(req);

        // trigger prior inv, element by element
        assert forall |r| #![auto] self.sync_requests.buffered_reqs@.contains(r) implies r.input is SyncInput by {
            if r != req { assert( old(self).sync_requests.buffered_reqs@.contains(r) ); }
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
        Self::debug_print(&"maybe_launch_superblock...");
        if self.sync_requests.superblocking_reqs.len() > 0 {    // todo write as in_flight -- for journal truncation case
            Self::debug_print(&"  └─ another superblock in flight");
        } else {
            if self.sync_requests.journal_cleaning_reqs.len() == 0 {
                if self.sync_requests.buffered_reqs.len() == 0 {
                    Self::debug_print(&"  └─ nobody is waiting for a superblock send.");
                    return;
                }
                // "now" lsn is at least as new as than all the buffered reqs
                self.sync_requests.journal_cleaning_target_lsn = 7; // self.journal.exec_get_seq_end();
                std::mem::swap(&mut self.sync_requests.buffered_reqs, &mut self.sync_requests.journal_cleaning_reqs);
            }
            Self::debug_print(&"  └─ send_superblock");
            self.send_superblock(api, SuperblockMotivation::PushJournal);
        }
    }

    exec fn clean_journal_for_sync(&mut self, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).sync_requests.superblocking_reqs.len() == 0,
        old(self).sync_requests.journal_cleaning_reqs.len() == 0,
        old(self).sync_requests.buffered_reqs.len() > 0,
    ensures
        self.inv_api(api),
        self.ready_for_user_operation(),
    {
        // record journal current version as journal_cleaning_target_lsn,
        // move all reqs from buffered_reqs to journal_cleaning_reqs,
    }

    exec fn send_superblock(&mut self, api: &mut ClientAPI<ConcreteProgramModel>, motivation: SuperblockMotivation)
    requires
        old(self).inv_api(old(api)),
        // do we have room to send a superblock?
        old(self).in_flight is None,
        // this requirement nonsense for map-only (journal truncation) case:
        old(self).sync_requests.journal_cleaning_reqs.len() > 0,
        old(self).ready_for_user_operation(),
    ensures
        self.inv_api(api),
        self.ready_for_user_operation(),
    {
        proof { self.system_inv_implies_atomic_state_wf(); }

        assert( self.journal@.wf() );
        let version = self.journal.exec_seq_end();

//         assert(self.journal@@.discard_recent(version as nat) == self.journal@@);

        let mut raw_page = Vec::new();
        let mut tmp_store = VecMap::new();

        let mut sb;
        let mut self_in_flight;
        let ghost mut new_abstract_store;
        match motivation {
            SuperblockMotivation::PushMap => {
                // sync the ephemeral map with an empty journal
                api.log("send_superblock: sync store and truncate the journal");
                std::mem::swap(&mut self.store, &mut tmp_store);
        
                sb = ISuperblock{
                    journal_snapshot: JournalSnapshot::new_empty(version),
                    store: tmp_store.v,
                };
                raw_page = DiskLayout::new().marshall(&sb);

                let ISuperblock{store: mut tmp_store_v, /*store: mut tmp_store,*/ ..} = sb;
                tmp_store.v = tmp_store_v;
                std::mem::swap(&mut self.store, &mut tmp_store);
                
                // After swap-back: self.store.v@ == sb@.store (the Vec contents are the same)
                // sb.store was tmp_store.v which held old(self).store.v
                // After swap-back, self.store.v == old(self).store.v
                // And tmp_store_v came from sb.store, so they're all the same Vec
                proof {
                    assert( self.store.v@ == sb@.store );
                }

                self_in_flight = Some(InFlight{
                    new_boundary_lsn: version,
                    freshest_rec: None,
                    new_persistent_lsn: version,
                    new_store: self.store.clone(),
                });
                proof { new_abstract_store = self.i_ephemeral_store()->v.stamped_map; }
            },
            SuperblockMotivation::PushJournal => {
                // sync the ephemeral journal with the existing persistent map
                api.log("send_superblock: journal sync only");

                let ready = true; // self.journal.clean_for_commit(self.sync_requests.journal_cleaning_target_lsn);
                if !ready { return }

                assert( old(self).sync_requests.superblocking_reqs.len() == 0 );  // by in_flight is None invariant

                // Okay, the journal is clean up to the point of journal_cleaning_target_lsn, which
                // means the journal_cleaning_reqs are now eligible to be delivered in a
                // superblock.
                std::mem::swap(&mut self.sync_requests.superblocking_reqs, &mut self.sync_requests.journal_cleaning_reqs);

    //             std::mem::swap(&mut self.journal, &mut tmp_journal);
                std::mem::swap(&mut self.persistent_store, &mut tmp_store);

                sb = ISuperblock{
                    journal_snapshot: self.journal.get_snapshot(),
                    store: tmp_store.v,
                };
                api.log("sending this particular superblock: ");
                Self::debug_print(&sb);
                raw_page = DiskLayout::new().marshall(&sb);

                let ISuperblock{journal_snapshot: mut tmp_journal, store: mut tmp_store_v, ..} = sb;
    //             std::mem::swap(&mut self.journal, &mut tmp_journal);
                tmp_store.v = tmp_store_v;
                std::mem::swap(&mut self.persistent_store, &mut tmp_store);

                // After swap-back: self.persistent_store.v@ == sb@.store
                proof {
                    assert( self.persistent_store.v@ == sb@.store );
                }
                
                self_in_flight = Some(InFlight{
                    new_boundary_lsn: self.journal.exec_seq_start(),
                    freshest_rec: self.journal.get_snapshot().freshest_rec,
                    // TODO 7 placeholder: need to learn the persistent lsn described by freshest_rec
                    // (or by a freshest_rec None snapshot).
                    new_persistent_lsn: 7,
                    new_store: self.persistent_store.clone(),
                });
                proof { new_abstract_store = self.i_persistent_store(); }

    //             assert(self.journal@@.discard_recent(version as nat).discard_old(self.journal.seq_start as nat) 
    //                 == self.journal@@.discard_recent(version as nat)); // ext_eq
            },
        }

        // First step: freeze the map, via a cache internal step
        let ghost frozen_store = AbstractCrashAwareMap::State{
            in_flight: Some(new_abstract_store),
            ..old(self).state().store
        };
        let ghost state_after_freeze = AtomicState{
            store: frozen_store,
            ..old(self).state()
        };
        {
            let tracked mut model = KVStoreTokenized::model::arbitrary();
            let ghost pre_store = old(self).state().store;
            let ghost post_store = frozen_store;
            let ghost post_state = ConcreteProgramModel {
                state: state_after_freeze
            };

            proof {
                // Witness that AbstractCrashAwareMap::State::next holds via freeze_persistent_internal
                // (for the !sync_map case) or freeze_map_internal (for the sync_map case)
                let map_lbl = AbstractCrashAwareMap::Label::InternalLabel;
                
                reveal(AbstractCrashAwareMap::State::next_by);
                reveal(AbstractCrashAwareMap::State::next);
                reveal(AbstractMap::State::next_by);
                reveal(AbstractMap::State::next);
                assert( old(self).state().store == old(self).view_store() );  // trigger for ext eq
                
                match motivation {
                    SuperblockMotivation::PushMap => {
                        let new_map = pre_store.ephemeral->v;
                        assert( AbstractMap::State::next_by(pre_store.ephemeral->v, new_map,
                            AbstractMap::Label::FreezeAsLabel{stamped_map: new_abstract_store}, AbstractMap::Step::freeze_as()) ); // witness
                        assert( AbstractCrashAwareMap::State::next_by(pre_store, post_store, map_lbl,
                            AbstractCrashAwareMap::Step::freeze_map_internal(new_abstract_store, new_map)) ); // witness
                    },
                    SuperblockMotivation::PushJournal => {
                        assert( AbstractCrashAwareMap::State::next_by(pre_store, post_store, map_lbl,
                            AbstractCrashAwareMap::Step::freeze_persistent_internal()) );   // witness
                    },
                }
                
                tracked_swap(self.model.borrow_mut(), &mut model);
                self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp,
                    post_state,
                    &mut model,
                );
            }
            self.model = Tracked(model);
        }

        // Second step, which we can do right away because our store doesn't actually need to be
        // cleaned from the cache yet: send the superblock containing the frozen map.
        self.in_flight = self_in_flight;
        
        // Capture the branch-dependent equality for the proof later
        // In both branches: Some(new_abstract_store) == i_inflight_store()
        // This follows from clone() ensuring out == self
        proof {
            // In sync_map case:
            //   new_abstract_store = StampedMap{value: view_as_kmmap(self.store), seq_end: version}
            //   self.in_flight.unwrap().new_store = self.store.clone() == self.store
            //   self.in_flight.unwrap().new_boundary_lsn = version
            // In !sync_map case:
            //   new_abstract_store = StampedMap{value: view_as_kmmap(self.persistent_store), seq_end: seq_start}
            //   self.in_flight.unwrap().new_store = self.persistent_store.clone() == self.persistent_store
            //   self.in_flight.unwrap().new_boundary_lsn = seq_start
            assert( Some(new_abstract_store) == self.i_inflight_store() );
        }

        let ghost new_persistent_map = sb.store@;

        let req_id_perm = Tracked( api.send_disk_request_predict_id() );
        let ghost disk_req_id = req_id_perm@;
        let disk_request = IDiskRequest::WriteReq{to: superblock_addr(), data: raw_page};
//         let ghost disk_event = DiskEvent::ExecuteSyncBegin{req: disk_request@, req_id: disk_req_id/*, sync_map*/};
        let ghost disk_reqs = multiset_map_singleton(disk_req_id, disk_request@);
        let ghost info = ProgramDiskInfo{ reqs: disk_reqs, resps: Multiset::empty() };

        let ghost inflight_info = InflightInfo{
            journal_version: version as nat,
            req_id: disk_req_id
        };
        // pre-state for this transition is state_after_freeze (after the internal freeze step)
        let ghost post_state = ConcreteProgramModel {
            state: AtomicState{
                in_flight: Some(inflight_info),
                ..state_after_freeze}
        };

        let tracked empty_disk_responses: DiskRespShard = DiskRespShard::empty(self.instance_id());

        let ghost lbl = KVStoreTokenized::Label::DiskOp{
                disk_request_tuples: disk_reqs,
                disk_response_tuples: empty_disk_responses.multiset(),
            };

        let ghost info = ProgramDiskInfo{
                reqs: lbl->disk_request_tuples,
                resps: lbl->disk_response_tuples,
            };

        proof {
            // Now pre-state is state_after_freeze, which has store.in_flight = Some(new_abstract_store)
            // This satisfies commit_start's precondition
            assert( state_after_freeze.store.in_flight is Some );
            assert( state_after_freeze.in_flight is None );  // no superblock write in flight yet
            
// 200 lines of cursor's intermediate efforts completing this proof
//            // Build the witness for execute_sync_begin
//            let frozen_journal = sb@.journal;
//            let frozen_seq_end = version as nat;
//            let frozen_domain = Set::empty();  // TODO: actual journal page addresses
//            let reads = Map::empty();  // TODO: actual cache reads
//            
//            // Witness the disk transition via execute_sync_begin
//            let disk_event = DiskEvent::ExecuteSyncBegin{
//                req_id: disk_req_id,
//                req: disk_request@,
//                frozen_journal,
//                frozen_seq_end,
//                frozen_domain,
//                reads,
//            };
//            
//            // Prove preconditions of execute_sync_begin:
//            let pre = state_after_freeze;
//            let post = post_state.state;
//            
//            // 1. pre.client_ready() - inherited from old(self).state() since freeze doesn't change it
//            assert( pre.client_ready() );
//            
//            // 2. pre.in_flight is None - already asserted above
//            assert( pre.in_flight is None );
//            
//            // 3. AbstractCrashAwareMap::State::next(pre.store, post.store, CommitStartLabel)
//            //    commit_start requires pre.store.in_flight is Some (which we have after freeze)
//            //    and doesn't change the state, so post.store == pre.store
//            let map_lbl = AbstractCrashAwareMap::Label::CommitStartLabel{
//                new_boundary_lsn: frozen_journal.boundary_lsn};
//            reveal(AbstractCrashAwareMap::State::next_by);
//            reveal(AbstractCrashAwareMap::State::next);
//            // commit_start doesn't change state, so post.store == pre.store
//            assert( post.store == pre.store );
//            assert( pre.store.in_flight is Some );
//            assert( pre.store.ephemeral is Known );
//            // boundary_lsn constraints for commit_start:
//            //   pre.persistent.seq_end <= new_boundary_lsn
//            //   new_boundary_lsn == pre.in_flight.unwrap().seq_end
//            // Our frozen map is new_abstract_store, and we need its seq_end to match
//            assert( pre.store.in_flight.unwrap() == new_abstract_store );
//            
//            // frozen_journal.boundary_lsn == new_abstract_store.seq_end
//            // In sync_map case: both equal version
//            // In !sync_map case: both relate to journal.seq_start
//            assert( frozen_journal.boundary_lsn == new_abstract_store.seq_end ) by {
//                match motivation {
//                    SuperblockMotivation::PushMap => {
//                        // sb.journal_snapshot = JournalSnapshot::new_empty(version)
//                        // new_abstract_store = i_ephemeral_store()->v.stamped_map with seq_end = version
//                        assert( frozen_journal.boundary_lsn == version as nat );
//                        assert( new_abstract_store.seq_end == version as nat );
//                    },
//                    SuperblockMotivation::PushJournal => {
//                        // sb.journal_snapshot = self.journal.get_snapshot() = self.journal.snapshot
//                        // frozen_journal.boundary_lsn = self.journal.snapshot.boundary_lsn as LSN
//                        // new_abstract_store = i_persistent_store() with seq_end = journal.seq_start()
//                        // This equality should follow from journal invariants relating snapshot.boundary_lsn to seq_start()
//                        assume( frozen_journal.boundary_lsn == new_abstract_store.seq_end );
//                    },
//                }
//            };
//            
//            // pre.store.persistent.seq_end <= frozen_journal.boundary_lsn
//            // pre.store.persistent = old(self).state().store.persistent = view_store().persistent
//            // view_store().persistent.seq_end = i_persistent_store().seq_end = journal.seq_start()
//            assert( pre.store.persistent.seq_end <= frozen_journal.boundary_lsn ) by {
//                // Connect pre.store.persistent to view_store
//                assert( old(self).state().store == old(self).view_store() );
//                assert( pre.store.persistent == old(self).view_store().persistent );
//                assert( pre.store.persistent == old(self).i_persistent_store() );
//                
//                // In sync_map case: frozen_journal.boundary_lsn == version == journal.seq_end()
//                // We need: journal.seq_start() <= journal.seq_end() (always true)
//                // In !sync_map case: frozen_journal.boundary_lsn == snapshot.boundary_lsn
//                // We need: journal.seq_start() <= snapshot.boundary_lsn (journal invariant)
//                
//                // TODO: prove this from journal invariants
//                // For now, this follows from journal wellformedness
//                assume( pre.store.persistent.seq_end <= frozen_journal.boundary_lsn );
//            };
//            assert( AbstractCrashAwareMap::State::next_by(pre.store, post.store, map_lbl,
//                AbstractCrashAwareMap::Step::commit_start()) );
//            
//            // 4-5. Cache and Journal transitions
//            // First, establish that cache and journal don't change between pre and post
//            assert( pre.cache == old(self).state().cache );
//            assert( post.cache == old(self).state().cache );
//            assert( pre.cache == post.cache );
//            assert( pre.journal == old(self).state().journal );
//            assert( post.journal == old(self).state().journal );
//            assert( pre.journal == post.journal );
//            
//            // Cache::Access with empty reads/writes
//            // The proof requires showing that union_prefer_right with empty map is identity
//            reveal(Cache::State::next_by);
//            reveal(Cache::State::next);
//            
//            // Cache::Access with empty writes should be a no-op
//            // The proof requires showing: when writes is empty, write_slots is empty,
//            // updated_entries/status_map have empty domain, and union_prefer_right with
//            // empty map is identity. This requires a map identity lemma.
//            assume( Cache::State::next(pre.cache, post.cache,
//                Cache::Label::Access{reads: reads, writes: Map::empty()}) );
//            
//            // Cache::EvictableCheck with empty addrs is trivial - forall is vacuously true
//            assert( Cache::State::next_by(pre.cache, post.cache,
//                Cache::Label::EvictableCheck{addrs: frozen_domain},
//                Cache::Step::evictable()) ) by {
//                assert( frozen_domain =~= Set::<Address>::empty() );
//                // The evictable transition doesn't update any state, just checks conditions
//                // With empty addrs, the forall is vacuously satisfied
//            };
//            
//            // Journal FreezeForCommit - more complex
//            assume( CachedJournal::State::next(pre.journal, post.journal,
//                CachedJournal::Label::FreezeForCommit{
//                    frozen: frozen_journal, frozen_seq_end, frozen_domain, 
//                    reads: to_journal_reads(reads)}) );
//            
//            // 6. Disk request matches superblock
//            assert( disk_request@ is WriteReq );
//            assert( disk_request@->to == spec_superblock_addr() );
//            // The superblock we're writing matches what execute_sync_begin expects
//            // expected_sb.store = pre.in_flight_map() = new_abstract_store
//            // expected_sb.journal = frozen_journal = sb@.journal
//            // sb@@ comes from DiskLayout::marshall postcondition
//            // Need: new_abstract_store == sb@@.store
//            let expected_sb = Superblock{
//                store: pre.in_flight_map(),
//                journal: frozen_journal,
//            };
//            // marshall ensures sb@@ == spec_parse(output)
//            // disk_request@->data == raw_page@
//            assert( pre.in_flight_map() == new_abstract_store );
//            
//            // Prove that spec_parse(disk_request@->data) == expected_sb
//            // From marshall postcondition: sb@@ == DiskLayout::spec_new().spec_parse(raw_page@)
//            // And disk_request@->data == raw_page@ (by construction)
//            assert( DiskLayout::spec_new().spec_parse(disk_request@->data) == sb@@ );
//            
//            // Now prove sb@@ == expected_sb
//            // sb@@.journal == frozen_journal (both equal sb.journal_snapshot@)
//            assert( sb@@.journal == frozen_journal );
//            // sb@@.store == new_abstract_store
//            // sb@@.store = arawstore_as_stamped_map(sb@.store, sb@.journal.boundary_lsn)
//            //            = StampedMap{value: map_to_kmmap(VecMap::seq_to_map(sb.store@)), seq_end: ...}
//            // new_abstract_store = StampedMap{value: view_as_kmmap(self.store), seq_end: ...}
//            //                    = StampedMap{value: map_to_kmmap(self.store@), seq_end: ...}
//            // And self.store@ = VecMap::seq_to_map(self.store.v@)
//            // So we need: sb.store@ == self.store.v@ (the store was copied into sb)
//            assert( sb@@.store == new_abstract_store ) by {
//                // In sync_map case: 
//                //   sb.store@ = old(self).store.v@ (captured before swap-back)
//                //   new_abstract_store = i_ephemeral_store()->v.stamped_map
//                //   i_ephemeral_store().value = view_as_kmmap(self.store) = map_to_kmmap(self.store@)
//                //   And self.store == old(self).store after swap-back
//                // In !sync_map case:
//                //   sb.store@ = old(self).persistent_store.v@ (captured before swap-back)
//                //   new_abstract_store = i_persistent_store()
//                //   i_persistent_store().value = view_as_kmmap(self.persistent_store)
//                //   And self.persistent_store == old(self).persistent_store after swap-back
//                
//                // The value maps are equal because they come from the same source
//                // The seq_end is also equal:
//                // - sync_map: both are version
//                // - !sync_map: both are journal.seq_start()
//                
//                // Connect view_as_kmmap to arawstore_as_stamped_map
//                // The Vec in sb.store came from self.store.v (sync_map) or self.persistent_store.v (!sync_map)
//                // After swap-back, self.store/persistent_store have the same contents
//                // 
//                // sb@@.store = arawstore_as_stamped_map(sb@.store, frozen_journal.boundary_lsn)
//                //            = StampedMap{value: map_to_kmmap(VecMap::seq_to_map(sb@.store)), seq_end: ...}
//                // new_abstract_store = StampedMap{value: view_as_kmmap(self.store), seq_end: ...}
//                //                    = StampedMap{value: map_to_kmmap(self.store@), seq_end: ...}
//                //                    = StampedMap{value: map_to_kmmap(VecMap::seq_to_map(self.store.v@)), seq_end: ...}
//                //
//                // Need: sb@.store == self.store.v@ (the Vec contents match)
//                // This is true because sb.store = tmp_store.v which held old(self).store.v,
//                // and after swap-back self.store.v == old(self).store.v
//                //
//                // For seq_end: in sync_map case both are version, in !sync_map both are journal.seq_start()
//                assume( sb@@.store == new_abstract_store );  // requires proving Vec contents preserved through swap
//            };
//            
//            assert( DiskLayout::spec_new().spec_parse(disk_request@->data) == expected_sb );
//            
//            // 7. post has correct shape  
//            assert( post.in_flight == Some(inflight_info) );
//            // reqs is a singleton as expected
//            assert( disk_reqs == Multiset::singleton((disk_req_id, disk_request@)) ) by {
//                assert( disk_reqs == multiset_map_singleton(disk_req_id, disk_request@) );
//                // multiset_map_singleton == Multiset::singleton by definition
//            };
//            
//            // Now we can prove execute_sync_begin holds
//            // All preconditions have been proven above (modulo some assumes)
//            assert( AtomicState::execute_sync_begin(pre, post,
//                disk_req_id, disk_request@, disk_reqs, Multiset::empty(),
//                frozen_journal, frozen_seq_end, frozen_domain, reads) );
//            
//            assert( AtomicState::disk_transition(
//                state_after_freeze, post_state.state, disk_event, disk_reqs, Multiset::empty()) );
//            
//            // Witness the existential in valid_disk_transition
//            let pre_model = ConcreteProgramModel{state: state_after_freeze};
//            assert( ConcreteProgramModel::valid_disk_transition(pre_model, post_state, info) ) by {
//                // disk_event is our witness for the existential
//                assert( AtomicState::disk_transition(
//                    pre_model.state, post_state.state, disk_event, info.reqs, info.resps) );
//            };
        }

        // // take the transition, get the token
        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof { tracked_swap(self.model.borrow_mut(), &mut model); }
        let tracked new_reply_token = self.instance.borrow().disk_transitions(
            lbl,
            post_state,
            &mut model,
            empty_disk_responses,
        );
        self.model = Tracked(model);
        std::mem::swap(&mut self.sync_requests.superblocking_reqs, &mut self.sync_requests.buffered_reqs);

        assert( new_reply_token.multiset() == multiset_map_singleton(req_id_perm@, disk_request@) );    // extn
        api.send_disk_request(disk_request, req_id_perm, Tracked(new_reply_token));
        
// 300 lines of cursor's intermediate efforts completing this proof
//        // Postcondition 1: ready_for_user_operation()
//        // recovery_phase is unchanged, so this follows from the precondition
//        assert( self.recovery_phase == old(self).recovery_phase );
//        assert( self.ready_for_user_operation() );
//        
//        // Postcondition 2: inv_api(api)
//        // This requires showing the invariant holds after all transitions
//        // Prove inv_api(api):
//        // 1. api.instance_id() == self.instance_id() - unchanged
//        assert( api.instance_id() == self.instance_id() );
//        
//        // 2. self.inv() requires several parts. Let's prove what we can:
//        
//        // cache.inv() - cache is unchanged (swaps were on store/persistent_store)
//        assert( self.cache == old(self).cache );
//        
//        // recovery_phase is unchanged
//        assert( self.recovery_phase == old(self).recovery_phase );
//        
//        // in_flight is now Some
//        assert( self.in_flight is Some );
//        
//        // instance is unchanged
//        assert( self.instance == old(self).instance );
//        
//        // The model was updated via disk_transitions to post_state
//        // model@.instance_id() == instance@.id() should hold from the token system
//        
//        // For inv_running, key properties:
//        // - self.store == old(self).store (after swap-back)
//        // - self.persistent_store == old(self).persistent_store (after swap-back)
//        // - self.journal == old(self).journal (unchanged)
//        // - self.in_flight is Some, and state().in_flight is Some (from post_state)
//        
//        // Prove inv() conjuncts:
//        
//        // 1. cache.inv() - cache unchanged, so follows from old(self).inv()
//        assert( self.cache.inv() ) by {
//            assert( self.cache == old(self).cache );
//            // old(self).inv() ==> old(self).cache.inv()
//        };
//        
//        // 2. recovery_phase implications - recovery_phase unchanged
//        // We're in ReadyForUserOperation, so we need inv_running()
//        
//        // 3. in_flight is Some ==> recovery_phase is ReadyForUserOperation
//        // Both are true, so implication holds
//        assert( self.in_flight is Some ==> self.recovery_phase is ReadyForUserOperation );
//        
//        // 4. model@.instance_id() == instance@.id()
//        // This should follow from the token system - the model comes from disk_transitions
//        // which borrows from instance, so the instance_id is preserved
//        
//        // 5. inv_running() - try to prove individual conjuncts
//        
//        // store.wf() and persistent_store are unchanged
//        assert( self.store.wf() ) by { assert( self.store == old(self).store ); };
//        assert( self.journal.wf() ) by { assert( self.journal == old(self).journal ); };
//        assert( self.journal.index_ready() ) by { assert( self.journal == old(self).journal ); };
//        
//        // state().recovery_state - should be RecoveryComplete since we set it via post_state
//        // post_state.state has recovery_state from state_after_freeze which has it from old(self).state()
//        
//        // state().in_flight is Some <==> self.in_flight is Some
//        // Both are Some now
//        assert( self.in_flight is Some );
//        // self.state() comes from self.model which now has post_state.state
//        // post_state.state.in_flight = Some(inflight_info)
//        
//        // sync_requests.in_flight() - we swapped satisfied/deferred
//        // Before: superblocking_reqs was empty, buffered_reqs had pending syncs
//        // After swap: superblocking_reqs has the old buffered_reqs, buffered_reqs is empty
//        // in_flight() checks if superblocking_reqs is non-empty
//        
//        // Try to prove state().store == view_store()
//        // self.state() = post_state.state (after disk_transitions puts post_state into model)
//        // post_state.state.store = frozen_store
//        // frozen_store = {in_flight: Some(new_abstract_store), ..old(self).state().store}
//        
//        // view_store() uses self.i_persistent_store(), self.i_ephemeral_store(), self.i_inflight_store()
//        // After swap-back: self.store == old(self).store, self.persistent_store == old(self).persistent_store
//        // So i_persistent_store() and i_ephemeral_store() match old(self)'s versions
//        // And by old(self).inv_running(): old(self).state().store.persistent == old(self).i_persistent_store()
//        //                                  old(self).state().store.ephemeral == old(self).i_ephemeral_store()
//        
//        // For in_flight:
//        // frozen_store.in_flight = Some(new_abstract_store)
//        // self.i_inflight_store() = Some(StampedMap{value: view_as_kmmap(self_in_flight.new_store), 
//        //                                           seq_end: self_in_flight.new_boundary_lsn})
//        // In sync_map case: self_in_flight.new_store = self.store.clone() = old(self).store
//        //                   self_in_flight.new_boundary_lsn = version = self.journal.seq_end()
//        //                   new_abstract_store = i_ephemeral_store()->v.stamped_map
//        // So both should equal StampedMap{value: view_as_kmmap(self.store), seq_end: version}
//        
//        // state().journal == self.journal@
//        // self.state().journal = post_state.state.journal = state_after_freeze.journal = old(self).state().journal
//        // self.journal@ == old(self).journal@ since journal unchanged
//        // By old(self).inv_running(): old(self).state().journal == old(self).journal@
//        
//        // state().in_flight is Some <==> self.in_flight is Some
//        // Both are Some now
//        
//        // state().in_flight is Some <==> self.sync_requests.in_flight()
//        // We swapped satisfied/deferred. Before: satisfied was empty. After: satisfied has old deferred.
//        // sync_requests.in_flight() = superblocking_reqs@.len() > 0
//        // Need: old(self).sync_requests.buffered_reqs@.len() > 0
//        // This should follow from the precondition that we have pending sync requests
//        
//        // After disk_transitions, self.model contains post_state (via model token)
//        // So self.state() == post_state.state
//        proof {
//            // After disk_transitions:
//            // The postcondition ensures model.value() == post_state
//            // We assigned self.model = Tracked(model)
//            // So self.model@.value() == post_state
//            assert( self.model@.value() == post_state );
//            
//            // Therefore self.state() == post_state.state
//            assert( self.state() == post_state.state );
//            
//            // Now we can trace the structure of self.state():
//            // post_state.state = AtomicState{in_flight: Some(inflight_info), ..state_after_freeze}
//            // state_after_freeze = AtomicState{store: frozen_store, ..old(self).state()}
//            
//            // So:
//            assert( self.state().in_flight == Some(inflight_info) );
//            assert( self.state().store == frozen_store );
//            assert( self.state().journal == old(self).state().journal );
//            assert( self.state().recovery_state == old(self).state().recovery_state );
//            assert( self.state().cache == old(self).state().cache );
//            
//            // From old(self).inv_running():
//            // old(self).state().journal == old(self).journal@
//            // And self.journal == old(self).journal
//            // So self.state().journal == self.journal@
//            
//            // From old(self).inv_running():
//            // old(self).state().recovery_state is RecoveryComplete
//            // So self.state().recovery_state is RecoveryComplete
//            
//            // state().in_flight is Some - proven above
//            assert( self.state().in_flight is Some );
//            
//            // self.in_flight is Some - proven earlier
//            
//            // state().in_flight is Some <==> self.in_flight is Some - both are Some
//            
//            // Now prove state().store == view_store()
//            // self.state().store = frozen_store
//            // frozen_store = AbstractCrashAwareMap::State{in_flight: Some(new_abstract_store), 
//            //                                              persistent: old(self).state().store.persistent,
//            //                                              ephemeral: old(self).state().store.ephemeral}
//            //
//            // view_store() = AbstractCrashAwareMap::State{persistent: i_persistent_store(),
//            //                                              ephemeral: i_ephemeral_store(),
//            //                                              in_flight: i_inflight_store()}
//            //
//            // By old(self).inv_running(): old(self).state().store == old(self).view_store()
//            // So: frozen_store.persistent == old(self).i_persistent_store() == self.i_persistent_store()
//            //     frozen_store.ephemeral == old(self).i_ephemeral_store() == self.i_ephemeral_store()
//            //     (since self.store == old(self).store and self.persistent_store == old(self).persistent_store)
//            
//            assert( frozen_store.persistent == self.i_persistent_store() ) by {
//                assert( self.persistent_store == old(self).persistent_store );
//                assert( self.journal == old(self).journal );
//                // old(self).state().store.persistent == old(self).i_persistent_store() by inv_running
//                // frozen_store.persistent == old(self).state().store.persistent by construction
//            };
//            
//            assert( frozen_store.ephemeral == self.i_ephemeral_store() ) by {
//                assert( self.store == old(self).store );
//                assert( self.journal == old(self).journal );
//                // old(self).state().store.ephemeral == old(self).i_ephemeral_store() by inv_running
//                // frozen_store.ephemeral == old(self).state().store.ephemeral by construction
//            };
//            
//            // The tricky part: frozen_store.in_flight == self.i_inflight_store()
//            // frozen_store.in_flight = Some(new_abstract_store)
//            // self.i_inflight_store() = Some(StampedMap{value: view_as_kmmap(self.in_flight.unwrap().new_store),
//            //                                           seq_end: self.in_flight.unwrap().new_boundary_lsn})
//            // self.in_flight = Some(self_in_flight)
//            // self_in_flight.new_store = self.store.clone() (in sync_map case) or self.persistent_store.clone()
//            // self_in_flight.new_boundary_lsn = version (in sync_map case) or journal.seq_start()
//            // new_abstract_store = i_ephemeral_store()->v.stamped_map (in sync_map) or i_persistent_store()
//            //
//            // Need to show these match - this requires that Clone preserves @
//            // In sync_map case:
//            //   new_abstract_store = i_ephemeral_store()->v.stamped_map 
//            //                      = StampedMap{value: view_as_kmmap(self.store), seq_end: version}
//            //   i_inflight_store() = Some(StampedMap{value: view_as_kmmap(self.in_flight.unwrap().new_store),
//            //                                        seq_end: self.in_flight.unwrap().new_boundary_lsn})
//            //   self.in_flight.unwrap() = self_in_flight
//            //   self_in_flight.new_store = self.store.clone() (same @ as self.store)
//            //   self_in_flight.new_boundary_lsn = version
//            // So both equal StampedMap{value: view_as_kmmap(self.store), seq_end: version}
//            //
//            // In !sync_map case:
//            //   new_abstract_store = i_persistent_store()
//            //                      = StampedMap{value: view_as_kmmap(self.persistent_store), seq_end: journal.seq_start()}
//            //   self_in_flight.new_store = self.persistent_store.clone() (same @ as self.persistent_store)
//            //   self_in_flight.new_boundary_lsn = journal.exec_seq_start()
//            //
//            // Clone ensures out == self, so view_as_kmmap(store.clone()) == view_as_kmmap(store)
//            // VecMap::clone ensures out == self
//            assert( frozen_store.in_flight == self.i_inflight_store() ) by {
//                // frozen_store.in_flight = Some(new_abstract_store)
//                // i_inflight_store() = Some(StampedMap{value: view_as_kmmap(in_flight.new_store), 
//                //                                      seq_end: in_flight.new_boundary_lsn})
//                // self.in_flight = Some(self_in_flight)
//                assert( self.in_flight is Some );
//                
//                // In sync_map case:
//                //   new_abstract_store = i_ephemeral_store()->v.stamped_map
//                //                      = StampedMap{value: view_as_kmmap(self.store), seq_end: version}
//                //   self_in_flight.new_store = self.store.clone()
//                //   self_in_flight.new_boundary_lsn = version
//                //   i_inflight_store() = Some(StampedMap{value: view_as_kmmap(self.store.clone()),
//                //                                        seq_end: version})
//                //   By clone postcondition: self.store.clone() == self.store
//                //   So view_as_kmmap(self.store.clone()) == view_as_kmmap(self.store)
//                // 
//                // In !sync_map case:
//                //   new_abstract_store = i_persistent_store()
//                //                      = StampedMap{value: view_as_kmmap(self.persistent_store), 
//                //                                   seq_end: journal.seq_start()}
//                //   self_in_flight.new_store = self.persistent_store.clone()
//                //   self_in_flight.new_boundary_lsn = journal.exec_seq_start()
//                //   By clone postcondition: self.persistent_store.clone() == self.persistent_store
//                
//                // The clone postcondition gives equality, so the views match
//                // The boundary_lsn also matches (version in sync_map, seq_start in !sync_map)
//                
//                // frozen_store.in_flight = Some(new_abstract_store)
//                // self.i_inflight_store() = Some(StampedMap{...})
//                // Need: new_abstract_store == the StampedMap in i_inflight_store()
//                
//                // The key insight: in both branches, self_in_flight.new_store is a clone
//                // of the same VecMap that view_as_kmmap is applied to in new_abstract_store.
//                // And clone ensures equality.
//                
//                // self.in_flight.unwrap() == self_in_flight (by assignment)
//                // view_as_kmmap uses self.store@ or self.persistent_store@
//                // self_in_flight.new_store == self.store or self.persistent_store (by clone postcondition)
//                
//                // We proved Some(new_abstract_store) == self.i_inflight_store() earlier
//                // frozen_store.in_flight = Some(new_abstract_store)
//                // So frozen_store.in_flight == self.i_inflight_store()
//                assert( frozen_store.in_flight == self.i_inflight_store() );
//            };
//            
//            assert( self.state().store == self.view_store() );
//            
//            // state().journal == self.journal@
//            // self.state().journal == old(self).state().journal (proven above)
//            // old(self).state().journal == old(self).journal@ (by old(self).inv_running())
//            // old(self).journal@ == self.journal@ (since self.journal == old(self).journal)
//            assert( self.state().journal == self.journal@ );
//            
//            // state().recovery_state is RecoveryComplete
//            assert( self.state().recovery_state is RecoveryComplete );
//            
//            // state().wf()
//            // This should follow from the transition preserving wf
//            
//            // state().in_flight is Some <==> self.in_flight is Some
//            // Both are Some
//            assert( self.state().in_flight is Some );
//            assert( self.in_flight is Some );
//            assert( self.state().in_flight is Some <==> self.in_flight is Some );
//            
//            // state().in_flight is Some <==> self.sync_requests.in_flight()
//            // After swap: superblocking_reqs = old(self).sync_requests.buffered_reqs
//            // in_flight() = superblocking_reqs@.len() > 0
//            // Need: old(self).sync_requests.buffered_reqs@.len() > 0
//            // This follows from the precondition old(self).sync_requests.buffered_reqs.len() > 0
//            
//            // After std::mem::swap: superblocking_reqs@.len() == old(self).sync_requests.buffered_reqs@.len()
//            assert( self.sync_requests.superblocking_reqs@.len() == old(self).sync_requests.buffered_reqs@.len() );
//            assert( self.sync_requests.superblocking_reqs@.len() > 0 );
//            // in_flight() is defined as superblocking_reqs@.len() > 0
//            assert( self.sync_requests.in_flight() );
//            // state().in_flight is Some (proven above)
//            assert( self.state().in_flight is Some <==> self.sync_requests.in_flight() );
//            
//            // Additional inv_running conjuncts:
//            
//            // state.journal.seq_end() == state.ephemeral_map().seq_end
//            // state.journal == self.journal@ == old(self).journal@ (by old(self).inv_running)
//            // state.ephemeral_map() uses view_store().ephemeral which equals old(self).view_store().ephemeral
//            // By old(self).inv_running: old(self).state().journal.seq_end() == old(self).state().ephemeral_map().seq_end
//            // These haven't changed, so equality still holds
//            
//            // state().wf() - should follow from transition preserving wf
//            
//            // state.in_flight is Some ==> various conditions
//            // self.in_flight.unwrap().new_boundary_lsn <= state.journal.status...
//            // This needs: version <= journal.seq_start (for sync_map) or seq_start <= seq_start
//            // Also: self.journal.seq_start() <= new_persistent_map_version <= sync_version
//            // new_persistent_map_version = self.in_flight.unwrap().new_boundary_lsn = version
//            // sync_version = state.in_flight.unwrap().journal_version = version
//            // So: journal.seq_start() <= version <= version ✓
//            
//            // sync_reqs_in_version(superblocking_reqs@, sync_version)
//            // After swap: superblocking_reqs = old(self).buffered_reqs
//            // old(self) had: sync_reqs_in_version(buffered_reqs@, old(self).version())
//            // sync_version = version = self.version() = old(self).version()
//            // So this should hold
//            
//            // sync_requests.wf(instance@.id()) - unchanged
//            // sync_reqs_in_version(buffered_reqs@, version) - after swap, buffered_reqs is empty or was satisfied
//            // sync_req_lists_mutually_unique - after swap
//        }
//        
//        assume( self.inv() );
//        assert( self.inv_api(api) );
    }

    exec fn deliver_inflight_replies(&mut self, ready_reqs: &mut Vec<Request>, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).sync_reqs_in_version(old(ready_reqs)@, old(self).state().persistent_journal_seq_end),
        // can't break in-flight inv because there aren't any superblocking_reqs during this call
        old(self).sync_requests.superblocking_reqs@.len()==0,
        Self::sync_req_lists_mutually_unique(old(ready_reqs)@, old(self).sync_requests.buffered_reqs@),
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
            self.sync_requests.superblocking_reqs@.len()==0,
            ready_reqs@.len() <= old(ready_reqs)@.len(),
            old(self).sync_requests.buffered_reqs@ == self.sync_requests.buffered_reqs@,
            Self::sync_req_lists_mutually_unique(old(ready_reqs)@, old(self).sync_requests.buffered_reqs@),   // mutter mutter
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
        &&& (forall |j| #![auto] 0<=j<self.sync_requests.superblocking_reqs@.len() ==> self.sync_requests.superblocking_reqs@[j].id!=id)
        &&& (forall |j| #![auto] 0<=j<self.sync_requests.buffered_reqs@.len() ==> self.sync_requests.buffered_reqs@[j].id!=id)
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
        old(self).sync_requests.buffered_reqs@ == self.sync_requests.buffered_reqs@,
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
        std::mem::swap(&mut self.sync_requests.superblocking_reqs, &mut ready_reqs);
//         (ready_reqs,self.sync_requests.superblocking_reqs) = (self.sync_requests.superblocking_reqs,ready_reqs);

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
            let ghost freshest_rec_a = match freshest_rec { None => None, Some(f) => Some(f@) };
            let ghost post_state = ConcreteProgramModel{ state: AtomicState{
                in_flight: None,
                journal: CachedJournal::State {
                    snapshot: CachedJournal_v::JournalSnapShot{
                        boundary_lsn: new_boundary_lsn as LSN,
                        freshest_rec: freshest_rec_a,
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
            api.log("handle_disk_superblock_write_response: received non superblock related disk response");
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
                Self::todo_placeholder();
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
