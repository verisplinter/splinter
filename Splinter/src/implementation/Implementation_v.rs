// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
//use vstd::prelude_macros::*;
use vstd::pervasive::*;
use vstd::prelude::*;
use vstd::modes::*;
use vstd::assert_maps_equal;
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
use crate::allocation_layer::LikesJournal_v::lsn_addr_index_discard_up_to;
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
// use crate::implementation::CacheImpl_v::CacheImpl;
use crate::implementation::Cache_v::Cache;
use crate::implementation::FracCacheImpl_v::*;

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
    pub closed spec fn valid_empty_sync_buffer(self, instance_id: InstanceId) -> bool
    {
        &&& !self.in_flight()
        &&& self.buffered_reqs@.len() == 0
        &&& self.journal_cleaning_reqs@.len() == 0
        &&& self.superblocking_reqs@.len() == 0
        &&& self.journal_cleaning_target_lsn == 0
        &&& self.wf(instance_id)
    }

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
        forall |instance_id: InstanceId| out.valid_empty_sync_buffer(instance_id),
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

enum OutstandingReqInfo{
    SuperBlockReq{},
    CacheLoadReq{read_addr: IAddress, load_handle: MutHandle},
    CacheWriteReq{write_addr: IAddress, handle: MutHandle},
}

// This struct supplies KVStoreTrait, which has both the entry point to the implementation and the
// proof hooks to satisfy the refinement obligation trait.
pub struct Implementation {
    recovery_phase: RecoveryPhase,

    sync_counter: u64,

    store: VecMap<Key, Value>,
    store_lsn: u64, // tracks current store's version

    // starts at persistent_store.version, ends matching store
    journal: JournalImpl,
    
    cache: FracCacheImpl,

    // this is a truncate in flight, only set when a truncation is occuring
    in_flight: Option<InFlight>,

    // remember the actual persistent version on disk and
    // its journal info, so we can interpret to the floating versions.
    persistent_store: VecMap<Key, Value>,

    // token for the program model variable
    model: Tracked<ModelShard>,

    // we do not own a mutable reference to this
    instance: Tracked<KVStoreTokenized::Instance<ConcreteProgramModel>>,

    sync_requests: SyncRequestBuffer,

    outstanding_requests: HashMapWithView<ID, OutstandingReqInfo>,
}

impl Implementation {

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
        &&& self.sync_requests.valid_empty_sync_buffer(self.instance@.id())
        &&& self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty()
        &&& self.state().outstanding_cache_reqs == Map::<ID, Address>::empty()
        &&& self.store.wf()
        &&& self.state().recovery_state is Begin
        &&& self.cache.wf()
    }

    closed spec fn outstanding_requests_wf_map(outstanding: Map<ID, OutstandingReqInfo>, cache: FracCacheImpl) -> bool
    {
        forall |id| #[trigger] outstanding.contains_key(id) ==> {
            match outstanding[id] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& cache.entry_fetched(&read_addr)
                    &&& cache.valid_load_handle(&read_addr, load_handle)
                },
                _ => { true }
            }
        }
    }

    closed spec fn outstanding_requests_wf(self) -> bool
    {
        Self::outstanding_requests_wf_map(self.outstanding_requests@, self.cache)
    }

    closed spec fn outstanding_requests_match_cache_reqs_map(outstanding: Map<ID, OutstandingReqInfo>, m: Map<ID, Address>) -> bool
    {
        &&& m.is_injective()
        &&& forall |id| #[trigger] outstanding.contains_key(id) ==> {
            match outstanding[id] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& m.contains_key(id)
                    &&& m[id] == read_addr@
                },
                OutstandingReqInfo::CacheWriteReq{write_addr, handle} => {
                    &&& m.contains_key(id)
                    &&& m[id] == write_addr@
                },
                OutstandingReqInfo::SuperBlockReq{} => {
                    !m.contains_key(id)
                }
            }
        }
    }

    closed spec fn outstanding_requests_match_cache_reqs(self) -> bool
    {
        Self::outstanding_requests_match_cache_reqs_map(self.outstanding_requests@, self.state().outstanding_cache_reqs)
    }

    closed spec fn inv_running(self) -> bool {
        let state = self.state();

        &&& self.journal.wf()
        // &&& self.model@.instance_id() == self.instance@.id() // TODO delete covered by inv

        &&& self.journal.index_ready()

        // physical state consistent with model
        &&& state.recovery_state is RecoveryComplete

        &&& self.journal.seq_end() == self.store_lsn
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
            &&& self.journal.seq_start() <= new_persistent_map_version
            &&& new_persistent_map_version <= sync_version
            // The in-flight 'satisfied requests' can indeed be satisfied by the in-flight version
            &&& self.sync_reqs_in_version(self.sync_requests.superblocking_reqs@, sync_version)
        })

        &&& self.sync_requests.wf(self.instance@.id())
        &&& self.sync_reqs_in_version(self.sync_requests.buffered_reqs@, self.version())
        &&& self.sync_requests.journal_cleaning_target_lsn <= self.version()
        &&& self.sync_reqs_in_version(self.sync_requests.journal_cleaning_reqs@, self.sync_requests.journal_cleaning_target_lsn as nat)
        // This is getting to be a nasty framing-shaped disjointness argument.
        &&& Self::three_sync_req_lists_mutually_unique(
                self.sync_requests.superblocking_reqs@,
                self.sync_requests.journal_cleaning_reqs@,
                self.sync_requests.buffered_reqs@)
    }

    spec fn three_sync_req_lists_mutually_unique(l1: Seq<Request>, l2: Seq<Request>, l3: Seq<Request>) -> bool
    {
        &&& Self::sync_req_lists_mutually_unique(l1, l2)
        &&& Self::sync_req_lists_mutually_unique(l2, l3)
        &&& Self::sync_req_lists_mutually_unique(l1, l3)
    }

    // Shared relation after fetching the superblock: implementation state matches model view.
    spec fn inv_post_superblock_common(self) -> bool
    {
        &&& self.store.wf()
        &&& self.state().store == self.view_store()
        &&& self.state().journal == self.journal@
    }

    spec fn inv_reading_journal(self) -> bool
    {
        &&& self.state().recovery_state is SuperblockAvailable
        &&& self.state().in_flight is None
        &&& self.sync_requests.valid_empty_sync_buffer(self.instance@.id())
        &&& self.store_lsn as nat == self.journal.seq_start()
        &&& self.journal.wf()
        &&& !self.journal.index_ready()
        &&& forall |id| #[trigger] self.outstanding_requests@.contains_key(id)
            ==> self.outstanding_requests@[id] is CacheLoadReq
    }

    spec fn inv_applying_journal(self) -> bool
    {
        &&& self.state().recovery_state is JournalIndexComplete
        &&& self.state().in_flight is None
        &&& self.sync_requests.valid_empty_sync_buffer(self.instance@.id())
        &&& self.store_lsn as nat <= self.journal.seq_end()
        &&& self.journal.wf()
        &&& self.journal.index_ready()
        &&& self.journal.no_unmarshalled_entries()
        &&& forall |id| #[trigger] self.outstanding_requests@.contains_key(id)
            ==> self.outstanding_requests@[id] is CacheLoadReq
    }

    closed spec fn inv(self) -> bool {
        &&& self.cache.wf()
        &&& self.state().cache == self.cache@
        &&& self.outstanding_requests_wf()
        &&& self.outstanding_requests_match_cache_reqs()

        // from the physical phase field to stuff we know
        &&& self.recovery_phase is FetchingSuperblock ==> self.inv_recover()
        &&& !(self.recovery_phase is FetchingSuperblock) ==> self.inv_post_superblock_common()
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
                stamped_map: StampedMap{value: view_as_kmmap(self.store), seq_end: self.store_lsn as nat}
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
            let new_store_lsn = self.journal.exec_seq_end();
            self.store_lsn = new_store_lsn;

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
        let ghost old_buffered_reqs = old(self).sync_requests.buffered_reqs@;
        let ghost old_journal_cleaning_reqs = old(self).sync_requests.journal_cleaning_reqs@;
        let ghost old_superblocking_reqs = old(self).sync_requests.superblocking_reqs@;
        assert({
            &&& forall |i| #![auto] 0 <= i < old_buffered_reqs.len() ==> old_buffered_reqs[i].id != req.id
            &&& forall |i| #![auto] 0 <= i < old_journal_cleaning_reqs.len() ==> old_journal_cleaning_reqs[i].id != req.id
            &&& forall |i| #![auto] 0 <= i < old_superblocking_reqs.len() ==> old_superblocking_reqs[i].id != req.id
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
                self.sync_requests.journal_cleaning_target_lsn = self.journal.exec_seq_end();
                std::mem::swap(&mut self.sync_requests.buffered_reqs, &mut self.sync_requests.journal_cleaning_reqs);
            }
            Self::debug_print(&"  └─ send_superblock");
            self.send_superblock(api, SuperblockMotivation::PushJournal);
        }
    }

    exec fn clean_journal_for_sync(&mut self, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).ready_for_user_operation(),
        old(self).sync_requests.superblocking_reqs.len() == 0,
        old(self).sync_requests.journal_cleaning_reqs.len() == 0,
        old(self).sync_requests.buffered_reqs.len() > 0,
    ensures
        self.inv_api(api),
        self.ready_for_user_operation(),
    {
        // record journal current version as journal_cleaning_target_lsn,
        // move all reqs from buffered_reqs to journal_cleaning_reqs,
        // make progress on cleaning the journal
    }

    exec fn send_superblock(&mut self, api: &mut ClientAPI<ConcreteProgramModel>, motivation: SuperblockMotivation)
    requires
        old(self).inv_api(old(api)),
        // do we have room to send a superblock?
        old(self).in_flight is None,
        // this requirement nonsense for map-only (journal truncation) case:
        old(self).sync_requests.journal_cleaning_reqs.len() > 0,
        old(self).ready_for_user_operation(),
        !(motivation is PushMap),
    ensures
        self.inv_api(api),
        self.ready_for_user_operation(),
    {
        proof { self.system_inv_implies_atomic_state_wf(); }

        let mut raw_page = Vec::new();
        let mut tmp_store = VecMap::new();

        let mut sb;
        let mut self_in_flight;
        let ghost mut new_abstract_store;
        let ghost mut cache_before_fetch = self.cache;
        let mut frozen_journal;
        match motivation {
            SuperblockMotivation::PushMap => {
                // Disabled: PushMap tries to push a frozen map with an empty journal.
                // CachedJournal's FreezeForCommit requires freezing a prefix of an existing journal.
                // We'll revisit this later.
                proof { assert(false); }
                return;
                // // sync the ephemeral map with an empty journal
                // api.log("send_superblock: sync store and truncate the journal");
                // std::mem::swap(&mut self.store, &mut tmp_store);
        
                // sb = ISuperblock{
                //     journal_snapshot: IJournalSnapshot::new_empty(version),
                //     store: tmp_store.v,
                // };
                // raw_page = DiskLayout::new().marshall(&sb);

                // let ISuperblock{store: mut tmp_store_v, /*store: mut tmp_store,*/ ..} = sb;
                // tmp_store.v = tmp_store_v;
                // std::mem::swap(&mut self.store, &mut tmp_store);
                
                // // After swap-back: self.store.v@ == sb@.store (the Vec contents are the same)
                // // sb.store was tmp_store.v which held old(self).store.v
                // // After swap-back, self.store.v == old(self).store.v
                // // And tmp_store_v came from sb.store, so they're all the same Vec
                // proof {
                //     assert( self.store.v@ == sb@.store );
                // }

                // self_in_flight = Some(InFlight{
                //     new_boundary_lsn: version,
                //     freshest_rec: None,
                //     new_persistent_lsn: version,
                //     new_store: self.store.clone(),
                // });
                // proof { new_abstract_store = self.i_ephemeral_store()->v.stamped_map; }
            },
            SuperblockMotivation::PushJournal => {
                // sync the ephemeral journal with the existing persistent map
                api.log("send_superblock: journal sync only");

                let ready = self.journal.clean_for_commit(&self.cache, self.sync_requests.journal_cleaning_target_lsn);
                if !ready { return }

                // Okay, the journal is clean up to the point of journal_cleaning_target_lsn, which
                // means the journal_cleaning_reqs are now eligible to be delivered in a
                // superblock.
                std::mem::swap(&mut self.sync_requests.superblocking_reqs, &mut self.sync_requests.journal_cleaning_reqs);

                std::mem::swap(&mut self.persistent_store, &mut tmp_store);

                // Read the journal page at freshest_rec from cache to verify frozen_seq_end
                // This is required by CachedJournal::freeze_for_commit which needs to verify
                // that the journal record's message_seq.seq_end matches frozen_seq_end
                frozen_journal = self.journal.freeze_journal(&self.cache);
                
                // Capture cache state before fetch for proving cache is unchanged after release
                proof {
                    cache_before_fetch = self.cache;
                }
                
                let slot_handle = match frozen_journal.snapshot.freshest_rec {
                    Some(freshest_addr) => {
                        let fetch_result = self.cache.fetch(&freshest_addr);
                        match fetch_result {
                            FetchErrorCode::Success{slot_handle} => {
                                proof {
                                    assert( cache_before_fetch@.entries[slot_handle.idx].get_addr() == freshest_addr@ );  // trigger
                                    assert( cache_before_fetch.wf() );  // trigger
                                }
                                Some(slot_handle)
                            },
                            _ => {
                                api.log("Unimplemented: async journal read in send_superblock");
                                Self::todo_placeholder();
                                return;
                            }
                        }
                    },
                    None => { None },
                };

                sb = ISuperblock{
                    journal_snapshot: frozen_journal.snapshot,
                    store: tmp_store.v,
                };

                // Release the handle - fetch+release round-trip is a no-op on cache state
                if let Some(handle) = slot_handle {
                    if let Some(freshest_addr) = frozen_journal.snapshot.freshest_rec {
                        self.cache.handle_release(&freshest_addr, handle);
                        // cache@ == cache_before_fetch@ follows from fetch+release round-trip
                    }
                }
                
                
                api.log("sending this particular superblock: ");
                Self::debug_print(&sb);
                raw_page = DiskLayout::new().marshall(&sb);

                let ISuperblock{store: mut tmp_store_v, ..} = sb;
                tmp_store.v = tmp_store_v;
                std::mem::swap(&mut self.persistent_store, &mut tmp_store);

                self_in_flight = Some(InFlight{
                    new_boundary_lsn: self.journal.exec_seq_start(),
                    freshest_rec: self.journal.exec_freshest_rec(),
                    new_persistent_lsn: frozen_journal.seq_end,
                    new_store: self.persistent_store.clone(),
                });
                proof { new_abstract_store = self.i_persistent_store(); }
            },
        }

        // First step: freeze the map, via a cache internal step
        let ghost frozen_store = AbstractCrashAwareMap::State{
            in_flight: Some(new_abstract_store),
            ..old(self).state().store
        };
        // fetch+release is a no-op on the cache state
        let ghost state_after_freeze = AtomicState{
            store: frozen_store,
            cache: old(self).state().cache,
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
                assert(ConcreteProgramModel::valid_internal_transition(model.value(), post_state)) by {
                    assert(AtomicState::internal_transitions(
                        model.value().state,
                        post_state.state,
                        InternalEvent::StoreInternal{}
                    )) by {
                        assert(old(self).inv());
                        reveal(Implementation::inv);
                        reveal(Implementation::ready_for_user_operation);
                        assert(old(self).ready_for_user_operation());
                        assert(old(self).recovery_phase is ReadyForUserOperation);
                        assert(old(self).inv_running());
                        reveal(Implementation::inv_running);
                        broadcast use JournalImpl::view_ensures;
                        assert(old(self).state().journal.status is Some) by {
                            assert(old(self).state().journal == old(self).journal@);
                            assert(old(self).journal.index_ready() <==> old(self).journal@.status is Some);
                            assert(old(self).journal@.status is Some);
                        }
                        assert(old(self).state().client_ready());
                        assert(model.value().state == old(self).state());
                        assert(model.value().state.client_ready());
                        assert(post_state.state == AtomicState{store: post_state.state.store, ..model.value().state});
                        assert(AtomicState::store_internal(model.value().state, post_state.state));
                    }
                }
                assert(ConcreteProgramModel::next(model.value(), post_state, ProgramLabel::Internal{}));
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
        
        let req_id_perm = Tracked( api.send_disk_request_predict_id() );
        let ghost disk_req_id = req_id_perm@;
        let disk_request = IDiskRequest::WriteReq{to: superblock_addr(), data: raw_page};
        let ghost disk_reqs = multiset_map_singleton(disk_req_id, disk_request@);

        // inflight_info records the frozen journal's seq_end (the clean watermark)
        let ghost inflight_info = InflightInfo{
            journal_version: frozen_journal.seq_end as nat,
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
            // frozen_journal.snapshot@.freshest_rec is the cropped pointer
            // (freeze_journal may crop back from self's freshest_rec to the clean watermark)
            let ptr_witness = frozen_journal.snapshot@.freshest_rec;

            // Construct reads map from the cache at the frozen journal's freshest_rec
            let reads: Map<Address, RawPage> = if ptr_witness is Some {
                let addr = ptr_witness.unwrap();
                // freshest_rec_page_agrees ensures lookup_map.contains_key(addr)
                let slot = state_after_freeze.cache.lookup_map[addr];
                let data = state_after_freeze.cache.entries[slot]->data;
                Map::empty().insert(addr, data)
            } else {
                Map::empty()
            };

            // Witness the disk transition via execute_sync_begin
            let disk_event = DiskEvent::ExecuteSyncBegin{
                req_id: disk_req_id,
                req: disk_request@,
                frozen_journal: sb@.journal,
                frozen_seq_end: frozen_journal.seq_end as nat,
                frozen_domain: self.journal.iaddrs_for_lsns(frozen_journal.seq_start() as LSN, frozen_journal.seq_end as LSN),
                reads,
            };

            // Prove preconditions of execute_sync_begin:
            let pre = state_after_freeze;
            let post = post_state.state;

            let map_lbl = AbstractCrashAwareMap::Label::CommitStartLabel{
                new_boundary_lsn: frozen_journal.seq_start() as nat};
            assert( AbstractCrashAwareMap::State::next_by(pre.store, post.store, map_lbl,
                AbstractCrashAwareMap::Step::commit_start()) ); // step witness

            reveal(Cache::State::next_by);
            reveal(Cache::State::next);

            if ptr_witness is None {
                crate::implementation::Cache_v::Cache::State::access_empty_is_noop(pre.cache);
            } else {
                let lbl = Cache::Label::Access{reads: reads, writes: Map::empty()};
                let updated_entries = pre.cache.write_updated_entries(lbl->writes);
                let updated_status_map = pre.cache.write_updated_status(lbl->writes);
                assert( pre.cache.entries.union_prefer_right(updated_entries) =~= pre.cache.entries );  // extn
                assert( pre.cache.status_map.union_prefer_right(updated_status_map) =~= pre.cache.status_map );  // extn
                assert( Cache::State::next_by(pre.cache, post.cache, lbl, Cache::Step::access()) ); // witness
            }

            let journal_lbl = CachedJournal::Label::FreezeForCommit{
                frozen: frozen_journal.snapshot@,
                frozen_seq_end: frozen_journal.seq_end as nat,
                frozen_domain: self.journal.iaddrs_for_lsns(frozen_journal.seq_start() as LSN, frozen_journal.seq_end as LSN),
                reads: to_journal_reads(reads)};

            reveal(CachedJournal::State::next);
            reveal(CachedJournal::State::next_by);

            // CachedJournal::freeze_for_commit at depth 0:
            // out.snapshot@ == self@.snapshot means frozen freshest_rec == pre freshest_rec,
            // so pointer_after_crop_index(ptr, 0) == ptr == frozen.freshest_rec.
            // can_crop_index(ptr, 0) is trivially true (0 < depth ==> ... is vacuous).
            // freeze_for_commit has no update statements, so post.journal == pre.journal.
            assert( CachedJournal::State::next_by(pre.journal, post.journal, journal_lbl,
                CachedJournal::Step::freeze_for_commit(0nat)) );
            
            // 6. Disk request matches superblock
            // The superblock we're writing matches what execute_sync_begin expects
            // expected_sb.store = pre.in_flight_map() = new_abstract_store
            // expected_sb.journal = frozen_journal = sb@.journal
            // sb@@ comes from DiskLayout::marshall postcondition
            // Need: new_abstract_store == sb@@.store
            // marshall ensures sb@@ == spec_parse(output), and disk_request@->data == raw_page@
            assert( sb@@.store == new_abstract_store );  // trigger
            assert( disk_reqs == Multiset::singleton((disk_req_id, disk_request@)) ) by {
                assert( disk_reqs == multiset_map_singleton(disk_req_id, disk_request@) );
            };

            // Witness the existential in valid_disk_transition
            let pre_model = ConcreteProgramModel{state: state_after_freeze};
            assert( ConcreteProgramModel::valid_disk_transition(pre_model, post_state, info) ) by {
                // disk_event is our witness for the existential
                assert( AtomicState::disk_transition(
                    pre_model.state, post_state.state, disk_event, info.reqs, info.resps) );
            };
        }

        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof { tracked_swap(self.model.borrow_mut(), &mut model); }
        let tracked new_reply_token = self.instance.borrow().disk_transitions(
            lbl,
            post_state,
            &mut model,
            empty_disk_responses,
        );
        self.model = Tracked(model);

        api.send_disk_request(disk_request, req_id_perm, Tracked(new_reply_token));
        
        proof {
            assert( self.state() == post_state.state );
            self.journal.seq_start_le_marshalled_end();
        }

    }

    exec fn deliver_inflight_replies(&mut self, ready_reqs: &mut Vec<Request>, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).sync_reqs_in_version(old(ready_reqs)@, old(self).state().persistent_journal_seq_end),
        // can't break in-flight inv because there aren't any superblocking_reqs during this call
        old(self).sync_requests.superblocking_reqs@.len()==0,
        Self::three_sync_req_lists_mutually_unique(old(ready_reqs)@,
                old(self).sync_requests.journal_cleaning_reqs@,
                old(self).sync_requests.buffered_reqs@),
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
            Self::three_sync_req_lists_mutually_unique(old(ready_reqs)@,
                    self.sync_requests.journal_cleaning_reqs@,
                    self.sync_requests.buffered_reqs@),
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
        &&& (forall |j| #![auto] 0<=j<self.sync_requests.journal_cleaning_reqs@.len() ==> self.sync_requests.journal_cleaning_reqs@[j].id!=id)
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
        old(self).sync_requests.journal_cleaning_reqs@ == self.sync_requests.journal_cleaning_reqs@,
        self.ready_for_user_operation(),
    {
        // Convert the model state back into a shard
        let ghost pre_state = self.model@.value();
        
        let ghost post_state = ConcreteProgramModel {
            state: AtomicState{
                sync_req_map: pre_state.state.sync_req_map.remove(req.id),
                ..pre_state.state}
        };

        let ghost oself = *self;
        assert( self.sync_reqs_in_version(self.sync_requests.journal_cleaning_reqs@, self.sync_requests.journal_cleaning_target_lsn as nat) );
        assert( oself.sync_reqs_in_version(oself.sync_requests.journal_cleaning_reqs@, oself.sync_requests.journal_cleaning_target_lsn as nat) );
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

    proof fn singleton_map_dom<K,V>(k: K, v: V)
    ensures
        forall |k2| #[trigger] map!{k => v}.dom().contains(k2) <==> k2 == k
    {
        let m = map!{k => v};
        broadcast use vstd::set::group_set_axioms;
        broadcast use vstd::map::axiom_map_empty;
        vstd::map::axiom_map_insert_domain(Map::<K,V>::empty(), k, v);
        assert forall |k2| m.dom().contains(k2) <==> k2 == k by {
            if k2 == k {
                assert(Map::<K,V>::empty().dom().insert(k).contains(k)) by {
                    vstd::set::axiom_set_insert_same(Map::<K,V>::empty().dom(), k);
                }
                assert(m.dom() == Map::<K,V>::empty().dom().insert(k));
            } else {
                assert(Map::<K,V>::empty().dom().insert(k).contains(k2)
                    == Map::<K,V>::empty().dom().contains(k2)) by {
                    vstd::set::axiom_set_insert_different(Map::<K,V>::empty().dom(), k2, k);
                }
                assert(!Map::<K,V>::empty().dom().contains(k2)) by {
                    vstd::set::axiom_set_empty::<K>(k2);
                    assert(Map::<K,V>::empty().dom() == Set::<K>::empty());
                }
                assert(m.dom() == Map::<K,V>::empty().dom().insert(k));
            }
        }
    }

    proof fn singleton_map_value<K,V>(k: K, v: V)
    ensures
        forall |v2| #[trigger] map!{k => v}.contains_value(v2) <==> v2 == v
    {
        let m = map!{k => v};
        Self::singleton_map_dom(k, v);
        assert forall |v2| m.contains_value(v2) <==> v2 == v by {
            if v2 == v {
                vstd::map::axiom_map_insert_same(Map::<K,V>::empty(), k, v);
                assert(m.dom().contains(k));
                assert(m[k] == v);
                assert(m.contains_pair(k, v));
            } else {
                if m.contains_value(v2) {
                    reveal(Map::contains_value);
                    let k2 = choose |k2| m.contains_pair(k2, v2);
                    assert(m.dom().contains(k2));
                    assert(k2 == k);
                    vstd::map::axiom_map_insert_same(Map::<K,V>::empty(), k, v);
                    assert(m[k] == v);
                    assert(v2 == v);
                    assert(false);
                }
            }
        }
    }

    proof fn invert_singleton<K,V>(k: K, v: V)
    ensures
        map!{k => v}.invert() == map!{v => k}
    {
        let m = map!{k => v};
        reveal(Map::invert);
        Self::singleton_map_value(k, v);
        assert_maps_equal!(m.invert(), map!{v => k}, key => {
            if key == v {
                assert(m.contains_value(key));
                assert(m.invert().dom().contains(key));
                vstd::map::axiom_map_insert_same(Map::<K,V>::empty(), k, v);
                assert(m.dom().contains(k));
                assert(m[k] == v);
                assert(m.contains_pair(k, key));
                assert(m.contains_pair(m.invert()[key], key)) by {
                    reveal(Map::invert);
                    assert(exists |k2| m.contains_pair(k2, key)) by {
                        assert(m.contains_pair(k, key));
                    }
                }
                assert forall |k2| m.contains_pair(k2, key) implies k2 == k by {
                    assert(m.dom().contains(k2));
                    assert(m.dom().contains(k2) <==> k2 == k);
                    assert(k2 == k);
                }
                assert(m.invert()[key] == k) by {
                    assert(m.contains_pair(m.invert()[key], key));
                }
            } else {
                assert(!m.contains_value(key));
                assert(!m.invert().dom().contains(key));
            }
        });
    }

    proof fn set_singleton_to_multiset<A>(x: A)
    ensures
        set!{x}.to_multiset() == Multiset::empty().insert(x)
    {
        let s = set!{x};
        broadcast use vstd::set::group_set_axioms;
        broadcast use vstd::multiset::group_multiset_axioms;

        assert(Set::<A>::empty().finite());
        vstd::set::axiom_set_insert_finite(Set::<A>::empty(), x);
        vstd::set::axiom_set_insert_same(Set::<A>::empty(), x);
        assert(s.finite());
        assert(s.contains(x));
        vstd::set::axiom_set_contains_len(s, x);
        assert(s.len() != 0);

        vstd::set::axiom_set_choose_len(s);
        assert(s.contains(s.choose()));
        assert forall |y| s.contains(y) implies y == x by {
            if y != x {
                vstd::set::axiom_set_insert_different(Set::<A>::empty(), y, x);
                vstd::set::axiom_set_empty::<A>(y);
                assert(!Set::<A>::empty().contains(y));
                assert(false);
            }
        }
        assert(s.choose() == x);

        assert forall |y| s.remove(s.choose()).contains(y) implies false by {
            if y == s.choose() {
                vstd::set::axiom_set_remove_same(s, y);
                assert(false);
            } else {
                vstd::set::axiom_set_remove_different(s, y, s.choose());
                assert(s.contains(y));
                assert(y == x);
                assert(false);
            }
        }
        assert(s.remove(s.choose()) =~= Set::<A>::empty());
        assert(s.remove(s.choose()) == Set::<A>::empty());

        reveal(Set::to_multiset);
        assert(Set::<A>::empty().to_multiset() == Multiset::<A>::empty()) by {
            assert(Set::<A>::empty().len() == 0);
        }
        assert(s.to_multiset()
            == Multiset::<A>::empty().insert(s.choose()).add(Set::<A>::empty().to_multiset()));
        assert(s.to_multiset()
            == Multiset::<A>::empty().insert(x).add(Multiset::<A>::empty()));
        assert_multisets_equal!(
            Multiset::<A>::empty().insert(x).add(Multiset::<A>::empty()),
            Multiset::<A>::empty().insert(x)
        );
    }

    proof fn map_to_multiset_singleton<K,V>(k: K, v: V)
    ensures
        map_to_multiset(map!{k => v}) == multiset_map_singleton(k, v)
    {
        let m = map!{k => v};
        reveal(map_to_multiset);
        reveal(multiset_map_singleton);
        Self::singleton_map_dom(k, v);
        assert forall |kv| m.kv_pairs().contains(kv) implies kv == (k, v) by {
            if m.kv_pairs().contains(kv) {
                reveal(Map::kv_pairs);
                assert(m.dom().contains(kv.0));
                assert(m.dom().contains(kv.0) <==> kv.0 == k);
                assert(kv.0 == k);
                vstd::map::axiom_map_insert_same(Map::<K,V>::empty(), k, v);
                assert(m[k] == v);
                assert(kv.1 == v);
                assert(kv == (k, v));
            }
        }
        assert forall |kv| kv == (k, v) implies m.kv_pairs().contains(kv) by {
            if kv == (k, v) {
                reveal(Map::kv_pairs);
                assert(m.dom().contains(k));
                vstd::map::axiom_map_insert_same(Map::<K,V>::empty(), k, v);
                assert(m[k] == v);
            }
        }
        assert(m.kv_pairs() =~= set!{(k, v)});
        assert(m.kv_pairs() == set!{(k, v)});
        Self::set_singleton_to_multiset((k, v));
        assert(m.kv_pairs().to_multiset() == set!{(k, v)}.to_multiset());
        assert(m.kv_pairs().to_multiset() == Multiset::empty().insert((k, v)));
    }

    proof fn cache_resps_singleton(pre_cache_reqs: Map<ID, Address>, id: ID, addr: Address, resp: DiskResponse)
    requires
        pre_cache_reqs.is_injective(),
        pre_cache_reqs.contains_key(id),
        pre_cache_reqs[id] == addr,
    ensures ({
        let resp_map = map!{id => resp};
        let finished_cache_reqs = pre_cache_reqs.restrict(resp_map.dom()).invert();
        let cache_resps = Map::new(|a| finished_cache_reqs.contains_key(a), |a| resp_map[finished_cache_reqs[a]]);
        cache_resps == map!{addr => resp}
    })
    {
        let resp_map = map!{id => resp};
        Self::singleton_map_dom(id, resp);

        let restricted = pre_cache_reqs.restrict(resp_map.dom());
        assert_maps_equal!(restricted, map!{id => addr}, k => {
            if k == id {
                assert(pre_cache_reqs.contains_key(k));
                assert(resp_map.dom().contains(k));
                assert(restricted[k] == pre_cache_reqs[k]);
                assert(restricted[k] == addr);
            } else {
                assert(!resp_map.dom().contains(k));
            }
        });

        let finished_cache_reqs = restricted.invert();
        Self::invert_singleton(id, addr);
        assert(finished_cache_reqs == map!{addr => id});

        let cache_resps = Map::new(|a| finished_cache_reqs.contains_key(a), |a| resp_map[finished_cache_reqs[a]]);
        assert_maps_equal!(cache_resps, map!{addr => resp}, k => {
            if k == addr {
                Self::singleton_map_dom(addr, id);
                assert(finished_cache_reqs.contains_key(k));
                assert(finished_cache_reqs[k] == id);
                assert(cache_resps[k] == resp_map[id]);
                assert(cache_resps[k] == resp);
            } else {
                assert(!finished_cache_reqs.contains_key(k));
            }
        });
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
                    snapshot: CachedJournal_v::JournalSnapshot{
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

    exec fn handle_disk_cache_load_response(&mut self, id: ID, disk_response: IDiskResponse, response_shard: Tracked<DiskRespShard>, req_info: OutstandingReqInfo, pre_outstanding: Ghost<Map<ID, OutstandingReqInfo>>, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).good_disk_response(id, disk_response, response_shard@),
        response_shard@.multiset() == multiset_map_singleton(id, disk_response@),
        old(self).outstanding_requests@ == pre_outstanding@.remove(id),
        pre_outstanding@.contains_key(id),
        pre_outstanding@[id] == req_info,
        req_info is CacheLoadReq,
        Self::outstanding_requests_wf_map(pre_outstanding@, old(self).cache),
        Self::outstanding_requests_match_cache_reqs_map(pre_outstanding@, old(self).state().outstanding_cache_reqs),
    ensures
        self.inv_api(api),
        self.recovery_phase == old(self).recovery_phase,
    {
        let ghost pre_outstanding = pre_outstanding@;
        let OutstandingReqInfo::CacheLoadReq{read_addr, mut load_handle} = req_info else { unreached() };
        let data = match disk_response {
            IDiskResponse::ReadResp{data} => data,
            IDiskResponse::WriteResp{} => {
                assume(false); // should be impossible for a cache load
                unreached()
            }
        };

        // assume disk always returns full pages
        assume(data.len() == PAGE_SIZE_BYTES);
        load_handle.rec = data;
        self.cache.load_release(&read_addr, load_handle);

        let ghost pre_cache_reqs = old(self).state().outstanding_cache_reqs;
        let ghost pre_state = self.model@.value();
        let ghost resp_map = map!{id => disk_response@};
        let ghost disk_request_tuples = Multiset::empty();
        let ghost disk_response_tuples = multiset_map_singleton(id, disk_response@);
        let ghost post_state = ConcreteProgramModel{
            state: AtomicState{
                cache: self.cache@,
                outstanding_cache_reqs: pre_state.state.outstanding_cache_reqs.remove_keys(resp_map.dom()),
                ..pre_state.state
            }
        };

        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof { tracked_swap(self.model.borrow_mut(), &mut model); }

        proof {
            let info = ProgramDiskInfo{reqs: disk_request_tuples, resps: disk_response_tuples};
            let disk_event = DiskEvent::CacheIOEnd{resp_map};
            let new_outstanding_cache_reqs = pre_state.state.outstanding_cache_reqs.remove_keys(resp_map.dom());
            let finished_cache_reqs = pre_state.state.outstanding_cache_reqs.restrict(resp_map.dom()).invert();
            let cache_resps = Map::new(|addr| finished_cache_reqs.contains_key(addr), |addr| resp_map[finished_cache_reqs[addr]]);
            // trigger
            assert(map_to_multiset(resp_map) == info.resps) by {
                Self::map_to_multiset_singleton(id, disk_response@);
            }
            assert(cache_resps == map!{read_addr@ => disk_response@}) by {
                Self::cache_resps_singleton(pre_cache_reqs, id, read_addr@, disk_response@);
            }
            assert(Cache::State::next(pre_state.state.cache, post_state.state.cache,
                Cache::Label::DiskOps{requests: set![], responses: cache_resps})) by {
                assert(Cache::State::next(pre_state.state.cache, post_state.state.cache,
                    Cache::Label::DiskOps{requests: set![], responses: map!{read_addr@ => disk_response@}}));
            }
            assert(AtomicState::disk_transition(pre_state.state, post_state.state, disk_event, info.reqs, info.resps));
            assert(ConcreteProgramModel::valid_disk_transition(pre_state, post_state, info));
            assert(ConcreteProgramModel::next(pre_state, post_state, ProgramLabel::DiskIO{info}));
        }

        let tracked _disk_req_token = self.instance.borrow().disk_transitions(
            KVStoreTokenized::Label::DiskOp{
                disk_request_tuples,
                disk_response_tuples,
            },
            post_state,
            &mut model,
            response_shard.get(),
        );

        self.model = Tracked(model);
        proof {
            self.system_inv_implies_atomic_state_wf();
        }
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
        let ghost pre_outstanding = self.outstanding_requests@;
        let req_info = self.outstanding_requests.remove_take(&id);
        match req_info {
            None => { Self::todo_placeholder(); }
            Some(req_info) => match req_info {
                OutstandingReqInfo::SuperBlockReq{} => {
                    self.handle_disk_superblock_write_response(id, disk_response, response_shard, api);
                },
                OutstandingReqInfo::CacheLoadReq{..} => {
                    self.handle_disk_cache_load_response(id, disk_response, response_shard, req_info, Ghost(pre_outstanding), api);
                },
                OutstandingReqInfo::CacheWriteReq{write_addr, handle} => {
                    assume(false);
                },
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
        let ghost pre_outstanding = self.outstanding_requests@;
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
            assert(self.store.wf());
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
                assert(superblock@@ == psb);
                assert(psb.journal == superblock.journal_snapshot@);
                assert(self.journal@.snapshot == superblock.journal_snapshot@);
                assert(psb.store.seq_end == psb.journal.boundary_lsn);
                self.journal.view_seq_start_ensures();
                assert(psb.store.seq_end == self.journal.seq_start());

                // Something about constructing a ProgramDiskInfo object is necessary to trigger a
                // pattern match in the disk_transitions preconditions below.
                let info = ProgramDiskInfo{
                    reqs: disk_request_tuples,
                    resps: disk_response_tuples,
                };
                assert(post_state.state.store.ephemeral is Known);
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
            assert(self.i().store.ephemeral is Known);
            proof {
                assert(self.state().store.persistent.seq_end == self.journal.seq_start());
            }
        }

        api.log("recovery phase now ReadingJournalIndex");
        self.recovery_phase = RecoveryPhase::ReadingJournalIndex;

        proof {
            assert(self.outstanding_requests@ == pre_outstanding);
            assert(pre_outstanding == Map::<ID, OutstandingReqInfo>::empty()) by {
                reveal(Implementation::inv);
                assert(old(self).inv());
                assert(old(self).recovery_phase is FetchingSuperblock);
                assert(old(self).inv_recover());
                reveal(Implementation::inv_recover);
            }
            assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty());
            assert forall |id| #[trigger] self.outstanding_requests@.contains_key(id)
                implies self.outstanding_requests@[id] is CacheLoadReq
            by {
                if self.outstanding_requests@.contains_key(id) {
                    broadcast use vstd::map::axiom_map_empty;
                    assert(!Map::<ID, OutstandingReqInfo>::empty().contains_key(id));
                    assert(false);
                }
            }
        }
        assert( self.inv() );
    }

    fn recover_read_journal_index(&mut self, api: &mut ClientAPI<ConcreteProgramModel>) -> (progress: bool)
    requires
        old(self).inv(),
        old(self).inv_api(old(api)),
        old(self).recovery_phase is ReadingJournalIndex,
    ensures
        self.inv(),
        self.inv_api(api),
        self.recovery_phase is ReadingJournalIndex || self.recovery_phase is ApplyingJournalToRecoverEphemeralMap,
    {
        assert( self.journal.wf() );
        
        let ghost pre_state = self.model@.value();
        let ghost pre_outstanding = self.outstanding_requests@;
        let ghost cache_before_index = self.cache;
        let ghost start_store_lsn = self.store_lsn as nat;
        let ghost start_journal_seq_start = self.journal.seq_start();
        proof {
            assert(self.inv());
            assert(self.recovery_phase is ReadingJournalIndex);
            assert(self.inv_reading_journal()) by {
                reveal(Implementation::inv);
                assert(self.inv());
            }
            assert(start_store_lsn == start_journal_seq_start);
            self.system_inv_implies_atomic_state_wf();
            assert(pre_state.state.wf());
        }
        let result = self.journal.recover_index_step(&mut self.cache);
        proof {
            assert(self.cache.valid_load_handles_preserved(cache_before_index));
        }

        match result {
            RecoverIndexResult::CacheLoad{slot_handle, addr} => {
            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

                let ghost old_outstanding = self.outstanding_requests@;
                proof {
                    assert(self.outstanding_requests@ == pre_outstanding);
                }

                let req_id_perm = Tracked( api.send_disk_request_predict_id() );
                let disk_req = IDiskRequest::ReadReq{from: addr};

                let ghost post_state = ConcreteProgramModel{
                    state: AtomicState{
                        journal: self.journal@,
                        cache: self.cache@,
                        outstanding_cache_reqs: pre_state.state.outstanding_cache_reqs.insert(req_id_perm@, addr@),
                        ..pre_state.state
                    }
                };

                let ghost disk_request_tuples = multiset_map_singleton(req_id_perm@, disk_req@);
                let ghost disk_response_tuples = Multiset::empty();

                proof {
                    let program_lbl = ProgramLabel::DiskIO{info: ProgramDiskInfo{
                        reqs: disk_request_tuples, 
                        resps: disk_response_tuples, 
                    }};
                    let ghost req_map = map!{req_id_perm@ => disk_req@};
                    let disk_event = DiskEvent::CacheIOBegin{req_map};
                    let cache_lbl = cache_load_label(&addr);
                    assert(map_to_multiset(disk_event->req_map) == disk_request_tuples) by {
                        Self::map_to_multiset_singleton(req_id_perm@, disk_req@);
                    }
                    assert(disk_event->req_map.values() == set!{disk_req@}) by {
                        Self::singleton_map_value(req_id_perm@, disk_req@);
                    }

                    assert(Cache::State::next(old(self).cache@, self.cache@, cache_lbl));
                    assert(Cache::State::next(pre_state.state.cache, post_state.state.cache, cache_lbl));
                    assert(!cache_before_index.entry_fetched(&addr));

                    let updated_outstanding_cache_reqs = Map::new(|id| disk_event->req_map.contains_key(id), |id| disk_event->req_map[id].addr());
                    let new_outstanding_cache_reqs = pre_state.state.outstanding_cache_reqs.union_prefer_right(updated_outstanding_cache_reqs);
                    assert(updated_outstanding_cache_reqs == map!{req_id_perm@ => addr@}) by {
                        assert_maps_equal!(updated_outstanding_cache_reqs, map!{req_id_perm@ => addr@}, id2 => {
                            if id2 == req_id_perm@ {
                                assert(disk_event->req_map.contains_key(id2));
                                assert(updated_outstanding_cache_reqs.contains_key(id2));
                                assert(updated_outstanding_cache_reqs[id2] == disk_event->req_map[id2].addr());
                                vstd::map::axiom_map_insert_same(Map::<ID, DiskRequest>::empty(), req_id_perm@, disk_req@);
                                assert(disk_event->req_map[id2] == disk_req@);
                                assert(updated_outstanding_cache_reqs[id2] == addr@);
                                vstd::map::axiom_map_insert_same(Map::<ID, Address>::empty(), req_id_perm@, addr@);
                            } else {
                                assert(!disk_event->req_map.contains_key(id2)) by {
                                    Self::singleton_map_dom(req_id_perm@, disk_req@);
                                }
                                assert(!updated_outstanding_cache_reqs.contains_key(id2));
                                assert(!map!{req_id_perm@ => addr@}.contains_key(id2)) by {
                                    Self::singleton_map_dom(req_id_perm@, addr@);
                                }
                            }
                        });
                    }
                    assert(new_outstanding_cache_reqs == pre_state.state.outstanding_cache_reqs.insert(req_id_perm@, addr@)) by {
                        vstd::map_lib::lemma_union_insert_right(pre_state.state.outstanding_cache_reqs, Map::<ID, Address>::empty(), req_id_perm@, addr@);
                        assert(pre_state.state.outstanding_cache_reqs.union_prefer_right(Map::<ID, Address>::empty()) =~= pre_state.state.outstanding_cache_reqs);
                    }
                    assert(post_state.state.outstanding_cache_reqs == new_outstanding_cache_reqs);
                    assert(AtomicState::cache_io_begin(pre_state.state, post_state.state, disk_event->req_map, disk_request_tuples, disk_response_tuples));
                    assert(AtomicState::disk_transition(pre_state.state, post_state.state, disk_event, program_lbl->info.reqs, program_lbl->info.resps)); // witness
                    assert(ConcreteProgramModel::valid_disk_transition(pre_state, post_state, program_lbl->info)); 
                    assert(ConcreteProgramModel::next(pre_state, post_state, program_lbl)); 
                }

                let tracked empty_disk_responses: DiskRespShard = DiskRespShard::empty(self.instance_id());
                let tracked new_disk_req_token = self.instance.borrow().disk_transitions(
                    KVStoreTokenized::Label::DiskOp{
                        disk_request_tuples,
                        disk_response_tuples
                    },
                    post_state,
                    &mut model,
                    empty_disk_responses,
                );
                self.model = Tracked(model);

                let id = api.send_disk_request(disk_req, req_id_perm, Tracked(new_disk_req_token));
                self.outstanding_requests.insert(id, OutstandingReqInfo::CacheLoadReq{read_addr: addr, load_handle: slot_handle});
                proof {
                    let ghost new_info = OutstandingReqInfo::CacheLoadReq{read_addr: addr, load_handle: slot_handle};
                    assert(self.cache.entry_fetched(&addr));
                    assert(self.cache.valid_load_handle(&addr, slot_handle));
                    assert(self.outstanding_requests@ == old_outstanding.insert(id, new_info));
                    assert(self.outstanding_requests_match_cache_reqs()) by {
                        let ghost new_outstanding = self.outstanding_requests@;
                        let ghost new_cache_reqs = post_state.state.outstanding_cache_reqs;
                        let ghost old_cache_reqs = pre_state.state.outstanding_cache_reqs;
                        assert(new_outstanding == old_outstanding.insert(id, new_info));
                        assert(new_cache_reqs == old_cache_reqs.insert(id, addr@));

                        assert(new_cache_reqs.is_injective()) by {
                            reveal(Implementation::outstanding_requests_match_cache_reqs);
                            assert(old_cache_reqs.is_injective());

                            assert(!old_cache_reqs.contains_value(addr@)) by {
                                if old_cache_reqs.contains_value(addr@) {
                                    assert(pre_state.state.wf());
                                    assert(old_cache_reqs.values().contains(addr@)) by {
                                        reveal(Map::values);
                                        assert(old_cache_reqs.contains_value(addr@));
                                    }
                                    assert(pre_state.state.outstanding_cache_reqs.values() <= pre_state.state.cache.lookup_map.dom());
                                    assert(pre_state.state.cache.lookup_map.dom().contains(addr@)) by {
                                        assert(pre_state.state.outstanding_cache_reqs.values().contains(addr@));
                                    }
                                    assert(pre_state.state.cache == cache_before_index@);
                                    assert(cache_before_index@.lookup_map.dom().contains(addr@));
                                    assert(cache_before_index.entry_fetched(&addr)) by {
                                        assert(cache_before_index@.lookup_map.contains_key(addr@)) by {
                                            reveal(Map::contains_key);
                                        }
                                        FracCacheImpl::entry_fetched_from_view(&cache_before_index, &addr);
                                    }
                                    assert(false);
                                }
                            }

                        }

                    }
                }
                proof {
                    assert(self.store_lsn as nat == start_store_lsn);
                    assert(self.journal.seq_start() == start_journal_seq_start);
                    assert(self.store_lsn as nat == self.journal.seq_start());
                }
                assert( self.inv_api(api) );

                return false; // cache waiting on data, not ready to make more progress
            }
            RecoverIndexResult::IndexComplete{reads} => {
                self.recovery_phase = RecoveryPhase::ApplyingJournalToRecoverEphemeralMap;
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                let ghost pre_state = self.model@.value();
                proof { tracked_swap(self.model.borrow_mut(), &mut model); }

                let ghost post_state = ConcreteProgramModel{
                    state: AtomicState {
                        recovery_state: RecoveryState::JournalIndexComplete,
                        cache: self.cache@,
                        journal: self.journal@,
                        ..pre_state.state
                    }
                };

                proof {
                    assert(model.value() == pre_state);
                    assert(ConcreteProgramModel::valid_internal_transition(pre_state, post_state)) by {
                        assert(AtomicState::internal_transitions(
                            pre_state.state,
                            post_state.state,
                            InternalEvent::JournalRecovery{reads: reads@}
                        )) by {
                            let (cache_lbl, journal_lbl) = load_index_labels(reads@);
                            assert(pre_state.state.recovery_state is SuperblockAvailable);
                            assert(Cache::State::next(pre_state.state.cache, post_state.state.cache, cache_lbl));
                            assert(CachedJournal::State::next(pre_state.state.journal, post_state.state.journal, journal_lbl));
                            assert(AtomicState::journal_recovery(pre_state.state, post_state.state, reads@));
                        };
                    }
                    assert(ConcreteProgramModel::next(pre_state, post_state, ProgramLabel::Internal{}));
                }

                let tracked new_reply_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp{},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);

                // index complete means that we can now 
                assert( self.i().recovery_state is JournalIndexComplete );
                proof {
                    assert(self.store_lsn as nat == start_store_lsn);
                    assert(self.journal.seq_start() == start_journal_seq_start);
                    assert(self.store_lsn as nat == self.journal.seq_start());
                    assert(self.journal.seq_start() <= self.journal.seq_end());
                    assert(self.store_lsn as nat <= self.journal.seq_end());
                }
                proof {
                    self.system_inv_implies_atomic_state_wf();
                }
                assert(self.inv());
                assert(self.inv_api(api));
            }
            RecoverIndexResult::IndexProgress{} => { }
        }
        assert(self.inv());
        assert(self.inv_api(api));
        return true; // either index is complete or journal has made progress building the index
    }

    fn recover_apply_journal_to_recover_ephemeral_map(&mut self, api: &mut ClientAPI<ConcreteProgramModel>) -> (progress: bool)
    requires
        old(self).inv_api(old(api)),
        old(self).recovery_phase is ApplyingJournalToRecoverEphemeralMap,
    ensures
        self.inv_api(api),
        self.recovery_phase is ApplyingJournalToRecoverEphemeralMap
            || self.recovery_phase is ReadyForUserOperation,
    {
        let exec_seq_end = self.journal.exec_seq_end();
        if self.store_lsn < exec_seq_end {
            // 

            // get the journal record
            // how to apply it 

            // how do we apply journal pages?
            // we parse and return a journal record out?
            // this would be the easiest option, and 

            Self::todo_placeholder();   // Go restore more blocks from journal
            // this branch may return progress false if we are waiting for
            // disk IO to fetch the next page.
        }

        // assert(self.store_lsn == self.journal.seq_end());
        // assert(self.store_lsn == self.state().ephemeral_map().seq_end);
        // assert(self.journal.seq_end() == self.state().ephemeral_map().seq_end);

        let ghost pre_state = self.state();
        proof {
            assert(self.inv_api(api));
            assert(self.recovery_phase is ApplyingJournalToRecoverEphemeralMap);
            assert(self.inv_applying_journal()) by {
                reveal(Implementation::inv);
                assert(self.inv());
            }
            assert(self.store_lsn >= exec_seq_end);
            assert(exec_seq_end == self.journal.seq_end());
            assert(self.store_lsn as nat >= self.journal.seq_end());
            assert(self.store_lsn as nat == self.journal.seq_end()) by {
                assert(self.store_lsn as nat <= self.journal.seq_end());
            }
            self.journal.view_seq_end_ensures();
            assert(pre_state.ephemeral_map().seq_end == pre_state.journal.seq_end()) by {
                assert(self.store_lsn as nat == pre_state.ephemeral_map().seq_end);
                assert(pre_state.journal == self.journal@);
                assert(pre_state.journal.status is Some);
                assert(pre_state.journal.seq_end() == self.journal.seq_end());
                assert(pre_state.ephemeral_map().seq_end == self.journal.seq_end());
            }
        }

        {
            self.recovery_phase = RecoveryPhase::ReadyForUserOperation;

            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

//             assert( model.value()@ == self.state() )@;
            assert( model.value() == ConcreteProgramModel { state: pre_state } );
            let ghost post_state = ConcreteProgramModel{
                state: AtomicState {
                    recovery_state: RecoveryState::RecoveryComplete,
                    journal: pre_state.journal,
                    persistent_journal_seq_end: pre_state.ephemeral_map().seq_end,
                    ..pre_state
                }
            };

            proof {
                assert(model.value() == ConcreteProgramModel { state: pre_state });
                assert(ConcreteProgramModel::valid_internal_transition(
                    ConcreteProgramModel { state: pre_state }, post_state
                )) by {
                    assert(AtomicState::internal_transitions(
                        pre_state,
                        post_state.state,
                        InternalEvent::RecoveryComplete{}
                    )) by {
                        let end_lsn = pre_state.ephemeral_map().seq_end;
                        let journal_lbl = CachedJournal::Label::QueryEndLsn{end_lsn: end_lsn};
                        assert(pre_state.recovery_state is JournalIndexComplete);
                        reveal(CachedJournal::State::next_by);
                        reveal(CachedJournal::State::next);
                        assert(CachedJournal::State::next_by(
                            pre_state.journal,
                            post_state.state.journal,
                            journal_lbl,
                            CachedJournal::Step::query_end_lsn()
                        ));
                        assert(AtomicState::recovery_complete(pre_state, post_state.state));
                    };
                }
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
            proof {
                self.system_inv_implies_atomic_state_wf();
            }

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
    ensures *api == *old(api) // liiiies
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
        &&& self.state().cache == self.cache@
        &&& self.outstanding_requests_wf()
        &&& self.outstanding_requests_match_cache_reqs()
        &&& self.outstanding_requests@.dom() == Set::<ID>::empty()
    }

    closed spec fn instance_id(self) -> InstanceId
    {
        self.instance@.id()
    }

    fn new() -> (out: Self)
        ensures out.wf_init()
    {
        let cache = FracCacheImpl::new();
        let tracked (
            Tracked(instance),
            Tracked(model),         // non sharded model
            Tracked(requests),      // request perm map (multiset), empty
            Tracked(replies),       // reply perm map (multiset), empty
            Tracked(disk_requests),
            Tracked(disk_responses),
        ) = KVStoreTokenized::Instance::initialize(ConcreteProgramModel{state: AtomicState::init(cache.total_slots() as nat)});

        // TODO maybe another Option<> wrapper?
        let placeholder_snapshot = IJournalSnapshot{
            boundary_lsn: 0, freshest_rec: None, };
        let selff = Implementation{
            recovery_phase: RecoveryPhase::FetchingSuperblock,
            sync_counter: 0,
            store: new_empty_vec_map(),
            store_lsn: 7,
            journal: JournalImpl::new(placeholder_snapshot),
            cache,
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
        proof { assert(self.inv()); }
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

} // verus!
