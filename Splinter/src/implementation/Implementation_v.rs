// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use builtin::*;
use builtin_macros::*;
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

use crate::spec::MapSpec_t::{ID, MapSpec, PersistentState};
use crate::spec::TotalKMMap_t::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::spec::FloatingSeq_t::*;
use crate::abstract_system::StampedMap_v;
use crate::abstract_system::StampedMap_v::{StampedMap};
use crate::abstract_system::MsgHistory_v::{MsgHistory, KeyedMessage};
use crate::abstract_system::AbstractCrashAwareSystemRefinement_v;

use crate::implementation::ModelRefinement_v::*;
use crate::implementation::ConcreteProgramModel_v::*;
use crate::implementation::AtomicState_v::*;
use crate::implementation::MultisetMapRelation_v::*;
use crate::implementation::VecMap_v::*;
use crate::implementation::JournalTypes_v::*;
use crate::implementation::SuperblockTypes_v::*;
use crate::marshalling::Marshalling_v::Deepview;
use crate::marshalling::WF_v::WF;


#[allow(unused_imports)]
use vstd::multiset::*;
#[allow(unused_imports)]
use vstd::tokens::*;
#[allow(unused_imports)]
use crate::spec::AsyncDisk_t::*;
use crate::spec::ImplDisk_t::*;
#[allow(unused_imports)]
use crate::implementation::DiskLayout_v::*;

verus!{

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
// This struct supplies KVStoreTrait, which has both the entry point to the implementation and the
// proof hooks to satisfy the refinement obligation trait.
pub struct Implementation {
    store: VecMap<Key, Value>,
    journal: Journal,
    version: u64,

    model: Tracked<KVStoreTokenized::model<ConcreteProgramModel>>,
    instance: Tracked<KVStoreTokenized::Instance<ConcreteProgramModel>>,

    sync_requests: SyncRequestBuffer,
}

// This struct supplies KVStoreTrait, which has both the entry point to the implementation and the
// proof hooks to satisfy the refinement obligation trait.
// this was Jon's thing, I guess? Replaced by Jialin's thing above?
// pub struct Implementation {
//     // store: HashMapWithView<Key, Value>,
//     journal: Journal,
//
//     // token for the program model variable
//     model: Tracked<ModelShard>,
//
//     // we do not own a mutable reference to this
//     instance: Tracked<KVStoreTokenized::Instance<ConcreteProgramModel>>,
//
//     sync_requests: SyncRequestBuffer,
// }

pub type RequestShard = KVStoreTokenized::requests<ConcreteProgramModel>;
pub type ReplyShard = KVStoreTokenized::replies<ConcreteProgramModel>;

pub type DiskRespShard = KVStoreTokenized::disk_responses_multiset<ConcreteProgramModel>;
pub type DiskReqShard = KVStoreTokenized::disk_requests_multiset<ConcreteProgramModel>;


impl Journal {
    pub open spec fn inv(self) -> bool
    {
        self@.wf()
    }

    pub closed spec fn to_stamped_map(&self) -> StampedMap
    {
        MsgHistory::map_plus_history(StampedMap_v::empty(), self@)
    }

    fn new_empty() -> (out: Self)
        ensures out.inv(), out@.is_empty(), out.seq_start == 0
    {
        Journal{ msg_history: vec![], seq_start:0 }
    }

    fn insert(&mut self, key: Key, value: Value)
        requires old(self).inv()
        ensures
            self.inv(),
            self@.seq_start == old(self)@.seq_start,
            self@.seq_end == old(self)@.seq_end+1,
            self@.msgs =~= old(self)@.msgs.insert(old(self)@.seq_end,
                KeyedMessage{key, message: Message::Define{value}}),
    {
        self.msg_history.push(KeyedMessage{key, message: Message::Define{value}})
    }
}

impl Implementation {
    closed spec(checked) fn view_as_kmmap(self) -> TotalKMMap
        recommends self.journal.seq_start == 0
    {
        self.view_as_floating_versions().last().appv.kmmap
    }

    closed spec(checked) fn view_as_floating_versions(self) -> FloatingSeq<PersistentState>
        recommends self.journal.seq_start == 0
    {
        AbstractCrashAwareSystemRefinement_v::floating_versions(
            StampedMap_v::empty(), self.journal@, self.journal.seq_start as nat)
    }

    broadcast proof fn view_as_kmmap_ensures(self)
        requires self.journal.seq_start == 0, self.journal.inv()
        ensures #[trigger] self.view_as_kmmap() =~= MsgHistory::map_plus_history(StampedMap_v::empty(), self.journal@).value
    {
        assert(self.journal@.discard_recent((self.journal@.seq_end) as nat) =~= self.journal@);
    }

    pub closed spec fn i(self) -> AtomicState {
        self.state()
    }

    closed spec fn state(&self) -> AtomicState
    {
        self.model@.value().state

    // pub history: FloatingSeq<PersistentState>,

    // // tells us what syncs can be replied
    // pub persistent_version: nat,

    // // tells us what we can bump persistent_version when the disk response comes back.
    // pub in_flight: Option<InflightInfo>,

    // // maps each syncreq id with a version
    // pub sync_req_map: Map<SyncReqId, nat>,
// }
        // self.model@.value().state
    }

    closed spec fn version(&self) -> nat
    {
        (self.journal.seq_start + self.journal.msg_history.len()) as nat
    }

    closed spec fn inv(self) -> bool {
        let state = self.state();

        &&& self.store.wf()
        &&& self.model@.instance_id() == self.instance@.id()
        &&& state.recovery_state is RecoveryComplete

        // model
        // &&& self.i().mapspec().kmmap == self.view_as_kmmap()
        &&& self.i().history == self.view_as_floating_versions()

        &&& (state.in_flight is Some
            <==> self.sync_requests.in_flight())
        &&& self.sync_requests.wf(self.instance@.id())

        // physical version num tracks ghost model versions
        &&& self.version() == self.state().history.len()-1
        &&& self.journal.seq_start == 0

        &&& (state.in_flight is Some ==> {
            // The in-flight version stays active so get_suffix doesn't choke on it when it's time
            // to handle the disk response
            &&& state.history.is_active(state.in_flight->Some_0.version as int)
            // The in-flight 'satisfied requests' can indeed be satisfied by the in-flight version
            &&& self.sync_reqs_in_version(self.sync_requests.satisfied_reqs@, state.in_flight->Some_0.version as int)
        })
        &&& self.sync_reqs_in_version(self.sync_requests.deferred_reqs@, self.version() as int)
        &&& Self::sync_req_lists_mutually_unique(self.sync_requests.satisfied_reqs@, self.sync_requests.deferred_reqs@)
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
    ensures
        self.inv_api(api),
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
                    reveal(MapSpec::State::next);
                    reveal(MapSpec::State::next_by);
                    assert( MapSpec::State::next_by(post_state.state.history.last().appv, post_state.state.history.last().appv,
                            map_lbl, MapSpec::Step::noop())); // witness to step
                    assert( post_state.state.history.get_prefix(pre_state.state.history.len()) == pre_state.state.history );  // extn
                    assert( AtomicState::map_transition(pre_state.state, post_state.state, map_req, map_reply) );
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
        req.input is PutInput,
    ensures
        self.inv_api(api),
    {
        broadcast use
            Implementation::view_as_kmmap_ensures,
            MsgHistory::map_plus_history_lemma;

        let out = match req.input {
        Input::PutInput{key, value} => {
            let ghost pre_state = self.model@.value();

            self.journal.insert(key.clone(), value);

            assert(self.journal@.msgs == old(self).journal@.msgs.insert(old(self).journal@.seq_end,
                KeyedMessage{key, message: Message::Define{value}}));

            assert(self.journal@.msgs[old(self).journal@.seq_end].key == key);

            let reply = Reply{output: Output::PutOutput, id: req.id};
            let ghost post_state = ConcreteProgramModel{
                state: AtomicState{
                    history: self.view_as_floating_versions(),
                    ..self.state()
                }
            };

            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

            proof {
                let map_req = req.mapspec_req();
                let map_reply = reply.mapspec_reply();
                let ghost map_lbl = MapSpec::Label::Put{input: map_req.input, output: map_reply.output};
                reveal(MapSpec::State::next);
                reveal(MapSpec::State::next_by);

                assert forall |lsn| self.journal@.seq_start <= lsn <= old(self).journal@.seq_end
                implies self.journal@.discard_recent(lsn) =~= old(self).journal@.discard_recent(lsn) by {}

                assert(self.view_as_kmmap() =~= old(self).view_as_kmmap().insert(key, Message::Define{value}));
                assert( MapSpec::State::next_by(pre_state.state.mapspec(), post_state.state.mapspec(), map_lbl, MapSpec::Step::put())); // witness to step

                assert( post_state.state.history.get_prefix(pre_state.state.history.len()) =~= pre_state.state.history );  // extn
                assert( AtomicState::map_transition(pre_state.state, post_state.state, map_req, map_reply) );
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

            assert( self.i().mapspec().kmmap == self.view_as_kmmap() ); // trigger extn equality
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
    }

    pub exec fn handle_query(&mut self, req: Request, req_shard: Tracked<RequestShard>, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).good_req(req, req_shard@),
        req.input is QueryInput,
    ensures
        self.inv_api(api),
    {
        match req.input {
        Input::QueryInput{key} => {
            /*
            let value = match self.store.get(&key) {
                Some(v) => *v,
                None => { Value(0) },
            };

            let ghost pre_state = self.model@.value();
            let ghost post_state = pre_state;

            let reply = Reply{output: Output::QueryOutput{value: value}, id: req.id};

            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

            proof {
                let map_req = req.mapspec_req();
                let map_reply = reply.mapspec_reply();
                let ghost map_lbl = MapSpec::Label::Query{input: map_req.input, output: map_reply.output};
                reveal(MapSpec::State::next);
                reveal(MapSpec::State::next_by);
                assert( MapSpec::State::next_by(pre_state.state.mapspec(), post_state.state.mapspec(),
                        map_lbl, MapSpec::Step::query())); // witness to step
                assert( post_state.state.history.get_prefix(pre_state.state.history.len()) == pre_state.state.history );  // extn
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
            */
        },
            _ => unreached(),
        }
    }

    pub exec fn handle_sync_request(&mut self, req: Request, req_shard: Tracked<RequestShard>, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).good_req(req, req_shard@),
        req.input is SyncInput,
    ensures
        self.inv_api(api),
    {
        let ghost old_satisfied_reqs = old(self).sync_requests.satisfied_reqs@;
        let ghost old_deferred_reqs = old(self).sync_requests.deferred_reqs@;
        assert({
            &&& forall |i| #![auto] 0 <= i < old_satisfied_reqs.len() ==> old_satisfied_reqs[i].id != req.id
            &&& forall |i| #![auto] 0 <= i < old_deferred_reqs.len() ==> old_deferred_reqs[i].id != req.id
        }) by {
            self.system_inv_sync_request_fresh_id(req, req_shard);
            assume( false );    // fresh id stuff
        }

        // Consume the shard to convert into model state
        let ghost pre_state = self.model@.value();
        let ghost version = (pre_state.state.history.len()-1) as nat;
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

        self.maybe_launch_superblock(api);
    }

    pub exec fn maybe_launch_superblock(&mut self, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
    ensures
        self.inv_api(api),
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
    ensures
        self.inv_api(api),
    {
        proof { self.system_inv_implies_atomic_state_wf(); }

        let ghost version_index = self.version();

        // NOTE: swap out journal to avoid making a copy of it when marshalling the superblock
        // this is temporary because we are shoving map/journal right into the superblock
        // actual implementation will only contain pointers of these metadata and not the entire structure
        let mut tmp_journal = Journal::new_empty();
        std::mem::swap(&mut self.journal, &mut tmp_journal);
        let mut tmp_store = VecMap::new();
        std::mem::swap(&mut self.store, &mut tmp_store);
        // Why are we doing all this nonsense? Can't we just borrow this stuff immutably?

        let sb = ISuperblock{
            journal: tmp_journal,
            store: tmp_store.borrow_vec().clone(),  // TODO(jonh): clone perf mess
        };

        // Yoink the store out of self just long enough to marshall it as part of the superblock.
        let raw_page = DiskLayout::new().marshall(&sb);
        let ISuperblock{journal: mut tmp_journal, /*store: mut tmp_store,*/ ..} = sb;
        std::mem::swap(&mut self.journal, &mut tmp_journal);    // un-yoink
        std::mem::swap(&mut self.store, &mut tmp_store);    // un-yoink

        let req_id_perm = Tracked( api.send_disk_request_predict_id() );
        let ghost disk_req_id = req_id_perm@;
        let ghost disk_event = DiskEvent::ExecuteSyncBegin{req_id: disk_req_id};
        let disk_request = IDiskRequest::WriteReq{to: superblock_addr(), data: raw_page};
        let ghost disk_reqs = multiset_map_singleton(disk_req_id, disk_request@);
        let ghost info = ProgramDiskInfo{ reqs: disk_reqs, resps: Multiset::empty() };

        let ghost inflight_info = InflightInfo{version: version_index, req_id: disk_req_id};
        let ghost post_state = ConcreteProgramModel {
            state: AtomicState{
                in_flight: Some(inflight_info),
                ..old(self).state()}
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
            let pre_sb = self.state().ephemeral_sb();
            assume( false );    // TODO(jonh): left off trying to relate the disk request we just
                                // sent to the current ephemeral state. But Superblock doesn't seem
                                // connected to ASuperblock yet.
//             assert(pre_sb == ASuperblock{
//                 journal: self.journal.deepv(),
//                 store: self.store.borrow_vec()@,
// //                 version_index: self.version, // TODO(jonh): delete
//             }) by {
//                 self.view_as_kmmap_ensures();
//                 self.journal@.apply_to_stamped_map_length_lemma(StampedMap_v::empty());
//             }
            assert( disk_reqs == Multiset::singleton(
                (disk_event.arrow_ExecuteSyncBegin_req_id(),
                DiskRequest::WriteReq{to: spec_superblock_addr(), data: DiskLayout::spec_new().spec_marshall(pre_sb)}))
            );   // extn
            assert( AtomicState::disk_transition(self.state(), post_state.state, disk_event, info.reqs, info.resps) );  // witness
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
        std::mem::swap(&mut self.sync_requests.satisfied_reqs, &mut self.sync_requests.deferred_reqs);

        assert( new_reply_token.multiset() == multiset_map_singleton(req_id_perm@, disk_request@) );    // extn
        api.send_disk_request(disk_request, req_id_perm, Tracked(new_reply_token));
    }

    exec fn deliver_inflight_replies(&mut self, ready_reqs: &mut Vec<Request>, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).sync_reqs_in_version(old(ready_reqs)@, old(self).state().history.first_active_index()),
        // can't break in-flight inv because there aren't any satisfied_reqs during this call
        old(self).sync_requests.satisfied_reqs@.len()==0,
        Self::sync_req_lists_mutually_unique(old(ready_reqs)@, old(self).sync_requests.deferred_reqs@),
    ensures
        self.inv_api(api),
    {
        assert( ready_reqs@.take(ready_reqs@.len() as int) == ready_reqs@ ); // extn
        loop
        invariant
            self.inv_api(api),
            self.sync_reqs_in_version(ready_reqs@, self.state().history.first_active_index()),
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

    closed spec fn sync_reqs_in_version(&self, reqs: Seq<Request>, version_num: int) -> bool
    {
        &&& forall |i| #![auto] 0<=i<reqs.len() ==> {
            &&& reqs[i].input is SyncInput
            &&& self.sync_req_in_version(reqs[i].id, version_num)
        }
        &&& forall |i,j| #![auto] 0 <= i < reqs.len() && 0 <= j < reqs.len() && i!=j ==> reqs[i].id != reqs[j].id
    }

    closed spec fn sync_req_in_version(&self, id: ID, version_num: int) -> bool
    {
        self.state().sync_req_map[id] <= version_num
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
        old(self).sync_req_in_version(req.id, old(self).state().history.first_active_index()),
        old(self).no_matching_sync_req_id(req.id),
    ensures
        self.inv_api(api),
//         self.store == old(self).store,
//         self.sync_requests == old(self).sync_requests,
        (self.state() == AtomicState{
            sync_req_map: old(self).state().sync_req_map.remove(req.id),
            ..old(self).state()
        }),
        old(self).sync_requests.deferred_reqs@ == self.sync_requests.deferred_reqs@,
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
    ensures
        self.inv_api(api),
    {
        match req.input {
            Input::NoopInput => self.handle_noop(req, req_shard, api),
            Input::PutInput{..} => self.handle_put(req, req_shard, api),
            Input::QueryInput{..} => self.handle_query(req, req_shard, api),
            Input::SyncInput{} => self.handle_sync_request(req, req_shard, api),
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
//             assert( !system_model.state().sync_requests.contains(req.id) );
        }
//         multiset_map_singleton_ensures(disk_req_id, i_disk_response@);
//         assert(disk_response_token@.multiset().contains((disk_req_id, i_disk_response@))); //trigger
        assume( false );   // fresh id stuff
    }

    pub exec fn handle_disk_response(&mut self, id: ID, disk_response: IDiskResponse, response_shard: Tracked<DiskRespShard>,
        api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).good_disk_response(id, disk_response, response_shard@),
        response_shard@.multiset() == multiset_map_singleton(id, disk_response@),
    ensures
        self.inv_api(api),
    {
        let mut ready_reqs = vec![];
        std::mem::swap(&mut self.sync_requests.satisfied_reqs, &mut ready_reqs);
//         (ready_reqs,self.sync_requests.satisfied_reqs) = (self.sync_requests.satisfied_reqs,ready_reqs);

        // take a tokenized transition to mark disk response receipt

        // we just took out all the in-flights; need to simultaneously change model.value().state to
        // restore self.inv
        // TODO(jialin): why do these Noop requests have ids? :v/
        let ghost req = Request{input: Input::NoopInput, id: 0};
        let reply = Reply{output: Output::NoopOutput, id: 0};


        assume(false);

        let ghost pre_state = self.model@.value();
        let ghost new_persistent_version = pre_state.state.in_flight->Some_0.version;
        let ghost post_state = ConcreteProgramModel{ state: AtomicState{
            in_flight: None,
            history: pre_state.state.history.get_suffix(new_persistent_version as int),
            persistent_version: new_persistent_version,
            ..pre_state.state
        }};

        proof {
            // Learn this before we yoink model out of self
            assert( self.i().recovery_state is RecoveryComplete );
            self.system_inv_response_implies_in_flight(id, disk_response, response_shard);
        }

        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof { tracked_swap(self.model.borrow_mut(), &mut model); }

        proof {
            let info = ProgramDiskInfo{ reqs: Multiset::empty(), resps: response_shard@.multiset() };
            let disk_event = DiskEvent::ExecuteSyncEnd{};

            assert( response_shard@.multiset() == Multiset::singleton((pre_state.state.in_flight->Some_0.req_id, DiskResponse::WriteResp{})) );    // extn

            assert( AtomicState::disk_transition(
                pre_state.state, post_state.state, disk_event, info.reqs, info.resps) );    // witness
//             assert( ConcreteProgramModel::next(pre_state, post_state,
//                     ProgramLabel::DiskIO{ info }) );
        }

        let tracked empty_disk_requests:KVStoreTokenized::disk_requests_multiset<ConcreteProgramModel>
            = KVStoreTokenized::disk_requests_multiset::empty(self.instance_id());
        let tracked new_reply_token = self.instance.borrow().disk_transitions(
            KVStoreTokenized::Label::DiskOp{
                disk_request_tuples: empty_disk_requests.multiset(),
                disk_response_tuples: response_shard@.multiset()},
            post_state,
            &mut model,
            response_shard.get(),
        );
        self.model = Tracked(model);

        self.deliver_inflight_replies(&mut ready_reqs, api);

        // maybe launch another superblock
        self.maybe_launch_superblock(api);
    }

    fn recover(&mut self, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).wf_init(),
        old(self).instance_id() == old(api).instance_id()
    ensures
        self.inv(),
        self.instance_id() == api.instance_id()
    {
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
        { // braces to scope variables used in this step
            let ghost pre_state = self.model@.value();
            let disk_resp = IDiskRequest::ReadReq{from: superblock_addr() };
            let (disk_req_id, i_disk_response, disk_response_token) = api.receive_disk_response();
            let raw_page = match i_disk_response {
                IDiskResponse::ReadResp{data} => data,
                IDiskResponse::WriteResp{} => {
                    proof { self.system_inv_cannot_receive_write_response_during_recovery(disk_req_id, i_disk_response, disk_response_token); };
                    unreached()
                }
            };

            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

            let superblock = DiskLayout::new().parse(&raw_page);
            assert( superblock.store.wf() ) by {
                assume( false ); // LEFT OFF extract model invariant
            }
            // Record our learnings in the physical model.
            // self.store = superblock.store;

            assume(false);

            // // Compute the next ghost model and transition our token
            // let ghost post_state = ConcreteProgramModel{state: AtomicState {
            //     recovery_state: RecoveryState::RecoveryComplete,
            //     history: view_store_as_singleton_floating_seq(superblock.version_index as nat, superblock.store),
            //     in_flight: None,
            //     persistent_version: superblock.version_index as nat,
            //     sync_req_map: Map::empty(),
            // }};

            // let ghost disk_response_tuples = multiset_map_singleton(disk_req_id, i_disk_response@);
            // // proof { multiset_map_singleton_ensures(disk_req_id, i_disk_response@); }

            // let ghost disk_event = DiskEvent::CompleteRecovery{req_id: disk_req_id, raw_page: raw_page};
            // // let ghost disk_lbl = AsyncDisk::Label::DiskOps{
            // //             requests: Map::empty(),
            // //             responses: Map::empty().insert(disk_req_id, i_disk_response@),
            // //         };
            // let ghost disk_request_tuples = Multiset::empty();

            // // extn; why isn't it triggered by requires in macro output?
            // // (Might also make a nice broadcast lemma, if that was usable.)
            // // assert( disk_lbl->requests == multiset_to_map(disk_request_tuples) );   // extn
            // proof {
            //     let info = ProgramDiskInfo{
            //         reqs: disk_request_tuples,
            //         resps: disk_response_tuples,
            //     };
            //     // TODO: this is crazy, I have to use info.reqs otherwise it doesn't match for
            //     // valid disk transition
            //     multiset_map_singleton_ensures(disk_req_id, i_disk_response@);
            //     assert(disk_response_token@.multiset().contains((disk_req_id, i_disk_response@))); //trigger
            //                                                                                //
            //     // assert( valid_checksum(raw_page) );
            //     assert(AtomicState::disk_transition(
            //         pre_state.state, post_state.state, disk_event, info.reqs, info.resps));
            //     assert(ConcreteProgramModel::valid_disk_transition(pre_state, post_state, info));
            //     assert(ConcreteProgramModel::next(pre_state, post_state, ProgramLabel::DiskIO{info}));
            // }

            // let tracked disk_request_tokens = self.instance.borrow().disk_transitions(
            //     KVStoreTokenized::Label::DiskOp{
            //         disk_request_tuples,
            //         disk_response_tuples,
            //     },
            //     post_state,
            //     &mut model,
            //     disk_response_token.get(),
            // );
            // self.model = Tracked(model);
            // self.version = superblock.version_index;
        }
    }
}

impl KVStoreTrait for Implementation {
    type ProgramModel = ConcreteProgramModel;
    type Proof = RefinementProof;

    closed spec fn wf_init(self) -> bool {
        &&& self.model@.instance_id() == self.instance@.id()
        &&& self.model@.value().state.recovery_state is Begin
        &&& !self.sync_requests.in_flight()
        &&& self.sync_requests.deferred_reqs@.len() == 0
        &&& self.store.wf()
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
            Tracked(replies),       // reply perm map (multiset), empty\
            Tracked(disk_requests),
            Tracked(disk_responses),
        ) = KVStoreTokenized::Instance::initialize(ConcreteProgramModel{state: AtomicState::init()});

        let selff = Implementation{
            store: new_empty_hash_map(),
            journal: Journal::new_empty(),
            version: 0,
            model: Tracked(model),
            instance: Tracked(instance),
            sync_requests: SyncRequestBuffer::new_empty(),
        };
        selff
    }

    #[verifier::exec_allows_no_decreases_clause]    // main loop doesn't terminate
    fn kvstore_main(&mut self, mut api: ClientAPI<Self::ProgramModel>)
    {
        self.recover(&mut api);

        let debug_print = true;
        loop
        invariant
            self.inv_api(&api),
            self.model@.value().state.recovery_state is RecoveryComplete,
        {
            let poll_result = api.poll();
            if poll_result.disk_response_ready {
                let (id, disk_response, response_shard) = api.receive_disk_response();
                self.handle_disk_response(id, disk_response, response_shard, &mut api);
            }
            if poll_result.user_input_ready {
                let (req, req_shard) = api.receive_request(debug_print);
                self.handle_user_request(req, req_shard, &mut api);
            }
        }
    }
}

pub fn new_empty_hash_map() -> (out: VecMap<Key,Value>)
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
