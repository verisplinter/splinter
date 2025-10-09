#[allow(unused_imports)]    // lost in erasure
use verus_builtin::*;
use vstd::prelude::*;

use vstd::{multiset::Multiset};
use crate::spec::AsyncDisk_t::*;
use crate::spec::MapSpec_t::*;
use crate::trusted::SystemModel_t::*;
use crate::trusted::RefinementObligation_t::*;
use crate::trusted::ProgramModelTrait_t::*;
use crate::implementation::AtomicState_v::*;
use crate::implementation::ConcreteProgramModel_v::*;
use crate::implementation::MultisetMapRelation_v::*;
use crate::implementation::DiskLayout_v::*;
use crate::implementation::SuperblockTypes_v::*;

verus!{

// TODO: put into vstd/multiset_lib.rs
pub open spec fn multiset_to_set<V>(m: Multiset<V>) -> Set<V> {
    Set::new(|v| m.contains(v))
}

impl SystemModel::State<ConcreteProgramModel>  {
    pub open spec fn inv(self) -> bool
    {
        &&& self.program.state.wf()
        &&& self.disk.inv()

        // &&& self.ephemeral_map() == self.journal.journal.apply_to_stamped_map(self.persistent_map())
        // TODO(move into inv)
        // &&& self.ephemeral_map() == self.journal.journal
        //         .discard_old(self.in_flight_map().seq_end)
        //         .apply_to_stamped_map(self.in_flight_map())

        &&& self.in_flight_request_present()
        &&& self.persistent_sb_disk_inv()

//         &&& self.no_writes_till_recovery_complete() // why should a property like this be an inv?
        &&& self.at_most_one_oustanding_request_per_address()
        &&& self.responses_consistent_with_disk()
        &&& self.cache_consistent_with_outstanding_reqs()
        // do we also need to require self.outstanding
        // NOTE(disk): 1 outstanding IO for each loading/writeback page, reserved & filled (!writeback) -> 0 I/O


        // id history tracking
        &&& self.requests_have_unique_ids()
        &&& self.replies_have_unique_ids()
        &&& self.requests_replies_id_disjoint()
        &&& self.request_ids_in_history()
        &&& self.reply_ids_in_history()
        &&& self.sync_req_reply_ids_disjoint()
        &&& self.sync_req_ids_in_history()
        &&& self.sync_reply_ids_in_history()
        &&& self.program.state.client_ready() ==> self.program_sync_req_ids_in_history()

        // disk write inv
        &&& self.superblock_writes_inv()
        &&& self.sync_requests_inv()
        &&& DiskLayout::impl_inv(self.disk.content[spec_superblock_addr()])
    }

    pub open spec fn in_flight_request_present(self) -> bool
    {
        &&& self.program.state.client_ready() ==> {
            let in_flight = self.program.state.in_flight;
            &&& in_flight is Some ==> {
                let id = in_flight.unwrap().req_id;
                &&& (self.disk.requests.contains_key(id) || self.disk.responses.contains_key(id))
                &&& self.disk.requests.contains_key(id) ==>  {
                    &&& self.disk.requests[id] is WriteReq
                    &&& self.disk.requests[id]->to == spec_superblock_addr()                    
                    &&& DiskLayout::spec_new().spec_parse(self.disk.requests[id]->data) == self.program.state.in_flight_sb()
                }
                &&& self.disk.responses.contains_key(id) ==>
                    self.disk.responses[id] == DiskResponse::WriteResp{}
            }

            &&& in_flight is None ==> {
                &&& forall |id| #[trigger] self.disk.requests.contains_key(id) //&& self.disk.requests[id] is WriteReq
                    ==> self.disk.requests[id].addr() != spec_superblock_addr()
                &&& forall |id| #[trigger] self.disk.responses.contains_key(id)
                    ==> self.addr_for_id(id) != spec_superblock_addr()
            }
        }
    }

    pub open spec fn persistent_sb_disk_inv(self) -> bool
    {
        &&& self.disk.content.contains_key(spec_superblock_addr())
        &&& {
            let sb : Superblock = DiskLayout::spec_new().spec_parse(self.disk.content[spec_superblock_addr()]);
            &&& sb.wf()
            &&& if self.program.state.client_ready() {
                    // on disk sb either contains inflight sb or persistent sb
                    let in_flight = self.program.state.in_flight;
                    if in_flight is Some && self.disk.responses.contains_key(in_flight.unwrap().req_id) {
                        sb == self.program.state.in_flight_sb()
                    } else {
                        sb == self.program.state.persistent_sb()
                    }
                } else {
                    forall |id| #![auto] self.disk.responses.contains_key(id) ==>
                        self.disk.responses[id] == DiskResponse::ReadResp{data: self.disk.content[spec_superblock_addr()]}
                }
        }
    }

//     // NOTE:
//     // pre recovery state constraint
//     pub open spec fn no_writes_till_recovery_complete(self) -> bool
//     {
//         &&& self.program.state.recovery_state is Begin ==>
//             self.disk.requests == Map::<ID, DiskRequest>::empty() && self.disk.responses == Map::<ID, DiskResponse>::empty()
//         &&& self.program.state.recovery_state is AwaitingSuperblock ==> {
//             &&& forall |id| #[trigger] self.disk.requests.contains_key(id) ==> !(self.disk.requests[id] is WriteReq)
//             &&& forall |id| #[trigger] self.disk.responses.contains_key(id) ==> !(self.disk.responses[id] is WriteResp)
//         }
//     }

    pub open spec fn sync_requests_inv(self) -> bool
    {
        &&& all_elems_single(self.sync_requests)
        &&& self.program.state.client_ready() ==>
            // sync reqs pass *out of* the system sync_requests into the program state
            self.program.state.sync_req_map.dom().disjoint(self.sync_requests.dom())
    }

    // assumes that all I/Os beside superblock are managed by the cache
    pub open spec fn addr_for_id(self, id: ID) -> Address
    {
        arbitrary()

        // let cache = self.program.state.cache;
        // if cache.outstanding_reqs.contains_key(id) {
        //     cache.entries[cache.outstanding_reqs[id]].get_addr()
        // } else {
        //     spec_superblock_addr()
        // }
    }

    pub open spec fn responses_consistent_with_disk(self) -> bool
    {
        forall |id| #[trigger] self.disk.responses.contains_key(id)
        ==> {
            &&& self.disk.content.contains_key(self.addr_for_id(id))
            &&& self.disk.responses[id] is ReadResp /* && valid_checksum(self.disk.responses[id]->data)*/ ==>
                self.disk.responses[id]->data == self.disk.content[self.addr_for_id(id)]
            &&& self.disk.responses[id] is WriteResp ==> {
                true
                // TODO:
                // let addr = self.addr_for_id(id);
                // let disk_data = DiskLayout::spec_new().spec_parse(addr);
                // &&& addr == spec_superblock_addr() ==> disk_data == self.program.state.in_flight_sb()
                // &&& addr != spec_superblock_addr() ==> {
                //     let cache = self.program.state.cache;
                //     &&& cache.lookup_map.contains_key(addr)
                //     &&& cache.entries[cache.lookup_map[addr]] is Filled
                //     &&& disk_data == cache.entries[cache.lookup_map[addr]]->data
                // }
            }
        }
    }

    pub open spec fn cache_consistent_with_outstanding_reqs(self) -> bool
    {
            //  &&& forall |addr| non_sb_addrs.contains(addr)
            // <==> ({
            //     let slot = self.cache.lookup_map[addr];
            //     // every req must be a loading or writeback page
            //     ||| self.entries[slot] is // the request is being mapped to  // requests  
            //     ||| 
            // })
        // do we also need to require self.outstanding
        // NOTE(disk): 1 outstanding IO for each loading/writeback page, reserved & filled (!writeback) -> 0 I/O
        true
    }
        // do we also need to require self.outstanding
        // NOTE(disk): 1 outstanding IO for each loading/writeback page, reserved & filled (!writeback) -> 0 I/O


    // for request, we only make one request at a time, losing the addr makes it hard
    // when we only have reply and can't restrict additional requests for an addr is present in the request queue
    // right now this is fine because the only I/O is writing to superblock
    pub open spec fn at_most_one_oustanding_request_per_address(self) -> bool
    {
        // TODO: temporary restriction only valid for the simple model
        // &&& forall |id| #[trigger] self.disk.requests.contains_key(id) ==>
        //         self.disk.requests[id].addr() == spec_superblock_addr()

        // no concurrent requests on the same address
        &&& forall |id1, id2| #[trigger] self.disk.requests.contains_key(id1) && #[trigger] self.disk.requests.contains_key(id2)
            && id1 != id2 ==> self.disk.requests[id1].addr() != self.disk.requests[id2].addr()

        // no concurrent responses on the same address
        &&& forall |id1, id2| #[trigger] self.disk.responses.contains_key(id1) && #[trigger] self.disk.responses.contains_key(id2)
            && id1 != id2 ==> self.addr_for_id(id1) != self.addr_for_id(id2)

        // no concurrent request response on the same address
        &&& forall |id1, id2| #[trigger] self.disk.requests.contains_key(id1) && #[trigger] self.disk.responses.contains_key(id2)
            ==> self.disk.requests[id1].addr() != self.addr_for_id(id2)
    }

    pub open spec(checked) fn requests_have_unique_ids(self) -> bool
    {
        &&& all_elems_single(self.requests)
        &&& forall |req1, req2| self.requests.contains(req1)
            && self.requests.contains(req2)
            && req1 != req2
            ==> #[trigger] req1.id != #[trigger] req2.id
    }

    pub open spec(checked) fn replies_have_unique_ids(self) -> bool
    {
        &&& all_elems_single(self.replies)
        &&& forall |reply1, reply2| self.replies.contains(reply1)
            && self.replies.contains(reply2)
            && reply1 != reply2
            ==> #[trigger] reply1.id != #[trigger] reply2.id
    }

    pub open spec(checked) fn requests_replies_id_disjoint(self) -> bool
    {
        forall |req, reply| self.requests.contains(req) && self.replies.contains(reply)
            ==> #[trigger] req.id != #[trigger] reply.id
    }

    pub open spec(checked) fn request_ids_in_history(self) -> bool
    {
        forall |req| #![auto] self.requests.contains(req) ==> self.id_history.contains(req.id)
    }

    pub open spec(checked) fn reply_ids_in_history(self) -> bool
    {
        forall |reply| #![auto] self.replies.contains(reply) ==> self.id_history.contains(reply.id)
    }

    pub open spec(checked) fn sync_req_reply_ids_disjoint(self) -> bool
    {
        forall |req_id, reply_id| #![auto] self.sync_requests.contains(req_id) && self.sync_replies.contains(reply_id)
            ==> req_id != reply_id
    }

    pub open spec(checked) fn sync_req_ids_in_history(self) -> bool
    {
        forall |req_id| #![auto] self.sync_requests.contains(req_id) ==> self.id_history.contains(req_id)
    }

    pub open spec(checked) fn sync_reply_ids_in_history(self) -> bool
    {
        forall |reply_id| #![auto] self.sync_replies.contains(reply_id) ==> self.id_history.contains(reply_id)
    }

    pub open spec(checked) fn program_sync_req_ids_in_history(self) -> bool
    {
        forall |req_id| #![auto] self.program.state.sync_req_map.dom().contains(req_id) ==> self.id_history.contains(req_id)
    }

    // TODO this is too specialized. It should probably become some indirection to a broad disk
    // invariant provided by the program.
    pub open spec(checked) fn superblock_writes_inv(self) -> bool
    {
        forall |id| #![auto] self.disk.requests.contains_key(id) 
            && self.disk.requests[id] is WriteReq 
            && self.disk.requests[id]->to == spec_superblock_addr()
            ==> DiskLayout::impl_inv(self.disk.requests[id]->data)
    }

//     // interpretation given no ephemeral state and only on persistent disk
//     closed spec(checked) fn i_persistent(self) -> (mapspec: CrashTolerantAsyncMap::State)
//     recommends
//         !self.program.state.client_ready(),
//         self.disk.content.contains_key(spec_superblock_addr()),    // quash recommendation not met
//     {
//         let sb = DiskLayout::spec_new().spec_parse(self.disk.content[spec_superblock_addr()]);
//         CrashTolerantAsyncMap::State{
//             versions: sb.initial_history(),
//             async_ephemeral: EphemeralState{
//                 requests: self.requests.dom(),
//                 replies: self.replies.dom(),
//             },
//             sync_requests: Map::empty(),
//         }
//     }

//     // ephemeral depends on whether things have landed on disk
//     closed spec(checked) fn i_ephemeral(self) -> (mapspec: CrashTolerantAsyncMap::State)
//     recommends
//         self.program.state.wf(),
//         self.program.state.client_ready(),
//     {
//         arbitrary()
//         // let model = self.program.state;
//         // let actual_versions =
//         //     if model.in_flight is Some
//         //         && self.disk.responses.contains_key(model.in_flight.unwrap().req_id)
//         //     {
//         //         model.history.get_suffix(model.in_flight.unwrap().version as int)
//         //     } else {
//         //         model.history
//         //     };

//         // CrashTolerantAsyncMap::State{
//         //     versions: actual_versions,
//         //     async_ephemeral: EphemeralState{
//         //         requests: self.requests.dom(),
//         //         replies: self.replies.dom(),
//         //     },
//         //     sync_requests: self.program.state.sync_req_map,
//         //  }
//     }

    closed spec fn sb_landed(self: Self, post: Self) -> bool
    {
        false
        // let state = self.program.state;
        // &&& state.client_ready()
        // &&& state.in_flight is Some
        // &&& !self.disk.responses.contains_key(state.in_flight.unwrap().req_id)
        // &&& post.disk.responses.contains_key(state.in_flight.unwrap().req_id)
    }
}

pub struct RefinementProof{}

impl RefinementObligation<ConcreteProgramModel> for RefinementProof {

    open spec fn inv(model: SystemModel::State<ConcreteProgramModel>) -> bool
    {
        model.inv()
    }

    closed spec fn i(model: SystemModel::State<ConcreteProgramModel>) -> (mapspec: CrashTolerantAsyncMap::State)
    {
        // if client ready 
        // either way we need a way to get from disk 

        

        // go from likes journal to abstracted version
            
        arbitrary()

        // if model.program.state.client_ready() {
        //     model.i_ephemeral()
        // } else {
        //     model.i_persistent()
        // }
    }

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
                if pre.sb_landed(post) {
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
        assume(false);
        assert( SystemModel::State::initialize(pre, pre.program, pre.disk) );
        assert( Self::i(pre).async_ephemeral == AsyncMap::State::init_ephemeral_state() );
        assert( Self::i(pre).sync_requests == Map::<SyncReqId,nat>::empty() );  // extn

        // We're gonna get this from mkfs, I guess?
        assume( DiskLayout::impl_inv(pre.disk.content[spec_superblock_addr()]) );
        assert( Self::inv(pre) );

        assert( ConcreteProgramModel::is_mkfs(pre.disk) );
        assert( CrashTolerantAsyncMap::State::initialize(Self::i(pre)) );
    }

    proof fn next_refines(pre: SystemModel::State<ConcreteProgramModel>, post: SystemModel::State<ConcreteProgramModel>, lbl: SystemModel::Label)
    {
        assume(false);
        reveal(CrashTolerantAsyncMap::State::next);
        reveal(CrashTolerantAsyncMap::State::next_by);
        reveal(AsyncMap::State::next);
        reveal(AsyncMap::State::next_by);
        reveal(MapSpec::State::next);
        reveal(MapSpec::State::next_by);

        // requires:
        assert( SystemModel::State::next(pre, post, lbl) );
        assert( Self::inv(pre) );

        reveal(SystemModel::State::next);
        reveal(SystemModel::State::next_by);

        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);

        broadcast use insert_new_preserves_cardinality;

        let step = choose |step| SystemModel::State::next_by(pre, post, lbl, step);

        let ipre = Self::i(pre);
        let ipost = Self::i(post);
        let ilbl = Self::i_lbl(pre, post, lbl);

//         match step {
//             SystemModel::Step::accept_request() => {
//                 assume(false); // TODO(fix jonh)
//                 let new_id = lbl->req.id;
//                 assert(post.inv()) by {
//                     assert( post.requests_have_unique_ids() ) by {
//                         assert forall |req1, req2| #[trigger] post.requests.contains(req1)
//                             && #[trigger] post.requests.contains(req2) && req1 != req2
//                         implies req1.id != req2.id
//                         by {
//                             if req1.id == req2.id {
//                                 if req1.id == new_id {
//                                     assert(pre.requests.contains(req1) || pre.requests.contains(req2));
//                                 } else {
//                                     assert(pre.requests.contains(req1) && pre.requests.contains(req2));
//                                 }
//                                 assert(false);
//                             }
//                         }
//                     }
//                     assert( all_elems_single(post.requests) ) by {
//                         assert forall |req| #[trigger] post.requests.contains(req) implies post.requests.count(req) == 1 by {
//                             if pre.requests.contains(req) {
//                                 assert( post.requests.count(req) == 1 );
//                             }
//                         }
//                     }
//                     assert forall |req, reply| post.requests.contains(req) && post.replies.contains(reply)
//                         implies #[trigger] req.id != #[trigger] reply.id
//                     by {
//                         assert( pre.replies.contains(reply) );
//                         if req == lbl->req {
//                             assert( pre.fresh_id(lbl->req.id) );
//                             assert( req.id != reply.id );
//                         } else {
//                             assert( pre.requests.contains(req) );
//                         }
//                     }
//                     assert( post.request_ids_in_history() ) by {
//                         assert forall |req| #![auto] post.requests.contains(req) implies post.id_history.contains(req.id) by {
//                             if req != lbl->req {
//                                 assert( pre.requests.contains(req) );
//                             }
//                         }
//                     }
//                     // prove program_sync_req_ids_in_history()
//                     assert( forall |id| pre.id_history.contains(id) ==> post.id_history.contains(id) );
//                 }

//                 assert(CrashTolerantAsyncMap::State::optionally_append_version(ipre.versions, ipost.versions));
//                 assert(ipre.versions == ipost.versions);

//                 assert(!ipre.async_ephemeral.requests.contains(lbl->req)) by {
//                     if ipre.async_ephemeral.requests.contains(lbl->req) {
//                         assume(pre.requests.contains(lbl->req)); // trigger
//                     }
//                 }
//                 assert(ipre.async_ephemeral.requests.insert(lbl->req) =~= ipost.async_ephemeral.requests);

//                 let iasync_pre = AsyncMap::State { persistent: ipre.versions.last(), ephemeral: ipre.async_ephemeral };
//                 let iasync_post = AsyncMap::State { persistent: ipost.versions.last(), ephemeral: ipost.async_ephemeral };
//                 assert(AsyncMap::State::next_by(iasync_pre, iasync_post, ilbl->base_op, AsyncMap::Step::request()));
//                 assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl,
//                     CrashTolerantAsyncMap::Step::operate(ipost.versions, ipost.async_ephemeral)));
//                 assert( post.inv() );
//             },
//             SystemModel::Step::deliver_reply() => {
//                 assume(false); // TODO(jonh)
//                 assert(post.inv()) by {
//                     assert(forall |r| #[trigger] post.replies.contains(r) ==> pre.replies.contains(r));
//                 }
//                 assert(ipre.async_ephemeral.replies.contains(lbl->reply));
//                 assert(!post.replies.contains(lbl->reply)) by {
//                     if (post.replies.contains(lbl->reply)) {
//                         assert(pre.replies.contains(lbl->reply));
//                         assert(pre.replies.count(lbl->reply) > 1);
//                         assert(false);
//                     }
//                 }
//                 assert(ipost.async_ephemeral.replies =~= ipre.async_ephemeral.replies.remove(lbl->reply));

//                 let iasync_pre = AsyncMap::State { persistent: ipre.versions.last(), ephemeral: ipre.async_ephemeral };
//                 let iasync_post = AsyncMap::State { persistent: ipost.versions.last(), ephemeral: ipost.async_ephemeral };
//                 assert(AsyncMap::State::next_by(iasync_pre, iasync_post, ilbl->base_op, AsyncMap::Step::reply()));
//                 assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl,
//                     CrashTolerantAsyncMap::Step::operate(ipost.versions, ipost.async_ephemeral)));
//                 assert( post.inv() );
//             },
//             SystemModel::Step::program_execute(new_program) => {
//                 // let req = lbl->op->req;
//                 // let reply = lbl->op->reply;

//                 // assert(AtomicState::execute_transition(pre.program.state, post.program.state, req, reply));

//                 // assert forall |i| #[trigger] post.program.state.history.is_active(i)
//                 // implies post.program.state.history[i].appv.invariant()
//                 // by {
//                 //     if i != pre.program.state.history.len() {
//                 //         assert(pre.program.state.history.is_active(i));
//                 //     } else {
//                 //         MapSpec::State::inv_next(pre.program.state.mapspec(), post.program.state.mapspec(), to_map_label(req, reply));
//                 //         assert(post.program.state.history.last().appv.invariant());
//                 //     }
//                 // }

//                 // assert(forall |req| #[trigger] post.requests.contains(req) ==> pre.requests.contains(req));
//                 // assert(post.requests_have_unique_ids());
//                 // assert(post.replies_have_unique_ids());

//                 // assert(pre.in_flight_request_present());
//                 // assert(post.in_flight_request_present()) by {
//                 //     assert(post.program.state.in_flight == pre.program.state.in_flight);
//                 //     assert(post.disk.requests == pre.disk.requests);
//                 //     assert(post.disk.responses == pre.disk.responses);
//                 // }

//                 // assert( post.reply_ids_in_history() ) by {
//                 //     assert forall |xreply| #![auto] post.replies.contains(xreply) implies post.id_history.contains(xreply.id) by {
//                 //         if xreply != reply {
//                 //             assert( pre.replies.contains(xreply) );
//                 //         }
//                 //     }
//                 // }

//                 // assert(post.inv());

//                 // assert(ipost.async_ephemeral.requests =~= ipre.async_ephemeral.requests.remove(lbl->op->req));
//                 // assert(ipost.async_ephemeral.replies =~= ipre.async_ephemeral.replies.insert(lbl->op->reply));

//                 // assert(CrashTolerantAsyncMap::State::optionally_append_version(ipre.versions, ipost.versions)) by {
//                 //     if ipre.versions.len() == ipost.versions.len() {
//                 //         assert(ipre.versions == ipost.versions);
//                 //     } else {
//                 //         assert(ipost.versions.get_prefix(ipre.versions.len()) == ipre.versions); // trigger
//                 //     }
//                 // }

//                 // let iasync_pre = AsyncMap::State { persistent: ipre.versions.last(), ephemeral: ipre.async_ephemeral };
//                 // let iasync_post = AsyncMap::State { persistent: ipost.versions.last(), ephemeral: ipost.async_ephemeral };
//                 // assert(AsyncMap::State::next_by(iasync_pre, iasync_post, ilbl->base_op, AsyncMap::Step::execute(to_map_label(req, reply), iasync_post.persistent)));
//                 // assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl,
//                 //         CrashTolerantAsyncMap::Step::operate(ipost.versions, ipost.async_ephemeral)));
//                 // assert( post.inv() );
//             },
//             SystemModel::Step::program_accept_sync_request(new_program) => {
//                 assert( all_elems_single(post.sync_requests) ) by {
//                     assert forall |req| #[trigger] post.sync_requests.contains(req) implies post.sync_requests.count(req) == 1 by {
//                         if pre.sync_requests.contains(req) {
//                             assert( post.sync_requests.count(req) == 1 );
//                         }
//                     }
//                 }
//                 let sync_req_id = lbl.arrow_ProgramUIOp_op().arrow_AcceptSyncRequest_sync_req_id();
//                 assert(post.sync_requests_inv()) by {
//                     assert forall |sr| #![auto] post.program.state.sync_req_map.dom().contains(sr)
//                         implies !(post.sync_requests.dom().contains(sr)) by {
//                         if sr == sync_req_id {
//                             assert( pre.sync_requests.contains(sync_req_id) );  // trigger all_elems_single
//                         }
//                     }
//                 }
//                 assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::req_sync()));
//                 assert( post.sync_req_reply_ids_disjoint() ) by {
//                     assert forall |req_id, reply_id| #![auto] post.sync_requests.contains(req_id) && post.sync_replies.contains(reply_id)
//                     implies req_id != reply_id by {
//                         if req_id != sync_req_id {
//                             assert( pre.sync_requests.contains(req_id) );
//                         }
//                     }
//                 }
//                 assert( post.inv() );
//             }
//             SystemModel::Step::program_deliver_sync_reply(new_program) => {
//                 assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::reply_sync()));
//                 let sync_req_id = lbl.arrow_ProgramUIOp_op().arrow_DeliverSyncReply_sync_req_id();
//                 assert( post.sync_req_reply_ids_disjoint() ) by {
//                     assert forall |req_id, reply_id| #![auto] post.sync_requests.contains(req_id) && post.sync_replies.contains(reply_id)
//                     implies req_id != reply_id by {
//                         if reply_id!== sync_req_id {
//                             assert( pre.sync_replies.contains(reply_id) );
//                         }
//                     }
//                 }
//                 assert( post.inv() );
//             },
//             SystemModel::Step::program_disk(new_program, new_disk) => {
//                 assert(ConcreteProgramModel::valid_disk_transition(pre.program, post.program, lbl->info));
//                 let reqs = lbl->info.reqs;
//                 let resps = lbl->info.resps;
//                 let disk_event = choose |disk_event| AtomicState::disk_transition(
//                     pre.program.state, post.program.state, disk_event, reqs, resps);

//                 let disk_lbl = DiskLabel::DiskOps{
//                     requests: multiset_to_map(reqs),
//                     responses: multiset_to_map(resps),
//                 };

//                 assert(disk_lbl->responses <= pre.disk.responses);
//                 assert(disk_lbl->requests <= post.disk.requests);

//                 match disk_event {
//                     DiskEvent::InitiateRecovery{req_id} => {
//                         assert(AtomicState::initiate_recovery(pre.program.state, post.program.state, reqs, resps, req_id));
//                         assert(post.program.state.wf());
//                         multiset_map_singleton_ensures(req_id, DiskRequest::ReadReq{from: spec_superblock_addr()});

//                         assert( post.superblock_writes_inv() ) by {
//                             // The disk request buffer changed, but only by the addition of a read request
//                             assert forall |id| #![auto] post.disk.requests.contains_key(id) && post.disk.requests[id] is WriteReq && post.disk.requests[id]->to == spec_superblock_addr()
//                                 implies DiskLayout::impl_inv(post.disk.requests[id]->data) by {
//                                 assert( pre.disk.requests.contains_key(id) );
//                             }
//                         }
//                     },
//                     DiskEvent::CompleteRecovery{req_id, raw_page} => {
//                         assert(AtomicState::complete_recovery(pre.program.state, post.program.state, reqs, resps, req_id, raw_page));
//                         assert(AsyncDisk::State::disk_ops(pre.disk, post.disk, disk_lbl));
//                         multiset_map_membership(resps, req_id, DiskResponse::ReadResp{data: raw_page});
//                         assert(disk_lbl->responses == map!{req_id => DiskResponse::ReadResp{data: raw_page}});

//                         assert(disk_lbl->responses.contains_key(req_id)); // trigger
//                         assert(pre.disk.responses.contains_key(req_id));
//                         assert(raw_page == pre.disk.content[spec_superblock_addr()]);

//                         let superblock = DiskLayout::spec_new().spec_parse(raw_page);
//                         assert(superblock.wf());
//                         assert(post.program.state.wf());
//                         assert(post.sync_requests_inv());
//                         assert( post.superblock_writes_inv() );
//                     },
//                     DiskEvent::ExecuteSyncBegin{req_id, req, sync_map} => {
//                         AtomicState::execute_sync_begin(pre.program.state, post.program.state, req_id, req, sync_map, reqs, resps);
//                         let sb = pre.program.state.sync_sb(sync_map);
//                         multiset_map_membership(reqs, req_id, req);

//                         // We get this from AtomicState
//                         assert( DiskLayout::spec_new().spec_parse(req->data) == sb );
//                         // This is what impl_inv is gonna need; how would we show it here? It's
//                         // going down the stack to ASuperblock
//                         assume( DiskLayout::spec_new().spec_parse_inner(req->data).wf() );
//                         // This definition is closed and there's no provision yet for establishing
//                         // it.
//                         assume( DiskLayout::impl_inv(req->data) );
//                         assert( post.superblock_writes_inv() );
//                     },
//                     DiskEvent::ExecuteSyncEnd{} => {
//                         // AtomicState::execute_sync_end(pre.program.state, post.program.state, reqs, resps);
//                         // let info = pre.program.state.in_flight.unwrap();
//                         // multiset_map_membership(resps, info.req_id, DiskResponse::WriteResp{});

//                         // assert(forall |i| #[trigger] post.program.state.history.is_active(i)
//                         //     ==> pre.program.state.history.is_active(i)); // trigger
//                         // assert(post.program.state.wf());
//                         // assert( post.superblock_writes_inv() );
//                     },
//                 }
//                 assert(post.inv());
//                 assert(ipre == ipost);
//                 assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
//                 assert( post.inv() );
//             },
//             SystemModel::Step::program_internal(new_program) => {
//                 assert(ipre == ipost);
//                 assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
//                 assert( post.inv() );
//             },
//             SystemModel::Step::disk_internal(new_disk) => {
//                 if pre.sb_landed(post) {
// //                     assert( DiskLayout::impl_inv(post.disk.content[spec_superblock_addr()]) );
// //                     assert(post.inv());
//                     let info = pre.program.state.in_flight.unwrap();
// //                     assert(ipre.stable_index() <= info.version < ipre.versions.len());
// //                     assert(ipost.versions == ipre.versions.get_suffix(info.version as int));
//                     assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::sync(info.map_version() as int)));
//                 } else {
//                     assert(post.inv());
//                     assert(ipre == ipost);
//                     assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
//                 }
//                 assert( post.inv() );
//             },
//             SystemModel::Step::crash(new_program, new_disk) => {
//                 assert(post.inv());
//                 assume(ipre.versions.get_prefix(ipre.stable_index()+1) == ipost.versions);   // TODO(jonh)
//                 assert(ipost.async_ephemeral == AsyncMap::State::init_ephemeral_state()); // ext_eq
//                 assert( post.inv() );
//                 assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::crash()));
//             },
//             SystemModel::Step::noop() => {
//                 assert(ipre == ipost);
//                 assert( post.inv() );
//                 assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
//             },
//             SystemModel::Step::accept_sync_request() => {
//                 let sync_req_id = lbl.arrow_AcceptSyncRequest_sync_req_id();
//                 assert( pre.fresh_id(sync_req_id) );
//                 assert( !pre.sync_requests.contains(sync_req_id) );
//                 assert( all_elems_single(post.sync_requests) );
//                 assert( post.program.state == pre.program.state );
//                 assert( post.sync_req_ids_in_history() ) by {
//                     assert forall |req_id| #![auto] post.sync_requests.contains(req_id)
//                         implies post.id_history.contains(req_id) by {
//                         if req_id != sync_req_id {
//                             assert( pre.id_history.contains(req_id) );
//                         }
//                     }
//                 }
//                 assert( post.sync_requests_inv() ) by {
//                     if post.program.state.client_ready() {
//                         assert forall |id| #![auto] post.program.state.sync_req_map.dom().contains(id)
//                             implies !post.sync_requests.dom().contains(id) by {
//                             if id != sync_req_id {
//                                 assert( pre.program.state.sync_req_map.dom().contains(id) );
//                             }
//                         }
//                     }
//                 }
//                 assert( post.sync_req_reply_ids_disjoint() ) by {
//                     assert forall |req_id, reply_id| #![auto] post.sync_requests.contains(req_id) && post.sync_replies.contains(reply_id)
//                     implies req_id != reply_id by {
//                         if req_id == sync_req_id {
//                             assert( !pre.id_history.contains(sync_req_id) );
//                             assert( pre.sync_replies.contains(reply_id) );
//                             assert( pre.id_history.contains(reply_id) );
//                             assert( req_id != reply_id );
//                         } else {
//                             assert( pre.sync_requests.contains(req_id) );
//                         }
//                     }
//                 }
//                 // prove program_sync_req_ids_in_history
//                 if post.program.state.client_ready() {
//                     assert( forall |id| pre.id_history.contains(id) ==> post.id_history.contains(id) );
//                 }
//                 assert(post.inv());
//                 assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
//             },
//             SystemModel::Step::deliver_sync_reply() => {
//                 let sync_req_id = lbl.arrow_DeliverSyncReply_sync_req_id();
//                 assert( post.sync_req_reply_ids_disjoint() ) by {
//                     assert forall |req_id, reply_id| #![auto] post.sync_requests.contains(req_id) && post.sync_replies.contains(reply_id)
//                     implies req_id != reply_id by {
//                         if req_id != sync_req_id {
//                             assert( pre.sync_requests.contains(req_id) );
//                             assert( pre.sync_replies.contains(reply_id) );
//                         }
//                     }
//                 }
//                 assert(post.inv());
//                 assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
//             },
//             _ => { assert(false); }
//         }
        assert( CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl) );
    }
}

broadcast proof fn insert_new_preserves_cardinality<V>(m: Multiset<V>, new: V)
    requires all_elems_single(m), !m.contains(new)
    ensures #[trigger] all_elems_single(m.insert(new))
{
    let post_m = m.insert(new);
    assert forall |e| #[trigger] post_m.contains(e)
    implies post_m.count(e) == 1
    by {
        if e != new {
            assert(m.contains(e)); // trigger
        }
    }
}
}
