#[allow(unused_imports)]    // lost in erasure
use vstd::prelude::*;
use vstd::prelude::*;

use vstd::{math, multiset::Multiset};
use crate::spec::AsyncDisk_t::{Address, AsyncDisk, DiskRequest, DiskResponse, RawPage};
use crate::spec::MapSpec_t::{AsyncMap, CrashTolerantAsyncMap, EphemeralState, ID, MapSpec, SyncReqId, Version};
use crate::trusted::SystemModel_t::SystemModel;
use crate::trusted::RefinementObligation_t::RefinementObligation;
use crate::trusted::ProgramModelTrait_t::{DiskLabel, ProgramModelTrait, ProgramUserOp};
use crate::disk::GenericDisk_v::Pointer;
use crate::abstract_system::AbstractCrashAwareJournal_v::AbstractCrashAwareJournal;
use crate::implementation::ConcreteJournal_v::ConcreteJournal;
use crate::journal::LinkedJournal_v::{DiskView, TruncatedJournal};
use crate::implementation::AtomicState_v::{AtomicState, DiskEvent, InternalEvent, ProgramEvent, raw_page_to_record, to_map_label, to_journal_reads};
use crate::implementation::JournalImpl_v::journal_disk_inv;
use crate::implementation::Cache_v::{Cache, Slot};
use crate::implementation::CachedJournal_v::build_lsn_addr_index_from_reads;
use crate::allocation_layer::LikesJournal_v::{LikesJournal, LsnAddrIndex};
use crate::implementation::JournalCoordinationSystem_v::{JournalCoordinationSystem, cj_boundary_lsn, cj_freshest_rec, cj_lsn_addr_index, cj_unmarshalled_tail};
use crate::implementation::ConcreteProgramModel_v::ConcreteProgramModel;
use crate::implementation::MultisetMapRelation_v::{all_elems_single, multiset_map_membership, multiset_map_singleton_ensures, multiset_to_map};
use crate::implementation::DiskLayout_v::{DiskLayout, spec_superblock_addr};
use crate::implementation::SuperblockTypes_v::{ASuperblock, Superblock, singleton_floating_seq};
use crate::marshalling::IJournalRecordFormat_v::IJournalRecordFormat;
use crate::marshalling::Marshalling_v::Marshal;
use crate::abstract_system::AbstractCrashAwareMap_v::AbstractCrashAwareMap;
use crate::abstract_system::AbstractCrashAwareSystemRefinement_v::floating_versions;
use crate::abstract_system::StampedMap_v::{LSN, StampedMap};
use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::abstract_system::AbstractCrashAwareJournal_v::Ephemeral;
use crate::abstract_system::AbstractJournal_v::AbstractJournal;
use crate::abstract_system::AbstractMap_v::AbstractMap;
use crate::implementation::SystemModelTwo_v::SystemModelTwo;
use crate::implementation::BracketRefinement_v;
use crate::implementation::ModelRefinement_v::multiset_to_set;

verus!{

// ================================================================
// Shared helper lemmas (copied from ModelRefinement_v since they're not pub)
// ================================================================

proof fn floating_versions_len(base: StampedMap, msg_history: MsgHistory, stable_lsn: LSN)
    requires
        stable_lsn <= msg_history.seq_end + 1,
    ensures floating_versions(base, msg_history, stable_lsn).len() == msg_history.seq_end + 1
{}

proof fn floating_versions_start(base: StampedMap, msg_history: MsgHistory, stable_lsn: LSN)
    ensures floating_versions(base, msg_history, stable_lsn).first_active_index() == stable_lsn
{}

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

// ================================================================
// Projection helpers and invariants for SystemModelTwo → CrashTolerantAsyncMap refinement
// ================================================================

impl SystemModelTwo::State {
    // Convenience: access the JCS view through concrete_journal
    pub open spec fn jcs(self) -> JournalCoordinationSystem::State
    {
        self.concrete_journal.jcs_view()
    }

    // Convenience: access the full journal through concrete_journal
    pub open spec fn full_journal(self) -> MsgHistory
    {
        self.concrete_journal.full_journal()
    }

    // Interpret concrete CachedJournal state as AbstractCrashAwareJournal state.
    pub open spec fn i_journal(self) -> AbstractCrashAwareJournal::State
    {
        self.concrete_journal.i()
    }

    // ================================================================
    // Invariant predicates (ported from ModelRefinement_v.rs impl SystemModel::State<CPM>)
    // ================================================================

    pub open spec fn inv(self) -> bool
    {
        &&& self.to_atomic().wf()
        &&& self.concrete_journal.disk.inv()

        &&& self.persistent_sb_disk_inv()
        &&& self.awaiting_sb_response_is_disk_content()
        &&& self.no_writes_till_recovery_complete()
        &&& self.outstanding_reqs_consistent()
        &&& self.sb_req_id_disjoint_cache_reqs()
        &&& self.sb_response_is_write_resp()
        &&& self.sync_requests_inv()
        &&& self.journal_pages_parsable()
        &&& self.journal_seq_end_inv()
        &&& self.cache_reads_agree_with_disk()
        &&& self.persistent_journal_structure()
        &&& self.persistent_journal_index_matches_disk()
        // JCS structural invariant: ephemeral journal chain is well-formed
        &&& self.client_ready() ==> self.jcs().valid_journal_structure()

        // id history tracking
        &&& self.requests_have_unique_ids()
        &&& self.replies_have_unique_ids()
        &&& self.requests_replies_id_disjoint()
        &&& self.request_ids_in_history()
        &&& self.reply_ids_in_history()
        &&& self.sync_req_reply_ids_disjoint()
        &&& self.sync_req_ids_in_history()
        &&& self.sync_reply_ids_in_history()
        &&& self.client_ready() ==> self.program_sync_req_ids_in_history()
    }

    pub open spec fn cache_reads_agree_with_disk(self) -> bool
    {
        !(self.recovery_state is RecoveryComplete) ==>
            forall |addr: Address, data: RawPage| #[trigger] self.concrete_journal.cache.valid_read(addr, data)
                ==> addr != spec_superblock_addr()
                    && self.concrete_journal.disk.content.contains_key(addr)
                    && self.concrete_journal.disk.content[addr] == data
    }

    pub open spec fn persistent_sb_disk_inv(self) -> bool
    {
        &&& self.concrete_journal.disk.content.contains_key(spec_superblock_addr())
        &&& {
            let asb : ASuperblock = DiskLayout::spec_new().spec_parse_inner(self.concrete_journal.disk.content[spec_superblock_addr()]);
            let sb : Superblock = asb@;
            &&& asb.wf()
            &&& sb.wf()
            &&& self.client_ready() ==>
            {
                if self.concrete_journal.in_flight is Some && self.concrete_journal.disk.responses.contains_key(self.concrete_journal.in_flight.unwrap().req_id) {
                    sb == self.to_atomic().in_flight_sb()
                } else {
                    sb == self.to_atomic().persistent_sb()
                }
            }
        }
    }

    pub open spec fn awaiting_sb_response_is_disk_content(self) -> bool
    {
        self.recovery_state is AwaitingSuperblock ==>
            forall |id| #[trigger] self.concrete_journal.disk.responses.contains_key(id)
                && self.concrete_journal.disk.responses[id] is ReadResp
                ==> self.concrete_journal.disk.responses[id]->data == self.concrete_journal.disk.content[spec_superblock_addr()]
    }

    pub open spec fn journal_pages_parsable(self) -> bool
    {
        let fmt = IJournalRecordFormat::spec_new();
        forall |addr: Address| self.concrete_journal.disk.content.contains_key(addr)
            && addr != spec_superblock_addr()
            ==> #[trigger] fmt.parsable(self.concrete_journal.disk.content[addr])
    }

    pub open spec fn persistent_journal_structure(self) -> bool
    {
        !(self.recovery_state is AwaitingSuperblock)
        && !(self.recovery_state is RecoveryComplete)
        ==> {
            let raw_disk = self.concrete_journal.disk.content.remove(spec_superblock_addr());
            let journal_disk = DiskView{
                boundary_lsn: self.concrete_journal.journal.snapshot.boundary_lsn,
                entries: to_journal_reads(raw_disk),
            };
            self.concrete_journal.journal.snapshot.freshest_rec is Some
                ==> journal_disk_inv(journal_disk, self.concrete_journal.journal.snapshot.freshest_rec)
        }
    }

    pub open spec fn persistent_journal_index_matches_disk(self) -> bool
    {
        !(self.recovery_state is RecoveryComplete)
        && self.concrete_journal.journal.status is Some
        && self.concrete_journal.journal.snapshot.freshest_rec is Some
        ==> {
            let raw_disk = self.concrete_journal.disk.content.remove(spec_superblock_addr());
            let journal_dv = DiskView{
                boundary_lsn: self.concrete_journal.journal.snapshot.boundary_lsn,
                entries: to_journal_reads(raw_disk),
            };
            let tj = TruncatedJournal{
                freshest_rec: self.concrete_journal.journal.snapshot.freshest_rec,
                disk_view: journal_dv,
            };
            tj.build_lsn_addr_index() == self.concrete_journal.journal.status.unwrap().lsn_addr_index
        }
    }

    pub open spec fn no_writes_till_recovery_complete(self) -> bool
    {
        !(self.recovery_state is RecoveryComplete) ==> {
            &&& forall |id| #[trigger] self.concrete_journal.disk.requests.contains_key(id) ==> !(self.concrete_journal.disk.requests[id] is WriteReq)
            &&& forall |id| #[trigger] self.concrete_journal.disk.responses.contains_key(id) ==> !(self.concrete_journal.disk.responses[id] is WriteResp)
        }
    }

    pub open spec fn sync_requests_inv(self) -> bool
    {
        &&& all_elems_single(self.sync_requests)
        &&& self.client_ready() ==>
            self.sync_req_map.dom().disjoint(self.sync_requests.dom())
    }

    pub open spec fn journal_seq_end_inv(self) -> bool
    {
        self.client_ready() ==> {
            let tail = self.concrete_journal.journal.status.unwrap().unmarshalled_tail;
            &&& tail.can_discard_to(self.concrete_journal.persistent_journal_seq_end)
            &&& self.concrete_journal.in_flight is Some ==> {
                &&& tail.can_discard_to(self.concrete_journal.in_flight.unwrap().journal_version)
                &&& self.concrete_journal.persistent_journal_seq_end <= self.concrete_journal.in_flight.unwrap().journal_version
            }
        }
    }

    pub open spec fn id_has_addr(self, id: ID) -> bool
    {
        self.concrete_journal.in_flight is Some && self.concrete_journal.in_flight.unwrap().req_id == id
        || self.outstanding_cache_reqs.dom().contains(id)
    }

    pub open spec fn io_id_valid(self, id: ID) -> bool
    {
        &&& self.id_has_addr(id)
        &&& self.concrete_journal.disk.content.dom().contains(self.addr_for_id(id))
        &&& self.outstanding_cache_reqs.contains_key(id) ==> {
            let addr = self.outstanding_cache_reqs[id];
            let slot = self.concrete_journal.cache.lookup_map[addr];
            &&& self.concrete_journal.cache.entries.dom().contains(slot)
            &&& self.concrete_journal.cache.status_map.dom().contains(slot)
            &&& self.concrete_journal.disk.content.dom().contains(addr)
        }
    }

    pub open spec(checked) fn addr_for_id(self, id: ID) -> Address
        recommends self.id_has_addr(id)
    {
        if self.concrete_journal.in_flight is Some && self.concrete_journal.in_flight.unwrap().req_id == id {
            spec_superblock_addr()
        } else {
            self.outstanding_cache_reqs[id]
        }
    }

    pub open spec /*(checked)*/ fn outstanding_reqs_consistent(self) -> bool
        recommends
            self.to_atomic().wf(),
            self.client_ready(),
            forall |id: ID|
                #![trigger self.concrete_journal.disk.requests.contains_key(id)]
                #![trigger self.concrete_journal.disk.responses.contains_key(id)]
                (self.concrete_journal.disk.requests.contains_key(id) || self.concrete_journal.disk.responses.contains_key(id))
                ==> self.io_id_valid(id),
    {
        let in_flight_sb_id = if self.concrete_journal.in_flight is Some { set!{self.concrete_journal.in_flight.unwrap().req_id} } else { set!{} };

        // 1. all disk ids are bounded by cache reqs and inflight_sb
        &&& self.concrete_journal.disk.requests.dom() + self.concrete_journal.disk.responses.dom() == self.outstanding_cache_reqs.dom() + in_flight_sb_id
        // 2. disk requests are correctly recorded
        &&& forall |id| #[trigger] self.concrete_journal.disk.requests.contains_key(id)
        ==> {
            let req = self.concrete_journal.disk.requests[id];
            &&& req.addr() == self.addr_for_id(id)
            &&& req is ReadReq && self.outstanding_cache_reqs.contains_key(id) ==> {
                let slot = self.concrete_journal.cache.lookup_map[self.outstanding_cache_reqs[id]];
                &&& self.concrete_journal.cache.entries[slot] is Loading
            }
            &&& req is WriteReq ==> {
                if self.outstanding_cache_reqs.contains_key(id) {
                    let slot = self.concrete_journal.cache.lookup_map[self.outstanding_cache_reqs[id]];
                    &&& self.concrete_journal.cache.status_map[slot] is Writeback
                    &&& self.concrete_journal.cache.entries[slot]->data == req->data
                } else {
                    &&& req->to == spec_superblock_addr()
                    &&& self.concrete_journal.in_flight is Some
                    &&& self.concrete_journal.in_flight.unwrap().req_id == id
                    &&& DiskLayout::spec_new().spec_parse(req->data) == self.to_atomic().in_flight_sb()
                }
            }
        }
        // 3. disk responses are correctly reflected
        &&& forall |id| #[trigger] self.concrete_journal.disk.responses.contains_key(id)
        ==> {
            let resp = self.concrete_journal.disk.responses[id];
            &&& resp is ReadResp ==> {
                &&& resp->data == self.concrete_journal.disk.content[self.addr_for_id(id)]
                &&& self.outstanding_cache_reqs.contains_key(id) ==> {
                    let slot = self.concrete_journal.cache.lookup_map[self.outstanding_cache_reqs[id]];
                    &&& self.concrete_journal.cache.entries[slot] is Loading
                }
            }
            &&& resp is WriteResp && self.outstanding_cache_reqs.contains_key(id) ==> {
                let addr = self.outstanding_cache_reqs[id];
                let slot = self.concrete_journal.cache.lookup_map[addr];
                &&& self.concrete_journal.cache.status_map[slot] is Writeback
                &&& self.concrete_journal.disk.content[addr] == self.concrete_journal.cache.entries[slot]->data
            }
        }
    }

    pub open spec(checked) fn sb_response_is_write_resp(self) -> bool
    {
        self.concrete_journal.in_flight is Some ==>
            forall |id| #[trigger] self.concrete_journal.disk.responses.contains_key(id)
                && self.concrete_journal.in_flight.unwrap().req_id == id
                ==> self.concrete_journal.disk.responses[id] is WriteResp
    }

    pub open spec(checked) fn sb_req_id_disjoint_cache_reqs(self) -> bool
    {
        self.concrete_journal.in_flight is Some ==>
            !self.outstanding_cache_reqs.dom().contains(
                self.concrete_journal.in_flight.unwrap().req_id)
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
        forall |req_id| #![auto] self.sync_req_map.dom().contains(req_id) ==> self.id_history.contains(req_id)
    }

    // ================================================================
    // Interpretation functions
    // ================================================================

    // interpretation given no ephemeral state and only on persistent disk
    closed spec(checked) fn i_persistent(self) -> (mapspec: CrashTolerantAsyncMap::State)
    recommends
        !self.client_ready(),
        self.concrete_journal.disk.content.contains_key(spec_superblock_addr()),
    {
        let sb = DiskLayout::spec_new().spec_parse(self.concrete_journal.disk.content[spec_superblock_addr()]);
        CrashTolerantAsyncMap::State{
            versions: singleton_floating_seq(sb.store.seq_end, sb.store.value),
            async_ephemeral: EphemeralState{
                requests: multiset_to_set(self.requests),
                replies: multiset_to_set(self.replies),
            },
            sync_requests: Map::empty(),
        }
    }

    // ephemeral depends on whether things have landed on disk
    closed spec fn i_ephemeral(self) -> (mapspec: CrashTolerantAsyncMap::State)
    recommends
        self.to_atomic().wf(),
        self.client_ready(),
    {
        let journal = self.i_journal();
        let mapadt = self.store;

        let inflight_on_disk =
            self.concrete_journal.in_flight is Some
            && journal.in_flight is Some
            && self.concrete_journal.disk.responses.contains_key(self.concrete_journal.in_flight.unwrap().req_id);

        let versions = if inflight_on_disk {
            let in_flight_map = mapadt.in_flight.unwrap();
            let remaining_journal = journal.i().discard_old(in_flight_map.seq_end);
            let stable_lsn = journal.in_flight.unwrap().seq_end;
            floating_versions(in_flight_map, remaining_journal, stable_lsn)
        } else {
            let stable_lsn = journal.persistent.seq_end;
            floating_versions(mapadt.persistent, journal.i(), stable_lsn)
        };

        CrashTolerantAsyncMap::State{
            versions,
            async_ephemeral: EphemeralState{
                requests: multiset_to_set(self.requests),
                replies: multiset_to_set(self.replies),
            },
            sync_requests: self.sync_req_map,
        }
    }

    pub closed spec fn sb_landed(self: Self, post: Self) -> bool
    {
        &&& self.client_ready()
        &&& self.concrete_journal.in_flight is Some
        &&& !self.concrete_journal.disk.responses.contains_key(self.concrete_journal.in_flight.unwrap().req_id)
        &&& post.concrete_journal.disk.responses.contains_key(self.concrete_journal.in_flight.unwrap().req_id)
    }
}

// ================================================================
// Top-level interpretation functions (free functions, not methods)
// ================================================================

pub closed spec fn sm2_i(model: SystemModelTwo::State) -> CrashTolerantAsyncMap::State
{
    if model.client_ready() {
        model.i_ephemeral()
    } else {
        model.i_persistent()
    }
}

pub open spec fn sm2_i_lbl(pre: SystemModelTwo::State, post: SystemModelTwo::State, lbl: SystemModelTwo::Label) -> CrashTolerantAsyncMap::Label
{
    match lbl {
        SystemModelTwo::Label::AcceptRequest{req} => {
            CrashTolerantAsyncMap::Label::OperateOp{
                base_op: AsyncMap::Label::RequestOp { req }
            }
        },
        SystemModelTwo::Label::DeliverReply{reply} => {
            CrashTolerantAsyncMap::Label::OperateOp{
                base_op: AsyncMap::Label::ReplyOp { reply }
            }
        },
        SystemModelTwo::Label::ProgramUIOp{op} => {
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
        SystemModelTwo::Label::ProgramDiskOp{ info } =>
            CrashTolerantAsyncMap::Label::Noop{},
        SystemModelTwo::Label::ProgramInternal =>
            CrashTolerantAsyncMap::Label::Noop{},
        SystemModelTwo::Label::DiskInternal => {
            if pre.sb_landed(post) {
                CrashTolerantAsyncMap::Label::SyncOp{}
            } else {
                CrashTolerantAsyncMap::Label::Noop{}
            }
        },
        SystemModelTwo::Label::Crash =>
            CrashTolerantAsyncMap::Label::CrashOp{},
        _ =>
            CrashTolerantAsyncMap::Label::Noop{},
    }
}

// ================================================================
// Proof: SystemModelTwo → CrashTolerantAsyncMap
// ================================================================

proof fn sm2_i_lbl_valid(pre: SystemModelTwo::State, post: SystemModelTwo::State, lbl: SystemModelTwo::Label, ctam_lbl: CrashTolerantAsyncMap::Label)
    requires
        ctam_lbl == sm2_i_lbl(pre, post, lbl),
    ensures
        // SM2 labels are isomorphic to SM1 labels; compose with BracketRefinement::i_lbl
        // to get the SM1 label_correspondence
        true, // placeholder — the adapter will handle label_correspondence
{
}

proof fn sm2_init_refines(pre: SystemModelTwo::State)
    requires
        // We'll get the SM2 init state from BracketRefinement of the SM1 init state
        true,
    ensures
        CrashTolerantAsyncMap::State::initialize(sm2_i(pre)),
        pre.inv(),
{
    assume(false); // TODO
}

pub proof fn next_refines_ctam(pre: SystemModelTwo::State, post: SystemModelTwo::State, lbl: SystemModelTwo::Label)
    requires
        SystemModelTwo::State::next(pre, post, lbl),
        pre.inv(),
    ensures
        CrashTolerantAsyncMap::State::next(sm2_i(pre), sm2_i(post), sm2_i_lbl(pre, post, lbl)),
        post.inv(),
{
    reveal(CrashTolerantAsyncMap::State::next);
    reveal(CrashTolerantAsyncMap::State::next_by);
    reveal(AsyncMap::State::next);
    reveal(AsyncMap::State::next_by);
    reveal(MapSpec::State::next);
    reveal(MapSpec::State::next_by);

    reveal(SystemModelTwo::State::next);
    reveal(SystemModelTwo::State::next_by);

    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);

    broadcast use insert_new_preserves_cardinality;

    let step = choose |step| SystemModelTwo::State::next_by(pre, post, lbl, step);

    let ipre = sm2_i(pre);
    let ipost = sm2_i(post);
    let ilbl = sm2_i_lbl(pre, post, lbl);

    match step {
        SystemModelTwo::Step::accept_request() => {
            let new_id = lbl->req.id;
            assert(post.inv()) by {
                assert( post.requests_have_unique_ids() ) by {
                    assert forall |req1, req2| #[trigger] post.requests.contains(req1)
                        && #[trigger] post.requests.contains(req2) && req1 != req2
                    implies req1.id != req2.id
                    by {
                        if req1.id == req2.id {
                            if req1.id == new_id {
                                assert(pre.requests.contains(req1) || pre.requests.contains(req2));
                            } else {
                                assert(pre.requests.contains(req1) && pre.requests.contains(req2));
                            }
                            assert(false);
                        }
                    }
                }
                assert( all_elems_single(post.requests) ) by {
                    assert forall |req| #[trigger] post.requests.contains(req) implies post.requests.count(req) == 1 by {
                        if pre.requests.contains(req) {
                            assert( post.requests.count(req) == 1 );
                        }
                    }
                }
                assert forall |req, reply| post.requests.contains(req) && post.replies.contains(reply)
                    implies #[trigger] req.id != #[trigger] reply.id
                by {
                    assert( pre.replies.contains(reply) );
                    if req == lbl->req {
                        assert( pre.fresh_id(lbl->req.id) );
                        assert( req.id != reply.id );
                    } else {
                        assert( pre.requests.contains(req) );
                    }
                }
                assert( post.request_ids_in_history() ) by {
                    assert forall |req| #![auto] post.requests.contains(req) implies post.id_history.contains(req.id) by {
                        if req != lbl->req {
                            assert( pre.requests.contains(req) );
                        }
                    }
                }
                // prove program_sync_req_ids_in_history()
                assert( forall |id| pre.id_history.contains(id) ==> post.id_history.contains(id) );
            }

            assert(CrashTolerantAsyncMap::State::optionally_append_version(ipre.versions, ipost.versions));
            assert(ipre.versions == ipost.versions);

            assert(!ipre.async_ephemeral.requests.contains(lbl->req)) by {
                if ipre.async_ephemeral.requests.contains(lbl->req) {
                    assert(pre.requests.contains(lbl->req)); // trigger
                }
            }
            assert(ipre.async_ephemeral.requests.insert(lbl->req) =~= ipost.async_ephemeral.requests);

            let iasync_pre = AsyncMap::State { persistent: ipre.versions.last(), ephemeral: ipre.async_ephemeral };
            let iasync_post = AsyncMap::State { persistent: ipost.versions.last(), ephemeral: ipost.async_ephemeral };
            assert(AsyncMap::State::next_by(iasync_pre, iasync_post, ilbl->base_op, AsyncMap::Step::request()));
            assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl,
                CrashTolerantAsyncMap::Step::operate(ipost.versions, ipost.async_ephemeral)));
            assert( post.inv() );
        },
        SystemModelTwo::Step::deliver_reply() => {
            assert(post.inv()) by {
                assert(forall |r| #[trigger] post.replies.contains(r) ==> pre.replies.contains(r));
            }
            assert(ipre.async_ephemeral.replies.contains(lbl->reply));
            assert(!post.replies.contains(lbl->reply)) by {
                if (post.replies.contains(lbl->reply)) {
                    assert(pre.replies.contains(lbl->reply));
                    assert(pre.replies.count(lbl->reply) > 1);
                    assert(false);
                }
            }
            assert(ipost.async_ephemeral.replies =~= ipre.async_ephemeral.replies.remove(lbl->reply));

            let iasync_pre = AsyncMap::State { persistent: ipre.versions.last(), ephemeral: ipre.async_ephemeral };
            let iasync_post = AsyncMap::State { persistent: ipost.versions.last(), ephemeral: ipost.async_ephemeral };
            assert(AsyncMap::State::next_by(iasync_pre, iasync_post, ilbl->base_op, AsyncMap::Step::reply()));
            assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl,
                CrashTolerantAsyncMap::Step::operate(ipost.versions, ipost.async_ephemeral)));
            assert( post.inv() );
        },
        SystemModelTwo::Step::program_execute(new_concrete_journal, new_store) => {
            let req = lbl->op->req;
            let reply = lbl->op->reply;

            // Reveal interpretation so solver can see versions structure
            reveal(sm2_i);
            reveal(SystemModelTwo::State::i_ephemeral);

            // Extract the existential witness for which program event happened
            let pe = choose |e: ProgramEvent|
                AtomicState::execute_transition(pre.to_atomic(), post.to_atomic(), req, reply, e);

            let map_label = to_map_label(req, reply);

            match pe {
                ProgramEvent::NoOp{} | ProgramEvent::Query{..} => {
                    // NoOp/Query: post == pre for AtomicState, so concrete_journal preserved
                    assert(pre.concrete_journal == post.concrete_journal);

                    // NoOp/Query: program state effectively unchanged, versions preserved
                    if pe is Query {
                        reveal(AbstractCrashAwareMap::State::next);
                        reveal(AbstractCrashAwareMap::State::next_by);
                    }

                    // MapSpec step: case-split on request type for the witness
                    if req.input is NoopInput {
                        MapSpec::show::noop(ipre.versions.last().appv, ipost.versions.last().appv, map_label);
                    } else {
                        // Query/Put input with NoOp/Query event
                        assume(MapSpec::State::next(ipre.versions.last().appv, ipost.versions.last().appv, map_label));
                    }
                },
                ProgramEvent::Put{puts} => {
                    assume(false); // TODO: Put extends journal, appends a new version
                },
            }
            assert(CrashTolerantAsyncMap::State::optionally_append_version(ipre.versions, ipost.versions));

            // Request was in the system → in the abstract requests
            assert(ipost.async_ephemeral.requests =~= ipre.async_ephemeral.requests.remove(req));
            assert(ipost.async_ephemeral.replies =~= ipre.async_ephemeral.replies.insert(reply));

            let iasync_pre = AsyncMap::State { persistent: ipre.versions.last(), ephemeral: ipre.async_ephemeral };
            let iasync_post = AsyncMap::State { persistent: ipost.versions.last(), ephemeral: ipost.async_ephemeral };
            assert(AsyncMap::State::next_by(iasync_pre, iasync_post, ilbl->base_op, AsyncMap::Step::execute(map_label, iasync_post.persistent)));
            assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl,
                CrashTolerantAsyncMap::Step::operate(ipost.versions, ipost.async_ephemeral)));

            // post.inv() preservation
            assert(post.inv()) by {
                assert( all_elems_single(post.requests) ) by {
                    assert forall |r| #[trigger] post.requests.contains(r)
                        implies post.requests.count(r) == 1
                    by {
                        assert( pre.requests.contains(r) );
                    }
                }
                assert( post.request_ids_in_history() ) by {
                    assert forall |r| #![auto] post.requests.contains(r)
                        implies post.id_history.contains(r.id)
                    by {
                        assert( pre.requests.contains(r) );
                    }
                }
                assert( post.reply_ids_in_history() );
            }
        },
        SystemModelTwo::Step::program_accept_sync_request(new_sync_req_map) => {
            assert( all_elems_single(post.sync_requests) ) by {
                assert forall |req| #[trigger] post.sync_requests.contains(req) implies post.sync_requests.count(req) == 1 by {
                    if pre.sync_requests.contains(req) {
                        assert( post.sync_requests.count(req) == 1 );
                    }
                }
            }
            let sync_req_id = lbl.arrow_ProgramUIOp_op().arrow_AcceptSyncRequest_sync_req_id();
            assert(post.sync_requests_inv()) by {
                assert forall |sr| #![auto] post.sync_req_map.dom().contains(sr)
                    implies !(post.sync_requests.dom().contains(sr)) by {
                    if sr == sync_req_id {
                        assert( pre.sync_requests.contains(sync_req_id) );  // trigger all_elems_single
                    }
                }
            }
            // Bridge: concrete sync_req_map records ephemeral_map().seq_end, abstract expects versions.len()-1.
            assert(pre.client_ready());
            let tail = pre.concrete_journal.journal.status.unwrap().unmarshalled_tail;
            let journal = pre.i_journal();
            let mapadt = pre.store;
            let inflight_on_disk =
                pre.concrete_journal.in_flight is Some
                && journal.in_flight is Some
                && pre.concrete_journal.disk.responses.contains_key(pre.concrete_journal.in_flight.unwrap().req_id);
            let versions = if inflight_on_disk {
                let in_flight_map = mapadt.in_flight.unwrap();
                let remaining_journal = journal.i().discard_old(in_flight_map.seq_end);
                let stable_lsn = journal.in_flight.unwrap().seq_end;
                floating_versions(in_flight_map, remaining_journal, stable_lsn)
            } else {
                let stable_lsn = journal.persistent.seq_end;
                floating_versions(mapadt.persistent, journal.i(), stable_lsn)
            };
            assert(ipre.versions == versions);
            // Prove full_journal properties from JCS invariant chain
            let jcs = pre.jcs();
            assert(jcs.valid_journal_structure()); // from inv()
            let etj = jcs.ephemeral_tj();
            assert(etj.decodable());
            assert(etj.wf());
            assert(etj.disk_view.acyclic());
            assert(etj.seq_end() == tail.seq_start);
            let lj = jcs.i().journal;
            assert(tail.wf());
            assert(lj.wf());
            let full_j = journal.i();
            if inflight_on_disk {
                let in_flight_map2 = mapadt.in_flight.unwrap();
                let remaining_journal = full_j.discard_old(in_flight_map2.seq_end);
                let stable_lsn = journal.in_flight.unwrap().seq_end;
                assert(remaining_journal.seq_end == tail.seq_end);
                assert(tail.can_discard_to(pre.concrete_journal.in_flight.unwrap().journal_version));
                assert(stable_lsn <= remaining_journal.seq_end + 1);
                floating_versions_len(in_flight_map2, remaining_journal, stable_lsn);
            } else {
                let stable_lsn = journal.persistent.seq_end;
                assert(tail.can_discard_to(pre.concrete_journal.persistent_journal_seq_end));
                assert(stable_lsn <= full_j.seq_end + 1);
                floating_versions_len(mapadt.persistent, full_j, stable_lsn);
            }
            assert(ipre.versions.len() == tail.seq_end + 1);
            assert(pre.to_atomic().journal.seq_end() == pre.to_atomic().ephemeral_map().seq_end);
            assert((ipre.versions.len() - 1) as nat == pre.to_atomic().ephemeral_map().seq_end as nat);
            assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::req_sync()));
            assert( post.sync_req_reply_ids_disjoint() ) by {
                assert forall |req_id, reply_id| #![auto] post.sync_requests.contains(req_id) && post.sync_replies.contains(reply_id)
                implies req_id != reply_id by {
                    if req_id != sync_req_id {
                        assert( pre.sync_requests.contains(req_id) );
                    }
                }
            }
            assert( post.inv() );
        },
        SystemModelTwo::Step::program_deliver_sync_reply(new_sync_req_map) => {
            assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::reply_sync()));
            let sync_req_id = lbl.arrow_ProgramUIOp_op().arrow_DeliverSyncReply_sync_req_id();
            assert( post.sync_req_reply_ids_disjoint() ) by {
                assert forall |req_id, reply_id| #![auto] post.sync_requests.contains(req_id) && post.sync_replies.contains(reply_id)
                implies req_id != reply_id by {
                    if reply_id != sync_req_id {
                        assert( pre.sync_replies.contains(reply_id) );
                    }
                }
            }
            assert( post.inv() );
        },
        SystemModelTwo::Step::program_disk(new_concrete_journal, new_outstanding_cache_reqs, new_recovery_state, new_store, new_sync_req_map) => {
            // Extract the disk event witness
            let de = choose |de: DiskEvent|
                AtomicState::disk_transition(pre.to_atomic(), post.to_atomic(),
                    de, lbl->info.reqs, lbl->info.resps);

            reveal(sm2_i);

            match de {
                DiskEvent::InitiateRecovery{..} | DiskEvent::SuperblockRecovery{..} => {
                    reveal(SystemModelTwo::State::i_persistent);
                    assert(!pre.client_ready());
                    assert(!post.client_ready());
                    assume(post.inv());
                },
                DiskEvent::CacheIOBegin{..} | DiskEvent::CacheIOEnd{..} => {
                    if pre.client_ready() {
                        reveal(SystemModelTwo::State::i_ephemeral);
                        assume(ipre == ipost);
                    } else {
                        reveal(SystemModelTwo::State::i_persistent);
                    }
                    assume(post.inv());
                },
                DiskEvent::ExecuteSyncBegin{..} => {
                    assume(false); // TODO: needs FreezeForCommit reasoning + wf invariant
                },
                DiskEvent::ExecuteSyncEnd{..} => {
                    assume(false); // TODO: needs commit_complete reasoning
                },
            }
            assert(ipre == ipost);
            assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
            assert( post.inv() );
        },
        SystemModelTwo::Step::program_internal(new_concrete_journal, new_outstanding_cache_reqs, new_recovery_state, new_store) => {
            // Extract internal event witness
            let ie = choose |ie: InternalEvent|
                AtomicState::internal_transitions(pre.to_atomic(), post.to_atomic(), ie);

            reveal(sm2_i);
            match ie {
                InternalEvent::StoreInternal{} => {
                    // store_internal: only store changes (AbstractCrashAwareMap internal step)
                    // i_journal() unchanged, inflight_on_disk unchanged, versions unchanged.
                    reveal(SystemModelTwo::State::i_ephemeral);
                    reveal(AbstractCrashAwareMap::State::next);
                    reveal(AbstractCrashAwareMap::State::next_by);

                    // ACM internal transitions (freeze_map, freeze_persistent, ephemeral)
                    // all preserve ephemeral->v.stamped_map via AbstractMap freeze_as/internal
                    reveal(AbstractMap::State::next);
                    reveal(AbstractMap::State::next_by);
                    assert(pre.concrete_journal == post.concrete_journal);
                    assert(post.store.ephemeral == pre.store.ephemeral);
                    assert(post.to_atomic().wf());
                },
                InternalEvent::JournalRecovery{..} | InternalEvent::MapRecovery{..} => {
                    // During recovery: !client_ready for both pre and post.
                    // i() uses i_persistent() which only depends on disk.content[sb_addr]
                    // and requests/replies. Disk unchanged (SM2 constraint), requests/replies
                    // unchanged by internal transitions.
                    reveal(SystemModelTwo::State::i_persistent);
                    assume(post.inv());
                },
                InternalEvent::RecoveryComplete{} => {
                    assume(false); // TODO: must prove i_persistent(pre) == i_ephemeral(post)
                },
            }
            assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
            assert( post.inv() );
        },
        SystemModelTwo::Step::disk_internal(new_disk) => {
            if pre.sb_landed(post) {
                assume(false); // TODO: maps to SyncOp
                let info = pre.concrete_journal.in_flight.unwrap();
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::sync(info.journal_version as int)));
            } else {
                reveal(sm2_i);
                if pre.client_ready() {
                    reveal(SystemModelTwo::State::i_ephemeral);
                    assume(ipre == ipost);
                } else {
                    reveal(SystemModelTwo::State::i_persistent);
                    reveal(AsyncDisk::State::next);
                    reveal(AsyncDisk::State::next_by);
                    if !(pre.recovery_state is RecoveryComplete) {
                        assert(ipre == ipost);
                    } else {
                        assume(ipre == ipost);
                    }
                }
                assume(post.inv());
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
            }
            assert( post.inv() );
        },
        SystemModelTwo::Step::crash(new_concrete_journal, new_disk, new_store) => {
            assume(false); // TODO: depends on i() returning meaningful state
            assert(post.inv());
            assume(ipre.versions.get_prefix(ipre.stable_index()+1) == ipost.versions);
            assert(ipost.async_ephemeral == AsyncMap::State::init_ephemeral_state());
            assert( post.inv() );
            assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::crash()));
        },
        SystemModelTwo::Step::noop() => {
            assert(ipre == ipost);
            assert( post.inv() );
            assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
        },
        SystemModelTwo::Step::accept_sync_request() => {
            let sync_req_id = lbl.arrow_AcceptSyncRequest_sync_req_id();
            assert( pre.fresh_id(sync_req_id) );
            assert( !pre.sync_requests.contains(sync_req_id) );
            assert( all_elems_single(post.sync_requests) );
            assert( post.sync_req_ids_in_history() ) by {
                assert forall |req_id| #![auto] post.sync_requests.contains(req_id)
                    implies post.id_history.contains(req_id) by {
                    if req_id != sync_req_id {
                        assert( pre.id_history.contains(req_id) );
                    }
                }
            }
            assert( post.sync_requests_inv() ) by {
                if post.client_ready() {
                    assert forall |id| #![auto] post.sync_req_map.dom().contains(id)
                        implies !post.sync_requests.dom().contains(id) by {
                        if id != sync_req_id {
                            assert( pre.sync_req_map.dom().contains(id) );
                        }
                    }
                }
            }
            assert( post.sync_req_reply_ids_disjoint() ) by {
                assert forall |req_id, reply_id| #![auto] post.sync_requests.contains(req_id) && post.sync_replies.contains(reply_id)
                implies req_id != reply_id by {
                    if req_id == sync_req_id {
                        assert( !pre.id_history.contains(sync_req_id) );
                        assert( pre.sync_replies.contains(reply_id) );
                        assert( pre.id_history.contains(reply_id) );
                        assert( req_id != reply_id );
                    } else {
                        assert( pre.sync_requests.contains(req_id) );
                    }
                }
            }
            // prove program_sync_req_ids_in_history
            if post.client_ready() {
                assert( forall |id| pre.id_history.contains(id) ==> post.id_history.contains(id) );
            }
            assert(post.inv());
            assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
        },
        SystemModelTwo::Step::deliver_sync_reply() => {
            let sync_req_id = lbl.arrow_DeliverSyncReply_sync_req_id();
            assert( post.sync_req_reply_ids_disjoint() ) by {
                assert forall |req_id, reply_id| #![auto] post.sync_requests.contains(req_id) && post.sync_replies.contains(reply_id)
                implies req_id != reply_id by {
                    if req_id != sync_req_id {
                        assert( pre.sync_requests.contains(req_id) );
                        assert( pre.sync_replies.contains(reply_id) );
                    }
                }
            }
            assert(post.inv());
            assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
        },
        _ => { assert(false); }
    }
    assert( CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl) );
}

}
