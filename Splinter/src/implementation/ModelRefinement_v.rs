#[allow(unused_imports)]    // lost in erasure
use vstd::prelude::*;
use vstd::prelude::*;

use vstd::{math, multiset::Multiset};
use crate::spec::AsyncDisk_t::{Address, AsyncDisk, DiskRequest, DiskResponse};
use crate::spec::MapSpec_t::{AsyncMap, CrashTolerantAsyncMap, EphemeralState, ID, MapSpec, SyncReqId, Version};
use crate::trusted::SystemModel_t::SystemModel;
use crate::trusted::RefinementObligation_t::RefinementObligation;
use crate::trusted::ProgramModelTrait_t::{DiskLabel, ProgramModelTrait, ProgramUserOp};
use crate::disk::GenericDisk_v::Pointer;
use crate::abstract_system::AbstractCrashAwareJournal_v::AbstractCrashAwareJournal;
use crate::journal::LinkedJournal_v::DiskView;
use crate::implementation::AtomicState_v::{AtomicState, DiskEvent, raw_page_to_record, to_map_label};
use crate::implementation::Cache_v::{Cache, Slot};
use crate::implementation::CachedJournal_v::build_lsn_addr_index_from_reads;
use crate::allocation_layer::LikesJournal_v::{LikesJournal, LsnAddrIndex};
use crate::implementation::ConcreteProgramModel_v::ConcreteProgramModel;
use crate::implementation::MultisetMapRelation_v::{all_elems_single, multiset_map_membership, multiset_map_singleton_ensures, multiset_to_map};
use crate::implementation::DiskLayout_v::{DiskLayout, spec_superblock_addr};
use crate::implementation::SuperblockTypes_v::{ASuperblock, Superblock, singleton_floating_seq};
use crate::marshalling::IJournalRecordFormat_v::IJournalRecordFormat;
use crate::marshalling::Marshalling_v::Marshal;
use crate::abstract_system::AbstractCrashAwareMap_v::AbstractCrashAwareMap;
use crate::abstract_system::AbstractCrashAwareSystemRefinement_v::floating_versions;
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::AbstractCrashAwareJournal_v::Ephemeral;
use crate::abstract_system::AbstractJournal_v::AbstractJournal;

verus!{

// TODO: put into vstd/multiset_lib.rs
pub open spec fn multiset_to_set<V>(m: Multiset<V>) -> Set<V> {
    Set::new(|v| m.contains(v))
}

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

proof fn build_lsn_addr_index_from_reads_refines(dv: DiskView, root: Pointer)
requires 
    dv.buildable(root),
    // curr_end == dv.seq_end(root),
ensures 
    build_lsn_addr_index_from_reads(dv.entries, dv.boundary_lsn, root)
    == dv.build_lsn_addr_index(root)
decreases dv.the_rank_of(root)
{
    if root is Some {
        let curr_msgs = dv.entries[root.unwrap()].message_seq;
        let start_lsn = math::max(dv.boundary_lsn as int, curr_msgs.seq_start as int) as nat;
        let next_ptr = dv.entries[root.unwrap()].cropped_prior(dv.boundary_lsn);
        build_lsn_addr_index_from_reads_refines(dv, next_ptr);
    }
}

impl SystemModel::State<ConcreteProgramModel>  {
    // we have to build the ephemeral journal
    // because we are not tracking the freshest rec

    // pub open spec fn persistent_journal(self) -> TruncatedJournal
    // {
    //     let full_disk =  Map::new(
    //         |addr| self.disk.content.contains_key(addr),
    //         |addr| raw_page_to_record(self.disk.content[addr])
    //     );

    //     let dv = DiskView{
    //         boundary_lsn: self.program.state.store.persistent.seq_end,
    //         entries: full_disk
    //     };

    //     let tj = TruncatedJournal {
    //         freshest_rec: self.program.state.journal., // root address of journal
    //         pub disk_view: DiskView,
    //     }


    //     tj.build_tight()
    // }


    // I think what I want to do is this 
    // 1. have a version that passes all disk addresses to journal data
    //    build lsn addr index based on that 
    //    restrict the 

    /*
        ephemeral: 
            ephemeral journal => likesjournal


            I am confused because I tried to build a disk when there isn't one 
            before I did this I did a whole other thing of 
    */ 



    // persistent is always part of the ephemeral 
    // let's write the ephemeral first? 

    // you have to merge with the cache?
    // how do we get any of the persistet page addresses

  

    // pub open spec fn dirty_journal_cache(self) -> Map<Address, JournalRecord>
    // {
    //     Map::new(
    //         |addr| self.cache.valid_dirty_addr(addr),
    //         |addr| raw_page_to_record(self.cache.entries[self.cache.lookup_map[addr]]->data)
    //     )
    // }

    // NOTE(JL): in our actual version where cache contains different types 
    // of pages we will use the domain map of each component to determine marshalled type
    // pub open spec fn ephemeral_disk(self) -> DiskView
    // {
    //     DiskView{
    //         boundary_lsn: self.journal.boundary_lsn,
    //         entries: self.persistent_journal_disk().union_prefer_right(self.dirty_journal_cache()),
    //     }
    // }

    // pub open spec fn ephemeral_tj(self) -> TruncatedJournal
    // {
    //     TruncatedJournal{freshest_rec: self.journal.freshest_rec, disk_view: self.ephemeral_disk()}
    // }

    // // all relative to an ephemeral disk (cache+disk)
    // pub open spec fn valid_journal_structure(self) -> bool 
    // {
    //     &&& self.ephemeral_tj().decodable()
    //     &&& self.ephemeral_tj().seq_end() == self.journal.unmarshalled_tail.seq_start 
    //     &&& self.journal.lsn_addr_index == self.ephemeral_tj().build_lsn_addr_index()
    //     &&& self.journal.lsn_addr_index.values() =~= self.ephemeral_tj().disk_view.entries.dom()
    // }

    // Interpret concrete CachedJournal state as AbstractCrashAwareJournal state.
    // Only called from i_ephemeral(), so client_ready() holds (status is Some).
    pub open spec fn i_journal(self) -> AbstractCrashAwareJournal::State
    {
        let state = self.program.state;
        let tail = state.journal.status.unwrap().unmarshalled_tail;
        AbstractCrashAwareJournal::State {
            persistent: tail.discard_recent(state.persistent_journal_seq_end),
            ephemeral: Ephemeral::Known {
                v: AbstractJournal::State { journal: tail }
            },
            in_flight: if state.in_flight is Some {
                Some(tail.discard_recent(state.in_flight.unwrap().journal_version))
            } else {
                None
            },
        }
    }

    // pub open spec fn i(self) -> CrashTolerantAsyncMap::State
    // {

        // if we can refine and prove in terms of abstract crash aware journal we should be ok

        // our starting one is a stamped map
        // let persistent = self.program.state.persistent; // store image
        // applying this 


        // let versions = 
        // i_persistent 
        // has to apply to the journal entry

        // let async_ephemeral = EphemeralState{
        //     requests: self.requests.dom(),
        //     replies: self.replies.dom(),
        // }

        // CrashTolerantAsyncMap::State{
        //     versions: arbitrary(),
        //     async_ephemeral,
        //     sync_requests: self.program.state.sync_req_map,
        // }

        // pub versions: FloatingSeq<Version>,
        /// The async ephemeral state (set of outstanding client requests and replies).
        /// See comments for EphemeralState struct
    // }

    pub open spec fn inv(self) -> bool
    {
        // let cache = self.program.state.cache;

        &&& self.program.state.wf()
        &&& self.disk.inv()

        // &&& cache.clean_pages_agree_with_disk()
        // &&& self.program.state.client_ready() ==> {
        //     let index = self.program.state.journal.status.unwrap().lsn_addr_index;
        //     &&& cache.dirty_pages_bounded_by_journal_index(index)
        // }

        // we do need to track the decodable part probably 
        

        // ephemeral map 
        // &&& self.ephemeral_map() == self.journal.journal.apply_to_stamped_map(self.persistent_map())
        // &&& self.ephemeral_map() == self.journal.journal
        //         .discard_old(self.in_flight_map().seq_end)
        //         .apply_to_stamped_map(self.in_flight_map())

        &&& self.persistent_sb_disk_inv()
        &&& self.awaiting_sb_response_is_disk_content()
        &&& self.no_writes_till_recovery_complete()
        &&& self.outstanding_reqs_consistent()
        &&& self.sb_req_id_disjoint_cache_reqs()
        &&& self.sb_response_is_write_resp()
        &&& self.sync_requests_inv()
        &&& self.journal_pages_parsable()

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
    }

    // pub open spec fn clean_pages_agree_with_disk(self) -> bool
    // {
    //     forall |slot| #[trigger] self.valid_clean_slot(slot)
    //     ==> disk_content[self.entries[slot].get_addr()] == self.entries[slot]->data
    // }

    // pub open spec fn dirty_pages_bounded_by_journal_index(self, lsn_addr_index: LsnAddrIndex) -> bool
    // {
    //     forall |addr| #[trigger] self.valid_dirty_addr(addr) 
    //     ==> lsn_addr_index.contains_value(addr)
    // }

    pub open spec fn persistent_sb_disk_inv(self) -> bool
    {
        let state = self.program.state;
        &&& self.disk.content.contains_key(spec_superblock_addr())
        &&& {
            let asb : ASuperblock = DiskLayout::spec_new().spec_parse_inner(self.disk.content[spec_superblock_addr()]);
            let sb : Superblock = asb@;
            // The raw store always has unique keys (survives crashes, writes)
            &&& asb.wf()
            &&& sb.wf()
            &&& state.client_ready() ==>
            {
                if state.in_flight is Some && self.disk.responses.contains_key(state.in_flight.unwrap().req_id) {
                    sb == state.in_flight_sb()
                } else {
                    sb == state.persistent_sb()
                }
            }
        }
    }

    // During AwaitingSuperblock, the only disk activity was the superblock read.
    // No writes happen (no_writes_till_recovery_complete), so the read response
    // data matches the current disk content at the superblock address.
    pub open spec fn awaiting_sb_response_is_disk_content(self) -> bool
    {
        self.program.state.recovery_state is AwaitingSuperblock ==>
            forall |id| #[trigger] self.disk.responses.contains_key(id)
                && self.disk.responses[id] is ReadResp
                ==> self.disk.responses[id]->data == self.disk.content[spec_superblock_addr()]
    }

    // All non-superblock disk pages are parsable as journal records.
    // This follows from: mkfs only writes the superblock, and journal writes
    // only write marshalled (hence parsable) journal records.
    pub open spec fn journal_pages_parsable(self) -> bool
    {
        let fmt = IJournalRecordFormat::spec_new();
        forall |addr: Address| self.disk.content.contains_key(addr)
            && addr != spec_superblock_addr()
            ==> #[trigger] fmt.parsable(self.disk.content[addr])
    }

    // NOTE: I think we needed this before to ensure that up until recovery is done all requests are read resps
    // pre recovery state constraint
    pub open spec fn no_writes_till_recovery_complete(self) -> bool
    {
        !(self.program.state.recovery_state is RecoveryComplete) ==> {
            &&& forall |id| #[trigger] self.disk.requests.contains_key(id) ==> !(self.disk.requests[id] is WriteReq)
            &&& forall |id| #[trigger] self.disk.responses.contains_key(id) ==> !(self.disk.responses[id] is WriteResp)
        }
    }

    pub open spec fn sync_requests_inv(self) -> bool
    {
        &&& all_elems_single(self.sync_requests)
        &&& self.program.state.client_ready() ==>
            // sync reqs pass *out of* the system sync_requests into the program state
            self.program.state.sync_req_map.dom().disjoint(self.sync_requests.dom())
    }

    // assumes all I/Os beside superblock are managed by the cache
    pub open spec(checked) fn addr_for_id(self, id: ID) -> Address
    {
        let state = self.program.state;
        if state.in_flight is Some && state.in_flight.unwrap().req_id == id {
            spec_superblock_addr()
        } else {
            state.outstanding_cache_reqs[id]
        }
    }

    // The reason we track these relations is so that we can bring them
    // down to the implementation layer instead of proving them? 
    // Q: does this mean we should remove the load request check in the state machine?
    // outstanding reqs must be consistent with cache and disk
    pub open spec(checked) fn outstanding_reqs_consistent(self) -> bool
        recommends self.program.state.wf()
    {
        let state = self.program.state;
        let in_flight_sb_id = if state.in_flight is Some { set!{state.in_flight.unwrap().req_id} } else { set!{} };

        // 1. all disk ids are bounded by cache reqs and inflight_sb
        &&& self.disk.requests.dom() + self.disk.responses.dom() == state.outstanding_cache_reqs.dom() + in_flight_sb_id        
        // 2. disk requests are correctly recorded
        &&& forall |id| #[trigger] self.disk.requests.contains_key(id)
        ==> {
            let req = self.disk.requests[id];
            &&& req.addr() == self.addr_for_id(id)
            &&& req is ReadReq && state.outstanding_cache_reqs.contains_key(id) ==> {
                let slot = state.cache.lookup_map[state.outstanding_cache_reqs[id]];
                &&& state.cache.entries[slot] is Loading
            }
            &&& req is WriteReq ==> {
                if state.outstanding_cache_reqs.contains_key(id) {
                    let slot = state.cache.lookup_map[state.outstanding_cache_reqs[id]];
                    &&& state.cache.status_map[slot] is Writeback
                    &&& state.cache.entries[slot]->data == req->data
                } else {
                    &&& req->to == spec_superblock_addr()
                    &&& state.in_flight is Some
                    &&& state.in_flight.unwrap().req_id == id
                    &&& DiskLayout::spec_new().spec_parse(req->data) == state.in_flight_sb()
                }
            }
        }
        // 3. disk responses are correctly reflected
        &&& forall |id| #[trigger] self.disk.responses.contains_key(id) 
        ==> {
            let resp = self.disk.responses[id];
            &&& resp is ReadResp ==> {
                &&& resp->data == self.disk.content[self.addr_for_id(id)]
                &&& state.outstanding_cache_reqs.contains_key(id) ==> {
                    let slot = state.cache.lookup_map[state.outstanding_cache_reqs[id]];
                    &&& state.cache.entries[slot] is Loading
                }
            }
            &&& resp is WriteResp && state.outstanding_cache_reqs.contains_key(id) ==> {
                let addr = state.outstanding_cache_reqs[id];
                let slot = state.cache.lookup_map[addr];
                &&& state.cache.status_map[slot] is Writeback
                &&& self.disk.content[addr] == state.cache.entries[slot]->data
                // SKIP the SB requirement because those are tracked by persistent sb inv
                //     let disk_sb = self.disk.content[spec_superblock_addr()];
                //     &&& state.in_flight is Some
                //     &&& state.in_flight.unwrap().req_id == id
                //     &&& DiskLayout::spec_new().spec_parse(disk_sb) == state.in_flight_sb()
                // }
            }
        }
    }

    // Disk responses at the superblock write ID are always WriteResp.
    // A superblock operation is always a WriteReq, and the disk model's
    // process_write converts WriteReq to WriteResp.
    pub open spec(checked) fn sb_response_is_write_resp(self) -> bool
    {
        let state = self.program.state;
        state.in_flight is Some ==>
            forall |id| #[trigger] self.disk.responses.contains_key(id)
                && state.in_flight.unwrap().req_id == id
                ==> self.disk.responses[id] is WriteResp
    }

    // Superblock write ID is disjoint from cache request IDs.
    // Follows from disk model freshness: when the superblock write is issued,
    // the ID is fresh relative to existing disk requests/responses, which
    // (by outstanding_reqs_consistent) coincide with outstanding_cache_reqs.
    // Subsequent cache IDs are also fresh, so they can't collide with the
    // superblock ID either.
    pub open spec(checked) fn sb_req_id_disjoint_cache_reqs(self) -> bool
    {
        self.program.state.in_flight is Some ==>
            !self.program.state.outstanding_cache_reqs.dom().contains(
                self.program.state.in_flight.unwrap().req_id)
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
    // pub open spec(checked) fn superblock_writes_inv(self) -> bool
    // {
    //     forall |id| #![auto] self.disk.requests.contains_key(id) 
    //         && self.disk.requests[id] is WriteReq 
    //         && self.disk.requests[id]->to == spec_superblock_addr()
    //         ==> DiskLayout::impl_inv(self.disk.requests[id]->data)
    // }

    // interpretation given no ephemeral state and only on persistent disk
    closed spec(checked) fn i_persistent(self) -> (mapspec: CrashTolerantAsyncMap::State)
    recommends
        !self.program.state.client_ready(),
        self.disk.content.contains_key(spec_superblock_addr()),    // quash recommendation not met
    {
        let sb = DiskLayout::spec_new().spec_parse(self.disk.content[spec_superblock_addr()]);
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
        self.program.state.wf(),
        self.program.state.client_ready(),
    {
        let state = self.program.state;
        let journal = self.i_journal(); // AbstractCrashAwareJournal::State (TODO: returns arbitrary)
        let mapadt = state.store;       // AbstractCrashAwareMap::State

        // Mirror CoordinationSystem.iversions_known() structure
        let inflight_on_disk =
            state.in_flight is Some
            && journal.in_flight is Some
            && self.disk.responses.contains_key(state.in_flight.unwrap().req_id);

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
            sync_requests: state.sync_req_map,
        }
    }

    closed spec fn sb_landed(self: Self, post: Self) -> bool
    {
        let state = self.program.state;
        &&& state.client_ready()
        &&& state.in_flight is Some
        &&& !self.disk.responses.contains_key(state.in_flight.unwrap().req_id)
        &&& post.disk.responses.contains_key(state.in_flight.unwrap().req_id)
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
        if model.program.state.client_ready() {
            model.i_ephemeral()
        } else {
            model.i_persistent()
        }
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

        match step {
            SystemModel::Step::accept_request() => {
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
                        assume(pre.requests.contains(lbl->req)); // trigger
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
            SystemModel::Step::deliver_reply() => {
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
            SystemModel::Step::program_execute(new_program) => {
                assume(false); // TODO: maps to operate(ExecuteOp)
                // Hints: let req = lbl->op->req; let reply = lbl->op->reply;
                // History invariant needs MapSpec::State::inv_next(..., to_map_label(req, reply))
                // Abstract step: AsyncMap::Step::execute(to_map_label(req, reply), ...)
            },
            SystemModel::Step::program_accept_sync_request(new_program) => {
                assume(false); // TODO: needs stable_index() reasoning
                assert( all_elems_single(post.sync_requests) ) by {
                    assert forall |req| #[trigger] post.sync_requests.contains(req) implies post.sync_requests.count(req) == 1 by {
                        if pre.sync_requests.contains(req) {
                            assert( post.sync_requests.count(req) == 1 );
                        }
                    }
                }
                let sync_req_id = lbl.arrow_ProgramUIOp_op().arrow_AcceptSyncRequest_sync_req_id();
                assert(post.sync_requests_inv()) by {
                    assert forall |sr| #![auto] post.program.state.sync_req_map.dom().contains(sr)
                        implies !(post.sync_requests.dom().contains(sr)) by {
                        if sr == sync_req_id {
                            assert( pre.sync_requests.contains(sync_req_id) );  // trigger all_elems_single
                        }
                    }
                }
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
            }
            SystemModel::Step::program_deliver_sync_reply(new_program) => {
                assume(false); // TODO: needs stable_index() reasoning
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
            SystemModel::Step::program_disk(new_program, new_disk) => {
                assume(false); // TODO: DiskEvent API has drifted; maps to Noop
            },
            SystemModel::Step::program_internal(new_program) => {
                assume(false); // TODO: needs help proving interpretation preserved across internal step
                assert(ipre == ipost);
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
                assert( post.inv() );
            },
            SystemModel::Step::disk_internal(new_disk) => {
                if pre.sb_landed(post) {
                    assume(false); // TODO: maps to SyncOp; InflightInfo.journal_version replaces old map_version
                    let info = pre.program.state.in_flight.unwrap();
                    assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::sync(info.journal_version as int)));
                } else {
                    assume(false); // TODO: inv(post) depends on i() being meaningful
                    assert(post.inv());
                    assert(ipre == ipost);
                    assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
                }
                assert( post.inv() );
            },
            SystemModel::Step::crash(new_program, new_disk) => {
                assume(false); // TODO: depends on i() returning meaningful state
                assert(post.inv());
                assume(ipre.versions.get_prefix(ipre.stable_index()+1) == ipost.versions);   // TODO(jonh)
                assert(ipost.async_ephemeral == AsyncMap::State::init_ephemeral_state()); // ext_eq
                assert( post.inv() );
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::crash()));
            },
            SystemModel::Step::noop() => {
                assert(ipre == ipost);
                assert( post.inv() );
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
            },
            SystemModel::Step::accept_sync_request() => {
                let sync_req_id = lbl.arrow_AcceptSyncRequest_sync_req_id();
                assert( pre.fresh_id(sync_req_id) );
                assert( !pre.sync_requests.contains(sync_req_id) );
                assert( all_elems_single(post.sync_requests) );
                assert( post.program.state == pre.program.state );
                assert( post.sync_req_ids_in_history() ) by {
                    assert forall |req_id| #![auto] post.sync_requests.contains(req_id)
                        implies post.id_history.contains(req_id) by {
                        if req_id != sync_req_id {
                            assert( pre.id_history.contains(req_id) );
                        }
                    }
                }
                assert( post.sync_requests_inv() ) by {
                    if post.program.state.client_ready() {
                        assert forall |id| #![auto] post.program.state.sync_req_map.dom().contains(id)
                            implies !post.sync_requests.dom().contains(id) by {
                            if id != sync_req_id {
                                assert( pre.program.state.sync_req_map.dom().contains(id) );
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
                if post.program.state.client_ready() {
                    assert( forall |id| pre.id_history.contains(id) ==> post.id_history.contains(id) );
                }
                assert(post.inv());
                assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
            },
            SystemModel::Step::deliver_sync_reply() => {
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
