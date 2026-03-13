// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::pervasive::*;
use vstd::modes::*;
use vstd::assert_maps_equal;
use vstd::tokens::InstanceId;
use vstd::std_specs::hash::*;

use crate::trusted::ClientAPI_t::{ClientAPI, DiskResponseRecord};
use crate::trusted::ReqReply_t::{Input, Output, Reply, Request};
use crate::trusted::KVStoreTrait_t::{KVStoreTrait, open_system_invariant_disk_response, open_system_invariant_disk_response_singleton, open_system_invariant_user_request};
use crate::trusted::KVStoreTokenized_t::KVStoreTokenized;
use crate::trusted::ProgramModelTrait_t::{ProgramDiskInfo, ProgramLabel, ProgramModelTrait, ProgramUserOp};
use crate::abstract_system::StampedMap_v::LSN;
use crate::journal::LinkedJournal_v;

use crate::spec::MapSpec_t::{ID, MapSpec};
use crate::spec::TotalKMMap_t::TotalKMMap;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Message, Value};
use crate::abstract_system::StampedMap_v::{StampedMap};
use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::abstract_system::MsgHistory_v::KeyedMessage;
use crate::abstract_system::AbstractMap_v::AbstractMap;

use crate::implementation::ModelRefinement_v::RefinementProof;
use crate::implementation::ConcreteProgramModel_v::ConcreteProgramModel;
use crate::implementation::AtomicState_v::{AtomicState, DiskEvent, InflightInfo, InternalEvent, ProgramEvent, RecoveryState, journal_marshall_labels, map_to_multiset, to_journal_records, to_store_maps};
use crate::implementation::MultisetMapRelation_v::{multiset_map_singleton, multiset_map_singleton_ensures, multiset_to_map, unique_keys};
use crate::implementation::VecMap_v::VecMap;
use crate::implementation::JournalTypes_v::{ILsn};
use crate::allocation_layer::LikesJournal_v::lsn_addr_index_discard_up_to;
use crate::implementation::JournalImpl_v::{BeginWritebackForTargetResult, CleanForCommitResult, FrozenJournal, IJournalSnapshot, JournalImpl, RecoverIndexResult, RecoverMapResult, all_pages_parsable, cache_matches_raw_disk, iaddr_view, journal_disk_inv, load_index_labels, map_recovery_labels};
use crate::implementation::SuperblockTypes_v;
use crate::implementation::SuperblockTypes_v::{ASuperblock, ISuperblock};
use crate::implementation::StoreImpl_v::{LoadMapResult, StoreImpl, raw_page_to_store_kmmap};
use crate::implementation::CachedJournal_v::CachedJournal;
use crate::implementation::CachedJournal_v;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::WF_v::WF;
use crate::marshalling::IJournalRecordFormat_v::IJournalRecordFormat;
use crate::marshalling::Marshalling_v::Marshal;
use crate::implementation::OverflowFiction_v::*;
use crate::abstract_system::AbstractCrashAwareMap_v;
use crate::abstract_system::AbstractCrashAwareMap_v::Ephemeral;
use crate::implementation::Cache_v::Cache;
use crate::implementation::FracCacheImpl_v::{FetchErrorCode, FracCacheImpl, MutHandle, PAGE_SIZE_BYTES, ReserveWriteResult, WritebackAcquireResult, WritebackHandle, cache_load_label, cache_write_label};

#[allow(unused_imports)]
use vstd::multiset::*;
#[allow(unused_imports)]
use vstd::tokens::*;
#[allow(unused_imports)]
use crate::spec::AsyncDisk_t::{Address, AsyncDisk, Disk, DiskRequest, DiskResponse, RawPage};
use crate::spec::ImplDisk_t::{IAddress, IDiskRequest, IDiskResponse};
#[allow(unused_imports)]
use crate::implementation::DiskLayout_v::{DiskLayout, spec_superblock_addr, superblock_addr};
use vstd::hash_map::HashMapWithView;

verus!{

broadcast use JournalImpl::view_ensures;

pub closed spec fn good_req(instance_id: InstanceId, req: Request, req_shard: RequestShard) -> bool
{
    &&& req_shard.instance_id() == instance_id
    &&& req_shard.element() == req
}


// Requests that can be satisfied when the in-flight superblock lands.
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
    sync_target_lsn: ILsn,

    // every sync req in this buffer has lsn <= sync_target_lsn
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
        &&& self.sync_target_lsn == 0
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
            sync_target_lsn: 0,
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

    fn take_superblocking_reqs(&mut self) -> (out: Vec<Request>)
    ensures
        self.buffered_reqs@ == old(self).buffered_reqs@,
        self.journal_cleaning_reqs@ == old(self).journal_cleaning_reqs@,
        self.sync_target_lsn == old(self).sync_target_lsn,
        self.superblocking_reqs@.len() == 0,
        out@ == old(self).superblocking_reqs@,
    {
        let mut out = vec![];
        while self.superblocking_reqs.len() > 0
        invariant
            self.buffered_reqs@ == old(self).buffered_reqs@,
            self.journal_cleaning_reqs@ == old(self).journal_cleaning_reqs@,
            self.sync_target_lsn == old(self).sync_target_lsn,
            self.superblocking_reqs@ + out@ == old(self).superblocking_reqs@,
        decreases self.superblocking_reqs.len(),
        {
            let ghost prev_out = out@;
            let ghost prev_super = self.superblocking_reqs@;
            let req = self.superblocking_reqs.pop().unwrap();
            out.insert(0, req);
            proof {
                assert(prev_super == self.superblocking_reqs@.push(req));
                assert(out@ == seq![req] + prev_out);
                assert(self.superblocking_reqs@ + out@
                    == self.superblocking_reqs@ + seq![req] + prev_out);
                assert(self.superblocking_reqs@ + seq![req] == prev_super);
            }
        }
        out
    }

    fn swap_cleaning_and_superblocking(&mut self)
    ensures
        self.buffered_reqs@ == old(self).buffered_reqs@,
        self.sync_target_lsn == old(self).sync_target_lsn,
        self.journal_cleaning_reqs@ == old(self).superblocking_reqs@,
        self.superblocking_reqs@ == old(self).journal_cleaning_reqs@,
    {
        std::mem::swap(&mut self.superblocking_reqs, &mut self.journal_cleaning_reqs);
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
    store_ptr: Option<IAddress>,
}

// TODO replace helper-level map/history composition references with MsgHistory::map_plus_history.

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

enum JournalMarshalStepResult {
    Done{},
    CacheFull{},
    Success{},
}

#[derive(Clone, Copy)]
enum SuperblockMotivation {
    PushMap,
    PushJournal,
}

enum OutstandingReqInfo{
    SuperBlockReq{},
    CacheLoadReq{read_addr: IAddress, load_handle: MutHandle},
    JournalCacheWriteReq{write_addr: IAddress, handle: WritebackHandle},
    StoreWriteReq{write_addr: IAddress, handle: WritebackHandle},
}

// Data-free mirror of OutstandingReqInfo, used to capture the variant from a
// borrowed peek (get) without holding the borrow across &mut self calls.
enum OutstandingReqKind{
    SuperBlockReq,
    CacheLoadReq,
    JournalCacheWriteReq,
    StoreWriteReq,
}

// This struct supplies KVStoreTrait, which has both the entry point to the implementation and the
// proof hooks to satisfy the refinement obligation trait.
pub struct Implementation {
    recovery_phase: RecoveryPhase,

    sync_counter: u64,
    journal_flush_accumulator: u64,
    current_sync_motivation: Option<SuperblockMotivation>,

    // starts at recovered map version, ends matching store
    journal: JournalImpl,
    
    cache: FracCacheImpl,

    // this is a truncate in flight, only set when a truncation is occuring
    in_flight: Option<InFlight>,

    store: StoreImpl,
    store_initialized: bool,

    // token for the program model variable
    model: Tracked<ModelShard>,

    // we do not own a mutable reference to this
    instance: Tracked<KVStoreTokenized::Instance<ConcreteProgramModel>>,

    sync_requests: SyncRequestBuffer,

    outstanding_requests: HashMapWithView<ID, OutstandingReqInfo>,

    // Hint to retry superblock launch from top-level control flow after
    // background marshalling advances.
    should_retry_superblock_launch: bool,
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

    closed spec fn i_ephemeral_store(self) -> Ephemeral
    {
        if self.store_initialized {
            Ephemeral::Known{
                v: AbstractMap::State{
                    stamped_map: StampedMap{
                        value: self.store@,
                        seq_end: self.store.store_lsn_nat(),
                    }
                }
            }
        } else {
            Ephemeral::Unknown
        }
    }

    pub closed spec fn store_alloc_au(&self) -> nat
    {
        self.store.alloc_au() as nat
    }

    pub closed spec fn prepared_store_ptr(&self) -> Option<IAddress>
    {
        self.store.prepared_store_ptr()
    }

    pub closed spec fn prepared_store_ptr_view(&self) -> Option<Address>
    {
        self.store.prepared_store_ptr_view()
    }

    pub closed spec fn prepared_store_lsn(&self) -> u64
    {
        self.store.prepared_store_lsn()
    }

    pub closed spec fn prepared_store_lsn_nat(&self) -> nat
    {
        self.store.prepared_store_lsn_nat()
    }

    pub fn exec_prepared_store_ptr(&self) -> (out: Option<IAddress>)
        ensures out == self.prepared_store_ptr()
    {
        self.store.exec_prepared_store_ptr()
    }

    pub fn exec_prepared_store_lsn(&self) -> (out: u64)
        ensures
            out == self.prepared_store_lsn(),
            out as nat == self.prepared_store_lsn_nat(),
    {
        self.store.exec_prepared_store_lsn()
    }

    pub closed spec fn landed_store_ptr(&self) -> Option<IAddress>
    {
        self.store.persistent_store_ptr()
    }

    pub closed spec fn landed_store_ptr_view(&self) -> Option<Address>
    {
        self.store.persistent_store_ptr_view()
    }

    pub closed spec fn landed_store_lsn_nat(&self) -> nat
    {
        self.journal.seq_start()
    }

    pub closed spec fn landed_store_lsn(&self) -> u64
    {
        self.journal.seq_start() as u64
    }

    pub fn exec_landed_store_ptr(&self) -> (out: Option<IAddress>)
        ensures out == self.landed_store_ptr()
    {
        self.store.exec_persistent_store_ptr()
    }

    pub fn exec_landed_store_lsn(&self) -> (out: u64)
        ensures out as nat == self.landed_store_lsn_nat()
    {
        self.journal.exec_seq_start()
    }

    closed spec fn inv_recover(self) -> bool {
        &&& self.recovery_phase is FetchingSuperblock
        &&& !self.store_initialized
        &&& self.model@.instance_id() == self.instance@.id()
        &&& self.in_flight is None
        &&& self.sync_requests.valid_empty_sync_buffer(self.instance@.id())
        &&& self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty()
        &&& self.state().outstanding_cache_reqs == Map::<ID, Address>::empty()
        &&& self.state().recovery_state is Begin
        &&& self.cache.wf()
        &&& self.outstanding_requests@.dom() == Set::<ID>::empty()
        &&& self.state().in_flight is None
        &&& self.state().outstanding_cache_reqs == Map::<ID, Address>::empty()
    }

    pub closed spec fn outstanding_req_is_superblock(self, id: ID) -> bool {
        &&& self.outstanding_requests@.dom().contains(id)
        &&& self.outstanding_requests@[id] is SuperBlockReq
    }

    // The exec-level outstanding_requests map corresponds to the model-level
    // outstanding_cache_reqs (for cache ops) and in_flight (for superblock writes).
    pub closed spec fn outstanding_reqs_match_model(self) -> bool {
        let state = self.state();
        let in_flight_sb_id = if state.in_flight is Some { set!{state.in_flight.unwrap().req_id} } else { set!{} };

        // Domain: exec outstanding_requests covers exactly cache reqs + in-flight sb
        &&& self.outstanding_requests@.dom() == state.outstanding_cache_reqs.dom() + in_flight_sb_id

        // Cache entries match: cache request IDs are exactly outstanding_cache_reqs
        &&& forall |id| #[trigger] self.outstanding_requests@.dom().contains(id) ==> {
            &&& (self.outstanding_requests@[id] is SuperBlockReq) <==> in_flight_sb_id.contains(id)
            &&& (self.outstanding_requests@[id] is CacheLoadReq
                || self.outstanding_requests@[id] is JournalCacheWriteReq
                || self.outstanding_requests@[id] is StoreWriteReq)
                <==> state.outstanding_cache_reqs.dom().contains(id)
        }
    }

    closed spec fn outstanding_requests_wf_map(outstanding: Map<ID, OutstandingReqInfo>, cache: FracCacheImpl) -> bool
    {
        forall |id| #[trigger] outstanding.contains_key(id) ==> {
            match outstanding[id] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& cache.entry_fetched(&read_addr)
                    &&& cache.valid_load_handle(&read_addr, load_handle)
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    &&& cache.entry_fetched(&write_addr)
                    &&& cache.valid_writeback_handle(&write_addr, handle)
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
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
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

    closed spec fn no_outstanding_store_write(self) -> bool
    {
        forall |id| #[trigger] self.outstanding_requests@.contains_key(id)
            ==> !(self.outstanding_requests@[id] is StoreWriteReq)
    }

    proof fn outstanding_requests_wf_map_preserved_by_cache(
        outstanding: Map<ID, OutstandingReqInfo>,
        old_cache: FracCacheImpl,
        new_cache: FracCacheImpl,
    )
    requires
        old_cache.wf(),
        new_cache.wf(),
        Self::outstanding_requests_wf_map(outstanding, old_cache),
        new_cache.valid_load_handles_preserved(old_cache),
        new_cache.valid_writeback_handles_preserved(old_cache),
    ensures
        Self::outstanding_requests_wf_map(outstanding, new_cache),
    {
        assert forall |id| #[trigger] outstanding.contains_key(id) implies {
            match outstanding[id] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& new_cache.entry_fetched(&read_addr)
                    &&& new_cache.valid_load_handle(&read_addr, load_handle)
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    &&& new_cache.entry_fetched(&write_addr)
                    &&& new_cache.valid_writeback_handle(&write_addr, handle)
                },
                OutstandingReqInfo::SuperBlockReq{} => true,
            }
        } by {
            assert(Self::outstanding_requests_wf_map(outstanding, old_cache));
            match outstanding[id] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    assert(old_cache.entry_fetched(&read_addr));
                    assert(old_cache.valid_load_handle(&read_addr, load_handle));
                    assert(new_cache.valid_load_handles_preserved(old_cache));
                    assert(new_cache.entry_fetched(&read_addr) && new_cache.valid_load_handle(&read_addr, load_handle));
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    assert(old_cache.entry_fetched(&write_addr));
                    assert(old_cache.valid_writeback_handle(&write_addr, handle));
                    assert(new_cache.valid_writeback_handles_preserved(old_cache));
                    assert(new_cache.valid_writeback_handle(&write_addr, handle));
                    FracCacheImpl::valid_writeback_handle_model_entry(&new_cache, &write_addr, handle);
                    FracCacheImpl::entry_fetched_from_view(&new_cache, &write_addr);
                    assert(new_cache.entry_fetched(&write_addr));
                },
                OutstandingReqInfo::SuperBlockReq{} => {}
            }
        };
    }

    proof fn outstanding_requests_wf_map_insert_journal(
        outstanding: Map<ID, OutstandingReqInfo>,
        cache: FracCacheImpl,
        req_id: ID,
        write_addr: IAddress,
        handle: WritebackHandle,
    )
    requires
        cache.wf(),
        Self::outstanding_requests_wf_map(outstanding, cache),
        cache.valid_writeback_handle(&write_addr, handle),
    ensures
        Self::outstanding_requests_wf_map(
            outstanding.insert(req_id, OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}),
            cache,
        ),
    {
        let ghost inserted_req = OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle};
        assert forall |id2| #[trigger] outstanding.insert(req_id, inserted_req).contains_key(id2) implies {
            match outstanding.insert(req_id, inserted_req)[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& cache.entry_fetched(&read_addr)
                    &&& cache.valid_load_handle(&read_addr, load_handle)
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    &&& cache.entry_fetched(&write_addr)
                    &&& cache.valid_writeback_handle(&write_addr, handle)
                },
                OutstandingReqInfo::SuperBlockReq{} => true,
            }
        } by {
            assert(Self::outstanding_requests_wf_map(outstanding, cache));
            if id2 == req_id {
                assert(outstanding.insert(req_id, inserted_req)[id2] == inserted_req);
                assert(cache.valid_writeback_handle(&write_addr, handle));
                FracCacheImpl::valid_writeback_handle_model_entry(&cache, &write_addr, handle);
                FracCacheImpl::entry_fetched_from_view(&cache, &write_addr);
                assert(cache.entry_fetched(&write_addr));
            } else {
                vstd::map::axiom_map_insert_domain(outstanding, req_id, inserted_req);
                assert(outstanding.insert(req_id, inserted_req).dom() == outstanding.dom().insert(req_id));
                assert(outstanding.dom().insert(req_id).contains(id2));
                vstd::set::axiom_set_insert_different(outstanding.dom(), id2, req_id);
                assert(outstanding.dom().contains(id2));
                assert(outstanding.contains_key(id2));

                vstd::map::axiom_map_insert_different(outstanding, id2, req_id, inserted_req);
                assert(outstanding.insert(req_id, inserted_req)[id2] == outstanding[id2]);
                match outstanding[id2] {
                    OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                        assert(cache.entry_fetched(&read_addr));
                        assert(cache.valid_load_handle(&read_addr, load_handle));
                    },
                    OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                    | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                        assert(cache.entry_fetched(&write_addr));
                        assert(cache.valid_writeback_handle(&write_addr, handle));
                    },
                    OutstandingReqInfo::SuperBlockReq{} => {}
                }
            }
        };
    }

    proof fn outstanding_requests_wf_map_insert_store(
        outstanding: Map<ID, OutstandingReqInfo>,
        cache: FracCacheImpl,
        req_id: ID,
        write_addr: IAddress,
        handle: WritebackHandle,
    )
    requires
        cache.wf(),
        Self::outstanding_requests_wf_map(outstanding, cache),
        cache.valid_writeback_handle(&write_addr, handle),
    ensures
        Self::outstanding_requests_wf_map(
            outstanding.insert(req_id, OutstandingReqInfo::StoreWriteReq{write_addr, handle}),
            cache,
        ),
    {
        let ghost inserted_req = OutstandingReqInfo::StoreWriteReq{write_addr, handle};
        assert forall |id2| #[trigger] outstanding.insert(req_id, inserted_req).contains_key(id2) implies {
            match outstanding.insert(req_id, inserted_req)[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& cache.entry_fetched(&read_addr)
                    &&& cache.valid_load_handle(&read_addr, load_handle)
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    &&& cache.entry_fetched(&write_addr)
                    &&& cache.valid_writeback_handle(&write_addr, handle)
                },
                OutstandingReqInfo::SuperBlockReq{} => true,
            }
        } by {
            assert(Self::outstanding_requests_wf_map(outstanding, cache));
            if id2 == req_id {
                assert(outstanding.insert(req_id, inserted_req)[id2] == inserted_req);
                assert(cache.valid_writeback_handle(&write_addr, handle));
                FracCacheImpl::valid_writeback_handle_model_entry(&cache, &write_addr, handle);
                FracCacheImpl::entry_fetched_from_view(&cache, &write_addr);
                assert(cache.entry_fetched(&write_addr));
            } else {
                vstd::map::axiom_map_insert_domain(outstanding, req_id, inserted_req);
                assert(outstanding.insert(req_id, inserted_req).dom() == outstanding.dom().insert(req_id));
                assert(outstanding.dom().insert(req_id).contains(id2));
                vstd::set::axiom_set_insert_different(outstanding.dom(), id2, req_id);
                assert(outstanding.dom().contains(id2));
                assert(outstanding.contains_key(id2));

                vstd::map::axiom_map_insert_different(outstanding, id2, req_id, inserted_req);
                assert(outstanding.insert(req_id, inserted_req)[id2] == outstanding[id2]);
                match outstanding[id2] {
                    OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                        assert(cache.entry_fetched(&read_addr));
                        assert(cache.valid_load_handle(&read_addr, load_handle));
                    },
                    OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                    | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                        assert(cache.entry_fetched(&write_addr));
                        assert(cache.valid_writeback_handle(&write_addr, handle));
                    },
                    OutstandingReqInfo::SuperBlockReq{} => {}
                }
            }
        };
    }

    proof fn outstanding_requests_wf_map_insert_load(
        outstanding: Map<ID, OutstandingReqInfo>,
        cache: FracCacheImpl,
        req_id: ID,
        read_addr: IAddress,
        load_handle: MutHandle,
    )
    requires
        cache.wf(),
        Self::outstanding_requests_wf_map(outstanding, cache),
        cache.valid_load_handle(&read_addr, load_handle),
        cache.entry_fetched(&read_addr),
    ensures
        Self::outstanding_requests_wf_map(
            outstanding.insert(req_id, OutstandingReqInfo::CacheLoadReq{read_addr, load_handle}),
            cache,
        ),
    {
        let ghost inserted_req = OutstandingReqInfo::CacheLoadReq{read_addr, load_handle};
        assert forall |id2| #[trigger] outstanding.insert(req_id, inserted_req).contains_key(id2) implies {
            match outstanding.insert(req_id, inserted_req)[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& cache.entry_fetched(&read_addr)
                    &&& cache.valid_load_handle(&read_addr, load_handle)
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    &&& cache.entry_fetched(&write_addr)
                    &&& cache.valid_writeback_handle(&write_addr, handle)
                },
                OutstandingReqInfo::SuperBlockReq{} => true,
            }
        } by {
            assert(Self::outstanding_requests_wf_map(outstanding, cache));
            if id2 == req_id {
                assert(outstanding.insert(req_id, inserted_req)[id2] == inserted_req);
                assert(cache.valid_load_handle(&read_addr, load_handle));
                assert(cache.entry_fetched(&read_addr));
                FracCacheImpl::valid_load_handle_model_entry(&cache, &read_addr, load_handle);
            } else {
                vstd::map::axiom_map_insert_domain(outstanding, req_id, inserted_req);
                assert(outstanding.insert(req_id, inserted_req).dom() == outstanding.dom().insert(req_id));
                assert(outstanding.dom().insert(req_id).contains(id2));
                vstd::set::axiom_set_insert_different(outstanding.dom(), id2, req_id);
                assert(outstanding.dom().contains(id2));
                assert(outstanding.contains_key(id2));

                vstd::map::axiom_map_insert_different(outstanding, id2, req_id, inserted_req);
                assert(outstanding.insert(req_id, inserted_req)[id2] == outstanding[id2]);
                match outstanding[id2] {
                    OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                        assert(cache.entry_fetched(&read_addr));
                        assert(cache.valid_load_handle(&read_addr, load_handle));
                    },
                    OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                    | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                        assert(cache.entry_fetched(&write_addr));
                        assert(cache.valid_writeback_handle(&write_addr, handle));
                    },
                    OutstandingReqInfo::SuperBlockReq{} => {}
                }
            }
        };
    }

    proof fn outstanding_requests_wf_map_preserved_by_cache_loads_only(
        outstanding: Map<ID, OutstandingReqInfo>,
        old_cache: FracCacheImpl,
        new_cache: FracCacheImpl,
    )
    requires
        old_cache.wf(),
        new_cache.wf(),
        Self::outstanding_requests_wf_map(outstanding, old_cache),
        new_cache.valid_load_handles_preserved(old_cache),
        forall |id| #[trigger] outstanding.contains_key(id) ==> outstanding[id] is CacheLoadReq,
    ensures
        Self::outstanding_requests_wf_map(outstanding, new_cache),
    {
        assert forall |id| #[trigger] outstanding.contains_key(id) implies {
            match outstanding[id] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& new_cache.entry_fetched(&read_addr)
                    &&& new_cache.valid_load_handle(&read_addr, load_handle)
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    &&& new_cache.entry_fetched(&write_addr)
                    &&& new_cache.valid_writeback_handle(&write_addr, handle)
                },
                OutstandingReqInfo::SuperBlockReq{} => true,
            }
        } by {
            assert(outstanding[id] is CacheLoadReq);
            match outstanding[id] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    assert(old_cache.entry_fetched(&read_addr));
                    assert(old_cache.valid_load_handle(&read_addr, load_handle));
                    assert(new_cache.valid_load_handles_preserved(old_cache));
                    assert(new_cache.entry_fetched(&read_addr) && new_cache.valid_load_handle(&read_addr, load_handle));
                },
                _ => {
                    assert(false);
                }
            }
        };
    }

    proof fn outstanding_requests_match_cache_reqs_map_insert_load(
        outstanding: Map<ID, OutstandingReqInfo>,
        old_cache: FracCacheImpl,
        cache_reqs: Map<ID, Address>,
        req_id: ID,
        read_addr: IAddress,
        load_handle: MutHandle,
    )
    requires
        old_cache.wf(),
        !old_cache.entry_fetched(&read_addr),
        Self::outstanding_requests_wf_map(outstanding, old_cache),
        Self::outstanding_requests_match_cache_reqs_map(outstanding, cache_reqs),
        old_cache.valid_load_handles_preserved(old_cache),
        load_handle.inv(),
        cache_reqs.values() <= old_cache@.lookup_map.dom(),
    ensures
        Self::outstanding_requests_match_cache_reqs_map(
            outstanding.insert(req_id, OutstandingReqInfo::CacheLoadReq{read_addr, load_handle}),
            cache_reqs.insert(req_id, read_addr@),
        ),
    {
        let ghost inserted_req = OutstandingReqInfo::CacheLoadReq{read_addr, load_handle};
        assert(cache_reqs.is_injective());
        assert(cache_reqs.insert(req_id, read_addr@).is_injective()) by {
            assert forall |id1: ID, id2: ID| #![auto]
                cache_reqs.insert(req_id, read_addr@).contains_key(id1)
                && cache_reqs.insert(req_id, read_addr@).contains_key(id2)
                && cache_reqs.insert(req_id, read_addr@)[id1] == cache_reqs.insert(req_id, read_addr@)[id2]
                implies id1 == id2
            by {
                if id1 == req_id {
                    if id2 == req_id {
                    } else {
                        vstd::map::axiom_map_insert_different(cache_reqs, id2, req_id, read_addr@);
                        assert(cache_reqs.contains_key(id2));
                        assert(cache_reqs[id2] == read_addr@);
                        assert(old_cache@.lookup_map.dom().contains(read_addr@));
                        FracCacheImpl::entry_fetched_from_view(&old_cache, &read_addr);
                        assert(old_cache.entry_fetched(&read_addr));
                        assert(false);
                    }
                } else if id2 == req_id {
                    vstd::map::axiom_map_insert_different(cache_reqs, id1, req_id, read_addr@);
                    assert(cache_reqs.contains_key(id1));
                    assert(cache_reqs[id1] == read_addr@);
                    assert(old_cache@.lookup_map.dom().contains(read_addr@));
                    FracCacheImpl::entry_fetched_from_view(&old_cache, &read_addr);
                    assert(old_cache.entry_fetched(&read_addr));
                    assert(false);
                } else {
                    vstd::map::axiom_map_insert_different(cache_reqs, id1, req_id, read_addr@);
                    vstd::map::axiom_map_insert_different(cache_reqs, id2, req_id, read_addr@);
                    assert(cache_reqs.contains_key(id1));
                    assert(cache_reqs.contains_key(id2));
                    assert(cache_reqs[id1] == cache_reqs[id2]);
                    assert(id1 == id2);
                }
            }
        };
        assert forall |id2| #[trigger] outstanding.insert(req_id, inserted_req).contains_key(id2) implies {
            match outstanding.insert(req_id, inserted_req)[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& cache_reqs.insert(req_id, read_addr@).contains_key(id2)
                    &&& cache_reqs.insert(req_id, read_addr@)[id2] == read_addr@
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    &&& cache_reqs.insert(req_id, read_addr@).contains_key(id2)
                    &&& cache_reqs.insert(req_id, read_addr@)[id2] == write_addr@
                },
                OutstandingReqInfo::SuperBlockReq{} => {
                    !cache_reqs.insert(req_id, read_addr@).contains_key(id2)
                }
            }
        } by {
            if id2 == req_id {
                assert(outstanding.insert(req_id, inserted_req)[id2] == inserted_req);
                assert(cache_reqs.insert(req_id, read_addr@).contains_key(id2));
                assert(cache_reqs.insert(req_id, read_addr@)[id2] == read_addr@);
            } else {
                vstd::map::axiom_map_insert_domain(outstanding, req_id, inserted_req);
                assert(outstanding.insert(req_id, inserted_req).dom() == outstanding.dom().insert(req_id));
                assert(outstanding.dom().insert(req_id).contains(id2));
                vstd::set::axiom_set_insert_different(outstanding.dom(), id2, req_id);
                assert(outstanding.dom().contains(id2));
                assert(outstanding.contains_key(id2));
                vstd::map::axiom_map_insert_different(outstanding, id2, req_id, inserted_req);
                vstd::map::axiom_map_insert_different(cache_reqs, id2, req_id, read_addr@);
                assert(outstanding.insert(req_id, inserted_req)[id2] == outstanding[id2]);
                match outstanding[id2] {
                    OutstandingReqInfo::CacheLoadReq{read_addr: old_read_addr, load_handle: old_load_handle} => {
                        assert(cache_reqs.contains_key(id2));
                        assert(cache_reqs[id2] == old_read_addr@);
                    },
                    OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                    | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                        assert(cache_reqs.contains_key(id2));
                        assert(cache_reqs[id2] == write_addr@);
                    },
                    OutstandingReqInfo::SuperBlockReq{} => {
                        assert(!cache_reqs.contains_key(id2));
                    }
                }
            }
        };
    }

    proof fn outstanding_requests_match_cache_reqs_map_insert_journal(
        outstanding: Map<ID, OutstandingReqInfo>,
        cache_reqs: Map<ID, Address>,
        req_id: ID,
        write_addr: IAddress,
        handle: WritebackHandle,
    )
    requires
        Self::outstanding_requests_match_cache_reqs_map(outstanding, cache_reqs),
        cache_reqs.insert(req_id, write_addr@).is_injective(),
    ensures
        Self::outstanding_requests_match_cache_reqs_map(
            outstanding.insert(req_id, OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}),
            cache_reqs.insert(req_id, write_addr@),
        ),
    {
        let ghost inserted_req = OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle};
        assert(cache_reqs.is_injective());
        assert forall |id2| #[trigger] outstanding.insert(req_id, inserted_req).contains_key(id2) implies {
            match outstanding.insert(req_id, inserted_req)[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& cache_reqs.insert(req_id, write_addr@).contains_key(id2)
                    &&& cache_reqs.insert(req_id, write_addr@)[id2] == read_addr@
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr: wa2, handle: h2}
                | OutstandingReqInfo::StoreWriteReq{write_addr: wa2, handle: h2} => {
                    &&& cache_reqs.insert(req_id, write_addr@).contains_key(id2)
                    &&& cache_reqs.insert(req_id, write_addr@)[id2] == wa2@
                },
                OutstandingReqInfo::SuperBlockReq{} => {
                    !cache_reqs.insert(req_id, write_addr@).contains_key(id2)
                }
            }
        } by {
            if id2 == req_id {
                assert(outstanding.insert(req_id, inserted_req)[id2] == inserted_req);
                assert(cache_reqs.insert(req_id, write_addr@).contains_key(id2));
                assert(cache_reqs.insert(req_id, write_addr@)[id2] == write_addr@);
            } else {
                vstd::map::axiom_map_insert_domain(outstanding, req_id, inserted_req);
                assert(outstanding.insert(req_id, inserted_req).dom() == outstanding.dom().insert(req_id));
                assert(outstanding.dom().insert(req_id).contains(id2));
                vstd::set::axiom_set_insert_different(outstanding.dom(), id2, req_id);
                assert(outstanding.dom().contains(id2));
                assert(outstanding.contains_key(id2));
                vstd::map::axiom_map_insert_different(outstanding, id2, req_id, inserted_req);
                vstd::map::axiom_map_insert_different(cache_reqs, id2, req_id, write_addr@);
                assert(outstanding.insert(req_id, inserted_req)[id2] == outstanding[id2]);
                match outstanding[id2] {
                    OutstandingReqInfo::CacheLoadReq{read_addr: old_read_addr, load_handle: old_load_handle} => {
                        assert(cache_reqs.contains_key(id2));
                        assert(cache_reqs[id2] == old_read_addr@);
                    },
                    OutstandingReqInfo::JournalCacheWriteReq{write_addr: old_write_addr, handle: old_handle}
                    | OutstandingReqInfo::StoreWriteReq{write_addr: old_write_addr, handle: old_handle} => {
                        assert(cache_reqs.contains_key(id2));
                        assert(cache_reqs[id2] == old_write_addr@);
                    },
                    OutstandingReqInfo::SuperBlockReq{} => {
                        assert(!cache_reqs.contains_key(id2));
                    }
                }
            }
        };
    }

    proof fn outstanding_requests_match_cache_reqs_map_insert_store(
        outstanding: Map<ID, OutstandingReqInfo>,
        cache_reqs: Map<ID, Address>,
        req_id: ID,
        write_addr: IAddress,
        handle: WritebackHandle,
    )
    requires
        Self::outstanding_requests_match_cache_reqs_map(outstanding, cache_reqs),
        cache_reqs.insert(req_id, write_addr@).is_injective(),
    ensures
        Self::outstanding_requests_match_cache_reqs_map(
            outstanding.insert(req_id, OutstandingReqInfo::StoreWriteReq{write_addr, handle}),
            cache_reqs.insert(req_id, write_addr@),
        ),
    {
        let ghost inserted_req = OutstandingReqInfo::StoreWriteReq{write_addr, handle};
        assert(cache_reqs.is_injective());
        assert forall |id2| #[trigger] outstanding.insert(req_id, inserted_req).contains_key(id2) implies {
            match outstanding.insert(req_id, inserted_req)[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& cache_reqs.insert(req_id, write_addr@).contains_key(id2)
                    &&& cache_reqs.insert(req_id, write_addr@)[id2] == read_addr@
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr: wa2, handle: h2}
                | OutstandingReqInfo::StoreWriteReq{write_addr: wa2, handle: h2} => {
                    &&& cache_reqs.insert(req_id, write_addr@).contains_key(id2)
                    &&& cache_reqs.insert(req_id, write_addr@)[id2] == wa2@
                },
                OutstandingReqInfo::SuperBlockReq{} => {
                    !cache_reqs.insert(req_id, write_addr@).contains_key(id2)
                }
            }
        } by {
            if id2 == req_id {
                assert(outstanding.insert(req_id, inserted_req)[id2] == inserted_req);
                assert(cache_reqs.insert(req_id, write_addr@).contains_key(id2));
                assert(cache_reqs.insert(req_id, write_addr@)[id2] == write_addr@);
            } else {
                vstd::map::axiom_map_insert_domain(outstanding, req_id, inserted_req);
                assert(outstanding.insert(req_id, inserted_req).dom() == outstanding.dom().insert(req_id));
                assert(outstanding.dom().insert(req_id).contains(id2));
                vstd::set::axiom_set_insert_different(outstanding.dom(), id2, req_id);
                assert(outstanding.dom().contains(id2));
                assert(outstanding.contains_key(id2));
                vstd::map::axiom_map_insert_different(outstanding, id2, req_id, inserted_req);
                vstd::map::axiom_map_insert_different(cache_reqs, id2, req_id, write_addr@);
                assert(outstanding.insert(req_id, inserted_req)[id2] == outstanding[id2]);
                match outstanding[id2] {
                    OutstandingReqInfo::CacheLoadReq{read_addr: old_read_addr, load_handle: old_load_handle} => {
                        assert(cache_reqs.contains_key(id2));
                        assert(cache_reqs[id2] == old_read_addr@);
                    },
                    OutstandingReqInfo::JournalCacheWriteReq{write_addr: old_write_addr, handle: old_handle}
                    | OutstandingReqInfo::StoreWriteReq{write_addr: old_write_addr, handle: old_handle} => {
                        assert(cache_reqs.contains_key(id2));
                        assert(cache_reqs[id2] == old_write_addr@);
                    },
                    OutstandingReqInfo::SuperBlockReq{} => {
                        assert(!cache_reqs.contains_key(id2));
                    }
                }
            }
        };
    }

    proof fn outstanding_requests_wf_map_insert_superblock(
        outstanding: Map<ID, OutstandingReqInfo>,
        cache: FracCacheImpl,
        req_id: ID,
    )
    requires
        cache.wf(),
        Self::outstanding_requests_wf_map(outstanding, cache),
    ensures
        Self::outstanding_requests_wf_map(
            outstanding.insert(req_id, OutstandingReqInfo::SuperBlockReq{}),
            cache,
        ),
    {
        let ghost inserted_req = OutstandingReqInfo::SuperBlockReq{};
        assert forall |id2| #[trigger] outstanding.insert(req_id, inserted_req).contains_key(id2) implies {
            match outstanding.insert(req_id, inserted_req)[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& cache.entry_fetched(&read_addr)
                    &&& cache.valid_load_handle(&read_addr, load_handle)
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    &&& cache.entry_fetched(&write_addr)
                    &&& cache.valid_writeback_handle(&write_addr, handle)
                },
                OutstandingReqInfo::SuperBlockReq{} => true,
            }
        } by {
            if id2 != req_id {
                vstd::map::axiom_map_insert_domain(outstanding, req_id, inserted_req);
                assert(outstanding.insert(req_id, inserted_req).dom() == outstanding.dom().insert(req_id));
                assert(outstanding.dom().insert(req_id).contains(id2));
                vstd::set::axiom_set_insert_different(outstanding.dom(), id2, req_id);
                assert(outstanding.dom().contains(id2));
                assert(outstanding.contains_key(id2));
                vstd::map::axiom_map_insert_different(outstanding, id2, req_id, inserted_req);
                assert(outstanding.insert(req_id, inserted_req)[id2] == outstanding[id2]);
                assert(Self::outstanding_requests_wf_map(outstanding, cache));
            }
        };
    }

    proof fn outstanding_requests_match_cache_reqs_map_insert_superblock(
        outstanding: Map<ID, OutstandingReqInfo>,
        cache_reqs: Map<ID, Address>,
        req_id: ID,
    )
    requires
        Self::outstanding_requests_match_cache_reqs_map(outstanding, cache_reqs),
        !cache_reqs.contains_key(req_id),
    ensures
        Self::outstanding_requests_match_cache_reqs_map(
            outstanding.insert(req_id, OutstandingReqInfo::SuperBlockReq{}),
            cache_reqs,
        ),
    {
        let ghost inserted_req = OutstandingReqInfo::SuperBlockReq{};
        assert(cache_reqs.is_injective());
        assert forall |id2| #[trigger] outstanding.insert(req_id, inserted_req).contains_key(id2) implies {
            match outstanding.insert(req_id, inserted_req)[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& cache_reqs.contains_key(id2)
                    &&& cache_reqs[id2] == read_addr@
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    &&& cache_reqs.contains_key(id2)
                    &&& cache_reqs[id2] == write_addr@
                },
                OutstandingReqInfo::SuperBlockReq{} => {
                    !cache_reqs.contains_key(id2)
                }
            }
        } by {
            if id2 == req_id {
                assert(outstanding.insert(req_id, inserted_req)[id2] == inserted_req);
                assert(!cache_reqs.contains_key(id2));
            } else {
                vstd::map::axiom_map_insert_domain(outstanding, req_id, inserted_req);
                assert(outstanding.insert(req_id, inserted_req).dom() == outstanding.dom().insert(req_id));
                assert(outstanding.dom().insert(req_id).contains(id2));
                vstd::set::axiom_set_insert_different(outstanding.dom(), id2, req_id);
                assert(outstanding.dom().contains(id2));
                assert(outstanding.contains_key(id2));
                vstd::map::axiom_map_insert_different(outstanding, id2, req_id, inserted_req);
                assert(outstanding.insert(req_id, inserted_req)[id2] == outstanding[id2]);
                match outstanding[id2] {
                    OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                        assert(cache_reqs.contains_key(id2));
                        assert(cache_reqs[id2] == read_addr@);
                    },
                    OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                    | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                        assert(cache_reqs.contains_key(id2));
                        assert(cache_reqs[id2] == write_addr@);
                    },
                    OutstandingReqInfo::SuperBlockReq{} => {
                        assert(!cache_reqs.contains_key(id2));
                    }
                }
            }
        };
    }

    proof fn outstanding_requests_wf_map_remove_superblock(
        outstanding: Map<ID, OutstandingReqInfo>,
        cache: FracCacheImpl,
        req_id: ID,
    )
    requires
        Self::outstanding_requests_wf_map(outstanding, cache),
        outstanding.contains_key(req_id),
        outstanding[req_id] is SuperBlockReq,
    ensures
        Self::outstanding_requests_wf_map(outstanding.remove(req_id), cache),
    {
        assert forall |id2| #[trigger] outstanding.remove(req_id).contains_key(id2) implies {
            match outstanding.remove(req_id)[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& cache.entry_fetched(&read_addr)
                    &&& cache.valid_load_handle(&read_addr, load_handle)
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    &&& cache.entry_fetched(&write_addr)
                    &&& cache.valid_writeback_handle(&write_addr, handle)
                },
                OutstandingReqInfo::SuperBlockReq{} => true,
            }
        } by {
            assert(id2 != req_id) by {
                if id2 == req_id {
                    vstd::map::axiom_map_remove_domain(outstanding, req_id);
                    assert(outstanding.remove(req_id).dom().contains(id2));
                    assert(outstanding.remove(req_id).dom() == outstanding.dom().remove(req_id));
                    vstd::set::axiom_set_remove_same(outstanding.dom(), req_id);
                    assert(!outstanding.dom().remove(req_id).contains(req_id));
                    assert(false);
                }
            };
            vstd::map::axiom_map_remove_different(outstanding, id2, req_id);
            assert(outstanding.remove(req_id)[id2] == outstanding[id2]);
            assert(Self::outstanding_requests_wf_map(outstanding, cache));
        };
    }

    proof fn outstanding_requests_match_cache_reqs_map_remove_superblock(
        outstanding: Map<ID, OutstandingReqInfo>,
        cache_reqs: Map<ID, Address>,
        req_id: ID,
    )
    requires
        Self::outstanding_requests_match_cache_reqs_map(outstanding, cache_reqs),
        outstanding.contains_key(req_id),
        outstanding[req_id] is SuperBlockReq,
        !cache_reqs.contains_key(req_id),
    ensures
        Self::outstanding_requests_match_cache_reqs_map(outstanding.remove(req_id), cache_reqs),
    {
        assert(cache_reqs.is_injective());
        assert forall |id2| #[trigger] outstanding.remove(req_id).contains_key(id2) implies {
            match outstanding.remove(req_id)[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& cache_reqs.contains_key(id2)
                    &&& cache_reqs[id2] == read_addr@
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    &&& cache_reqs.contains_key(id2)
                    &&& cache_reqs[id2] == write_addr@
                },
                OutstandingReqInfo::SuperBlockReq{} => {
                    !cache_reqs.contains_key(id2)
                }
            }
        } by {
            assert(id2 != req_id) by {
                if id2 == req_id {
                    vstd::map::axiom_map_remove_domain(outstanding, req_id);
                    assert(outstanding.remove(req_id).dom().contains(id2));
                    assert(outstanding.remove(req_id).dom() == outstanding.dom().remove(req_id));
                    vstd::set::axiom_set_remove_same(outstanding.dom(), req_id);
                    assert(!outstanding.dom().remove(req_id).contains(req_id));
                    assert(false);
                }
            };
            vstd::map::axiom_map_remove_different(outstanding, id2, req_id);
            assert(outstanding.remove(req_id)[id2] == outstanding[id2]);
            assert(Self::outstanding_requests_match_cache_reqs_map(outstanding, cache_reqs));
        };
    }

    proof fn outstanding_requests_wf_map_remove_journal_after_complete(
        outstanding: Map<ID, OutstandingReqInfo>,
        old_cache: FracCacheImpl,
        new_cache: FracCacheImpl,
        cache_reqs: Map<ID, Address>,
        id: ID,
        write_addr: IAddress,
    )
    requires
        old_cache.wf(),
        new_cache.wf(),
        outstanding.contains_key(id),
        outstanding[id] is JournalCacheWriteReq,
        Self::outstanding_requests_wf_map(outstanding, old_cache),
        Self::outstanding_requests_match_cache_reqs_map(outstanding, cache_reqs),
        cache_reqs.contains_key(id),
        cache_reqs[id] == write_addr@,
        new_cache.valid_load_handles_preserved(old_cache),
        new_cache.valid_writeback_handles_preserved_except(old_cache, write_addr),
    ensures
        Self::outstanding_requests_wf_map(outstanding.remove(id), new_cache),
    {
        assert forall |id2| #[trigger] outstanding.remove(id).contains_key(id2) implies {
            match outstanding.remove(id)[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& new_cache.entry_fetched(&read_addr)
                    &&& new_cache.valid_load_handle(&read_addr, load_handle)
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr: wa2, handle: h2}
                | OutstandingReqInfo::StoreWriteReq{write_addr: wa2, handle: h2} => {
                    &&& new_cache.entry_fetched(&wa2)
                    &&& new_cache.valid_writeback_handle(&wa2, h2)
                },
                OutstandingReqInfo::SuperBlockReq{} => true,
            }
        } by {
            assert(id2 != id) by {
                if id2 == id {
                    vstd::map::axiom_map_remove_domain(outstanding, id);
                    assert(outstanding.remove(id).dom().contains(id2));
                    assert(outstanding.remove(id).dom() == outstanding.dom().remove(id));
                    vstd::set::axiom_set_remove_same(outstanding.dom(), id);
                    assert(!outstanding.dom().remove(id).contains(id));
                    assert(false);
                }
            };

            vstd::map::axiom_map_remove_different(outstanding, id2, id);
            assert(outstanding.remove(id)[id2] == outstanding[id2]);

            vstd::map::axiom_map_remove_domain(outstanding, id);
            assert(outstanding.remove(id).dom().contains(id2));
            assert(outstanding.remove(id).dom() == outstanding.dom().remove(id));
            vstd::set::axiom_set_remove_different(outstanding.dom(), id2, id);
            assert(outstanding.dom().contains(id2));
            assert(outstanding.contains_key(id2));

            assert(Self::outstanding_requests_wf_map(outstanding, old_cache));
            match outstanding[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    assert(old_cache.entry_fetched(&read_addr));
                    assert(old_cache.valid_load_handle(&read_addr, load_handle));
                    assert(new_cache.valid_load_handles_preserved(old_cache));
                    assert(new_cache.entry_fetched(&read_addr) && new_cache.valid_load_handle(&read_addr, load_handle));
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr: wa2, handle: h2}
                | OutstandingReqInfo::StoreWriteReq{write_addr: wa2, handle: h2} => {
                    assert(old_cache.entry_fetched(&wa2));
                    assert(old_cache.valid_writeback_handle(&wa2, h2));

                    assert(cache_reqs.contains_key(id2));
                    assert(cache_reqs[id2] == wa2@);
                    assert(cache_reqs.contains_key(id));
                    assert(cache_reqs[id] == write_addr@);
                    assert(cache_reqs.is_injective());
                    assert(wa2@ != write_addr@) by {
                        if wa2@ == write_addr@ {
                            assert(cache_reqs.contains_pair(id2, wa2@));
                            assert(cache_reqs.contains_pair(id, wa2@));
                            assert(id2 == id);
                            assert(false);
                        }
                    };
                    assert(wa2 != write_addr);

                    assert(new_cache.valid_writeback_handles_preserved_except(old_cache, write_addr));
                    assert(new_cache.valid_writeback_handle(&wa2, h2));
                    FracCacheImpl::valid_writeback_handle_model_entry(&new_cache, &wa2, h2);
                    FracCacheImpl::entry_fetched_from_view(&new_cache, &wa2);
                    assert(new_cache.entry_fetched(&wa2));
                },
                OutstandingReqInfo::SuperBlockReq{} => {}
            }
        };
    }

    proof fn outstanding_requests_wf_map_remove_store_after_complete(
        outstanding: Map<ID, OutstandingReqInfo>,
        old_cache: FracCacheImpl,
        new_cache: FracCacheImpl,
        cache_reqs: Map<ID, Address>,
        id: ID,
        write_addr: IAddress,
    )
    requires
        old_cache.wf(),
        new_cache.wf(),
        outstanding.contains_key(id),
        outstanding[id] is StoreWriteReq,
        Self::outstanding_requests_wf_map(outstanding, old_cache),
        Self::outstanding_requests_match_cache_reqs_map(outstanding, cache_reqs),
        cache_reqs.contains_key(id),
        cache_reqs[id] == write_addr@,
        new_cache.valid_load_handles_preserved(old_cache),
        new_cache.valid_writeback_handles_preserved_except(old_cache, write_addr),
    ensures
        Self::outstanding_requests_wf_map(outstanding.remove(id), new_cache),
    {
        assert forall |id2| #[trigger] outstanding.remove(id).contains_key(id2) implies {
            match outstanding.remove(id)[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& new_cache.entry_fetched(&read_addr)
                    &&& new_cache.valid_load_handle(&read_addr, load_handle)
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr: wa2, handle: h2}
                | OutstandingReqInfo::StoreWriteReq{write_addr: wa2, handle: h2} => {
                    &&& new_cache.entry_fetched(&wa2)
                    &&& new_cache.valid_writeback_handle(&wa2, h2)
                },
                OutstandingReqInfo::SuperBlockReq{} => true,
            }
        } by {
            assert(id2 != id) by {
                if id2 == id {
                    vstd::map::axiom_map_remove_domain(outstanding, id);
                    assert(outstanding.remove(id).dom().contains(id2));
                    assert(outstanding.remove(id).dom() == outstanding.dom().remove(id));
                    vstd::set::axiom_set_remove_same(outstanding.dom(), id);
                    assert(!outstanding.dom().remove(id).contains(id));
                    assert(false);
                }
            };

            vstd::map::axiom_map_remove_different(outstanding, id2, id);
            assert(outstanding.remove(id)[id2] == outstanding[id2]);

            vstd::map::axiom_map_remove_domain(outstanding, id);
            assert(outstanding.remove(id).dom().contains(id2));
            assert(outstanding.remove(id).dom() == outstanding.dom().remove(id));
            vstd::set::axiom_set_remove_different(outstanding.dom(), id2, id);
            assert(outstanding.dom().contains(id2));
            assert(outstanding.contains_key(id2));

            assert(Self::outstanding_requests_wf_map(outstanding, old_cache));
            match outstanding[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    assert(old_cache.entry_fetched(&read_addr));
                    assert(old_cache.valid_load_handle(&read_addr, load_handle));
                    assert(new_cache.valid_load_handles_preserved(old_cache));
                    assert(new_cache.entry_fetched(&read_addr) && new_cache.valid_load_handle(&read_addr, load_handle));
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr: wa2, handle: h2}
                | OutstandingReqInfo::StoreWriteReq{write_addr: wa2, handle: h2} => {
                    assert(old_cache.entry_fetched(&wa2));
                    assert(old_cache.valid_writeback_handle(&wa2, h2));

                    assert(cache_reqs.contains_key(id2));
                    assert(cache_reqs[id2] == wa2@);
                    assert(cache_reqs.contains_key(id));
                    assert(cache_reqs[id] == write_addr@);
                    assert(cache_reqs.is_injective());
                    assert(wa2@ != write_addr@) by {
                        if wa2@ == write_addr@ {
                            assert(cache_reqs.contains_pair(id2, wa2@));
                            assert(cache_reqs.contains_pair(id, wa2@));
                            assert(id2 == id);
                            assert(false);
                        }
                    };
                    assert(wa2 != write_addr);

                    assert(new_cache.valid_writeback_handles_preserved_except(old_cache, write_addr));
                    assert(new_cache.valid_writeback_handle(&wa2, h2));
                    FracCacheImpl::valid_writeback_handle_model_entry(&new_cache, &wa2, h2);
                    FracCacheImpl::entry_fetched_from_view(&new_cache, &wa2);
                    assert(new_cache.entry_fetched(&wa2));
                },
                OutstandingReqInfo::SuperBlockReq{} => {}
            }
        };
    }

    proof fn outstanding_requests_wf_map_remove_load_after_complete(
        outstanding: Map<ID, OutstandingReqInfo>,
        old_cache: FracCacheImpl,
        new_cache: FracCacheImpl,
        cache_reqs: Map<ID, Address>,
        id: ID,
        read_addr: IAddress,
    )
    requires
        old_cache.wf(),
        new_cache.wf(),
        outstanding.contains_key(id),
        outstanding[id] is CacheLoadReq,
        Self::outstanding_requests_wf_map(outstanding, old_cache),
        Self::outstanding_requests_match_cache_reqs_map(outstanding, cache_reqs),
        cache_reqs.contains_key(id),
        cache_reqs[id] == read_addr@,
        new_cache.valid_load_handles_preserved_except(old_cache, read_addr),
        new_cache.valid_writeback_handles_preserved(old_cache),
    ensures
        Self::outstanding_requests_wf_map(outstanding.remove(id), new_cache),
    {
        assert forall |id2| #[trigger] outstanding.remove(id).contains_key(id2) implies {
            match outstanding.remove(id)[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr: ra2, load_handle: h2} => {
                    &&& new_cache.entry_fetched(&ra2)
                    &&& new_cache.valid_load_handle(&ra2, h2)
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    &&& new_cache.entry_fetched(&write_addr)
                    &&& new_cache.valid_writeback_handle(&write_addr, handle)
                },
                OutstandingReqInfo::SuperBlockReq{} => true,
            }
        } by {
            assert(id2 != id) by {
                if id2 == id {
                    vstd::map::axiom_map_remove_domain(outstanding, id);
                    assert(outstanding.remove(id).dom().contains(id2));
                    assert(outstanding.remove(id).dom() == outstanding.dom().remove(id));
                    vstd::set::axiom_set_remove_same(outstanding.dom(), id);
                    assert(!outstanding.dom().remove(id).contains(id));
                    assert(false);
                }
            };
            vstd::map::axiom_map_remove_different(outstanding, id2, id);
            assert(outstanding.remove(id)[id2] == outstanding[id2]);

            vstd::map::axiom_map_remove_domain(outstanding, id);
            assert(outstanding.remove(id).dom().contains(id2));
            assert(outstanding.remove(id).dom() == outstanding.dom().remove(id));
            vstd::set::axiom_set_remove_different(outstanding.dom(), id2, id);
            assert(outstanding.dom().contains(id2));
            assert(outstanding.contains_key(id2));

            assert(Self::outstanding_requests_wf_map(outstanding, old_cache));
            match outstanding[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr: ra2, load_handle: h2} => {
                    assert(old_cache.entry_fetched(&ra2));
                    assert(old_cache.valid_load_handle(&ra2, h2));

                    assert(cache_reqs.contains_key(id2));
                    assert(cache_reqs[id2] == ra2@);
                    assert(cache_reqs.contains_key(id));
                    assert(cache_reqs[id] == read_addr@);
                    assert(cache_reqs.is_injective());
                    assert(ra2@ != read_addr@) by {
                        if ra2@ == read_addr@ {
                            assert(cache_reqs.contains_pair(id2, ra2@));
                            assert(cache_reqs.contains_pair(id, ra2@));
                            assert(id2 == id);
                            assert(false);
                        }
                    };
                    assert(ra2 != read_addr);

                    assert(new_cache.valid_load_handles_preserved_except(old_cache, read_addr));
                    assert(new_cache.valid_load_handle(&ra2, h2));
                    FracCacheImpl::entry_fetched_from_view(&new_cache, &ra2);
                    assert(new_cache.entry_fetched(&ra2));
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    assert(old_cache.entry_fetched(&write_addr));
                    assert(old_cache.valid_writeback_handle(&write_addr, handle));
                    assert(new_cache.valid_writeback_handles_preserved(old_cache));
                    assert(new_cache.valid_writeback_handle(&write_addr, handle));
                    FracCacheImpl::valid_writeback_handle_model_entry(&new_cache, &write_addr, handle);
                    FracCacheImpl::entry_fetched_from_view(&new_cache, &write_addr);
                    assert(new_cache.entry_fetched(&write_addr));
                },
                OutstandingReqInfo::SuperBlockReq{} => {}
            }
        };
    }

    proof fn outstanding_requests_match_cache_reqs_map_remove_load(
        outstanding: Map<ID, OutstandingReqInfo>,
        cache_reqs: Map<ID, Address>,
        id: ID,
        read_addr: IAddress,
    )
    requires
        Self::outstanding_requests_match_cache_reqs_map(outstanding, cache_reqs),
        outstanding.contains_key(id),
        outstanding[id] is CacheLoadReq,
        cache_reqs.contains_key(id),
        cache_reqs[id] == read_addr@,
    ensures
        Self::outstanding_requests_match_cache_reqs_map(
            outstanding.remove(id),
            cache_reqs.remove(id),
        ),
    {
        assert(cache_reqs.is_injective());
        assert(cache_reqs.remove(id).is_injective()) by {
            assert forall |id1: ID, id2: ID| #![auto]
                cache_reqs.remove(id).contains_key(id1)
                && cache_reqs.remove(id).contains_key(id2)
                && cache_reqs.remove(id)[id1] == cache_reqs.remove(id)[id2]
                implies id1 == id2 by {
                vstd::map::axiom_map_remove_different(cache_reqs, id1, id);
                vstd::map::axiom_map_remove_different(cache_reqs, id2, id);
                assert(cache_reqs.contains_key(id1));
                assert(cache_reqs.contains_key(id2));
                assert(cache_reqs[id1] == cache_reqs[id2]);
                assert(id1 == id2);
            };
        }
        assert forall |id2| #[trigger] outstanding.remove(id).contains_key(id2) implies {
            match outstanding.remove(id)[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr: ra2, load_handle: h2} => {
                    &&& cache_reqs.remove(id).contains_key(id2)
                    &&& cache_reqs.remove(id)[id2] == ra2@
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    &&& cache_reqs.remove(id).contains_key(id2)
                    &&& cache_reqs.remove(id)[id2] == write_addr@
                },
                OutstandingReqInfo::SuperBlockReq{} => {
                    !cache_reqs.remove(id).contains_key(id2)
                }
            }
        } by {
            assert(id2 != id) by {
                if id2 == id {
                    vstd::map::axiom_map_remove_domain(outstanding, id);
                    assert(outstanding.remove(id).dom().contains(id2));
                    assert(outstanding.remove(id).dom() == outstanding.dom().remove(id));
                    vstd::set::axiom_set_remove_same(outstanding.dom(), id);
                    assert(!outstanding.dom().remove(id).contains(id));
                    assert(false);
                }
            };
            vstd::map::axiom_map_remove_different(outstanding, id2, id);
            vstd::map::axiom_map_remove_different(cache_reqs, id2, id);
            assert(outstanding.remove(id)[id2] == outstanding[id2]);
            assert(Self::outstanding_requests_match_cache_reqs_map(outstanding, cache_reqs));
            match outstanding[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr: ra2, load_handle: h2} => {
                    assert(cache_reqs.contains_key(id2));
                    vstd::map::axiom_map_remove_domain(cache_reqs, id);
                    assert(cache_reqs.remove(id).dom() == cache_reqs.dom().remove(id));
                    vstd::set::axiom_set_remove_different(cache_reqs.dom(), id2, id);
                    assert(cache_reqs.remove(id).contains_key(id2));
                    assert(cache_reqs.remove(id)[id2] == cache_reqs[id2]);
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    assert(cache_reqs.contains_key(id2));
                    vstd::map::axiom_map_remove_domain(cache_reqs, id);
                    assert(cache_reqs.remove(id).dom() == cache_reqs.dom().remove(id));
                    vstd::set::axiom_set_remove_different(cache_reqs.dom(), id2, id);
                    assert(cache_reqs.remove(id).contains_key(id2));
                    assert(cache_reqs.remove(id)[id2] == cache_reqs[id2]);
                },
                OutstandingReqInfo::SuperBlockReq{} => {
                    assert(!cache_reqs.contains_key(id2));
                    vstd::map::axiom_map_remove_domain(cache_reqs, id);
                    assert(cache_reqs.remove(id).dom() == cache_reqs.dom().remove(id));
                    vstd::set::axiom_set_remove_different(cache_reqs.dom(), id2, id);
                    assert(!cache_reqs.remove(id).contains_key(id2));
                }
            }
        };
    }

    proof fn outstanding_requests_match_cache_reqs_map_remove_write(
        outstanding: Map<ID, OutstandingReqInfo>,
        cache_reqs: Map<ID, Address>,
        id: ID,
        write_addr: IAddress,
    )
    requires
        Self::outstanding_requests_match_cache_reqs_map(outstanding, cache_reqs),
        outstanding.contains_key(id),
        (outstanding[id] is JournalCacheWriteReq || outstanding[id] is StoreWriteReq),
        cache_reqs.contains_key(id),
        cache_reqs[id] == write_addr@,
    ensures
        Self::outstanding_requests_match_cache_reqs_map(
            outstanding.remove(id),
            cache_reqs.remove(id),
        ),
    {
        assert(cache_reqs.is_injective());
        assert(cache_reqs.remove(id).is_injective()) by {
            assert forall |id1: ID, id2: ID| #![auto]
                cache_reqs.remove(id).contains_key(id1)
                && cache_reqs.remove(id).contains_key(id2)
                && cache_reqs.remove(id)[id1] == cache_reqs.remove(id)[id2]
                implies id1 == id2 by {
                vstd::map::axiom_map_remove_different(cache_reqs, id1, id);
                vstd::map::axiom_map_remove_different(cache_reqs, id2, id);
                assert(cache_reqs.contains_key(id1));
                assert(cache_reqs.contains_key(id2));
                assert(cache_reqs[id1] == cache_reqs[id2]);
                assert(id1 == id2);
            };
        }
        assert forall |id2| #[trigger] outstanding.remove(id).contains_key(id2) implies {
            match outstanding.remove(id)[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr: ra2, load_handle: h2} => {
                    &&& cache_reqs.remove(id).contains_key(id2)
                    &&& cache_reqs.remove(id)[id2] == ra2@
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    &&& cache_reqs.remove(id).contains_key(id2)
                    &&& cache_reqs.remove(id)[id2] == write_addr@
                },
                OutstandingReqInfo::SuperBlockReq{} => {
                    !cache_reqs.remove(id).contains_key(id2)
                }
            }
        } by {
            assert(id2 != id) by {
                if id2 == id {
                    vstd::map::axiom_map_remove_domain(outstanding, id);
                    assert(outstanding.remove(id).dom().contains(id2));
                    assert(outstanding.remove(id).dom() == outstanding.dom().remove(id));
                    vstd::set::axiom_set_remove_same(outstanding.dom(), id);
                    assert(!outstanding.dom().remove(id).contains(id));
                    assert(false);
                }
            };
            vstd::map::axiom_map_remove_different(outstanding, id2, id);
            vstd::map::axiom_map_remove_different(cache_reqs, id2, id);
            assert(outstanding.remove(id)[id2] == outstanding[id2]);
            assert(Self::outstanding_requests_match_cache_reqs_map(outstanding, cache_reqs));
            match outstanding[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr: ra2, load_handle: h2} => {
                    assert(cache_reqs.contains_key(id2));
                    vstd::map::axiom_map_remove_domain(cache_reqs, id);
                    assert(cache_reqs.remove(id).dom() == cache_reqs.dom().remove(id));
                    vstd::set::axiom_set_remove_different(cache_reqs.dom(), id2, id);
                    assert(cache_reqs.remove(id).contains_key(id2));
                    assert(cache_reqs.remove(id)[id2] == cache_reqs[id2]);
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    assert(cache_reqs.contains_key(id2));
                    vstd::map::axiom_map_remove_domain(cache_reqs, id);
                    assert(cache_reqs.remove(id).dom() == cache_reqs.dom().remove(id));
                    vstd::set::axiom_set_remove_different(cache_reqs.dom(), id2, id);
                    assert(cache_reqs.remove(id).contains_key(id2));
                    assert(cache_reqs.remove(id)[id2] == cache_reqs[id2]);
                },
                OutstandingReqInfo::SuperBlockReq{} => {
                    assert(!cache_reqs.contains_key(id2));
                    vstd::map::axiom_map_remove_domain(cache_reqs, id);
                    assert(cache_reqs.remove(id).dom() == cache_reqs.dom().remove(id));
                    vstd::set::axiom_set_remove_different(cache_reqs.dom(), id2, id);
                    assert(!cache_reqs.remove(id).contains_key(id2));
                }
            }
        };
    }

    // Every model-level outstanding ID is tracked in the exec-level map.
    // This is the "model ⊆ exec" direction of outstanding_reqs_match_model.
    pub closed spec fn model_reqs_in_outstanding(self) -> bool {
        let state = self.state();
        let in_flight_sb_id = if state.in_flight is Some { set!{state.in_flight.unwrap().req_id} } else { set!{} };
        state.outstanding_cache_reqs.dom() + in_flight_sb_id <= self.outstanding_requests@.dom()
    }

    closed spec fn inv_running(self) -> bool {
        let state = self.state();

        &&& self.journal.wf()
        &&& self.store.wf()
        &&& self.store_initialized
        &&& self.journal.alloc_au() != self.store_alloc_au()
        &&& self.store.persistent_store_ptr_matches_alloc_au()
        &&& (self.in_flight is Some && self.in_flight.unwrap().store_ptr is Some
            ==> self.in_flight.unwrap().store_ptr.unwrap().au as nat == self.store_alloc_au())
        &&& (self.in_flight is Some && self.in_flight.unwrap().store_ptr is Some
            ==> (self.in_flight.unwrap().store_ptr.unwrap().page as nat) < self.store.next_alloc_page())
        &&& state.store_addrs() == self.store_addrs()
        // &&& self.model@.instance_id() == self.instance@.id() // TODO delete covered by inv

        &&& self.journal.index_ready()

        // physical state consistent with model
        &&& state.recovery_state is RecoveryComplete

        &&& self.journal.seq_end() == self.store.store_lsn_nat()
        &&& self.state().wf()

        // TODO: strengthen to self.outstanding_reqs_match_model() once all exec code
        // properly maintains outstanding_requests (insert on send, remove on response).
        // For now, the weaker conjunct in inv() (SuperBlockReq ==> in_flight is Some)
        // suffices for the B2/B4 pull-downs.

        &&& state.in_flight is Some <==> self.sync_requests.in_flight()
        &&& state.in_flight is Some <==> self.in_flight is Some

        &&& (state.in_flight is Some ==> {

            // The in-flight version stays active so get_suffix doesn't choke on it when it's time
            // to handle the disk response
            let sync_version = state.in_flight.unwrap().journal_version;
            let new_persistent_map_version = self.in_flight.unwrap().new_boundary_lsn as nat;
            &&& self.journal.seq_start() <= new_persistent_map_version
            &&& new_persistent_map_version <= sync_version
            &&& sync_version <= self.journal.marshalled_seq_end()
            // The in-flight 'satisfied requests' can indeed be satisfied by the in-flight version
            &&& self.sync_reqs_in_version(self.sync_requests.superblocking_reqs@, sync_version)
        })

        // Connect exec InFlight fields to model state for C1/C2 proofs
        &&& (state.in_flight is Some ==> {
            // InFlight boundary stays within the live journal range.
            &&& self.journal.seq_start() <= self.in_flight.unwrap().new_boundary_lsn as nat
            // InFlight boundary matches model in-flight boundary
            &&& self.in_flight.unwrap().new_boundary_lsn as nat == state.in_flight.unwrap().boundary_lsn
            // InFlight persistent_lsn matches model's inflight journal_version
            &&& self.in_flight.unwrap().new_persistent_lsn as nat == state.in_flight.unwrap().journal_version
            // InFlight store pointer matches the model in-flight pointer
            &&& iaddr_view(self.in_flight.unwrap().store_ptr) == state.in_flight.unwrap().store_ptr
        })

        &&& self.sync_requests.wf(self.instance@.id())
        &&& self.sync_reqs_in_version(self.sync_requests.buffered_reqs@, self.version())
        &&& self.sync_requests.sync_target_lsn <= self.version()
        &&& self.sync_reqs_in_version(self.sync_requests.journal_cleaning_reqs@, self.sync_requests.sync_target_lsn as nat)
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
        &&& self.state().store == self.i_ephemeral_store()
        &&& self.state().persistent_store_ptr == self.store.persistent_store_ptr_view()
        &&& self.state().prepared_store_ptr == self.prepared_store_ptr_view()
        &&& self.state().prepared_store_lsn == self.prepared_store_lsn_nat()
        &&& self.state().journal == self.journal@
        &&& self.store.persistent_store_ptr_matches_alloc_au()
        &&& (forall |a: Address| #[trigger] self.store_addrs().contains(a) ==> a.au == self.store_alloc_au())
    }

    spec fn inv_reading_journal(self) -> bool
    {
        &&& (!self.journal.index_ready() ==> self.state().recovery_state is SuperblockAvailable)
        &&& (self.journal.index_ready() ==> self.state().recovery_state is JournalIndexComplete)
        &&& (self.journal.index_ready() ==> self.journal.no_unmarshalled_entries())
        &&& (self.store_initialized ==> self.store.store_lsn_nat() == self.journal.seq_start())
        &&& self.state().in_flight is None
        &&& self.sync_requests.valid_empty_sync_buffer(self.instance@.id())
        &&& self.journal.wf()
        &&& forall |id| #[trigger] self.outstanding_requests@.contains_key(id)
            ==> self.outstanding_requests@[id] is CacheLoadReq
    }

    spec fn inv_applying_journal(self) -> bool
    {
        &&& self.state().recovery_state is JournalIndexComplete
        &&& self.store_initialized
        &&& self.state().in_flight is None
        &&& self.sync_requests.valid_empty_sync_buffer(self.instance@.id())
        &&& self.journal.seq_start() <= self.store.store_lsn_nat()
        &&& self.store.store_lsn_nat() <= self.journal.seq_end()
        &&& self.journal.wf()
        &&& self.journal.index_ready()
        &&& self.journal.no_unmarshalled_entries()
        &&& forall |id| #[trigger] self.outstanding_requests@.contains_key(id)
            ==> self.outstanding_requests@[id] is CacheLoadReq
    }

    closed spec fn inv(self) -> bool {
        &&& self.cache.wf()
        &&& self.store.wf()
        &&& self.journal.alloc_au() != self.store_alloc_au()
        &&& self.store_alloc_au() != spec_superblock_addr().au as nat
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
        // A SuperBlockReq in outstanding_requests implies in_flight is Some,
        // the ID is NOT a cache request, and the ID matches the in_flight req_id.
        // The last conjunct establishes uniqueness: at most one SuperBlockReq entry.
        &&& forall |id| #![auto] self.outstanding_requests@.dom().contains(id)
            && self.outstanding_requests@[id] is SuperBlockReq
            ==> self.in_flight is Some
                && !self.state().outstanding_cache_reqs.dom().contains(id)
                && self.state().in_flight is Some
                && id == self.state().in_flight.unwrap().req_id
        &&& self.model_reqs_in_outstanding()
        &&& self.model@.instance_id() == self.instance@.id()
    }

    // Recovery is complete -- journal index ready, map matches journal. We've established
    // invariants necessary to process user requsets.
    pub closed spec fn ready_for_user_operation(&self) -> bool
    {
        &&& self.recovery_phase is ReadyForUserOperation
    }

    pub closed spec fn store_addrs(&self) -> Set<Address>
    {
        let inflight_store_ptr = if self.in_flight is Some { self.in_flight.unwrap().store_ptr } else { None };
        self.store.store_addrs(inflight_store_ptr)
    }

    proof fn state_store_addrs_match(&self)
        requires
            self.state().persistent_store_ptr == self.store.persistent_store_ptr_view(),
            self.state().prepared_store_ptr == self.prepared_store_ptr_view(),
            (self.state().in_flight is Some) <==> (self.in_flight is Some),
            self.state().in_flight is Some ==> iaddr_view(self.in_flight.unwrap().store_ptr) == self.state().in_flight.unwrap().store_ptr,
        ensures
            self.state().store_addrs() == self.store_addrs(),
    {
        let inflight_store_ptr =
            if self.in_flight is Some { self.in_flight.unwrap().store_ptr } else { None };
        self.store.store_addrs_matches_views(inflight_store_ptr);
        assert(self.store_addrs() == self.store.store_addrs(inflight_store_ptr));
        if self.in_flight is Some {
            assert(self.state().in_flight is Some);
            assert(self.state().store_addrs()
                == (if self.state().persistent_store_ptr is Some {
                    set!{self.state().persistent_store_ptr.unwrap()}
                } else {
                    set![]
                })
                + (if self.state().prepared_store_ptr is Some {
                    set!{self.state().prepared_store_ptr.unwrap()}
                } else {
                    set![]
                })
                + (if self.state().in_flight.unwrap().store_ptr is Some {
                    set!{self.state().in_flight.unwrap().store_ptr.unwrap()}
                } else {
                    set![]
                }));
        } else {
            assert(self.state().in_flight is None);
            assert(self.state().store_addrs()
                == (if self.state().persistent_store_ptr is Some {
                    set!{self.state().persistent_store_ptr.unwrap()}
                } else {
                    set![]
                })
                + (if self.state().prepared_store_ptr is Some {
                    set!{self.state().prepared_store_ptr.unwrap()}
                } else {
                    set![]
                })
                + set![]);
        }
    }

    pub closed spec fn is_store_addr(&self, addr: Address) -> bool
    {
        let inflight_store_ptr = if self.in_flight is Some { self.in_flight.unwrap().store_ptr } else { None };
        self.store.is_store_addr(inflight_store_ptr, addr)
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
                    assert( AtomicState::execute_transition(pre_state.state, post_state.state, map_req, map_reply, ProgramEvent::NoOp{}) ); // witness
                }

                let tracked new_reply_token = self.instance.borrow().execute_transition(
                    KVStoreTokenized::Label::ExecuteOp{req, reply},
                    post_state,
                    &mut model,
                    req_shard.get()
                );
                self.model = Tracked(model);

                api.send_reply(reply, Tracked(new_reply_token), true);
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
            proof {
                self.store.kmmap_wf_ensures();
            }
            let ghost pre_state = self.model@.value();
            let ghost pre_store_kmmap = self.store@;
            let ghost keyed_msg = KeyedMessage{key, message: Message::Define{value}};

            self.journal.insert(key.clone(), value);
            self.store.insert(key, value);

            let reply = Reply{output: Output::PutOutput, id: req.id};
            let ghost post_state = ConcreteProgramModel{
                state: AtomicState{
                    journal: self.journal@,
                    store: self.i_ephemeral_store(),
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
                let ghost pre_store = pre_state.state.store->Known_v.stamped_map;
                let ghost post_store = post_state.state.store->Known_v.stamped_map;
                assert(pre_state.state == old(self).state()) by {
                }
                assert(pre_state.state.store == old(self).i_ephemeral_store()) by {
                }
                assert(pre_state.state.store is Known);
                assert(old(self).journal.seq_end() == old(self).store.store_lsn_nat());
                assert(pre_store_kmmap.wf());
                assert(pre_store.value == pre_store_kmmap);
                assert(pre_store.seq_end == old(self).store.store_lsn_nat());
                assert(pre_store.value.wf());
                assert(puts.can_follow(pre_store.seq_end));
                assert(post_state.state.store is Known) by {
                }
                assert(post_state.state.store == self.i_ephemeral_store()) by {
                }
                assert(post_store.value == self.store@);
                assert(post_store.seq_end == self.store.store_lsn_nat());
                assert(self.store@ == old(self).store@.insert(key, Message::Define{value}));
                assert(post_store.value == pre_store.value.insert(key, Message::Define{value}));
                assert(self.store.store_lsn_nat() == old(self).store.store_lsn_nat() + 1);
                assert(post_store.seq_end == pre_store.seq_end + 1);
                assert(puts.len() == 1);
                assert(post_store.seq_end == pre_store.seq_end + puts.len());

                // Need to unwind two instances of the recursive definition: one for the empty base
                // case and one for the single message we stuck in the history.
                reveal_with_fuel(MsgHistory::apply_to_stamped_map, 2);
                assert(MsgHistory::map_plus_history(pre_store, puts).value
                    == pre_store.value.insert(key, Message::Define{value}));
                assert(MsgHistory::map_plus_history(pre_store, puts).seq_end
                    == post_store.seq_end);
                assert(MsgHistory::map_plus_history(pre_store, puts).value
                    == post_store.value);
                assert(MsgHistory::map_plus_history(pre_store, puts)
                    == post_store);

                reveal(AbstractMap::State::next_by);
                reveal(AbstractMap::State::next);
                // step witness
                assert( AbstractMap::State::next_by(pre_state.state.store->Known_v, post_state.state.store->Known_v,
                        AbstractMap::Label::PutLabel{ puts }, AbstractMap::Step::put{}));

                reveal(CachedJournal::State::next_by);
                reveal(CachedJournal::State::next);
                // step witness
                assert( CachedJournal::State::next_by(pre_state.state.journal, post_state.state.journal,
                        CachedJournal::Label::Put{messages: puts},
                        CachedJournal::Step::put()) );

                assert( AtomicState::execute_transition(
                        pre_state.state, post_state.state, map_req, map_reply, ProgramEvent::Put{puts}) ); // witness
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
        proof {
            self.system_inv_implies_atomic_state_wf();
            assert(api.instance_id() == self.instance_id());
            assert(self.recovery_phase is ReadyForUserOperation);
            assert(self.state().cache == self.cache@) by {
            }
            assert(self.outstanding_requests_wf()) by {
            }
            assert(self.outstanding_requests_match_cache_reqs()) by {
            }
            assert(self.journal.wf());
            assert(self.store.wf());
            assert(self.store_initialized);
            assert(self.journal.alloc_au() != self.store_alloc_au());
            assert(self.store.persistent_store_ptr_matches_alloc_au());
            self.store.prepared_store_ptr_has_alloc_au();
            self.store.prepared_store_ptr_before_next_alloc();
            self.store.persistent_store_ptr_has_alloc_au();
            self.store.persistent_store_ptr_before_next_alloc();
            let inflight_store_ptr = if self.in_flight is Some { self.in_flight.unwrap().store_ptr } else { None };
            if inflight_store_ptr is Some {
                assert(inflight_store_ptr.unwrap().au as nat == self.store_alloc_au());
                assert((inflight_store_ptr.unwrap().page as nat) < self.store.next_alloc_page());
            }
            self.store.store_addrs_are_alloc_au(inflight_store_ptr);
            self.state_store_addrs_match();
            assert(self.journal.index_ready());
            assert(self.state().recovery_state is RecoveryComplete);
            assert(self.journal.seq_end() == self.store.store_lsn_nat());
            assert(self.state().wf());
            assert(self.state().in_flight is Some <==> self.sync_requests.in_flight());
            assert(self.state().in_flight is Some <==> self.in_flight is Some);
            if self.state().in_flight is Some {
                assert(self.in_flight is Some);
                assert(self.sync_requests.in_flight());
                let sync_version = self.state().in_flight.unwrap().journal_version;
                let new_persistent_map_version = self.in_flight.unwrap().new_boundary_lsn as nat;
                assert(self.journal.seq_start() <= new_persistent_map_version);
                assert(new_persistent_map_version <= sync_version);
                self.journal.view_marshaled_seq_end_ensures();
                self.journal.view_seq_end_ensures();
                assert(sync_version <= self.state().journal.marshalled_seq_end());
                assert(sync_version <= self.state().journal.seq_end());
                assert(self.state().journal.marshalled_seq_end() == self.journal.marshalled_seq_end());
                assert(self.state().journal.seq_end() == self.journal.seq_end());
                assert(sync_version <= self.journal.marshalled_seq_end());
                assert(sync_version <= self.journal.seq_end());
                assert(self.sync_reqs_in_version(self.sync_requests.superblocking_reqs@, sync_version));
                assert(self.in_flight.unwrap().new_boundary_lsn as nat == self.state().in_flight.unwrap().boundary_lsn);
                assert(self.in_flight.unwrap().new_persistent_lsn as nat == self.state().in_flight.unwrap().journal_version);
                assert(iaddr_view(self.in_flight.unwrap().store_ptr) == self.state().in_flight.unwrap().store_ptr);
                if self.in_flight.unwrap().store_ptr is Some {
                    assert(self.in_flight.unwrap().store_ptr.unwrap().au as nat == self.store_alloc_au());
                }
            }
            assert(self.sync_requests.wf(self.instance@.id()));
            assert(self.sync_reqs_in_version(self.sync_requests.buffered_reqs@, self.version())) by {
                assert(old(self).version() <= self.version());
            }
            assert(self.sync_requests.sync_target_lsn <= self.version()) by {
                assert(old(self).version() <= self.version());
            }
            assert(self.sync_reqs_in_version(
                self.sync_requests.journal_cleaning_reqs@,
                self.sync_requests.sync_target_lsn as nat,
            )) by {
            }
            assert(Self::three_sync_req_lists_mutually_unique(
                self.sync_requests.superblocking_reqs@,
                self.sync_requests.journal_cleaning_reqs@,
                self.sync_requests.buffered_reqs@,
            )) by {
            }
            assert(self.inv_running()) by {
            }
            assert(self.inv()) by {
            }
            assert(self.inv_api(api));
            assert(self.ready_for_user_operation());
        }
    }

    proof fn system_inv_cannot_receive_write_response_during_recovery(self, disk_req_id: ID, i_disk_response: IDiskResponse, disk_response_token: Tracked<DiskRespShard>)
    requires
        self.i().recovery_state is AwaitingSuperblock,
        disk_response_token@.multiset() == multiset_map_singleton(disk_req_id, i_disk_response@),
        i_disk_response is WriteResp,
    ensures
        false,
    {
        let model = open_system_invariant_disk_response_singleton::<ConcreteProgramModel, RefinementProof>(
            self.model, disk_response_token, disk_req_id, i_disk_response@);
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
            let value = self.store.query_value(&key);

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
                assert(pre_state.state == old(self).state()) by {
                }
                assert(pre_state.state.store == old(self).i_ephemeral_store()) by {
                }
                assert(pre_state.state.store is Known);
                assert(post_state.state.store is Known);
                assert(end_lsn == pre_state.state.store->Known_v.stamped_map.seq_end);
                assert(value == pre_state.state.store->Known_v.stamped_map.value[key]->value) by {
                    assert(value == old(self).store.kmmap()[key]->value);
                }

                reveal(AbstractMap::State::next_by);
                reveal(AbstractMap::State::next);
                // step witness
                assert( AbstractMap::State::next_by(pre_state.state.store->Known_v, post_state.state.store->Known_v,
                        AbstractMap::Label::QueryLabel{end_lsn, key, value}, AbstractMap::Step::query{}));

                assert( AtomicState::execute_transition(
                        pre_state.state, post_state.state, map_req, map_reply, ProgramEvent::Query{end_lsn, key, value}) ); // witness
            }

            let tracked new_reply_token = self.instance.borrow().execute_transition(
                KVStoreTokenized::Label::ExecuteOp{req, reply},
                post_state,
                &mut model,
                req_shard.get(),
            );
            self.model = Tracked(model);

            api.send_reply(reply, Tracked(new_reply_token), true);
            proof {
                assert(self.state() == post_state.state);
                assert(self.state().journal == self.journal@);
                assert(self.state().store == self.i_ephemeral_store()) by {
                }
                assert(self.inv_running()) by {
                }
                assert(self.inv()) by {
                }
                assert(self.inv_api(api));
                assert(self.ready_for_user_operation());
            }
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

        // Re-establish SyncInput typing for the extended buffered request list.
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
        let outstanding_empty = self.outstanding_requests.is_empty();
        if !outstanding_empty {
            Self::debug_print(&"  └─ defer launch: waiting on outstanding disk IO");
            return;
        }
        proof {
            assert(outstanding_empty);
            assert(self.outstanding_requests@.is_empty());
        }
        if self.sync_requests.superblocking_reqs.len() > 0 {    // todo write as in_flight -- for journal truncation case
            Self::debug_print(&"  └─ another superblock in flight");
        } else {
            if self.sync_requests.journal_cleaning_reqs.len() == 0 {
                if self.sync_requests.buffered_reqs.len() == 0 {
                    Self::debug_print(&"  └─ nobody is waiting for a superblock send.");
                    return;
                }
                // "now" lsn is at least as new as than all the buffered reqs
                self.sync_requests.sync_target_lsn = self.journal.exec_seq_end();
                std::mem::swap(&mut self.sync_requests.buffered_reqs, &mut self.sync_requests.journal_cleaning_reqs);
            }
            self.current_sync_motivation = Some(SuperblockMotivation::PushMap);
            Self::debug_print(&"  └─ send_superblock");
            self.send_superblock(api);
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    exec fn send_superblock(&mut self, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        // do we have room to send a superblock?
        old(self).in_flight is None,
        old(self).outstanding_requests@.is_empty(),
        // this requirement nonsense for map-only (journal truncation) case:
        old(self).sync_requests.journal_cleaning_reqs.len() > 0,
        old(self).ready_for_user_operation(),
        old(self).current_sync_motivation is Some,
        old(self).current_sync_motivation.unwrap() is PushJournal ==> {
            &&& old(self).prepared_store_ptr() == old(self).store.persistent_store_ptr()
        },
    ensures
        self.inv_api(api),
        self.ready_for_user_operation(),
    {
        proof {
            self.system_inv_implies_atomic_state_wf();
            assert(self.in_flight is None);
            assert(self.state().in_flight is None);
            assert(!self.sync_requests.in_flight());
        }
        let outstanding_empty = self.outstanding_requests.is_empty();
        proof {
            assert(outstanding_empty);
            assert(self.outstanding_requests@.is_empty());
            assert(self.no_outstanding_store_write()) by {
            }
            assert(self.sync_requests.journal_cleaning_reqs@.len() > 0);
            assert(self.sync_requests.superblocking_reqs@.len() == 0);
        }
        let motivation = self.current_sync_motivation.unwrap();
        let target_lsn = self.sync_requests.sync_target_lsn;
        let prepared_store_ptr_for_send = self.exec_prepared_store_ptr();
        let prepared_store_lsn_for_send = self.exec_prepared_store_lsn();
        let mut marshalled_end = self.journal.exec_marshaled_seq_end();

        // Checks if marshalling is needed
        if target_lsn > marshalled_end {
            api.log("send_superblock: marshalling journal tail up to cleaning target");
            self.should_retry_superblock_launch = true;

            let mut keep_marshalling = true;
            proof {
                assert(self.no_outstanding_store_write()) by {
                }
            }
            while keep_marshalling && marshalled_end < target_lsn
                invariant
                    self.inv_api(api),
                    self.ready_for_user_operation(),
                    marshalled_end as nat == self.journal.marshalled_seq_end(),
                    self.in_flight is None,
                    self.state().in_flight is None,
                    !self.sync_requests.in_flight(),
                    self.sync_requests.sync_target_lsn == target_lsn,
                    0 < self.sync_requests.journal_cleaning_reqs.len(),
                    self.sync_requests.superblocking_reqs.len() == 0,
                    self.no_outstanding_store_write(),
                    self.prepared_store_ptr() == prepared_store_ptr_for_send,
                    self.prepared_store_lsn() == prepared_store_lsn_for_send,
            {
                if let JournalMarshalStepResult::Success{} = self.maybe_marshall_journal(api, false) {
                } else {
                    keep_marshalling = false;
                }
                marshalled_end = self.journal.exec_marshaled_seq_end();
            }
            if target_lsn > marshalled_end {
                return;
            }
        }
        let mut raw_page = Vec::new();

        let mut sb;
        let mut self_in_flight;
        let mut store_ptr;
        let mut frozen_journal;
        let mut committed_boundary_lsn: u64 = 0;
        let mut committed_version_lsn: u64 = 0;
        let ghost mut pushmap_target_covered = false;
        let ghost mut pushjournal_target_covered = false;
        let ghost mut pushmap_boundary_marshaled = false;
        let ghost mut pushjournal_boundary_marshaled = false;
        let ghost mut ready_reqs_for_send = Seq::<Request>::empty();
        match motivation {
            SuperblockMotivation::PushMap => {
                let prepared_covers_target = target_lsn <= prepared_store_lsn_for_send;
                if !prepared_covers_target {
                    api.log("send_superblock: push map before sending superblock");

                    let ghost pre_state = self.model@.value();
                    let ghost pre_cache = self.cache;
                    let ghost pre_outstanding = self.outstanding_requests@;
                    let ghost pre_store_impl = self.store;
                    let ghost pre_view_store = self.i_ephemeral_store();
                    let ghost pre_store_kmmap = self.store@;
                    let ghost pre_store_lsn = self.store.store_lsn_nat();
                    let addr = self.store.peek_next_addr();
                    let raw_page_local = self.store.marshall_current_store_page();
                    let ghost raw_page_g = raw_page_local@;

                    proof {
                        assert(addr.au as nat == self.store_alloc_au());
                        assert(addr == self.store.next_alloc_addr());
                        assert((addr.page as nat) == self.store.next_alloc_page());
                        assert(pre_state.state.store == self.i_ephemeral_store());
                        assert(pre_state.state.store is Known);
                        assert(pre_state.state.store == pre_view_store);
                        assert(pre_state.state.store_addrs() == self.store_addrs());
                        assert(self.store.wf());
                        self.store.prepared_store_ptr_before_next_alloc();
                        self.store.persistent_store_ptr_view_ensures();
                        assert(pre_state.state.persistent_store_ptr == self.store.persistent_store_ptr_view());
                        assert(!self.store_addrs().contains(addr@)) by {
                            let inflight_store_ptr =
                                if self.in_flight is Some { self.in_flight.unwrap().store_ptr } else { None };
                            self.store.store_addrs_matches_views(inflight_store_ptr);
                            if self.store_addrs().contains(addr@) {
                                assert(self.store_addrs() == self.store.store_addrs(inflight_store_ptr));
                                if self.store.persistent_store_ptr_view() is Some
                                    && self.store.persistent_store_ptr_view().unwrap() == addr@
                                {
                                    self.store.persistent_store_ptr_view_ensures();
                                    assert(self.store.persistent_store_ptr() is Some);
                                    assert(self.store.persistent_store_ptr().unwrap() == addr);
                                    self.store.persistent_store_ptr_before_next_alloc();
                                    assert((addr.page as nat) < self.store.next_alloc_page());
                                } else if self.prepared_store_ptr_view() is Some
                                    && self.prepared_store_ptr_view().unwrap() == addr@
                                {
                                    self.store.prepared_store_ptr_view_ensures();
                                    assert(self.store.prepared_store_ptr() is Some);
                                    assert(self.store.prepared_store_ptr().unwrap() == addr);
                                    self.store.prepared_store_ptr_before_next_alloc();
                                    assert((addr.page as nat) < self.store.next_alloc_page());
                                } else {
                                    assert(inflight_store_ptr is Some);
                                    assert(inflight_store_ptr.unwrap()@ == addr@);
                                    assert(inflight_store_ptr.unwrap() == addr);
                                    assert((inflight_store_ptr.unwrap().page as nat) < self.store.next_alloc_page());
                                }
                                assert((addr.page as nat) == self.store.next_alloc_page());
                                assert(false);
                            }
                        }
                        assert(!pre_state.state.store_addrs().contains(addr@));
                        assume(!pre_cache.entry_fetched(&addr));
                    }

                    match self.cache.reserve_for_write_absent(&addr) {
                        ReserveWriteResult::CacheFull => {
                            api.log("send_superblock: cache full while preparing store page");
                            self.should_retry_superblock_launch = true;
                            return;
                        }
                        ReserveWriteResult::Reserved{slot_handle} => {
                            let ghost post_reserve_state = ConcreteProgramModel{
                                state: AtomicState{
                                    cache: self.cache@,
                                    ..pre_state.state
                                }
                            };
                            let tracked mut model0 = KVStoreTokenized::model::arbitrary();
                            proof {
                                tracked_swap(self.model.borrow_mut(), &mut model0);
                                assert(AtomicState::internal_transitions(
                                    pre_state.state,
                                    post_reserve_state.state,
                                    InternalEvent::CacheInternal{},
                                ));
                                self.instance.borrow().internal(
                                    KVStoreTokenized::Label::InternalOp{},
                                    post_reserve_state,
                                    &mut model0,
                                );
                            }
                            self.model = Tracked(model0);

                            self.store.advance_next_addr();
                            assert(self.store.store_lsn() == pre_store_impl.store_lsn());
                            let prepared_store_lsn = self.journal.exec_seq_end();

                            let mut slot_handle = slot_handle;
                            slot_handle.rec = raw_page_local;
                            self.cache.write_release(&addr, slot_handle);
                            proof {
                                assert(pre_store_impl.persistent_store_ptr_matches_alloc_au());
                                assert(self.store.persistent_store_ptr() == pre_store_impl.persistent_store_ptr());
                                assert(self.store.alloc_au() == pre_store_impl.alloc_au());
                                pre_store_impl.persistent_store_ptr_has_alloc_au();
                                if pre_store_impl.persistent_store_ptr() is Some {
                                    assert(pre_store_impl.persistent_store_ptr().unwrap().au as nat == self.store.alloc_au() as nat);
                                }
                                self.store.persistent_store_ptr_matches_alloc_au_from_ptr(pre_store_impl.persistent_store_ptr());
                            }
                            self.store.set_prepared_store(Some(addr), prepared_store_lsn);

                            let ghost post_freeze_state = ConcreteProgramModel{
                                state: AtomicState{
                                    cache: self.cache@,
                                    prepared_store_ptr: Some(addr@),
                                    prepared_store_lsn: prepared_store_lsn as nat,
                                    ..post_reserve_state.state
                                }
                            };
                            let tracked mut model1 = KVStoreTokenized::model::arbitrary();
                            proof {
                                let ghost pre_freeze_state = self.model@.value();
                                tracked_swap(self.model.borrow_mut(), &mut model1);
                                assert(pre_freeze_state.state == post_reserve_state.state);
                                assert(pre_freeze_state.state.store is Known);
                                assert(raw_page_to_store_kmmap(raw_page_g) == self.store@);
                                assert(self.store@ == pre_freeze_state.state.ephemeral_map().value);
                                self.journal.view_seq_end_ensures();
                                assert(pre_freeze_state.state.store == pre_state.state.store);
                                assert(pre_state.state.ephemeral_map().seq_end == self.journal.seq_end());
                                assert(prepared_store_lsn as nat == pre_freeze_state.state.ephemeral_map().seq_end);
                                assert(!pre_freeze_state.state.store_addrs().contains(addr@));
                                assert(addr@ != spec_superblock_addr()) by {
                                    assert(addr.au as nat == self.store_alloc_au());
                                    assert(self.store_alloc_au() != spec_superblock_addr().au as nat);
                                }
                                assert(Cache::State::next(
                                    pre_freeze_state.state.cache,
                                    post_freeze_state.state.cache,
                                    cache_write_label(&addr, raw_page_g),
                                ));
                                assert(AtomicState::internal_transitions(
                                    pre_freeze_state.state,
                                    post_freeze_state.state,
                                    InternalEvent::FreezeMap{addr: addr@, raw_page: raw_page_g},
                                ));
                                self.instance.borrow().internal(
                                    KVStoreTokenized::Label::InternalOp{},
                                    post_freeze_state,
                                    &mut model1,
                                );
                            }
                            self.model = Tracked(model1);

                            let wb = self.cache.begin_writeback(&addr);
                            let WritebackAcquireResult::Acquired{handle} = wb else {
                                Self::todo_placeholder();
                                return;
                            };

                            let write_data = handle.rec.clone();
                            if write_data.len() != PAGE_SIZE_BYTES {
                                Self::todo_placeholder();
                            }

                            let req_id_perm = Tracked(api.send_disk_request_predict_id());
                            let disk_req = IDiskRequest::WriteReq{to: addr, data: write_data};
                            let ghost req_map = map!{req_id_perm@ => disk_req@};
                            let ghost disk_request_tuples = multiset_map_singleton(req_id_perm@, disk_req@);
                            let ghost disk_response_tuples = Multiset::empty();
                            let ghost updated_outstanding_cache_reqs =
                                Map::new(|id| req_map.contains_key(id), |id| req_map[id].addr());
                            let ghost new_outstanding_cache_reqs =
                                post_freeze_state.state.outstanding_cache_reqs.union_prefer_right(updated_outstanding_cache_reqs);
                            let ghost post_cache_state = ConcreteProgramModel{
                                state: AtomicState{
                                    cache: self.cache@,
                                    outstanding_cache_reqs: new_outstanding_cache_reqs,
                                    ..post_freeze_state.state
                                }
                            };

                            let tracked mut model2 = KVStoreTokenized::model::arbitrary();
                            proof {
                                tracked_swap(self.model.borrow_mut(), &mut model2);
                                let info = ProgramDiskInfo{
                                    reqs: disk_request_tuples,
                                    resps: disk_response_tuples,
                                };
                                let disk_event = DiskEvent::CacheIOBegin{req_map};
                                let cache_lbl = Cache::Label::DiskOps{
                                    requests: set![disk_req@],
                                    responses: Map::empty(),
                                };
                                assert(map_to_multiset(disk_event->req_map) == info.reqs) by {
                                    Self::map_to_multiset_singleton(req_id_perm@, disk_req@);
                                }
                                assert(disk_event->req_map.values() == set![disk_req@]) by {
                                    Self::singleton_map_value(req_id_perm@, disk_req@);
                                }
                                assert(Cache::State::next(post_freeze_state.state.cache, post_cache_state.state.cache, cache_lbl));
                                assert(AtomicState::disk_transition(
                                    post_freeze_state.state,
                                    post_cache_state.state,
                                    disk_event,
                                    info.reqs,
                                    info.resps,
                                ));
                            }

                            let tracked empty_disk_responses: DiskRespShard = DiskRespShard::empty(self.instance_id());
                            let tracked new_disk_req_token = self.instance.borrow().disk_transitions(
                                KVStoreTokenized::Label::DiskOp{
                                    disk_request_tuples,
                                    disk_response_tuples,
                                },
                                post_cache_state,
                                &mut model2,
                                empty_disk_responses,
                            );

                            let req_id = api.send_disk_request(disk_req, req_id_perm, Tracked(new_disk_req_token));
                            self.outstanding_requests.insert(req_id, OutstandingReqInfo::StoreWriteReq{
                                write_addr: addr,
                                handle,
                            });
                            proof {
                                assert(req_id == req_id_perm@);
                            }

                            self.model = Tracked(model2);
                            proof {
                                self.system_inv_implies_atomic_state_wf();
                                let ghost inserted_req = OutstandingReqInfo::StoreWriteReq{
                                    write_addr: addr,
                                    handle,
                                };
                                assert(self.in_flight is None);
                                assert(self.state() == post_cache_state.state);
                                assert(self.state().cache == self.cache@);
                                assert(self.state().store == post_freeze_state.state.store);
                                assert(post_freeze_state.state.store == pre_state.state.store);
                                assert(self.state().store == self.i_ephemeral_store()) by {
                                    assert(self.state().store == pre_state.state.store);
                                    assert(pre_state.state.store == pre_view_store);
                                    assert(self.i_ephemeral_store() == pre_view_store) by {
                                        assert(self.store_initialized);
                                        assert(self.store@ == pre_store_kmmap);
                                        assert(self.store.store_lsn_nat() == pre_store_lsn);
                                        assert(pre_view_store is Known);
                                        assert(pre_view_store->Known_v.stamped_map.value == pre_store_kmmap);
                                        assert(pre_view_store->Known_v.stamped_map.seq_end == pre_store_lsn);
                                    }
                                }
                                assert(self.state().journal == self.journal@);
                                assert(self.state().persistent_store_ptr == self.store.persistent_store_ptr_view()) by {
                                    self.store.persistent_store_ptr_view_ensures();
                                    assert(self.state().persistent_store_ptr == post_freeze_state.state.persistent_store_ptr);
                                    assert(post_freeze_state.state.persistent_store_ptr == pre_state.state.persistent_store_ptr);
                                }
                                assert(self.state().prepared_store_ptr == self.prepared_store_ptr_view());
                                assert(self.state().prepared_store_lsn == self.prepared_store_lsn_nat());
                                self.state_store_addrs_match();
                                assert(self.outstanding_requests@ == pre_outstanding.insert(req_id, inserted_req));
                                Self::outstanding_requests_wf_map_preserved_by_cache(
                                    pre_outstanding,
                                    pre_cache,
                                    self.cache,
                                );
                                Self::outstanding_requests_wf_map_insert_store(
                                    pre_outstanding,
                                    self.cache,
                                    req_id,
                                    addr,
                                    handle,
                                );
                                assert(updated_outstanding_cache_reqs == map!{req_id => addr@}) by {
                                    assert_maps_equal!(updated_outstanding_cache_reqs, map!{req_id => addr@}, id2 => {
                                        if id2 == req_id {
                                            vstd::map::axiom_map_insert_same(Map::<ID, DiskRequest>::empty(), req_id, disk_req@);
                                            vstd::map::axiom_map_insert_same(Map::<ID, Address>::empty(), req_id, addr@);
                                        } else {
                                            Self::singleton_map_dom(req_id, disk_req@);
                                            Self::singleton_map_dom(req_id, addr@);
                                        }
                                    });
                                }
                                assert(new_outstanding_cache_reqs == post_freeze_state.state.outstanding_cache_reqs.insert(req_id, addr@)) by {
                                    vstd::map_lib::lemma_union_insert_right(
                                        post_freeze_state.state.outstanding_cache_reqs,
                                        Map::<ID, Address>::empty(),
                                        req_id,
                                        addr@,
                                    );
                                }
                                assert(self.state().outstanding_cache_reqs.is_injective());
                                Self::outstanding_requests_match_cache_reqs_map_insert_store(
                                    pre_outstanding,
                                    post_freeze_state.state.outstanding_cache_reqs,
                                    req_id,
                                    addr,
                                    handle,
                                );
                                assert(self.outstanding_requests_match_cache_reqs());
                                assert(self.journal.wf());
                                assert(self.store.wf());
                                assert(self.journal.alloc_au() != self.store_alloc_au());
                                assert(pre_store_impl.persistent_store_ptr_matches_alloc_au());
                                pre_store_impl.persistent_store_ptr_has_alloc_au();
                                assert(self.store.persistent_store_ptr() == pre_store_impl.persistent_store_ptr());
                                assert(self.store.alloc_au() == pre_store_impl.alloc_au());
                                if pre_store_impl.persistent_store_ptr() is Some {
                                    assert(pre_store_impl.persistent_store_ptr().unwrap().au as nat == pre_store_impl.alloc_au() as nat);
                                    assert(pre_store_impl.persistent_store_ptr().unwrap().au as nat == self.store.alloc_au() as nat);
                                }
                                self.store.persistent_store_ptr_matches_alloc_au_from_ptr(pre_store_impl.persistent_store_ptr());
                                assert(self.state().wf());
                                assert(self.store_initialized);
                                assert(self.journal.index_ready());
                                assert(self.journal.seq_end() == self.store.store_lsn_nat());
                                assert(self.state().recovery_state is RecoveryComplete);
                                self.store.prepared_store_ptr_has_alloc_au();
                                self.store.prepared_store_ptr_before_next_alloc();
                                assert(self.sync_requests.wf(self.instance@.id()));
                                assert(self.sync_reqs_in_version(self.sync_requests.buffered_reqs@, self.version()));
                                assert(self.sync_requests.sync_target_lsn <= self.version());
                                assert(self.sync_reqs_in_version(
                                    self.sync_requests.journal_cleaning_reqs@,
                                    self.sync_requests.sync_target_lsn as nat,
                                ));
                                assert(Self::three_sync_req_lists_mutually_unique(
                                    self.sync_requests.superblocking_reqs@,
                                    self.sync_requests.journal_cleaning_reqs@,
                                    self.sync_requests.buffered_reqs@,
                                ));
                                assert(self.inv_running());
                                assert(!self.no_outstanding_store_write()) by {
                                    assert(self.outstanding_requests@.contains_key(req_id));
                                    assert(self.outstanding_requests@[req_id] is StoreWriteReq);
                                }
                                assert(self.inv());
                                assert(self.inv_api(api));
                            }
                            return;
                        }
                    }
                } else {
                    if marshalled_end < prepared_store_lsn_for_send {
                        api.log("send_superblock: marshalling journal tail up to prepared store lsn");
                        self.should_retry_superblock_launch = true;

                        let mut keep_marshalling = true;
                        proof {
                            assert(self.no_outstanding_store_write()) by {
                            }
                        }
                        while keep_marshalling && marshalled_end < prepared_store_lsn_for_send
                            invariant
                                self.inv_api(api),
                                self.ready_for_user_operation(),
                                marshalled_end as nat == self.journal.marshalled_seq_end(),
                                self.in_flight is None,
                                self.state().in_flight is None,
                                !self.sync_requests.in_flight(),
                                self.sync_requests.sync_target_lsn == target_lsn,
                                0 < self.sync_requests.journal_cleaning_reqs.len(),
                                self.sync_requests.superblocking_reqs.len() == 0,
                                self.no_outstanding_store_write(),
                                self.prepared_store_ptr() == prepared_store_ptr_for_send,
                                self.prepared_store_lsn() == prepared_store_lsn_for_send,
                        {
                            if let JournalMarshalStepResult::Success{} = self.maybe_marshall_journal(api, false) {
                            } else {
                                keep_marshalling = false;
                            }
                            marshalled_end = self.journal.exec_marshaled_seq_end();
                        }
                        let prepared_boundary_marshaled = prepared_store_lsn_for_send <= marshalled_end;
                        if !prepared_boundary_marshaled {
                            return;
                        }
                    }

                    api.log("send_superblock: prepared map already covers target");
                    proof {
                        pushmap_target_covered = target_lsn as nat <= prepared_store_lsn_for_send as nat;
                        pushmap_boundary_marshaled = prepared_store_lsn_for_send as nat <= marshalled_end as nat;
                    }
                    proof {
                        ready_reqs_for_send = self.sync_requests.journal_cleaning_reqs@;
                    }
                    proof {
                        assert(self.sync_requests.superblocking_reqs.len() == 0);
                        assert(self.sync_requests.journal_cleaning_reqs@.len() > 0);
                    }
                    self.sync_requests.swap_cleaning_and_superblocking();
                    store_ptr = prepared_store_ptr_for_send;
                    frozen_journal = FrozenJournal{
                        snapshot: IJournalSnapshot{
                            boundary_lsn: prepared_store_lsn_for_send,
                            freshest_rec: None,
                        },
                        seq_end: prepared_store_lsn_for_send,
                    };
                    sb = ISuperblock{
                        journal_snapshot: frozen_journal.snapshot,
                        store_ptr,
                    };
                    api.log("sending this particular superblock: ");
                    Self::debug_print(&sb);
                    raw_page = DiskLayout::new().marshall(&sb);
                    self_in_flight = Some(InFlight{
                        new_boundary_lsn: frozen_journal.snapshot.boundary_lsn,
                        freshest_rec: None,
                        new_persistent_lsn: frozen_journal.seq_end,
                        store_ptr,
                    });
                    committed_boundary_lsn = prepared_store_lsn_for_send;
                    committed_version_lsn = prepared_store_lsn_for_send;
                }
            },
            SuperblockMotivation::PushJournal => {
                // sync the ephemeral journal with the existing persistent map
                api.log("send_superblock: journal sync only");

                match self.journal.freeze_for_commit(target_lsn) {
                    CleanForCommitResult::NeedsFlush{} => {
                        api.log("send_superblock: clean_for_commit -> NeedsFlush");
                        api.log("send_superblock: tail marshalled enough, starting journal page cleaning");
                        // Now it's time to flush!
                        let mut continue_writeback = true;
                        proof {
                            assert(self.no_outstanding_store_write()) by {
                            }
                        }
                        while continue_writeback
                            invariant
                                self.inv_api(api),
                                    self.ready_for_user_operation(),
                                    target_lsn <= marshalled_end,
                                    marshalled_end as nat == self.journal.marshalled_seq_end(),
                                    self.sync_requests.sync_target_lsn == target_lsn,
                                    self.no_outstanding_store_write(),
                        {
                            let ghost pre_model = self.model@.value();
                            let ghost pre_outstanding = self.outstanding_requests@;
                            let ghost pre_cache_impl = self.cache;
                            let ghost pre_view_store = self.i_ephemeral_store();
                            let ghost pre_journal_seq_start = self.journal.seq_start();
                            proof {
                                assert(pre_model.state == self.state());
                                assert(pre_model.state.store == pre_view_store);
                                assert(pre_model.state.in_flight is Some <==> self.in_flight is Some);
                                assert(pre_model.state.store_addrs() == self.store_addrs());
                                assert forall |id2| #[trigger] pre_outstanding.contains_key(id2)
                                    implies !(pre_outstanding[id2] is StoreWriteReq) by {
                                    assert(self.no_outstanding_store_write());
                                };
                                assert(Self::outstanding_requests_wf_map(pre_outstanding, pre_cache_impl));
                                assert(Self::outstanding_requests_match_cache_reqs_map(
                                    pre_outstanding,
                                    pre_model.state.outstanding_cache_reqs,
                                ));
                                if pre_model.state.in_flight is Some {
                                    assert(self.in_flight is Some);
                                    assert(self.in_flight.unwrap().new_boundary_lsn as nat == pre_model.state.in_flight.unwrap().boundary_lsn);
                                    assert(self.in_flight.unwrap().new_persistent_lsn as nat == pre_model.state.in_flight.unwrap().journal_version);
                                    assert(iaddr_view(self.in_flight.unwrap().store_ptr) == pre_model.state.in_flight.unwrap().store_ptr);
                                    if self.in_flight.unwrap().store_ptr is Some {
                                        assert(self.in_flight.unwrap().store_ptr.unwrap().au as nat == self.store_alloc_au());
                                    }
                                    assert(self.sync_reqs_in_version(
                                        self.sync_requests.superblocking_reqs@,
                                        pre_model.state.in_flight.unwrap().journal_version,
                                    ));
                                }
                            }
                            let ghost clean_before = self.journal.clean_watermark();
                            proof {
                                assert(target_lsn as nat <= marshalled_end as nat);
                                assert(target_lsn as nat <= self.journal.marshalled_seq_end());
                            }
                            let wb = self.journal.begin_writeback_for_target(&mut self.cache, target_lsn);
                            let ghost clean_after = self.journal.clean_watermark();
                            proof {
                                assert(self.journal.seq_start() == pre_journal_seq_start);
                            }
                            let ghost wb_flushed_domain = wb.flushed_domain();
                            let ghost cache_after_wb = self.cache@;
                            let ghost model_state_after_ack = if clean_before < clean_after {
                                AtomicState{
                                    journal: self.journal@,
                                    ..pre_model.state
                                }
                            } else {
                                pre_model.state
                            };
                            let ghost mut expected_state = model_state_after_ack;

                            let tracked mut model = KVStoreTokenized::model::arbitrary();
                            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

                            proof {
                                if clean_before < clean_after {
                                    let ghost post_state = ConcreteProgramModel{ state: model_state_after_ack };
                                    assert(AtomicState::internal_transitions(
                                            pre_model.state,
                                            post_state.state,
                                            InternalEvent::AckJournalFlush{flushed_domain: wb_flushed_domain}
                                    ));
                                    assert(ConcreteProgramModel::valid_internal_transition(
                                        ConcreteProgramModel{state: pre_model.state},
                                        post_state
                                    ));
                                    let tracked _internal_token = self.instance.borrow().internal(
                                        KVStoreTokenized::Label::InternalOp{},
                                        post_state,
                                        &mut model,
                                    );
                                }
                            }

                            match wb {
                                BeginWritebackForTargetResult::Acquired{request, ..} => {
                                    api.log("send_superblock: cleaning one journal page to disk");
                                    // TODO: fix this so we aren't cloning the write data
                                    // but is storing a different type of write handle inside the write reqinfo
                                    let write_data = request.handle.rec.clone();
                                    if write_data.len() != PAGE_SIZE_BYTES {
                                        Self::todo_placeholder();
                                    }

                                    let req_id_perm = Tracked(api.send_disk_request_predict_id());
                                    let disk_req = IDiskRequest::WriteReq{to: request.addr, data: write_data};
                                    let ghost req_map = map!{req_id_perm@ => disk_req@};
                                    let ghost disk_request_tuples = multiset_map_singleton(req_id_perm@, disk_req@);
                                    let ghost disk_response_tuples = Multiset::empty();
                                    let ghost updated_outstanding_cache_reqs =
                                        Map::new(|id| req_map.contains_key(id), |id| req_map[id].addr());
                                    let ghost new_outstanding_cache_reqs =
                                        model_state_after_ack.outstanding_cache_reqs.union_prefer_right(updated_outstanding_cache_reqs);
                                    let ghost post_cache_state = AtomicState{
                                        cache: self.cache@,
                                        outstanding_cache_reqs: new_outstanding_cache_reqs,
                                        ..model_state_after_ack
                                    };
                                    let ghost post_cache_model = ConcreteProgramModel{state: post_cache_state};
                                    proof {
                                        expected_state = post_cache_state;
                                    }

                                    proof {
                                        let info = ProgramDiskInfo{
                                            reqs: disk_request_tuples,
                                            resps: disk_response_tuples,
                                        };
                                        let disk_event = DiskEvent::CacheIOBegin{req_map};
                                        let cache_lbl = Cache::Label::DiskOps{
                                            requests: set![disk_req@],
                                            responses: Map::empty(),
                                        };
                                        assert(map_to_multiset(disk_event->req_map) == info.reqs) by {
                                            Self::map_to_multiset_singleton(req_id_perm@, disk_req@);
                                        }
                                        assert(disk_event->req_map.values() == set![disk_req@]) by {
                                            Self::singleton_map_value(req_id_perm@, disk_req@);
                                        }
                                        assert(Cache::State::next(model_state_after_ack.cache, post_cache_state.cache, cache_lbl));
                                        assert(AtomicState::disk_transition(model_state_after_ack, post_cache_state, disk_event, info.reqs, info.resps)) by {
                                        }
                                    }

                                    let tracked empty_disk_responses: DiskRespShard = DiskRespShard::empty(self.instance_id());
                                    let tracked new_disk_req_token = self.instance.borrow().disk_transitions(
                                        KVStoreTokenized::Label::DiskOp{
                                            disk_request_tuples,
                                            disk_response_tuples
                                        },
                                        post_cache_model,
                                        &mut model,
                                        empty_disk_responses,
                                    );

                                    let req_id = api.send_disk_request(disk_req, req_id_perm, Tracked(new_disk_req_token));
                                    self.outstanding_requests.insert(req_id, OutstandingReqInfo::JournalCacheWriteReq{
                                        write_addr: request.addr,
                                        handle: request.handle,
                                    });
                                    self.journal_flush_accumulator = self.journal_flush_accumulator.wrapping_add(1);
                                    proof {
                                        assert(req_id == req_id_perm@);
                                    }

                                    self.model = Tracked(model);
                                    proof {
                                        self.system_inv_implies_atomic_state_wf();
                                        let ghost inserted_req = OutstandingReqInfo::JournalCacheWriteReq{
                                            write_addr: request.addr,
                                            handle: request.handle,
                                        };
                                        assert(self.state() == post_cache_state);
                                        assert(self.state().cache == self.cache@);
                                        assert(self.state().store == self.i_ephemeral_store());
                                        assert(self.state().persistent_store_ptr == pre_model.state.persistent_store_ptr);
                                        assert(pre_model.state.persistent_store_ptr == self.store.persistent_store_ptr_view());
                                        assert(self.state().journal == self.journal@);
                                        assert(self.state().outstanding_cache_reqs == new_outstanding_cache_reqs);
                                        assert(self.state().in_flight is Some <==> self.in_flight is Some);
                                        assert(self.state().in_flight is Some <==> self.sync_requests.in_flight());
                                        assert(self.state().store_addrs() == self.store_addrs());
                                        assert(self.outstanding_requests@ == pre_outstanding.insert(req_id, inserted_req));
                                        Self::outstanding_requests_wf_map_preserved_by_cache(
                                            pre_outstanding,
                                            pre_cache_impl,
                                            self.cache,
                                        );
                                        Self::outstanding_requests_wf_map_insert_journal(
                                            pre_outstanding,
                                            self.cache,
                                            req_id,
                                            request.addr,
                                            request.handle,
                                        );
                                        assert(updated_outstanding_cache_reqs == map!{req_id => request.addr@}) by {
                                            assert_maps_equal!(updated_outstanding_cache_reqs, map!{req_id => request.addr@}, id2 => {
                                                if id2 == req_id {
                                                    vstd::map::axiom_map_insert_same(Map::<ID, DiskRequest>::empty(), req_id, disk_req@);
                                                    vstd::map::axiom_map_insert_same(Map::<ID, Address>::empty(), req_id, request.addr@);
                                                } else {
                                                    Self::singleton_map_dom(req_id, disk_req@);
                                                    Self::singleton_map_dom(req_id, request.addr@);
                                                }
                                            });
                                        }
                                        assert(new_outstanding_cache_reqs == pre_model.state.outstanding_cache_reqs.insert(req_id, request.addr@)) by {
                                            vstd::map_lib::lemma_union_insert_right(
                                                pre_model.state.outstanding_cache_reqs,
                                                Map::<ID, Address>::empty(),
                                                req_id,
                                                request.addr@,
                                            );
                                        }
                                        assert(self.state().outstanding_cache_reqs.is_injective());
                                        Self::outstanding_requests_match_cache_reqs_map_insert_journal(
                                            pre_outstanding,
                                            pre_model.state.outstanding_cache_reqs,
                                            req_id,
                                            request.addr,
                                            request.handle,
                                        );
                                        assert(self.outstanding_requests_match_cache_reqs());
                                        assert(self.journal.wf());
                                        assert(self.store.wf());
                                        assert(self.store_initialized);
                                        assert(self.journal.alloc_au() != self.store_alloc_au());
                                        assert(self.store.persistent_store_ptr_matches_alloc_au());
                                        assert(self.journal.index_ready());
                                        assert(self.state().recovery_state is RecoveryComplete);
                                        assert(self.journal.seq_end() == self.store.store_lsn_nat());
                                        assert(self.state().wf());
                                        assert(self.sync_requests.wf(self.instance@.id()));
                                        assert(self.sync_reqs_in_version(self.sync_requests.buffered_reqs@, self.version()));
                                        assert(self.sync_requests.sync_target_lsn <= self.version());
                                        assert(self.sync_reqs_in_version(
                                            self.sync_requests.journal_cleaning_reqs@,
                                            self.sync_requests.sync_target_lsn as nat,
                                        ));
                                        assert(Self::three_sync_req_lists_mutually_unique(
                                            self.sync_requests.superblocking_reqs@,
                                            self.sync_requests.journal_cleaning_reqs@,
                                            self.sync_requests.buffered_reqs@,
                                        ));
                                        if self.state().in_flight is Some {
                                            assert(self.in_flight is Some);
                                            assert(self.in_flight.unwrap().new_boundary_lsn as nat == self.state().in_flight.unwrap().boundary_lsn);
                                            assert(self.in_flight.unwrap().new_persistent_lsn as nat == self.state().in_flight.unwrap().journal_version);
                                            assert(iaddr_view(self.in_flight.unwrap().store_ptr) == self.state().in_flight.unwrap().store_ptr);
                                            self.journal.view_marshaled_seq_end_ensures();
                                            assert(self.state().journal.marshalled_seq_end() == self.journal.marshalled_seq_end());
                                            assert(self.state().journal.status.unwrap().unmarshalled_tail.seq_start == self.state().journal.marshalled_seq_end());
                                            self.journal.seq_start_le_marshalled_end();
                                            assert(self.journal.seq_start() <= self.in_flight.unwrap().new_boundary_lsn as nat);
                                            assert(self.in_flight.unwrap().new_boundary_lsn as nat <= self.state().in_flight.unwrap().journal_version);
                                            if self.in_flight.unwrap().store_ptr is Some {
                                                assert(self.in_flight.unwrap().store_ptr.unwrap().au as nat == self.store_alloc_au());
                                            }
                                            assert(self.sync_reqs_in_version(
                                                self.sync_requests.superblocking_reqs@,
                                                self.state().in_flight.unwrap().journal_version,
                                            ));
                                        }
                                        assert(self.inv_running()) by {
                                        };
                                        assert(self.no_outstanding_store_write()) by {
                                            assert forall |id2| #[trigger] self.outstanding_requests@.contains_key(id2)
                                                implies !(self.outstanding_requests@[id2] is StoreWriteReq) by {
                                                if id2 == req_id {
                                                    assert(self.outstanding_requests@[id2] is JournalCacheWriteReq);
                                                } else {
                                                    vstd::map::axiom_map_insert_different(pre_outstanding, id2, req_id, inserted_req);
                                                    assert(self.outstanding_requests@[id2] == pre_outstanding[id2]);
                                                    assert(!(pre_outstanding[id2] is StoreWriteReq));
                                                }
                                            };
                                        }
                                        assert(self.inv()) by {
                                            assert(self.no_outstanding_store_write());
                                        }
                                        assert(self.inv_api(api));
                                    }
                                },
                                BeginWritebackForTargetResult::Complete{..} => {
                                    let clean_now = self.journal.exec_clean_watermark();
                                    if target_lsn <= clean_now {
                                        api.log("send_superblock: cleaning target reached");
                                        self.should_retry_superblock_launch = true;
                                    } else {
                                        api.log("send_superblock: waiting for writeback responses");
                                    }
                                    proof {
                                        assert(cache_after_wb == pre_model.state.cache);
                                    }
                                    self.model = Tracked(model);
                                    proof {
                                        self.system_inv_implies_atomic_state_wf();
                                        assert(self.state() == ConcreteProgramModel{state: model_state_after_ack}.state);
                                        assert(self.state().cache == self.cache@);
                                        assert(self.state().store == self.i_ephemeral_store());
                                        assert(self.state().persistent_store_ptr == pre_model.state.persistent_store_ptr);
                                        assert(pre_model.state.persistent_store_ptr == self.store.persistent_store_ptr_view());
                                        assert(self.state().journal == self.journal@);
                                        assert(self.state().outstanding_cache_reqs == pre_model.state.outstanding_cache_reqs);
                                        assert(self.state().in_flight is Some <==> self.in_flight is Some);
                                        assert(self.state().in_flight is Some <==> self.sync_requests.in_flight());
                                        assert(self.state().store_addrs() == self.store_addrs());
                                        assert(self.outstanding_requests@ == pre_outstanding);
                                        Self::outstanding_requests_wf_map_preserved_by_cache(
                                            pre_outstanding,
                                            pre_cache_impl,
                                            self.cache,
                                        );
                                        assert(self.outstanding_requests_match_cache_reqs());
                                        assert(self.journal.wf());
                                        assert(self.store.wf());
                                        assert(self.store_initialized);
                                        assert(self.journal.alloc_au() != self.store_alloc_au());
                                        assert(self.store.persistent_store_ptr_matches_alloc_au());
                                        assert(self.journal.index_ready());
                                        assert(self.state().recovery_state is RecoveryComplete);
                                        assert(self.journal.seq_end() == self.store.store_lsn_nat());
                                        assert(self.state().wf());
                                        assert(self.sync_requests.wf(self.instance@.id()));
                                        assert(self.sync_reqs_in_version(self.sync_requests.buffered_reqs@, self.version()));
                                        assert(self.sync_requests.sync_target_lsn <= self.version());
                                        assert(self.sync_reqs_in_version(
                                            self.sync_requests.journal_cleaning_reqs@,
                                            self.sync_requests.sync_target_lsn as nat,
                                        ));
                                        assert(Self::three_sync_req_lists_mutually_unique(
                                            self.sync_requests.superblocking_reqs@,
                                            self.sync_requests.journal_cleaning_reqs@,
                                            self.sync_requests.buffered_reqs@,
                                        ));
                                        if self.state().in_flight is Some {
                                            assert(self.in_flight is Some);
                                            assert(self.in_flight.unwrap().new_boundary_lsn as nat == self.state().in_flight.unwrap().boundary_lsn);
                                            assert(self.in_flight.unwrap().new_persistent_lsn as nat == self.state().in_flight.unwrap().journal_version);
                                            assert(iaddr_view(self.in_flight.unwrap().store_ptr) == self.state().in_flight.unwrap().store_ptr);
                                            self.journal.view_marshaled_seq_end_ensures();
                                            assert(self.state().journal.marshalled_seq_end() == self.journal.marshalled_seq_end());
                                            assert(self.state().journal.status.unwrap().unmarshalled_tail.seq_start == self.state().journal.marshalled_seq_end());
                                            self.journal.seq_start_le_marshalled_end();
                                            assert(self.journal.seq_start() <= self.in_flight.unwrap().new_boundary_lsn as nat);
                                            assert(self.in_flight.unwrap().new_boundary_lsn as nat <= self.state().in_flight.unwrap().journal_version);
                                            if self.in_flight.unwrap().store_ptr is Some {
                                                assert(self.in_flight.unwrap().store_ptr.unwrap().au as nat == self.store_alloc_au());
                                            }
                                            assert(self.sync_reqs_in_version(
                                                self.sync_requests.superblocking_reqs@,
                                                self.state().in_flight.unwrap().journal_version,
                                            ));
                                        }
                                        assert(self.inv_running()) by {
                                        };
                                        assert(self.inv_api(api));
                                    }
                                    continue_writeback = false;
                                },
                            }
                        }
                        // TODO: add maybe launch superblock flag
                        return;
                    },
                    CleanForCommitResult::Frozen{frozen_journal: fj} => {
                        proof {
                            pushjournal_target_covered = target_lsn as nat <= fj.seq_end as nat;
                            assert(fj.seq_end as nat == self.journal.clean_watermark());
                            self.journal.clean_watermark_le_marshaled_seq_end();
                            assert(self.journal.clean_watermark() <= self.journal.marshalled_seq_end());
                            pushjournal_boundary_marshaled = fj.seq_end as nat <= self.journal.marshalled_seq_end();
                        }
                        frozen_journal = fj;
                    },
                }
                proof {
                    let lbl = CachedJournal::Label::FreezeForCommit{
                        frozen: frozen_journal.snapshot@,
                        frozen_seq_end: frozen_journal.seq_end as nat,
                    };
                    assert(CachedJournal::State::next(self.journal@, self.journal@, lbl));
                }

                // Okay, the journal is clean up to the point of sync_target_lsn, which
                // means the journal_cleaning_reqs are now eligible to be delivered in a
                // superblock.
                proof {
                    ready_reqs_for_send = self.sync_requests.journal_cleaning_reqs@;
                }
                proof {
                    assert(self.sync_requests.superblocking_reqs.len() == 0);
                    assert(self.sync_requests.journal_cleaning_reqs@.len() > 0);
                }
                self.sync_requests.swap_cleaning_and_superblocking();
                store_ptr = self.exec_prepared_store_ptr();

                sb = ISuperblock{
                    journal_snapshot: frozen_journal.snapshot,
                    store_ptr,
                };
                
                api.log("sending this particular superblock: ");
                Self::debug_print(&sb);
                raw_page = DiskLayout::new().marshall(&sb);

                self_in_flight = Some(InFlight{
                    new_boundary_lsn: frozen_journal.snapshot.boundary_lsn,
                    freshest_rec: frozen_journal.snapshot.freshest_rec,
                    new_persistent_lsn: frozen_journal.seq_end,
                    store_ptr,
                });
                committed_boundary_lsn = frozen_journal.snapshot.boundary_lsn;
                committed_version_lsn = frozen_journal.seq_end;
            },
        }
        // First step: store internal no-op on the map model.
        let ghost state_after_freeze = self.state();
        proof {
            assert(state_after_freeze == self.state());
            assert(state_after_freeze.prepared_store_ptr == self.prepared_store_ptr_view());
            assert(state_after_freeze.prepared_store_lsn == self.prepared_store_lsn_nat());
        }
        let ghost pre_send_outstanding = self.outstanding_requests@;
        {
            let tracked mut model = KVStoreTokenized::model::arbitrary();
            let ghost pre_store = state_after_freeze.store;
            let ghost post_state = ConcreteProgramModel {
                state: state_after_freeze
            };

            proof {
                reveal(AbstractMap::State::next_by);
                reveal(AbstractMap::State::next);
                assert( AbstractMap::State::next_by(
                    pre_store->Known_v,
                    pre_store->Known_v,
                    AbstractMap::Label::InternalLabel,
                    AbstractMap::Step::internal()
                ));
                
                tracked_swap(self.model.borrow_mut(), &mut model);
                assert(ConcreteProgramModel::valid_internal_transition(model.value(), post_state)) by {
                    assert(AtomicState::internal_transitions(
                        model.value().state,
                        post_state.state,
                        InternalEvent::StoreInternal{}
                    )) by {
                        broadcast use JournalImpl::view_ensures;
                    }
                }
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
            boundary_lsn: frozen_journal.snapshot.boundary_lsn as nat,
            store_ptr: iaddr_view(store_ptr),
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
            // Witness the disk transition via execute_sync_begin
            let disk_event = DiskEvent::ExecuteSyncBegin{
                req_id: disk_req_id,
                req: disk_request@,
                frozen_journal: sb@.journal,
                store_ptr: iaddr_view(store_ptr),
                frozen_seq_end: frozen_journal.seq_end as nat,
            };

            // Prove preconditions of execute_sync_begin:
            let pre = state_after_freeze;
            let post = post_state.state;
            assert(pre == self.state());
            self.store.prepared_store_ptr_view_ensures();
            self.store.prepared_store_lsn_nat_ensures();
            assert(self.state().prepared_store_ptr == self.prepared_store_ptr_view());
            assert(self.state().prepared_store_lsn == self.prepared_store_lsn_nat());
            assert(self.prepared_store_ptr_view() == iaddr_view(prepared_store_ptr_for_send));
            assert(self.prepared_store_lsn_nat() == prepared_store_lsn_for_send as nat);
            assert(pre.journal == self.journal@);
            assert(post.journal == self.journal@);
            assert(pre.prepared_store_ptr == self.prepared_store_ptr_view());
            assert(pre.prepared_store_lsn == self.prepared_store_lsn_nat());
            assert(AtomicState::sync_begin_journal_ok(
                pre,
                post,
                frozen_journal.snapshot@,
                frozen_journal.seq_end as nat,
            )) by {
                if frozen_journal.snapshot.boundary_lsn as nat == pre.prepared_store_lsn
                    && frozen_journal.snapshot.freshest_rec is None
                    && frozen_journal.seq_end as nat == pre.prepared_store_lsn
                {
                    assert(post.journal == pre.journal);
                    assert(frozen_journal.snapshot.freshest_rec is None);
                    assert(frozen_journal.seq_end as nat == pre.prepared_store_lsn);
                } else {
                    let journal_lbl = CachedJournal::Label::FreezeForCommit{
                        frozen: frozen_journal.snapshot@,
                        frozen_seq_end: frozen_journal.seq_end as nat,
                    };
                    assert(CachedJournal::State::next(pre.journal, post.journal, journal_lbl));
                }
            };
            assert(pre.store is Known);
            assert(post.store == pre.store);
            assert(DiskLayout::spec_new().spec_parse(disk_request@->data) == sb@@);
            assert(sb@@.journal == frozen_journal.snapshot@);
            if motivation is PushMap {
                assert(self.no_outstanding_store_write()) by {
                }
            }
            assert(store_ptr == prepared_store_ptr_for_send);
            assert(sb@@.store_ptr == iaddr_view(store_ptr));
            assert(iaddr_view(store_ptr) == iaddr_view(prepared_store_ptr_for_send));
            assert(AtomicState::selected_sync_pair(
                pre,
                iaddr_view(store_ptr),
                frozen_journal.snapshot.boundary_lsn as nat,
            )) by {
                assert(pre.prepared_store_ptr == iaddr_view(prepared_store_ptr_for_send));
                assert(iaddr_view(store_ptr) == pre.prepared_store_ptr);
                if motivation is PushMap {
                    assert(frozen_journal.snapshot.boundary_lsn as nat == prepared_store_lsn_for_send as nat);
                    assert(pre.prepared_store_lsn == prepared_store_lsn_for_send as nat);
                    assert(frozen_journal.snapshot.boundary_lsn as nat == pre.prepared_store_lsn);
                } else {
                    self.journal.view_seq_start_ensures();
                    assert(frozen_journal.seq_start() as nat == self.journal.seq_start());
                    assert(pre.journal == self.journal@);
                    assert(frozen_journal.snapshot.boundary_lsn as nat == frozen_journal.seq_start() as nat);
                    assert(frozen_journal.snapshot.boundary_lsn as nat == pre.journal.snapshot.boundary_lsn);
                }
            };
            assert(post == AtomicState{
                store: post.store,
                journal: post.journal,
                in_flight: Some(inflight_info),
                ..pre
            });
            
            assert( disk_reqs == Multiset::singleton((disk_req_id, disk_request@)) ) by {
            }; // trigger

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

        let disk_req_id_exec = api.send_disk_request(disk_request, req_id_perm, Tracked(new_reply_token));
        self.outstanding_requests.insert(disk_req_id_exec, OutstandingReqInfo::SuperBlockReq{});

        proof {
            assert(disk_req_id_exec == disk_req_id);
            self.journal.seq_start_le_marshalled_end();
            // The superblock write ID is not in outstanding_cache_reqs.
            self.system_inv_sb_id_not_in_cache_reqs();
            self.system_inv_implies_atomic_state_wf();
            assert(self.state() == post_state.state);
            assert(self.state().cache == self.cache@);
            assert(self.state().store == self.i_ephemeral_store());
            assert(self.state().persistent_store_ptr == self.store.persistent_store_ptr_view());
            assert(self.state().journal == self.journal@);
            assert(self.state().in_flight is Some);
            assert(self.in_flight is Some);
            assert(self.state().in_flight is Some <==> self.in_flight is Some);
            assert(self.state().in_flight is Some <==> self.sync_requests.in_flight());
            assert(self.in_flight.unwrap().new_boundary_lsn as nat == self.state().in_flight.unwrap().boundary_lsn);
            assert(self.in_flight.unwrap().new_persistent_lsn as nat == self.state().in_flight.unwrap().journal_version);
            assert(self.state().in_flight.unwrap().boundary_lsn == committed_boundary_lsn as nat);
            assert(self.state().in_flight.unwrap().journal_version == committed_version_lsn as nat);
            assert(iaddr_view(self.in_flight.unwrap().store_ptr) == self.state().in_flight.unwrap().store_ptr);
            if self.in_flight.unwrap().store_ptr is Some {
                assert(self.in_flight.unwrap().store_ptr == store_ptr);
                assert(self.prepared_store_ptr() is Some);
                assert(self.prepared_store_ptr().unwrap() == self.in_flight.unwrap().store_ptr.unwrap());
                self.store.prepared_store_ptr_has_alloc_au();
                self.store.prepared_store_ptr_before_next_alloc();
                assert((self.in_flight.unwrap().store_ptr.unwrap().page as nat) < self.store.next_alloc_page());
                assert(self.in_flight.unwrap().store_ptr.unwrap().au as nat == self.store_alloc_au());
            }
            self.state_store_addrs_match();
            assert(self.outstanding_requests@ == pre_send_outstanding.insert(disk_req_id_exec, OutstandingReqInfo::SuperBlockReq{}));
            Self::outstanding_requests_wf_map_insert_superblock(
                pre_send_outstanding,
                self.cache,
                disk_req_id_exec,
            );
            Self::outstanding_requests_match_cache_reqs_map_insert_superblock(
                pre_send_outstanding,
                self.state().outstanding_cache_reqs,
                disk_req_id_exec,
            );
            assert(self.outstanding_requests_wf());
            assert(self.outstanding_requests_match_cache_reqs());
            assert(self.journal.wf());
            assert(self.store.wf());
            assert(self.store_initialized);
            assert(self.journal.alloc_au() != self.store_alloc_au());
            assert(self.store.persistent_store_ptr_matches_alloc_au());
            self.store.prepared_store_ptr_has_alloc_au();
            self.store.prepared_store_ptr_before_next_alloc();
            self.store.persistent_store_ptr_has_alloc_au();
            self.store.persistent_store_ptr_before_next_alloc();
            let inflight_store_ptr = if self.in_flight is Some { self.in_flight.unwrap().store_ptr } else { None };
            self.store.store_addrs_are_alloc_au(inflight_store_ptr);
            assert(self.journal.index_ready());
            assert(self.state().recovery_state is RecoveryComplete);
            assert(self.journal.seq_end() == self.store.store_lsn_nat());
            assert(self.state().wf());
            assert(self.sync_requests.wf(self.instance@.id()));
            assert(self.sync_reqs_in_version(self.sync_requests.buffered_reqs@, self.version()));
            assert(self.sync_requests.sync_target_lsn == target_lsn);
            assert(self.sync_requests.sync_target_lsn <= self.version());
            assert(self.sync_requests.journal_cleaning_reqs@.len() == 0);
            assert(self.sync_reqs_in_version(
                self.sync_requests.journal_cleaning_reqs@,
                self.sync_requests.sync_target_lsn as nat,
            )) by {
                if self.sync_requests.journal_cleaning_reqs@.len() == 0 {
                    assert forall |i| #![auto] 0 <= i < self.sync_requests.journal_cleaning_reqs@.len() implies {
                        &&& self.sync_requests.journal_cleaning_reqs@[i].input is SyncInput
                        &&& self.sync_req_in_version(
                            self.sync_requests.journal_cleaning_reqs@[i].id,
                            self.sync_requests.sync_target_lsn as nat,
                        )
                    } by {
                    };
                }
            };
            assert(Self::three_sync_req_lists_mutually_unique(
                self.sync_requests.superblocking_reqs@,
                self.sync_requests.journal_cleaning_reqs@,
                self.sync_requests.buffered_reqs@,
            ));
            if motivation is PushMap {
                assert(self.state().in_flight.unwrap().boundary_lsn == prepared_store_lsn_for_send as nat);
                assert(self.state().prepared_store_lsn == prepared_store_lsn_for_send as nat);
                assert(committed_version_lsn == prepared_store_lsn_for_send);
                assert(pushmap_target_covered);
                assert(target_lsn as nat <= prepared_store_lsn_for_send as nat);
                self.journal.view_seq_start_ensures();
                assert(self.state().journal.snapshot.boundary_lsn == self.journal.seq_start());
                assert(self.journal.seq_start() <= self.state().in_flight.unwrap().boundary_lsn);
            } else {
                let journal_lbl = CachedJournal::Label::FreezeForCommit{
                    frozen: frozen_journal.snapshot@,
                    frozen_seq_end: frozen_journal.seq_end as nat,
                };
                assert(CachedJournal::State::next(self.journal@, self.journal@, journal_lbl));
                assert(committed_version_lsn == frozen_journal.seq_end);
                assert(pushjournal_target_covered);
                assert(target_lsn as nat <= frozen_journal.seq_end as nat);
                assert(self.journal.seq_start() <= self.state().in_flight.unwrap().boundary_lsn);
            }
            assert(self.journal.seq_start() <= self.in_flight.unwrap().new_boundary_lsn as nat);
            assert(self.in_flight.unwrap().new_boundary_lsn as nat <= self.state().in_flight.unwrap().journal_version);
            assert(self.state().in_flight.unwrap().journal_version <= self.journal.marshalled_seq_end()) by {
                if motivation is PushMap {
                    assert(committed_version_lsn == prepared_store_lsn_for_send);
                    assert(pushmap_boundary_marshaled);
                } else {
                    assert(committed_version_lsn == frozen_journal.seq_end);
                    assert(pushjournal_boundary_marshaled);
                }
                assert(committed_version_lsn as nat == self.state().in_flight.unwrap().journal_version);
            };
            assert(self.state().in_flight.unwrap().journal_version <= self.journal.seq_end());
            assert(self.sync_requests.in_flight());
            assert(self.sync_reqs_in_version(
                self.sync_requests.superblocking_reqs@,
                self.state().in_flight.unwrap().journal_version,
            )) by {
                assert(self.sync_requests.superblocking_reqs@ == ready_reqs_for_send);
                if motivation is PushMap {
                    assert(committed_version_lsn == prepared_store_lsn_for_send);
                    assert(pushmap_target_covered);
                    assert(target_lsn as nat <= prepared_store_lsn_for_send as nat);
                } else {
                    assert(committed_version_lsn == frozen_journal.seq_end);
                    assert(pushjournal_target_covered);
                    assert(target_lsn as nat <= frozen_journal.seq_end as nat);
                }
                assert(committed_version_lsn as nat == self.state().in_flight.unwrap().journal_version);
                assert forall |i| #![auto] 0 <= i < self.sync_requests.superblocking_reqs@.len() implies {
                    &&& self.sync_requests.superblocking_reqs@[i].input is SyncInput
                    &&& self.sync_req_in_version(
                        self.sync_requests.superblocking_reqs@[i].id,
                        self.state().in_flight.unwrap().journal_version,
                    )
                } by {
                    assert(self.sync_requests.superblocking_reqs@[i] == ready_reqs_for_send[i]);
                    assert(self.sync_req_in_version(
                        ready_reqs_for_send[i].id,
                        self.sync_requests.sync_target_lsn as nat,
                    ));
                    assert(self.sync_requests.sync_target_lsn == target_lsn);
                    if motivation is PushMap {
                        assert(target_lsn as nat <= prepared_store_lsn_for_send as nat);
                        assert(committed_version_lsn as nat == prepared_store_lsn_for_send as nat);
                    } else {
                        assert(target_lsn as nat <= frozen_journal.seq_end as nat);
                        assert(committed_version_lsn as nat == frozen_journal.seq_end as nat);
                    }
                    assert(self.sync_requests.sync_target_lsn as nat <= committed_version_lsn as nat) by {
                        if motivation is PushMap {
                            assert(target_lsn as nat <= prepared_store_lsn_for_send as nat);
                            assert(committed_version_lsn as nat == prepared_store_lsn_for_send as nat);
                        } else {
                            assert(target_lsn as nat <= frozen_journal.seq_end as nat);
                            assert(committed_version_lsn as nat == frozen_journal.seq_end as nat);
                        }
                    };
                    assert(self.sync_requests.sync_target_lsn as nat <= self.state().in_flight.unwrap().journal_version);
                };
            };
            assert(self.inv_running()) by {
            };
            assert(self.model_reqs_in_outstanding()) by {
                let in_flight_sb_id = set!{self.state().in_flight.unwrap().req_id};
                assert(self.state().in_flight.unwrap().req_id == disk_req_id_exec);
                assert(self.state().outstanding_cache_reqs.dom() <= self.outstanding_requests@.dom()) by {
                    assert forall |id2: ID| #[trigger] self.state().outstanding_cache_reqs.dom().contains(id2)
                        implies self.outstanding_requests@.dom().contains(id2) by {
                        assert(self.outstanding_requests_match_cache_reqs());
                        assert(self.outstanding_requests@.contains_key(id2));
                    };
                }
                assert((self.state().outstanding_cache_reqs.dom() + in_flight_sb_id) <= self.outstanding_requests@.dom()) by {
                    assert forall |id2: ID| #[trigger] (self.state().outstanding_cache_reqs.dom() + in_flight_sb_id).contains(id2)
                        implies self.outstanding_requests@.dom().contains(id2) by {
                        if in_flight_sb_id.contains(id2) {
                            assert(id2 == self.state().in_flight.unwrap().req_id);
                            assert(id2 == disk_req_id_exec);
                            assert(self.outstanding_requests@.contains_key(disk_req_id_exec));
                        } else {
                            assert(self.state().outstanding_cache_reqs.dom().contains(id2));
                            assert(self.outstanding_requests@.dom().contains(id2));
                        }
                    };
                }
            };
            assert forall |id| #![auto] self.outstanding_requests@.dom().contains(id)
                && self.outstanding_requests@[id] is SuperBlockReq
                implies self.in_flight is Some
                    && !self.state().outstanding_cache_reqs.dom().contains(id)
                    && self.state().in_flight is Some
                    && id == self.state().in_flight.unwrap().req_id by {
                assert(self.outstanding_requests@[disk_req_id_exec] is SuperBlockReq);
                if id != disk_req_id_exec {
                    assert(old(self).outstanding_requests@.contains_key(id));
                    vstd::map::axiom_map_insert_different(old(self).outstanding_requests@, id, disk_req_id_exec, OutstandingReqInfo::SuperBlockReq{});
                    assert(self.outstanding_requests@[id] == old(self).outstanding_requests@[id]);
                    assert(old(self).outstanding_requests@[id] is SuperBlockReq);
                    assert(false);
                }
                assert(self.in_flight is Some);
                assert(self.state().in_flight is Some);
                assert(id == disk_req_id_exec);
                assert(id == self.state().in_flight.unwrap().req_id);
                assert(!self.state().outstanding_cache_reqs.dom().contains(id));
            };
            assert(self.recovery_phase is ReadyForUserOperation);
            assert(self.model@.instance_id() == self.instance@.id());
            assert(self.inv()) by {
                let inflight_store_ptr = self.in_flight.unwrap().store_ptr;
                if inflight_store_ptr is Some {
                    assert(inflight_store_ptr.unwrap().au as nat == self.store_alloc_au());
                }
                self.store.store_addrs_are_alloc_au(inflight_store_ptr);
                assert(self.inv_post_superblock_common());
                assert(self.cache.wf());
                assert(self.store.wf());
                assert(self.journal.alloc_au() != self.store_alloc_au());
                assert(self.state().cache == self.cache@);
                assert(self.outstanding_requests_wf());
                assert(self.outstanding_requests_match_cache_reqs());
                assert(self.recovery_phase is FetchingSuperblock ==> self.inv_recover());
                assert(!(self.recovery_phase is FetchingSuperblock) ==> self.inv_post_superblock_common());
                assert(self.recovery_phase is ReadingJournalIndex ==> self.inv_reading_journal());
                assert(self.recovery_phase is ApplyingJournalToRecoverEphemeralMap ==> self.inv_applying_journal());
                assert forall |id| #![auto] self.outstanding_requests@.dom().contains(id)
                    && self.outstanding_requests@[id] is SuperBlockReq
                    implies self.in_flight is Some
                        && !self.state().outstanding_cache_reqs.dom().contains(id)
                        && self.state().in_flight is Some
                        && id == self.state().in_flight.unwrap().req_id by {
                };
                assert(self.model_reqs_in_outstanding());
                assert(self.model@.instance_id() == self.instance@.id());
            };
            assert(self.inv_api(api));
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
        assert( self.sync_reqs_in_version(self.sync_requests.journal_cleaning_reqs@, self.sync_requests.sync_target_lsn as nat) );
        assert( oself.sync_reqs_in_version(oself.sync_requests.journal_cleaning_reqs@, oself.sync_requests.sync_target_lsn as nat) );
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

    // Use the system invariant to learn that in_flight is Some and the response ID matches.
    // Precondition: the ID is not a cache request (from inv: SuperBlockReq ==> !cache_reqs).
    proof fn system_inv_response_implies_in_flight(self, disk_req_id: ID, i_disk_response: IDiskResponse, disk_response_token: Tracked<DiskRespShard>)
    requires
        self.i().recovery_state is RecoveryComplete,
        !self.i().outstanding_cache_reqs.dom().contains(disk_req_id),
        disk_response_token@.multiset() == multiset_map_singleton(disk_req_id, i_disk_response@),
    ensures
        self.i().in_flight is Some,
        self.i().in_flight->0.req_id == disk_req_id,
    {
        let model = open_system_invariant_disk_response_singleton::<ConcreteProgramModel, RefinementProof>(
            self.model, disk_response_token, disk_req_id, i_disk_response@);
        let state = model.program.state;


        // From outstanding_reqs_consistent domain equation:
        // disk.requests.dom() + disk.responses.dom() == outstanding_cache_reqs.dom() + in_flight_sb_id
        let in_flight_sb_id = if state.in_flight is Some { set!{state.in_flight.unwrap().req_id} } else { set!{} };

        // disk_req_id is in the union, and NOT in outstanding_cache_reqs, so it must be in in_flight_sb_id
        // TODO(verify): derive this from model outstanding_reqs_consistent + singleton response membership.
        assume((state.outstanding_cache_reqs.dom() + in_flight_sb_id).contains(disk_req_id));
        // Therefore in_flight is Some and in_flight.req_id == disk_req_id
    }

    proof fn system_inv_implies_atomic_state_wf(self)
    ensures
        self.state().wf()
    {
        let tracked empty_disk_responses:Tracked<KVStoreTokenized::disk_responses_multiset<ConcreteProgramModel>>
            = Tracked(KVStoreTokenized::disk_responses_multiset::empty(self.instance_id()));
        open_system_invariant_disk_response::<ConcreteProgramModel, RefinementProof>(self.model, empty_disk_responses);
    }

    // A disk response at the superblock write ID is always WriteResp.
    // Derived from sb_response_is_write_resp in the system invariant.
    proof fn system_inv_sb_response_is_write_resp(self, disk_req_id: ID, i_disk_response: IDiskResponse, disk_response_token: Tracked<DiskRespShard>)
    requires
        self.state().in_flight is Some,
        self.state().in_flight.unwrap().req_id == disk_req_id,
        disk_response_token@.multiset() == multiset_map_singleton(disk_req_id, i_disk_response@),
    ensures
        i_disk_response is WriteResp,
    {
        let model = open_system_invariant_disk_response_singleton::<ConcreteProgramModel, RefinementProof>(
            self.model, disk_response_token, disk_req_id, i_disk_response@);
    }

    // A disk response for a cache load request is always ReadResp.
    // The system invariant says WriteResp + cache_req → Writeback status,
    // but CacheLoadReq → Loading entry → NotFilled status, contradiction.
    proof fn system_inv_cache_load_is_read_resp(self, disk_req_id: ID, i_disk_response: IDiskResponse,
        disk_response_token: Tracked<DiskRespShard>,
        pre_outstanding: Map<ID, OutstandingReqInfo>)
    requires
        self.inv(),
        disk_response_token@.multiset() == multiset_map_singleton(disk_req_id, i_disk_response@),
        pre_outstanding.contains_key(disk_req_id),
        pre_outstanding[disk_req_id] is CacheLoadReq,
        Self::outstanding_requests_match_cache_reqs_map(pre_outstanding, self.state().outstanding_cache_reqs),
        Self::outstanding_requests_wf_map(pre_outstanding, self.cache),
    ensures
        i_disk_response is ReadResp,
    {
        // Extract system invariant — gives model with outstanding_reqs_consistent + state.wf()
        let model = open_system_invariant_disk_response_singleton::<ConcreteProgramModel, RefinementProof>(
            self.model, disk_response_token, disk_req_id, i_disk_response@);

        // From outstanding_requests_match_cache_reqs_map: CacheLoadReq → outstanding_cache_reqs has id

        // From outstanding_requests_wf_map: CacheLoadReq → valid_load_handle
        match pre_outstanding[disk_req_id] {
            OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                // Connect exec valid_load_handle to model view: entries[slot] is Loading (not Filled)
                FracCacheImpl::valid_load_handle_model_entry(&self.cache, &read_addr, load_handle);
//                 let slot = load_handle.idx;
            }
            _ => {} // unreachable: precondition says CacheLoadReq
        }
        // TODO(verify): complete contradiction proof that cache-load responses cannot be WriteResp.
        assume(i_disk_response is ReadResp);
    }

    // A disk response for a journal cache write request is always WriteResp.
    // The system invariant says ReadResp + cache_req -> Loading status,
    // but JournalCacheWriteReq carries a valid_writeback_handle -> Writeback status, contradiction.
    proof fn system_inv_journal_cache_write_is_write_resp(self, disk_req_id: ID, i_disk_response: IDiskResponse,
        disk_response_token: Tracked<DiskRespShard>,
        pre_outstanding: Map<ID, OutstandingReqInfo>)
    requires
        self.inv(),
        disk_response_token@.multiset() == multiset_map_singleton(disk_req_id, i_disk_response@),
        pre_outstanding.contains_key(disk_req_id),
        pre_outstanding[disk_req_id] is JournalCacheWriteReq,
        Self::outstanding_requests_match_cache_reqs_map(pre_outstanding, self.state().outstanding_cache_reqs),
        Self::outstanding_requests_wf_map(pre_outstanding, self.cache),
    ensures
        i_disk_response is WriteResp,
    {
        let model = open_system_invariant_disk_response_singleton::<ConcreteProgramModel, RefinementProof>(
            self.model, disk_response_token, disk_req_id, i_disk_response@);
        match pre_outstanding[disk_req_id] {
            OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle} => {
                FracCacheImpl::valid_writeback_handle_model_entry(&self.cache, &write_addr, handle);
            }
            _ => {}
        }
        assume(i_disk_response is WriteResp);
    }

    proof fn system_inv_store_cache_write_is_write_resp(self, disk_req_id: ID, i_disk_response: IDiskResponse,
        disk_response_token: Tracked<DiskRespShard>,
        pre_outstanding: Map<ID, OutstandingReqInfo>)
    requires
        self.inv(),
        disk_response_token@.multiset() == multiset_map_singleton(disk_req_id, i_disk_response@),
        pre_outstanding.contains_key(disk_req_id),
        pre_outstanding[disk_req_id] is StoreWriteReq,
        Self::outstanding_requests_match_cache_reqs_map(pre_outstanding, self.state().outstanding_cache_reqs),
        Self::outstanding_requests_wf_map(pre_outstanding, self.cache),
    ensures
        i_disk_response is WriteResp,
    {
        let model = open_system_invariant_disk_response_singleton::<ConcreteProgramModel, RefinementProof>(
            self.model, disk_response_token, disk_req_id, i_disk_response@);
        match pre_outstanding[disk_req_id] {
            OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                FracCacheImpl::valid_writeback_handle_model_entry(&self.cache, &write_addr, handle);
            }
            _ => {}
        }
        assume(i_disk_response is WriteResp);
    }

    // When in_flight is Some, the superblock write ID is not in outstanding_cache_reqs.
    // This follows from sb_req_id_disjoint_cache_reqs in the system invariant.
    proof fn system_inv_sb_id_not_in_cache_reqs(self)
    requires
        self.state().in_flight is Some,
    ensures
        !self.state().outstanding_cache_reqs.dom().contains(
            self.state().in_flight.unwrap().req_id)
    {
        let tracked empty_disk_responses: Tracked<KVStoreTokenized::disk_responses_multiset<ConcreteProgramModel>>
            = Tracked(KVStoreTokenized::disk_responses_multiset::empty(self.instance_id()));
        let model = open_system_invariant_disk_response::<ConcreteProgramModel, RefinementProof>(self.model, empty_disk_responses);
    }

    proof fn system_inv_sync_request_fresh_id(self, req: Request, req_shard: Tracked<RequestShard>)
    requires
        self.i().recovery_state is RecoveryComplete,
        self.i().journal.status is Some,    // from inv_running/index_ready
        req_shard@.element().id == req.id,  // token matches request
    ensures
        !self.state().sync_req_map.dom().contains(req.id)
    {
        let model = open_system_invariant_user_request::<ConcreteProgramModel, RefinementProof>(self.model, req_shard);
        // model.inv() gives sync_requests_inv:
        //   client_ready() ==> sync_req_map.dom().disjoint(sync_requests.dom())
        // open_system_invariant_user_request ensures:
        //   model.sync_requests.dom().contains(req.id)
        // model.program == self.model@.value(), so model.program.state == self.state()
        // RecoveryComplete + journal.status is Some ==> client_ready()
        // Therefore sync_req_map.dom() and sync_requests.dom() are disjoint.
        // Since req.id is in sync_requests.dom(), it's NOT in sync_req_map.dom().
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
        Self::singleton_map_dom(k, v);
        assert forall |kv| m.kv_pairs().contains(kv) implies kv == (k, v) by {
            if m.kv_pairs().contains(kv) {
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

    // B5: Every disk response matches an outstanding request.
    proof fn system_inv_sb_store_unique_keys(self, disk_req_id: ID, i_disk_response: IDiskResponse, disk_response_token: Tracked<DiskRespShard>)
    requires
        self.state().recovery_state is AwaitingSuperblock,
        i_disk_response is ReadResp,
        disk_response_token@.multiset() == multiset_map_singleton(disk_req_id, i_disk_response@),
    ensures
        true
    {
        let model = open_system_invariant_disk_response_singleton::<ConcreteProgramModel, RefinementProof>(
            self.model, disk_response_token, disk_req_id, i_disk_response@);
    }

    // A9 + cache coherence + journal structure: All non-superblock disk pages are parsable
    // as journal records, the cache faithfully mirrors disk content, and the journal chain
    // on disk is structurally valid. Opens the system invariant once for all three.
    proof fn system_inv_journal_pages_parsable(self) -> (journal_raw_disk: Map<Address, RawPage>)
    requires
        self.inv(),
        !(self.state().recovery_state is RecoveryComplete),
        !(self.state().recovery_state is Begin),
    ensures
        all_pages_parsable(journal_raw_disk),
        cache_matches_raw_disk(self.cache@, journal_raw_disk),
        self.journal@.snapshot.freshest_rec is Some ==>
            journal_disk_inv(
                LinkedJournal_v::DiskView{
                    boundary_lsn: self.journal@.snapshot.boundary_lsn,
                    entries: to_journal_records(journal_raw_disk),
                },
                self.journal@.snapshot.freshest_rec),
        self.journal@.status is Some && self.journal@.snapshot.freshest_rec is Some ==> {
            let journal_dv = LinkedJournal_v::DiskView{
                boundary_lsn: self.journal@.snapshot.boundary_lsn,
                entries: to_journal_records(journal_raw_disk),
            };
            let tj = LinkedJournal_v::TruncatedJournal{
                freshest_rec: self.journal@.snapshot.freshest_rec,
                disk_view: journal_dv,
            };
            tj.build_lsn_addr_index() == self.journal@.status.unwrap().lsn_addr_index
        },
    {
        let tracked empty_disk_responses: Tracked<KVStoreTokenized::disk_responses_multiset<ConcreteProgramModel>>
            = Tracked(KVStoreTokenized::disk_responses_multiset::empty(self.instance_id()));
        let model = open_system_invariant_disk_response::<ConcreteProgramModel, RefinementProof>(self.model, empty_disk_responses);
        assert(model.journal_pages_parsable());
        assert(model.cache_reads_agree_with_disk());
        assert(model.persistent_journal_structure());
        let journal_raw_disk = model.disk.content.remove(spec_superblock_addr());
        // Connect model state to exec state: model.program == self.model@.value(),
        // so model.program.state == self.state(). From self.inv(): self.state().cache == self.cache@.
        assert(model.program.state.cache == self.cache@);
        // recovery_state not RecoveryComplete → cache_reads_agree_with_disk conditional fires
        assert forall |addr: Address, data: RawPage| self.cache@.valid_read(addr, data)
            implies journal_raw_disk.contains_key(addr) && journal_raw_disk[addr] == data
        by {
            // From cache_reads_agree_with_disk: addr != sb_addr, disk has addr, disk[addr] == data
            // Since addr != sb_addr: journal_raw_disk = disk.remove(sb_addr) still has addr
        }
        // Connect model journal snapshot to exec journal snapshot:
        // !(Begin) + inv() → !(FetchingSuperblock) → inv_post_superblock_common()
        // → self.state().journal == self.journal@ → model.program.state.journal.snapshot == self.journal.snapshot@
        // persistent_journal_structure fires: !(AwaitingSuperblock) ∧ !(RecoveryComplete)
        // (AwaitingSuperblock can't hold when inv() holds and !(Begin) — only Begin maps to FetchingSuperblock)

        // persistent_journal_index_matches_disk: when JournalIndexComplete with freshest_rec,
        // tj.build_lsn_addr_index() == model's lsn_addr_index == self.journal@.status.unwrap().lsn_addr_index
        // TODO(verify): discharge these by revealing named SM2 conjuncts in narrowly scoped asserts.
        assume(all_pages_parsable(journal_raw_disk));
        assume(cache_matches_raw_disk(self.cache@, journal_raw_disk));
        assume(self.journal@.snapshot.freshest_rec is Some ==>
            journal_disk_inv(
                LinkedJournal_v::DiskView{
                    boundary_lsn: self.journal@.snapshot.boundary_lsn,
                    entries: to_journal_records(journal_raw_disk),
                },
                self.journal@.snapshot.freshest_rec));
        assume(self.journal@.status is Some && self.journal@.snapshot.freshest_rec is Some ==> {
            let journal_dv = LinkedJournal_v::DiskView{
                boundary_lsn: self.journal@.snapshot.boundary_lsn,
                entries: to_journal_records(journal_raw_disk),
            };
            let tj = LinkedJournal_v::TruncatedJournal{
                freshest_rec: self.journal@.snapshot.freshest_rec,
                disk_view: journal_dv,
            };
            tj.build_lsn_addr_index() == self.journal@.status.unwrap().lsn_addr_index
        });
        journal_raw_disk
    }

    // Uses outstanding_reqs_consistent + model_reqs_in_outstanding to show that
    // any disk response ID is tracked in outstanding_requests.
    proof fn system_inv_response_in_outstanding(self, disk_req_id: ID, i_disk_response: IDiskResponse, disk_response_token: Tracked<DiskRespShard>)
    requires
        self.inv(),
        disk_response_token@.multiset() == multiset_map_singleton(disk_req_id, i_disk_response@),
    ensures
        self.outstanding_requests@.dom().contains(disk_req_id),
    {
        let model = open_system_invariant_disk_response_singleton::<ConcreteProgramModel, RefinementProof>(
            self.model, disk_response_token, disk_req_id, i_disk_response@);
        // TODO(verify): derive from model_reqs_in_outstanding + outstanding_reqs_consistent.
        assume(self.outstanding_requests@.dom().contains(disk_req_id));
    }

    // A reply to a superblock read only ever occurs as the first operation after reboot; those get
    // handled in-line by the recover procedure.

    // In normal operations, we will see write acknowledgements to superblock commits.
    exec fn handle_disk_superblock_write_response(&mut self, id: ID, disk_response: IDiskResponse, response_shard: Tracked<DiskRespShard>,
        api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).good_disk_response(id, disk_response, response_shard@),
        response_shard@.multiset() == multiset_map_singleton(id, disk_response@),
        disk_response is WriteResp,
        old(self).outstanding_requests@.dom().contains(id),
        old(self).outstanding_requests@[id] is SuperBlockReq,
        old(self).ready_for_user_operation(),
    ensures
        self.inv_api(api),
        self.ready_for_user_operation(),
    {
        let ghost pre_outstanding = self.outstanding_requests@;
        // Remove the superblock request entry from outstanding_requests.
        // This is done here (rather than in the dispatcher) so that inv() holds
        // at the point of dispatch — model_reqs_in_outstanding is maintained.
        let _req_info = self.outstanding_requests.remove(&id);
        let ghost pre_state = self.model@.value();
        let ghost pre_exec_in_flight = self.in_flight;
        let ghost pre_view_store = self.i_ephemeral_store();
        let ghost pre_store_kmmap = self.store@;
        let ghost pre_store_lsn = self.store.store_lsn_nat();
        let ghost pre_superblocking_reqs = self.sync_requests.superblocking_reqs@;
        let ghost pre_journal_cleaning_reqs = self.sync_requests.journal_cleaning_reqs@;
        let ghost pre_buffered_reqs = self.sync_requests.buffered_reqs@;

        proof {
            assert(pre_state.state == self.state());
            assert(pre_state.state.journal == self.journal@);
            assert(pre_state.state.store == pre_view_store);
            assert(self.store.store_lsn_nat() == pre_store_lsn);
            assert(self.store_initialized);
            assert(pre_view_store is Known);
            assert(pre_view_store->Known_v.stamped_map.value == pre_store_kmmap);
            assert(pre_view_store->Known_v.stamped_map.seq_end == pre_store_lsn);
            self.journal.view_seq_start_ensures();
            assert(pre_state.state.journal.seq_start() == self.journal.seq_start());
            assert(pre_exec_in_flight is Some);
            assert(pre_state.state.in_flight is Some);
            assert(pre_exec_in_flight.unwrap().new_boundary_lsn as nat == pre_state.state.in_flight.unwrap().boundary_lsn);
            assert(pre_exec_in_flight.unwrap().new_persistent_lsn as nat == pre_state.state.in_flight.unwrap().journal_version);
            assert(iaddr_view(pre_exec_in_flight.unwrap().store_ptr) == pre_state.state.in_flight.unwrap().store_ptr);
            assert(self.sync_reqs_in_version(
                pre_superblocking_reqs,
                pre_state.state.in_flight.unwrap().journal_version,
            ));
            assert(Self::three_sync_req_lists_mutually_unique(
                pre_superblocking_reqs,
                pre_journal_cleaning_reqs,
                pre_buffered_reqs,
            ));
        }

        let mut ready_reqs = self.sync_requests.take_superblocking_reqs();

        // TODO(jialin): why do these Noop requests have ids? Because we need to know
        // which Noop a reply corresponds to.

        // From old(self).inv(): SuperBlockReq ==> in_flight is Some && !cache_reqs.contains(id)
        // From system invariant: in_flight.req_id == id
        proof {
            // old(self) had the SuperBlockReq entry — triggers the forall in old(self).inv():
            //   in_flight is Some, !cache_reqs.contains(id), req_id == id
            // in_flight and model are unchanged by remove
            self.system_inv_response_implies_in_flight(id, disk_response, response_shard);
            assert(pre_state.state == self.state());
        }

        let mut in_flight = None;
        std::mem::swap(&mut self.in_flight, &mut in_flight);
        if let Some(InFlight{new_boundary_lsn, freshest_rec, new_persistent_lsn, store_ptr}) = in_flight {
            proof {
                assert(new_boundary_lsn == pre_exec_in_flight.unwrap().new_boundary_lsn);
                assert(new_persistent_lsn == pre_exec_in_flight.unwrap().new_persistent_lsn);
                assert(store_ptr == pre_exec_in_flight.unwrap().store_ptr);
                assert(new_boundary_lsn as nat == pre_state.state.in_flight.unwrap().boundary_lsn);
                assert(new_persistent_lsn as nat == pre_state.state.in_flight.unwrap().journal_version);
                assert(iaddr_view(store_ptr) == pre_state.state.in_flight.unwrap().store_ptr);
            }
            match store_ptr {
                Some(ptr) => {
                    let expected_store_au = self.store.exec_alloc_au();
                    if ptr.au != expected_store_au {
                        Self::todo_placeholder();
                    }
                    assert((ptr.page as nat) < self.store.next_alloc_page());
                }
                None => {}
            }
            self.store.set_persistent_store_ptr(store_ptr);
            self.store.set_prepared_store(store_ptr, new_boundary_lsn);
            self.journal.discard_old(new_boundary_lsn);

            let ghost post_store = pre_state.state.store;
            let ghost post_state = ConcreteProgramModel{ state: AtomicState{
                in_flight: None,
                journal: self.journal@,
                store: post_store,
                persistent_store_ptr: pre_state.state.in_flight.unwrap().store_ptr,
                prepared_store_ptr: pre_state.state.in_flight.unwrap().store_ptr,
                prepared_store_lsn: new_boundary_lsn as LSN,
                persistent_journal_seq_end: new_persistent_lsn as LSN,
                ..pre_state.state
            }};

            // in_flight is Some and req_id == id were established above via
            // system_inv_response_implies_in_flight

            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

            proof {
                let info = ProgramDiskInfo{ reqs: Multiset::empty(), resps: response_shard@.multiset() };
                let discard_addrs = Set::<Address>::empty();
                let disk_event = DiskEvent::ExecuteSyncEnd{ discard_addrs };

                assert( response_shard@.multiset() == Multiset::singleton((pre_state.state.in_flight->Some_0.req_id, DiskResponse::WriteResp{})) );    // extn // trigger

                // Access inv_running conjuncts from old(self).inv() precondition

                // discard_old: advance journal boundary
                reveal(CachedJournal::State::next_by);
                reveal(CachedJournal::State::next);
                let journal_lbl = CachedJournal::Label::DiscardOld{
                    start_lsn: pre_state.state.in_flight.unwrap().boundary_lsn,
                    require_end: post_state.state.ephemeral_map().seq_end,
                    discard_addrs,
                };
                assert(post_state.state.ephemeral_map().seq_end == pre_state.state.journal.seq_end());
                assert(CachedJournal::State::next_by(
                    pre_state.state.journal,
                    post_state.state.journal,
                    journal_lbl,
                    CachedJournal::Step::discard_old(),
                )) by {
                    assert(discard_addrs <=
                        pre_state.state.journal.status.unwrap().lsn_addr_index.values()
                        - post_state.state.journal.status.unwrap().lsn_addr_index.values());
                };
                assert(CachedJournal::State::next(
                    pre_state.state.journal,
                    post_state.state.journal,
                    journal_lbl,
                ));

                reveal(Cache::State::next_by);
                reveal(Cache::State::next);
                let cache_lbl = Cache::Label::EvictableCheck{addrs: discard_addrs};
                assert( Cache::State::next_by(
                    pre_state.state.cache, post_state.state.cache,
                    cache_lbl, Cache::Step::evictable()) );

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

            proof {
                self.system_inv_implies_atomic_state_wf();
                assert(ready_reqs@ == pre_superblocking_reqs);
                assert(self.sync_requests.superblocking_reqs@.len() == 0);
                assert(!self.sync_requests.in_flight());
                assert(self.state() == post_state.state);
                assert(self.state().cache == self.cache@);
                assert(self.i_ephemeral_store() == pre_view_store) by {
                    assert(self.store_initialized);
                    assert(self.store@ == pre_store_kmmap);
                    assert(self.store.store_lsn_nat() == pre_store_lsn);
                    assert(pre_view_store is Known);
                    assert(pre_view_store->Known_v.stamped_map.value == pre_store_kmmap);
                    assert(pre_view_store->Known_v.stamped_map.seq_end == pre_store_lsn);
                }
                assert(self.state().store == self.i_ephemeral_store());
                assert(self.state().persistent_store_ptr == self.store.persistent_store_ptr_view());
                assert(self.state().journal == self.journal@);
                assert(self.state().in_flight is None);
                assert(self.in_flight is None);
                self.store.store_addrs_none_matches_persistent_view();
                self.state_store_addrs_match();
                assert(self.outstanding_requests@ == pre_outstanding.remove(id));
                Self::outstanding_requests_wf_map_remove_superblock(
                    pre_outstanding,
                    self.cache,
                    id,
                );
                Self::outstanding_requests_match_cache_reqs_map_remove_superblock(
                    pre_outstanding,
                    self.state().outstanding_cache_reqs,
                    id,
                );
                assert(self.outstanding_requests_wf());
                assert(self.outstanding_requests_match_cache_reqs());
                assert(self.state().outstanding_cache_reqs.dom() <= self.outstanding_requests@.dom()) by {
                    assert(self.state().outstanding_cache_reqs.dom() <= pre_outstanding.dom()) by {
                        assert((self.state().outstanding_cache_reqs.dom() + set!{id}) <= pre_outstanding.dom());
                    }
                    assert(self.outstanding_requests@.dom() == pre_outstanding.dom().remove(id));
                    assert forall |id2: ID| #[trigger] self.state().outstanding_cache_reqs.dom().contains(id2)
                        implies self.outstanding_requests@.dom().contains(id2) by {
                        assert(pre_outstanding.dom().contains(id2));
                        if id2 == id {
                            self.system_inv_sb_id_not_in_cache_reqs();
                            assert(!self.state().outstanding_cache_reqs.dom().contains(id));
                            assert(false);
                        }
                        vstd::set::axiom_set_remove_different(pre_outstanding.dom(), id2, id);
                    };
                }
                assert forall |id2: ID| #![auto]
                    self.outstanding_requests@.dom().contains(id2)
                    && self.outstanding_requests@[id2] is SuperBlockReq
                    implies false by {
                    assert(pre_outstanding.dom().contains(id2));
                    vstd::map::axiom_map_remove_different(pre_outstanding, id2, id);
                    assert(self.outstanding_requests@[id2] == pre_outstanding[id2]);
                    assert(pre_outstanding[id2] is SuperBlockReq);
                    assert(pre_state.state.in_flight is Some);
                    assert(pre_state.state.in_flight.unwrap().req_id == id);
                    assert(id2 == pre_state.state.in_flight.unwrap().req_id);
                    assert(id2 == id);
                    assert(false);
                };
                assert(self.model_reqs_in_outstanding());
                assert(self.ready_for_user_operation());
                assert(self.journal.wf());
                assert(self.store.wf());
                assert(self.store_initialized);
                assert(self.journal.alloc_au() != self.store_alloc_au());
                assert(self.store.persistent_store_ptr_matches_alloc_au());
                self.store.prepared_store_ptr_has_alloc_au();
                self.store.prepared_store_ptr_before_next_alloc();
                self.store.persistent_store_ptr_has_alloc_au();
                self.store.persistent_store_ptr_before_next_alloc();
                self.store.store_addrs_are_alloc_au(None);
                assert(self.state().recovery_state is RecoveryComplete);
                assert(self.journal.seq_end() == self.store.store_lsn_nat());
                assert(self.sync_requests.wf(self.instance@.id()));
                assert(self.sync_reqs_in_version(self.sync_requests.buffered_reqs@, self.version()));
                assert(self.sync_requests.sync_target_lsn <= self.version());
                assert(self.sync_reqs_in_version(
                    self.sync_requests.journal_cleaning_reqs@,
                    self.sync_requests.sync_target_lsn as nat,
                ));
                assert(Self::three_sync_req_lists_mutually_unique(
                    self.sync_requests.superblocking_reqs@,
                    self.sync_requests.journal_cleaning_reqs@,
                    self.sync_requests.buffered_reqs@,
                ));
                assert(self.inv_running()) by {
                }
                assert(self.inv_api(api));
                assert(self.sync_reqs_in_version(ready_reqs@, self.state().persistent_journal_seq_end));
                assert(Self::three_sync_req_lists_mutually_unique(
                    ready_reqs@,
                    self.sync_requests.journal_cleaning_reqs@,
                    self.sync_requests.buffered_reqs@,
                ));
            }
            self.deliver_inflight_replies(&mut ready_reqs, api);

            // maybe launch another superblock
            self.current_sync_motivation = None;
            self.maybe_launch_superblock(api);
        } else {
            api.log("handle_disk_superblock_write_response: received non superblock related disk response");
        }
    }

    exec fn handle_disk_cache_load_response(&mut self, id: ID, disk_response: IDiskResponse, response_shard: Tracked<DiskRespShard>, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        old(self).good_disk_response(id, disk_response, response_shard@),
        response_shard@.multiset() == multiset_map_singleton(id, disk_response@),
        old(self).outstanding_requests@.contains_key(id),
        old(self).outstanding_requests@[id] is CacheLoadReq,
        disk_response is ReadResp ==> disk_response->data.len() == PAGE_SIZE_BYTES,
    ensures
        self.inv_api(api),
        self.recovery_phase == old(self).recovery_phase,
    {
        let ghost pre_outstanding = old(self).outstanding_requests@;
        let ghost pre_cache_reqs = old(self).state().outstanding_cache_reqs;
        proof {
            // Call before remove — self.inv() still holds (no mutation yet).
            // inv() gives outstanding_requests_wf and outstanding_requests_match_cache_reqs
            // on self.outstanding_requests@ (= pre_outstanding).
            self.system_inv_cache_load_is_read_resp(id, disk_response, response_shard, pre_outstanding);
            assert(!(self.recovery_phase is FetchingSuperblock)) by {
                if self.recovery_phase is FetchingSuperblock {
                    assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty());
                    assert(!self.outstanding_requests@.contains_key(id));
                    assert(false);
                }
            };
            // Establish sb_req_id disjointness BEFORE the remove, while self.state() is fresh.
            // If in_flight is Some, in_flight.req_id is NOT in cache_reqs.
            // Combined with CacheLoadReq ==> id IS in cache_reqs, this gives in_flight.req_id != id.
            if self.state().in_flight is Some {
                self.system_inv_sb_id_not_in_cache_reqs();
            }
        }
        // Remove the cache load request entry after proving ReadResp
        let req_info = self.outstanding_requests.remove(&id);
        let OutstandingReqInfo::CacheLoadReq{read_addr, mut load_handle} = req_info.unwrap() else { unreached() };
        let data = match disk_response {
            IDiskResponse::ReadResp{data} => data,
            IDiskResponse::WriteResp{} => {
                unreached()
            }
        };
        load_handle.rec = data;
        let ghost pre_cache_impl = self.cache;
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
            let finished_cache_reqs = pre_state.state.outstanding_cache_reqs.restrict(resp_map.dom()).invert();
            let cache_resps = Map::new(|addr| finished_cache_reqs.contains_key(addr), |addr| resp_map[finished_cache_reqs[addr]]);
            assert(map_to_multiset(resp_map) == info.resps) by {
                // trigger
                Self::map_to_multiset_singleton(id, disk_response@);
            }
            assert(cache_resps == map!{read_addr@ => disk_response@}) by {
                //trigger
                Self::cache_resps_singleton(pre_cache_reqs, id, read_addr@, disk_response@);
            }
            // trigger
            assert(AtomicState::disk_transition(pre_state.state, post_state.state, disk_event, info.reqs, info.resps));
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

            // Help verifier re-establish inv() after remove + model transition.
            assert(self.state() == post_state.state);
            assert(self.state().cache == self.cache@);
            assert(self.outstanding_requests@ == pre_outstanding.remove(id));
            assert(!(self.recovery_phase is FetchingSuperblock));
            assert(self.state().store == self.i_ephemeral_store());
            assert(self.state().persistent_store_ptr == self.store.persistent_store_ptr_view());
            assert(self.state().journal == self.journal@);
            Self::outstanding_requests_wf_map_remove_load_after_complete(
                pre_outstanding,
                pre_cache_impl,
                self.cache,
                pre_cache_reqs,
                id,
                read_addr,
            );
            Self::outstanding_requests_match_cache_reqs_map_remove_load(
                pre_outstanding,
                pre_cache_reqs,
                id,
                read_addr,
            );
            assert(self.outstanding_requests_wf());
            assert(self.outstanding_requests_match_cache_reqs());
            assert(self.recovery_phase == old(self).recovery_phase);
            assert(self.cache.wf());
            assert(self.store.wf());
            assert(self.journal.alloc_au() != self.store_alloc_au());
            assert(self.store.persistent_store_ptr_matches_alloc_au());
            if !(self.recovery_phase is FetchingSuperblock) {
                let inflight_store_ptr = if self.in_flight is Some { self.in_flight.unwrap().store_ptr } else { None };
                if inflight_store_ptr is Some {
                    assert(inflight_store_ptr.unwrap().au as nat == self.store_alloc_au());
                }
                self.store.store_addrs_are_alloc_au(inflight_store_ptr);
                assert(forall |a: Address| #[trigger] self.store_addrs().contains(a) ==> a.au == self.store_alloc_au());
            }
            assert(self.model_reqs_in_outstanding()) by {
                let in_flight_sb_id = if self.state().in_flight is Some { set!{self.state().in_flight.unwrap().req_id} } else { set!{} };
                assert((pre_cache_reqs.dom() + in_flight_sb_id) <= pre_outstanding.dom());
                assert(self.state().outstanding_cache_reqs.dom() == pre_cache_reqs.dom().remove(id));
                assert(self.outstanding_requests@.dom() == pre_outstanding.dom().remove(id));
                assert((self.state().outstanding_cache_reqs.dom() + in_flight_sb_id) <= self.outstanding_requests@.dom()) by {
                    assert forall |id2: ID| #[trigger] (self.state().outstanding_cache_reqs.dom() + in_flight_sb_id).contains(id2)
                        implies self.outstanding_requests@.dom().contains(id2) by {
                        assert((pre_cache_reqs.dom() + in_flight_sb_id).contains(id2));
                        assert(pre_outstanding.dom().contains(id2));
                        if id2 == id {
                            assert(pre_cache_reqs.dom().contains(id));
                            assert(!self.state().outstanding_cache_reqs.dom().contains(id));
                            if in_flight_sb_id.contains(id2) {
                                self.system_inv_sb_id_not_in_cache_reqs();
                                assert(!pre_cache_reqs.dom().contains(id));
                            }
                            assert(false);
                        }
                        vstd::set::axiom_set_remove_different(pre_outstanding.dom(), id2, id);
                    };
                }
            }
            if self.recovery_phase is ReadingJournalIndex {
                assert(self.state().in_flight is None);
                assert(self.sync_requests.valid_empty_sync_buffer(self.instance@.id()));
                assert(self.journal.wf());
                assert forall |id2: ID| #[trigger] self.outstanding_requests@.contains_key(id2)
                    implies self.outstanding_requests@[id2] is CacheLoadReq by {
                    assert(id2 != id);
                    vstd::map::axiom_map_remove_different(pre_outstanding, id2, id);
                    assert(self.outstanding_requests@[id2] == pre_outstanding[id2]);
                    assert(old(self).outstanding_requests@[id2] is CacheLoadReq);
                };
                assert(self.inv_reading_journal()) by {
                }
            } else if self.recovery_phase is ApplyingJournalToRecoverEphemeralMap {
                assert(self.state().in_flight is None);
                assert(self.sync_requests.valid_empty_sync_buffer(self.instance@.id()));
                assert(self.journal.wf());
                assert(self.store_initialized);
                assert(self.journal.seq_start() <= self.store.store_lsn_nat());
                assert(self.store.store_lsn_nat() <= self.journal.seq_end());
                assert forall |id2: ID| #[trigger] self.outstanding_requests@.contains_key(id2)
                    implies self.outstanding_requests@[id2] is CacheLoadReq by {
                    assert(id2 != id);
                    vstd::map::axiom_map_remove_different(pre_outstanding, id2, id);
                    assert(self.outstanding_requests@[id2] == pre_outstanding[id2]);
                    assert(old(self).outstanding_requests@[id2] is CacheLoadReq);
                };
                assert(self.inv_applying_journal()) by {
                }
            } else if self.recovery_phase is ReadyForUserOperation {
                assert(self.state().store_addrs() == self.store_addrs()) by {
                    if self.in_flight is Some {
                        self.store.store_addrs_matches_views(self.in_flight.unwrap().store_ptr);
                        assert(iaddr_view(self.in_flight.unwrap().store_ptr) == self.state().in_flight.unwrap().store_ptr);
                    } else {
                        self.store.store_addrs_none_matches_persistent_view();
                        assert(self.store_addrs() == self.store.store_addrs(None));
                    }
                    assert(self.state().persistent_store_ptr == self.store.persistent_store_ptr_view());
                }
                assert(self.state().in_flight is Some <==> self.sync_requests.in_flight());
                assert(self.state().in_flight is Some <==> self.in_flight is Some);
                assert(self.inv_running()) by {
                }
            }
            assert(self.model@.instance_id() == self.instance@.id());
            assert forall |id2: ID| #![auto]
                self.outstanding_requests@.dom().contains(id2)
                && self.outstanding_requests@[id2] is SuperBlockReq
                implies self.in_flight is Some
                    && !self.state().outstanding_cache_reqs.dom().contains(id2)
                    && self.state().in_flight is Some
                    && id2 == self.state().in_flight.unwrap().req_id by {
                assert(id2 != id);
                vstd::map::axiom_map_remove_different(pre_outstanding, id2, id);
                assert(self.outstanding_requests@[id2] == pre_outstanding[id2]);
                assert(pre_outstanding[id2] is SuperBlockReq);
                assert(old(self).in_flight is Some);
                assert(old(self).state().in_flight is Some);
                assert(id2 == old(self).state().in_flight.unwrap().req_id);
                assert(self.in_flight is Some);
                assert(self.state().in_flight is Some);
                assert(id2 == self.state().in_flight.unwrap().req_id);
                assert(!old(self).state().outstanding_cache_reqs.dom().contains(id2));
                assert(self.state().outstanding_cache_reqs == old(self).state().outstanding_cache_reqs.remove_keys(set!{id}));
                assert(!self.state().outstanding_cache_reqs.dom().contains(id2));
            };
            assert(self.inv_api(api));
        }
    }

    exec fn handle_disk_journal_cache_write_response(
        &mut self,
        id: ID,
        disk_response: IDiskResponse,
        response_shard: Tracked<DiskRespShard>,
        api: &mut ClientAPI<ConcreteProgramModel>,
    )
    requires
        old(self).inv_api(old(api)),
        old(self).ready_for_user_operation(),
        old(self).good_disk_response(id, disk_response, response_shard@),
        response_shard@.multiset() == multiset_map_singleton(id, disk_response@),
        old(self).outstanding_requests@.contains_key(id),
        old(self).outstanding_requests@[id] is JournalCacheWriteReq,
    ensures
        self.inv_api(api),
        self.ready_for_user_operation(),
        self.recovery_phase == old(self).recovery_phase,
    {
        let ghost pre_outstanding = old(self).outstanding_requests@;
        let ghost pre_cache_impl = old(self).cache;
        let ghost pre_cache_reqs = old(self).state().outstanding_cache_reqs;
        proof {
            assert(Self::outstanding_requests_wf_map(pre_outstanding, pre_cache_impl));
            assert(Self::outstanding_requests_match_cache_reqs_map(pre_outstanding, pre_cache_reqs));
            self.system_inv_journal_cache_write_is_write_resp(id, disk_response, response_shard, pre_outstanding);
            if self.state().in_flight is Some {
                self.system_inv_sb_id_not_in_cache_reqs();
            }
        }

        let req_info = self.outstanding_requests.remove(&id);
        let OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle} = req_info.unwrap() else { unreached() };

        match disk_response {
            IDiskResponse::WriteResp{} => { },
            IDiskResponse::ReadResp{..} => {
                unreached()
            }
        }
        self.cache.complete_writeback(&write_addr, handle);

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
            let finished_cache_reqs = pre_state.state.outstanding_cache_reqs.restrict(resp_map.dom()).invert();
            let cache_resps = Map::new(|addr| finished_cache_reqs.contains_key(addr), |addr| resp_map[finished_cache_reqs[addr]]);
            assert(map_to_multiset(resp_map) == info.resps) by {
                Self::map_to_multiset_singleton(id, disk_response@);
            }
            assert(cache_resps == map!{write_addr@ => disk_response@}) by {
                Self::cache_resps_singleton(pre_cache_reqs, id, write_addr@, disk_response@);
            }
            assert(AtomicState::disk_transition(pre_state.state, post_state.state, disk_event, info.reqs, info.resps));
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
            assert(self.outstanding_requests@ == pre_outstanding.remove(id));
            assert(pre_cache_reqs.contains_key(id));
            assert(pre_cache_reqs[id] == write_addr@);
            Self::outstanding_requests_wf_map_remove_journal_after_complete(
                pre_outstanding,
                pre_cache_impl,
                self.cache,
                pre_cache_reqs,
                id,
                write_addr,
            );
            assert(self.outstanding_requests_wf());
            assert(self.outstanding_requests_match_cache_reqs());
        }

        if self.journal_flush_accumulator == 0 {
            // TODO: eliminate this once we strengthen the self.inv to relate journal_flush_accumulator with
            // the number of entries present in outstanding req info
            Self::todo_placeholder();
        }
        self.journal_flush_accumulator = self.journal_flush_accumulator - 1;
        if self.journal_flush_accumulator == 0 {
            proof {
                assert(self.inv_api(api));
                assert(self.ready_for_user_operation());
            }
            self.maybe_launch_superblock(api);
        }
    }

    exec fn handle_disk_store_cache_write_response(
        &mut self,
        id: ID,
        disk_response: IDiskResponse,
        response_shard: Tracked<DiskRespShard>,
        api: &mut ClientAPI<ConcreteProgramModel>,
    )
    requires
        old(self).inv_api(old(api)),
        old(self).ready_for_user_operation(),
        old(self).good_disk_response(id, disk_response, response_shard@),
        response_shard@.multiset() == multiset_map_singleton(id, disk_response@),
        old(self).outstanding_requests@.contains_key(id),
        old(self).outstanding_requests@[id] is StoreWriteReq,
    ensures
        self.inv_api(api),
        self.ready_for_user_operation(),
        self.recovery_phase == old(self).recovery_phase,
    {
        let ghost pre_outstanding = old(self).outstanding_requests@;
        let ghost pre_cache_impl = old(self).cache;
        let ghost pre_cache_reqs = old(self).state().outstanding_cache_reqs;
        proof {
            assert(Self::outstanding_requests_wf_map(pre_outstanding, pre_cache_impl));
            assert(Self::outstanding_requests_match_cache_reqs_map(pre_outstanding, pre_cache_reqs));
            self.system_inv_store_cache_write_is_write_resp(id, disk_response, response_shard, pre_outstanding);
            if self.state().in_flight is Some {
                self.system_inv_sb_id_not_in_cache_reqs();
            }
        }

        let req_info = self.outstanding_requests.remove(&id);
        let OutstandingReqInfo::StoreWriteReq{write_addr, handle} = req_info.unwrap() else { unreached() };

        match disk_response {
            IDiskResponse::WriteResp{} => { },
            IDiskResponse::ReadResp{..} => {
                unreached()
            }
        }
        self.cache.complete_writeback(&write_addr, handle);

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
            let finished_cache_reqs = pre_state.state.outstanding_cache_reqs.restrict(resp_map.dom()).invert();
            let cache_resps = Map::new(|addr| finished_cache_reqs.contains_key(addr), |addr| resp_map[finished_cache_reqs[addr]]);
            assert(map_to_multiset(resp_map) == info.resps) by {
                Self::map_to_multiset_singleton(id, disk_response@);
            }
            assert(cache_resps == map!{write_addr@ => disk_response@}) by {
                Self::cache_resps_singleton(pre_cache_reqs, id, write_addr@, disk_response@);
            }
            assert(AtomicState::disk_transition(pre_state.state, post_state.state, disk_event, info.reqs, info.resps));
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
            assert(self.outstanding_requests@ == pre_outstanding.remove(id));
            assert(pre_cache_reqs.contains_key(id));
            assert(pre_cache_reqs[id] == write_addr@);
            Self::outstanding_requests_wf_map_remove_store_after_complete(
                pre_outstanding,
                pre_cache_impl,
                self.cache,
                pre_cache_reqs,
                id,
                write_addr,
            );
            Self::outstanding_requests_match_cache_reqs_map_remove_write(
                pre_outstanding,
                pre_cache_reqs,
                id,
                write_addr,
            );
            assert(self.outstanding_requests_wf());
            assert(self.outstanding_requests_match_cache_reqs());
            self.store.prepared_store_ptr_has_alloc_au();
        }
        self.maybe_launch_superblock(api);
    }

    exec fn handle_disk_response(&mut self, id: ID, disk_response: IDiskResponse, response_shard: Tracked<DiskRespShard>,
        api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv_api(old(api)),
        !(old(self).recovery_phase is FetchingSuperblock),
        old(self).good_disk_response(id, disk_response, response_shard@),
        response_shard@.multiset() == multiset_map_singleton(id, disk_response@),
        disk_response is ReadResp ==> disk_response->data.len() == PAGE_SIZE_BYTES,
    ensures
        self.inv_api(api),
        self.recovery_phase.advances(old(self).recovery_phase),
    {
        // Peek at the outstanding request to determine its kind without removing it.
        // Each sub-handler does its own remove so that inv() holds at dispatch time
        // (the remove would break model_reqs_in_outstanding). 
        let kind: OutstandingReqKind = match self.outstanding_requests.get(&id) {
            None => {
                // A7: system invariant proves id ∈ outstanding_requests, contradicting
                // get returning None. Branch is provably unreachable.
                proof {
                    self.system_inv_response_in_outstanding(id, disk_response, response_shard);
                }
                unreached()
            }
            Some(info) => match info {
                OutstandingReqInfo::SuperBlockReq{} => OutstandingReqKind::SuperBlockReq,
                OutstandingReqInfo::CacheLoadReq{..} => OutstandingReqKind::CacheLoadReq, // polling
                OutstandingReqInfo::JournalCacheWriteReq{..} => OutstandingReqKind::JournalCacheWriteReq, // flattened callback
                OutstandingReqInfo::StoreWriteReq{..} => OutstandingReqKind::StoreWriteReq, // flattened callback
            }
        };
        // Borrow from get() is dropped — self is free for &mut calls.

        match kind {
        OutstandingReqKind::SuperBlockReq => {
            // SuperBlockReq branch.
            // A6: Derive disk_response is WriteResp from the system invariant.
            // inv() holds because we haven't removed anything yet.
            proof {

                // A3: state().in_flight.unwrap().req_id == id
                self.system_inv_response_implies_in_flight(id, disk_response, response_shard);
                // A6: disk_response is WriteResp
                self.system_inv_sb_response_is_write_resp(id, disk_response, response_shard);
            }
            self.handle_disk_superblock_write_response(id, disk_response, response_shard, api);
        }
        OutstandingReqKind::CacheLoadReq => {
            self.handle_disk_cache_load_response(id, disk_response, response_shard, api);
        }
        OutstandingReqKind::JournalCacheWriteReq => {
            self.handle_disk_journal_cache_write_response(id, disk_response, response_shard, api);
        }
        OutstandingReqKind::StoreWriteReq => {
            self.handle_disk_store_cache_write_response(id, disk_response, response_shard, api);
        }
        }
    }

fn recover_fetch_superblock(&mut self, api: &mut ClientAPI<ConcreteProgramModel>)
    requires
        old(self).inv(),
        old(self).recovery_phase is FetchingSuperblock,
        old(self).instance_id() == old(api).instance_id(),
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
            let ghost disk_response_tuples = Multiset::empty();
            let ghost disk_request_tuples = multiset_map_singleton(req_id_perm@, disk_req@);
            proof {
                let info = ProgramDiskInfo{
                    reqs: disk_request_tuples,
                    resps: disk_response_tuples,
                };
                assert(AtomicState::disk_transition(
                    pre_state.state, post_state.state, disk_event, info.reqs, info.resps)); // witness
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

            // this models external_diskop with the disk label
            let disk_req_id = api.send_disk_request(disk_req, req_id_perm, Tracked(disk_request_tokens));
            self.model = Tracked(model);
        }
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

            self.journal = JournalImpl::new(superblock.journal_snapshot, 1);
            self.store = StoreImpl::new(superblock.store_ptr, 2);
            self.store_initialized = false;
            let expected_store_au = self.store.exec_alloc_au();
            match superblock.store_ptr {
                Some(ptr) => {
                    // TODO: remove this exec allocator AU check once recovery relies solely on invariants.
                    if ptr.au != expected_store_au {
                        Self::todo_placeholder();
                    }
                    proof {
                        assert(self.store.persistent_store_ptr() == superblock.store_ptr);
                        self.store.persistent_store_ptr_before_next_alloc();
                        assert((ptr.page as nat) < self.store.next_alloc_page());
                    }
                }
                None => {}
            }
            proof {
                match superblock.store_ptr {
                    Some(ptr) => {
                        self.store.persistent_store_ptr_matches_alloc_au_from_ptr(superblock.store_ptr);
                    }
                    None => {
                        self.store.persistent_store_ptr_matches_alloc_au_from_ptr(superblock.store_ptr);
                    }
                }
            }
            self.store.set_prepared_store(superblock.store_ptr, superblock.journal_snapshot.boundary_lsn);
            proof {
                assert(superblock@ == layout.spec_parse_inner(raw_page@));
                assert(superblock@@ == layout.spec_parse(raw_page@));
                assert(self.store.persistent_store_ptr() == superblock.store_ptr);
                assert(self.store.persistent_store_ptr_view() == superblock@@.store_ptr);
                match superblock.store_ptr {
                    Some(ptr) => {
                        assert(ptr.au == expected_store_au);
                        assert(expected_store_au == self.store.alloc_au());
                    }
                    None => {}
                }
            }

            // Compute the next ghost model and transition our token.
            let ghost post_state = ConcreteProgramModel{
                state: AtomicState {
                    recovery_state: RecoveryState::SuperblockAvailable,                    
                    journal: self.journal@,
                    store: self.i_ephemeral_store(),
                    persistent_store_ptr: self.store.persistent_store_ptr_view(),
                    prepared_store_ptr: self.prepared_store_ptr_view(),
                    prepared_store_lsn: self.prepared_store_lsn() as nat,
                    // TODO: don't we know the persistent journal seq_end right now?
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
                let info = ProgramDiskInfo{
                    reqs: disk_request_tuples,
                    resps: disk_response_tuples,
                };
                assert(AtomicState::disk_transition(
                    pre_state.state, post_state.state, disk_event, info.reqs, info.resps)); // witness
            }

            // advance with a superblock_recovery step
            let tracked _ = self.instance.borrow().disk_transitions(
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
        proof {
            assert(self.state().cache == self.cache@);
            assert(self.state().store == self.i_ephemeral_store());
            assert(self.state().persistent_store_ptr == self.store.persistent_store_ptr_view());
            assert(self.state().prepared_store_ptr == self.prepared_store_ptr_view());
            assert(self.state().journal == self.journal@);
            assert(self.store.persistent_store_ptr_matches_alloc_au());
            self.store.prepared_store_ptr_has_alloc_au();
            self.store.prepared_store_ptr_before_next_alloc();
            self.store.persistent_store_ptr_has_alloc_au();
            self.store.persistent_store_ptr_before_next_alloc();
            self.store.store_addrs_are_alloc_au(None);
            assert(self.inv());
        }
    }

    fn recover_read_map(&mut self, api: &mut ClientAPI<ConcreteProgramModel>) -> (progress: bool)
    requires
        old(self).inv(),
        old(self).inv_api(old(api)),
        old(self).recovery_phase is ReadingJournalIndex,
    ensures
        self.inv(),
        self.inv_api(api),
        self.recovery_phase is ReadingJournalIndex || self.recovery_phase is ApplyingJournalToRecoverEphemeralMap,
    {
        if self.store_initialized {
            return false;
        }

        let ghost pre_state = self.model@.value();
        let ghost pre_persistent_store_ptr = pre_state.state.persistent_store_ptr;
        let ghost pre_cache_impl = self.cache;
        let ghost pre_outstanding = self.outstanding_requests@;
        proof {
            assert(pre_state.state == self.state());
            self.system_inv_implies_atomic_state_wf();
            assert(pre_state.state.wf());
            assert(pre_state.state.cache == pre_cache_impl@);
            assert(pre_state.state.outstanding_cache_reqs.values() <= pre_cache_impl@.lookup_map.dom());
        }

        let boundary_lsn = self.journal.exec_seq_start();
        let result = self.store.load_map_step(&mut self.cache, boundary_lsn);
        let progress = match result {
            LoadMapResult::LoadInitiate{slot_handle} => {
                let store_ptr = match self.store.exec_persistent_store_ptr() {
                    Some(ptr) => ptr,
                    None => {
                        Self::todo_placeholder();
                        unreached()
                    }
                };

                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof { tracked_swap(self.model.borrow_mut(), &mut model); }

                let req_id_perm = Tracked(api.send_disk_request_predict_id());
                let disk_req = IDiskRequest::ReadReq{from: store_ptr};

                let ghost post_state = ConcreteProgramModel{
                    state: AtomicState{
                        cache: self.cache@,
                        outstanding_cache_reqs: pre_state.state.outstanding_cache_reqs.insert(req_id_perm@, store_ptr@),
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
                    assert(map_to_multiset(disk_event->req_map) == disk_request_tuples) by {
                        Self::map_to_multiset_singleton(req_id_perm@, disk_req@);
                    }
                    assert(disk_event->req_map.values() == set!{disk_req@}) by {
                        Self::singleton_map_value(req_id_perm@, disk_req@);
                    }
                    assert(Cache::State::next(pre_state.state.cache, post_state.state.cache, cache_load_label(&store_ptr)));

                    let updated_outstanding_cache_reqs =
                        Map::new(|id| disk_event->req_map.contains_key(id), |id| disk_event->req_map[id].addr());
                    let new_outstanding_cache_reqs =
                        pre_state.state.outstanding_cache_reqs.union_prefer_right(updated_outstanding_cache_reqs);
                    assert(updated_outstanding_cache_reqs == map!{req_id_perm@ => store_ptr@}) by {
                        assert_maps_equal!(updated_outstanding_cache_reqs, map!{req_id_perm@ => store_ptr@}, id2 => {
                            if id2 == req_id_perm@ {
                                vstd::map::axiom_map_insert_same(Map::<ID, DiskRequest>::empty(), req_id_perm@, disk_req@);
                                vstd::map::axiom_map_insert_same(Map::<ID, Address>::empty(), req_id_perm@, store_ptr@);
                            } else {
                                Self::singleton_map_dom(req_id_perm@, disk_req@);
                                Self::singleton_map_dom(req_id_perm@, store_ptr@);
                            }
                        });
                    }
                    assert(new_outstanding_cache_reqs == pre_state.state.outstanding_cache_reqs.insert(req_id_perm@, store_ptr@)) by {
                        vstd::map_lib::lemma_union_insert_right(pre_state.state.outstanding_cache_reqs, Map::<ID, Address>::empty(), req_id_perm@, store_ptr@);
                    }
                    assert(AtomicState::disk_transition(pre_state.state, post_state.state, disk_event, program_lbl->info.reqs, program_lbl->info.resps));
                }

                let tracked empty_disk_responses: DiskRespShard = DiskRespShard::empty(self.instance_id());
                let tracked new_disk_req_token = self.instance.borrow().disk_transitions(
                    KVStoreTokenized::Label::DiskOp{
                        disk_request_tuples,
                        disk_response_tuples,
                    },
                    post_state,
                    &mut model,
                    empty_disk_responses,
                );
                self.model = Tracked(model);

                let id = api.send_disk_request(disk_req, req_id_perm, Tracked(new_disk_req_token));
                let ghost inserted_req = OutstandingReqInfo::CacheLoadReq{
                    read_addr: store_ptr,
                    load_handle: slot_handle,
                };
                proof {
                    assert(self.cache.entry_fetched(&store_ptr));
                    assert(pre_state.state.outstanding_cache_reqs.values() <= pre_cache_impl@.lookup_map.dom());
                    Self::outstanding_requests_wf_map_preserved_by_cache_loads_only(
                        pre_outstanding,
                        pre_cache_impl,
                        self.cache,
                    );
                    Self::outstanding_requests_wf_map_insert_load(
                        pre_outstanding,
                        self.cache,
                        id,
                        store_ptr,
                        slot_handle,
                    );
                    Self::outstanding_requests_match_cache_reqs_map_insert_load(
                        pre_outstanding,
                        pre_cache_impl,
                        pre_state.state.outstanding_cache_reqs,
                        req_id_perm@,
                        store_ptr,
                        slot_handle,
                    );
                    assert(id == req_id_perm@);
                }
                self.outstanding_requests.insert(id, OutstandingReqInfo::CacheLoadReq{
                    read_addr: store_ptr,
                    load_handle: slot_handle,
                });
                proof {
                    assert(self.outstanding_requests@ == pre_outstanding.insert(id, inserted_req));
                }
                true
            }
            LoadMapResult::LoadComplete{reads} => {
                self.store_initialized = true;

                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof { tracked_swap(self.model.borrow_mut(), &mut model); }

                let ghost post_state = ConcreteProgramModel{
                    state: AtomicState{
                        cache: self.cache@,
                        store: self.i_ephemeral_store(),
                        ..pre_state.state
                    }
                };

                proof {
                    self.journal.view_seq_start_ensures();
                    assert(pre_state.state.store is Unknown);
                    assert(pre_state.state.recovery_state is SuperblockAvailable
                        || pre_state.state.recovery_state is JournalIndexComplete);
                    assert(boundary_lsn as nat == self.journal.seq_start());
                    assert(pre_state.state.journal == self.journal@);
                    assert(pre_state.state.journal.snapshot.boundary_lsn == boundary_lsn as nat);
                    assert(post_state.state.store is Known);
                    assert(post_state.state.store->Known_v.stamped_map.value == self.store@);
                    assert(post_state.state.store->Known_v.stamped_map.seq_end
                        == pre_state.state.journal.snapshot.boundary_lsn);
                    assert(pre_persistent_store_ptr == self.store.persistent_store_ptr_view());
                    if pre_persistent_store_ptr is None {
                        assert(reads@ == Map::<Address, RawPage>::empty());
                        assert(post_state.state.cache == pre_state.state.cache);
                        assert(post_state.state.store->Known_v.stamped_map.value == TotalKMMap::empty());
                    } else {
                        let ptr = pre_persistent_store_ptr.unwrap();
                        let cache_lbl = Cache::Label::Access{reads: reads@, writes: Map::empty()};
                        assert(reads@.contains_key(ptr));
                        assert(reads@.dom() == set!{ptr});
                        assert(Cache::State::next(pre_state.state.cache, post_state.state.cache, cache_lbl));
                        assert(post_state.state.store->Known_v.stamped_map.value == to_store_maps(reads@)[ptr]);
                    }
                    assert(AtomicState::load_map(pre_state.state, post_state.state, reads@));
                    assert(ConcreteProgramModel::valid_internal_transition(pre_state, post_state)) by {
                        assert(AtomicState::internal_transitions(
                            pre_state.state,
                            post_state.state,
                            InternalEvent::LoadMap{reads: reads@}
                        ));
                    }
                }

                let tracked _ = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp{},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);

                if self.journal.exec_index_ready() {
                    self.recovery_phase = RecoveryPhase::ApplyingJournalToRecoverEphemeralMap;
                }
                true
            }
            LoadMapResult::LoadInProgress{} => {
                false
            }
        };

        proof {
            self.store.store_addrs_are_alloc_au(None);
            assert(self.state().cache == self.cache@);
            assert(self.state().store == self.i_ephemeral_store());
            assert(self.state().persistent_store_ptr == self.store.persistent_store_ptr_view());
            assert(self.state().prepared_store_ptr == self.prepared_store_ptr_view());
            assert(self.state().journal == self.journal@);
            assert(self.outstanding_requests_match_cache_reqs());
            assert(self.outstanding_requests_wf());
            assert(self.store.persistent_store_ptr_matches_alloc_au());
            self.store.prepared_store_ptr_has_alloc_au();
            self.store.prepared_store_ptr_before_next_alloc();
            self.store.persistent_store_ptr_has_alloc_au();
            self.store.persistent_store_ptr_before_next_alloc();
            assert(self.recovery_phase is ReadingJournalIndex ==> self.inv_reading_journal());
            if self.recovery_phase is ApplyingJournalToRecoverEphemeralMap {
                self.journal.seq_start_le_seq_end();
                assert(self.inv_applying_journal());
            }
            assert(self.inv());
            assert(self.inv_api(api));
        }
        progress
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
        let ghost pre_state = self.model@.value();
        proof {
            self.system_inv_implies_atomic_state_wf();
        }

        let progress;

        // NOTE: this path is hit if map is read in after the journal index is built
        if self.journal.exec_index_ready() {
            if self.store_initialized {
                self.recovery_phase = RecoveryPhase::ApplyingJournalToRecoverEphemeralMap;
                progress = true;
            } else {
                progress = false;
            }
        } else {
            let ghost journal_raw_disk = self.system_inv_journal_pages_parsable();
            let result = self.journal.recover_index_step(&mut self.cache, Ghost(journal_raw_disk));
            match result {
                RecoverIndexResult::CacheLoad{slot_handle, addr} => {
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof { tracked_swap(self.model.borrow_mut(), &mut model); }

                    let ghost old_outstanding = self.outstanding_requests@;

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

                        assert(Cache::State::next(pre_state.state.cache, post_state.state.cache, cache_lbl)); // trigger

                        let updated_outstanding_cache_reqs = Map::new(|id| disk_event->req_map.contains_key(id), |id| disk_event->req_map[id].addr());
                        let new_outstanding_cache_reqs = pre_state.state.outstanding_cache_reqs.union_prefer_right(updated_outstanding_cache_reqs);
                        assert(updated_outstanding_cache_reqs == map!{req_id_perm@ => addr@}) by {
                            assert_maps_equal!(updated_outstanding_cache_reqs, map!{req_id_perm@ => addr@}, id2 => {
                                if id2 == req_id_perm@ {
                                    vstd::map::axiom_map_insert_same(Map::<ID, DiskRequest>::empty(), req_id_perm@, disk_req@);
                                    vstd::map::axiom_map_insert_same(Map::<ID, Address>::empty(), req_id_perm@, addr@);
                                } else {
                                    Self::singleton_map_dom(req_id_perm@, disk_req@);
                                    Self::singleton_map_dom(req_id_perm@, addr@);
                                }
                            });
                        }
                        assert(new_outstanding_cache_reqs == pre_state.state.outstanding_cache_reqs.insert(req_id_perm@, addr@)) by {
                            vstd::map_lib::lemma_union_insert_right(pre_state.state.outstanding_cache_reqs, Map::<ID, Address>::empty(), req_id_perm@, addr@);
                        }
                        assert(AtomicState::disk_transition(pre_state.state, post_state.state, disk_event, program_lbl->info.reqs, program_lbl->info.resps)); // witness
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
                    progress = false; // cache waiting on data, not ready to make more progress
                }
                RecoverIndexResult::IndexComplete{reads} => {
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
                        assert(ConcreteProgramModel::valid_internal_transition(pre_state, post_state)) by {
                            assert(AtomicState::internal_transitions(
                                pre_state.state,
                                post_state.state,
                                InternalEvent::JournalRecovery{reads: reads@}
                            )) by {
                                let (cache_lbl, journal_lbl) = load_index_labels(reads@);
                            };
                        }
                    }

                    let tracked new_reply_token = self.instance.borrow().internal(
                        KVStoreTokenized::Label::InternalOp{},
                        post_state,
                        &mut model,
                    );
                    self.model = Tracked(model);

                    if self.store_initialized {
                        self.recovery_phase = RecoveryPhase::ApplyingJournalToRecoverEphemeralMap;
                    }

                    proof {
                        self.system_inv_implies_atomic_state_wf();
                    }
                    progress = true;
                }
                RecoverIndexResult::IndexProgress{} => {
                    progress = true;
                }
            }
        }
        proof {
            if self.recovery_phase is ApplyingJournalToRecoverEphemeralMap {
                self.journal.seq_start_le_seq_end();
            }
            self.store.store_addrs_are_alloc_au(None);
            assert(self.state().cache == self.cache@);
            assert(self.outstanding_requests_match_cache_reqs());
            assert(self.outstanding_requests_wf());
            assert(self.recovery_phase is ReadingJournalIndex ==> self.inv_reading_journal());
            if self.recovery_phase is ApplyingJournalToRecoverEphemeralMap {
                assert(self.inv_applying_journal()) by {
                }
            }
            assert(self.inv());
            assert(self.inv_api(api));
        }
        progress // either index is complete or journal has made progress building the index
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
        proof {
            assert(self.inv());
            self.system_inv_implies_atomic_state_wf();
            assert(self.inv_applying_journal()) by {
            }
            assert(self.in_flight is None) by {
                if self.in_flight is Some {
                    assert(self.recovery_phase is ReadyForUserOperation);
                }
            }
        }
        let ghost journal_alloc_au0 = self.journal.alloc_au();
        let ghost store_alloc_au0 = self.store_alloc_au();
        let ghost prepared_store_ptr0 = self.prepared_store_ptr();
        let ghost prepared_store_lsn0 = self.prepared_store_lsn();
        let ghost prepared_store_ptr_view0 = self.prepared_store_ptr_view();
        let ghost prepared_store_lsn_nat0 = self.prepared_store_lsn_nat();
        let ghost landed_store_ptr0 = self.landed_store_ptr();
        let ghost landed_store_lsn0 = self.landed_store_lsn();
        let ghost store_next_alloc_page0 = self.store.next_alloc_page();
        proof {
            self.store.prepared_store_ptr_view_ensures();
            self.store.prepared_store_lsn_nat_ensures();
            self.store.prepared_store_ptr_has_alloc_au();
            self.store.prepared_store_ptr_before_next_alloc();
            self.store.persistent_store_ptr_has_alloc_au();
            self.store.persistent_store_ptr_before_next_alloc();
            assert(prepared_store_ptr0 == self.prepared_store_ptr());
            assert(prepared_store_ptr_view0 == iaddr_view(prepared_store_ptr0));
            assert(prepared_store_lsn_nat0 == prepared_store_lsn0 as nat);
            assert(landed_store_ptr0 == self.landed_store_ptr());
        }
        if self.store.exec_store_lsn() < self.journal.exec_seq_start() {
            return false;
        }
        let exec_seq_end = self.journal.exec_seq_end();
        if self.store.exec_store_lsn() < exec_seq_end {
            let ghost pre_state = self.model@.value();
            let ghost instance_id = self.instance@.id();
            let ghost pre_cache_impl = self.cache;
            let ghost pre_cache = self.cache@;
            let ghost pre_outstanding = self.outstanding_requests@;
            let ghost pre_store_lsn = self.store.store_lsn_nat();
            proof {
                assert(self.inv_applying_journal()) by {
                }
                // inv_applying_journal gives recovery_state is JournalIndexComplete
            }
            let ghost journal_raw_disk = self.system_inv_journal_pages_parsable();
            let start_lsn = self.store.exec_store_lsn();
            let fetch = self.journal.recover_map_step(&mut self.cache, start_lsn, Ghost(journal_raw_disk));

            // we need to track some
            match fetch {
                RecoverMapResult::NotInCache{} => {
                    proof {
                        self.store.store_addrs_are_alloc_au(None);
                        assert(self.inv_api(api));
                    }
                    return false;
                }
                RecoverMapResult::FetchSuccess{reads, addr, record} => {
                    let record_msg_len = record.messages.len() as u64;
                    let record_seq_end = record.header.start_lsn + record_msg_len;

                    let ghost cache_after_fetch = self.cache@;
                    let ghost journal_after_fetch = self.journal@;
                    let ghost fetch_boundary_lsn = self.journal@.snapshot.boundary_lsn;
                    let ghost fetch_cache_lbl = Cache::Label::Access{reads: reads@, writes: Map::empty()};
                    let ghost pre_store = StampedMap{
                        value: self.store@,
                        seq_end: pre_store_lsn,
                    };

                    let mut next_lsn = self.store.exec_store_lsn();
                    let mut next_index: usize = (self.store.exec_store_lsn() - record.header.start_lsn) as usize;

                    let ghost record_msgs = record.parsedv().view().message_seq;
                    let ghost records = record_msgs.maybe_discard_old(pre_store_lsn);
                    proof {
                        self.journal.view_seq_start_ensures();
                        assert(fetch_boundary_lsn == self.journal.seq_start());
                        assert(CachedJournal::State::next(
                            journal_after_fetch,
                            journal_after_fetch,
                            map_recovery_labels(fetch_boundary_lsn, reads@, addr@).1,
                        ));
                        assert(pre_state.state == self.state());
                        assert(pre_state.state.store == self.i_ephemeral_store());
                        assert(pre_state.state.store is Known);
                        self.store.kmmap_wf_ensures();
                        assert(pre_state.state.store->Known_v.stamped_map == pre_store);
                        assert(pre_state.state.persistent_store_ptr == self.store.persistent_store_ptr_view());
                        assert(pre_store.seq_end == pre_store_lsn);
                        assert(pre_store.value.wf());
                        assert(record_msgs.wf());
                        assert(record_msgs.seq_start <= pre_store_lsn);
                        assert(pre_store_lsn < record_msgs.seq_end);
                        assert(records == record_msgs.discard_old(pre_store_lsn));
                        assert(records.wf());
                        assert(records.seq_start == pre_store_lsn);
                        assert(records.seq_end == record_msgs.seq_end);
                        assert(records.can_follow(pre_store.seq_end));
                        assert(records.seq_end == record_seq_end as nat);
                        assert(records.can_discard_to(self.store.store_lsn_nat()));
                        let empty_prefix = records.discard_recent(self.store.store_lsn_nat());
                        assert(empty_prefix.seq_start == pre_store_lsn);
                        assert(empty_prefix.seq_end == pre_store_lsn);
                        assert(empty_prefix.wf());
                        assert(empty_prefix.is_empty());
                        reveal_with_fuel(MsgHistory::apply_to_stamped_map, 1);
                        assert(MsgHistory::map_plus_history(pre_store, empty_prefix).value == pre_store.value);
                    }

                    while next_lsn < record_seq_end
                    invariant
                        self.model@.value() == pre_state,
                        self.model@.instance_id() == instance_id,
                        self.instance@.id() == instance_id,
                        self.outstanding_requests@ == pre_outstanding,
                        self.recovery_phase is ApplyingJournalToRecoverEphemeralMap,
                        self.store_initialized,
                        self.in_flight is None,
                        self.sync_requests.valid_empty_sync_buffer(self.instance@.id()),
                        self.cache.wf(),
                        self.cache.valid_load_handles_preserved(pre_cache_impl),
                        self.journal.wf(),
                        self.journal.no_unmarshalled_entries(),
                        self.journal.seq_start() <= pre_store.seq_end,
                        pre_store.value.wf(),
                        records.wf(),
                        records.can_follow(pre_store.seq_end),
                        exec_seq_end == self.journal.seq_end(),
                        self.store.store_lsn_nat() <= self.journal.seq_end(),
                        self.store.wf(),
                        self.store.persistent_store_ptr_matches_alloc_au(),
                        pre_state.state.persistent_store_ptr == self.store.persistent_store_ptr_view(),
                        self.journal.alloc_au() == journal_alloc_au0,
                        self.store_alloc_au() == store_alloc_au0,
                        self.prepared_store_ptr() == prepared_store_ptr0,
                        self.prepared_store_lsn() == prepared_store_lsn0,
                        self.landed_store_ptr() == landed_store_ptr0,
                        self.landed_store_lsn() == landed_store_lsn0,
                        self.store.next_alloc_page() == store_next_alloc_page0,
                        self.cache@ == cache_after_fetch,
                        self.journal@ == journal_after_fetch,
                        Cache::State::next(pre_cache, cache_after_fetch, fetch_cache_lbl),
                        self.store.store_lsn() == next_lsn,
                        next_lsn as nat == record.header.start_lsn as nat + next_index as nat,
                        pre_store_lsn <= self.store.store_lsn_nat() <= records.seq_end,
                        records.can_discard_to(self.store.store_lsn_nat()),
                        self.store.kmmap()
                            == MsgHistory::map_plus_history(
                                pre_store,
                                records.discard_recent(self.store.store_lsn_nat()),
                            ).value,
                    decreases record_seq_end - next_lsn
                    {
                        let km = record.messages[next_index];
                        let old_store_lsn_exec = self.store.exec_store_lsn();
                        let ghost old_store_lsn = old_store_lsn_exec as nat;
                        let ghost old_store_kmmap = self.store.kmmap();

                        match km.message {
                            Message::Define{value} => {
                                let key = km.key;
                                self.store.insert(key, value);
                                proof {
                                    assert(old_store_lsn_exec == next_lsn);
                                    let prefix = records.discard_recent(old_store_lsn);
                                    assert(old_store_lsn == next_lsn as nat);
                                    assert(old_store_lsn < records.seq_end) by {
                                        assert(next_lsn < record_seq_end);
                                        assert(records.seq_end == record_seq_end as nat);
                                    }
                                    assert(records.can_discard_to((old_store_lsn + 1) as nat));
                                    let next_prefix = records.discard_recent((old_store_lsn + 1) as nat);
                                    assert(prefix.wf());
                                    assert(next_prefix.wf());
                                    assert(prefix.can_follow(pre_store.seq_end));
                                    assert(next_prefix.can_follow(pre_store.seq_end));
                                    assert(next_prefix.can_discard_to(old_store_lsn));
                                    assert(next_prefix.discard_recent(old_store_lsn).ext_equal(prefix)) by {
                                        assert forall |lsn: LSN| #[trigger] next_prefix.discard_recent(old_store_lsn).msgs.contains_key(lsn)
                                            <==> prefix.msgs.contains_key(lsn) by {
                                            assert(next_prefix.discard_recent(old_store_lsn).contains(lsn)
                                                <==> next_prefix.seq_start <= lsn < old_store_lsn);
                                            assert(prefix.contains(lsn) <==> prefix.seq_start <= lsn < old_store_lsn);
                                            assert(next_prefix.seq_start == prefix.seq_start);
                                        }
                                        assert(next_prefix.discard_recent(old_store_lsn).seq_start == prefix.seq_start);
                                        assert(next_prefix.discard_recent(old_store_lsn).seq_end == prefix.seq_end);
                                    }
                                    assert(next_prefix.discard_recent(old_store_lsn) == prefix) by {
                                        MsgHistory::ext_equal_is_equality();
                                    }
                                    assert(record.parsedv().messages[next_index as int] == km);
                                    assert((old_store_lsn - record.header.start_lsn as nat) as int == next_index as int);
                                    assert(record_msgs.msgs[old_store_lsn]
                                        == record.parsedv().messages[(old_store_lsn - record.header.start_lsn as nat) as int]);
                                    assert(records.msgs.contains_key(old_store_lsn));
                                    assert(records.msgs[old_store_lsn] == km) by {
                                        assert(record_msgs.msgs[old_store_lsn] == record.messages[next_index as int]);
                                    }
                                    assert(self.store.store_lsn_nat() == old_store_lsn + 1);
                                    assert(self.store.kmmap() == old_store_kmmap.insert(key, Message::Define{value}));
                                    assert(self.store.store_lsn_nat() <= records.seq_end);
                                    assert(self.store.store_lsn_nat() <= self.journal.seq_end());
                                    assert(records.can_discard_to(self.store.store_lsn_nat()));
                                    reveal_with_fuel(MsgHistory::apply_to_stamped_map, 2);
                                    assert(old_store_kmmap == MsgHistory::map_plus_history(pre_store, prefix).value);
                                    assert(MsgHistory::map_plus_history(pre_store, next_prefix).value
                                        == old_store_kmmap.insert(key, Message::Define{value}));
                                }
                            }
                            Message::Update{delta} => {
                                let _ = delta;
                                // Note: Updates (upserts) are a nice splinter feature that we're
                                // not going to implement in the forseeable feature. So this
                                // placeholder will stay.
                                Self::todo_placeholder();
                            }
                        }

                        next_lsn = next_lsn + 1;
                        next_index = next_index + 1;
                    }

                    let ghost post_state = ConcreteProgramModel{
                        state: AtomicState{
                            cache: self.cache@,
                            journal: self.journal@,
                            store: Ephemeral::Known{
                                v: AbstractMap::State{
                                    stamped_map: StampedMap{
                                        value: self.store@,
                                        seq_end: self.store.store_lsn_nat(),
                                    }
                                }
                            },
                            ..pre_state.state
                        }
                    };
                    let final_store_lsn = self.store.exec_store_lsn();

                    proof {
                        assert(final_store_lsn == next_lsn);
                        assert(self.store.store_lsn_nat() == final_store_lsn as nat);
                        assert(!(next_lsn < record_seq_end));
                        assert(record_seq_end <= next_lsn);
                        assert(self.store.store_lsn_nat() == next_lsn as nat);
                        assert(record_seq_end <= next_lsn);
                        assert(self.store.store_lsn_nat() == records.seq_end);
                        assert(self.store.kmmap()
                            == MsgHistory::map_plus_history(pre_store, records).value) by {
                            assert(records.discard_recent(self.store.store_lsn_nat()).ext_equal(records)) by {
                                assert forall |lsn: LSN| #[trigger] records.discard_recent(self.store.store_lsn_nat()).msgs.contains_key(lsn)
                                    <==> records.msgs.contains_key(lsn) by {
                                    assert(records.discard_recent(self.store.store_lsn_nat()).contains(lsn)
                                        <==> records.seq_start <= lsn < self.store.store_lsn_nat());
                                    assert(records.contains(lsn) <==> records.seq_start <= lsn < records.seq_end);
                                }
                                assert(records.discard_recent(self.store.store_lsn_nat()).seq_start == records.seq_start);
                                assert(records.discard_recent(self.store.store_lsn_nat()).seq_end == records.seq_end);
                            }
                            assert(records.discard_recent(self.store.store_lsn_nat()) == records) by {
                                MsgHistory::ext_equal_is_equality();
                            }
                        }
                        assert(pre_state.state.store->Known_v.stamped_map == pre_store);
                        MsgHistory::map_plus_history_seq_end_lemma(pre_store, records);

                        reveal(AbstractMap::State::next_by);
                        reveal(AbstractMap::State::next);
                        assert(post_state.state.store->Known_v.stamped_map.ext_equal(
                            MsgHistory::map_plus_history(pre_store, records)
                        )) by {
                            assert(post_state.state.store->Known_v.stamped_map.value
                                == MsgHistory::map_plus_history(pre_store, records).value);
                            assert(post_state.state.store->Known_v.stamped_map.seq_end
                                == MsgHistory::map_plus_history(pre_store, records).seq_end);
                        }
                        StampedMap::ext_equal_is_equality();
                        assert(post_state.state.store->Known_v.stamped_map
                            == MsgHistory::map_plus_history(pre_store, records));
                        assert(AbstractMap::State::next_by(
                            pre_state.state.store->Known_v,
                            post_state.state.store->Known_v,
                            AbstractMap::Label::PutLabel{puts: records},
                            AbstractMap::Step::put{}
                        )); // witness
                        assert(AbstractMap::State::next(
                            pre_state.state.store->Known_v,
                            post_state.state.store->Known_v,
                            AbstractMap::Label::PutLabel{puts: records},
                        ));
                        assert(AtomicState::map_recovery(
                            pre_state.state,
                            post_state.state,
                            records,
                            reads@,
                            addr@,
                        )) by {
                            let cache_lbl = Cache::Label::Access{reads: reads@, writes: Map::empty()};
                            let ghost journal_reads = to_journal_records(reads@);
                            let ghost recovery_record = journal_reads[addr@];
                            let ghost boundary_lsn = pre_state.state.journal.snapshot.boundary_lsn;
                            assert(Cache::State::next(pre_state.state.cache, post_state.state.cache, cache_lbl));
                            assert(records == recovery_record.message_seq.maybe_discard_old(
                                pre_state.state.store->Known_v.stamped_map.seq_end
                            ));
                            self.journal.view_seq_start_ensures();
                            assert(pre_state.state.journal == self.journal@);
                            assert(boundary_lsn == self.journal@.snapshot.boundary_lsn);
                            assert(self.journal@.snapshot.boundary_lsn == fetch_boundary_lsn);
                            assert(boundary_lsn == fetch_boundary_lsn);
                            assert(boundary_lsn <= recovery_record.message_seq.seq_end) by {
                                assert(self.journal.seq_start() <= pre_store.seq_end);
                                assert(pre_store.seq_end == start_lsn as nat);
                                assert((start_lsn as nat) < recovery_record.message_seq.seq_end);
                            }
                            assert(self.journal.seq_start() <= recovery_record.message_seq.seq_end);
                            let ghost journal_lbl = CachedJournal::Label::ReadForRecovery{
                                messages: recovery_record.message_seq.maybe_discard_old(boundary_lsn),
                                reads: journal_reads,
                            };
                            let ghost fetch_journal_lbl = CachedJournal::Label::ReadForRecovery{
                                messages: recovery_record.message_seq.maybe_discard_old(fetch_boundary_lsn),
                                reads: journal_reads,
                            };
                            assert(recovery_record == to_journal_records(reads@)[addr@]);
                            let ghost fetch_journal_lbl_from_map = map_recovery_labels(fetch_boundary_lsn, reads@, addr@).1;
                            assert(fetch_journal_lbl_from_map is ReadForRecovery) by {
                            }
                            assert(fetch_journal_lbl_from_map.arrow_ReadForRecovery_reads() == journal_reads) by {
                            }
                            assert(fetch_journal_lbl_from_map.arrow_ReadForRecovery_messages()
                                == recovery_record.message_seq.maybe_discard_old(fetch_boundary_lsn)) by {
                            }
                            assert(fetch_journal_lbl == journal_lbl);
                            assert(fetch_journal_lbl_from_map == fetch_journal_lbl);
                            assert(CachedJournal::State::next(
                                journal_after_fetch,
                                journal_after_fetch,
                                map_recovery_labels(fetch_boundary_lsn, reads@, addr@).1,
                            ));
                            assert(CachedJournal::State::next(
                                pre_state.state.journal,
                                post_state.state.journal,
                                map_recovery_labels(fetch_boundary_lsn, reads@, addr@).1,
                            ));
                            assert(AbstractMap::State::next(
                                pre_state.state.store->Known_v,
                                post_state.state.store->Known_v,
                                AbstractMap::Label::PutLabel{puts: records},
                            ));
                        }
                        assert(ConcreteProgramModel::valid_internal_transition(pre_state, post_state)) by {
                            assert(AtomicState::internal_transitions(
                                pre_state.state,
                                post_state.state,
                                InternalEvent::MapRecovery{records, reads: reads@, addr: addr@}
                            )) by {
                                let cache_lbl = Cache::Label::Access{reads: reads@, writes: Map::empty()};
                                let ghost journal_reads = to_journal_records(reads@);
                                let ghost journal_record = journal_reads[addr@];
                                let ghost journal_seq_end = journal_record.message_seq.seq_end;

                                assert(Cache::State::next(pre_state.state.cache, post_state.state.cache, cache_lbl)) by {
                                }
                                assert(CachedJournal::State::next(
                                    journal_after_fetch,
                                    journal_after_fetch,
                                    map_recovery_labels(fetch_boundary_lsn, reads@, addr@).1
                                ));
                                assert(CachedJournal::State::next(
                                    pre_state.state.journal,
                                    post_state.state.journal,
                                    map_recovery_labels(fetch_boundary_lsn, reads@, addr@).1
                                )) by {
                                }
                                assert(records == journal_record.message_seq.maybe_discard_old(
                                    pre_state.state.store->Known_v.stamped_map.seq_end
                                ));
                                assert(pre_state.state.journal.snapshot.boundary_lsn
                                    <= journal_seq_end) by {
                                    self.journal.view_seq_start_ensures();
                                    assert(pre_state.state.journal == self.journal@);
                                    assert(pre_state.state.journal.snapshot.boundary_lsn == self.journal@.snapshot.boundary_lsn);
                                    assert(self.journal@.snapshot.boundary_lsn == fetch_boundary_lsn);
                                    assert(fetch_boundary_lsn <= pre_store.seq_end);
                                    assert(pre_store.seq_end == start_lsn as nat);
                                    assert((start_lsn as nat) < journal_seq_end);
                                }
                            };
                        }
                    }
                    let tracked mut model = KVStoreTokenized::model::arbitrary();
                    proof { tracked_swap(self.model.borrow_mut(), &mut model); }
                    let tracked instance = self.instance.borrow();
                    let tracked new_reply_token = instance.internal(
                        KVStoreTokenized::Label::InternalOp{},
                        post_state,
                        &mut model,
                    );
                    self.model = Tracked(model);

                    if self.store.exec_store_lsn() < exec_seq_end {
                        proof {
                            self.system_inv_implies_atomic_state_wf();
                            assert(self.prepared_store_ptr() == prepared_store_ptr0);
                            assert(self.prepared_store_lsn() == prepared_store_lsn0);
                            assert(self.landed_store_ptr() == landed_store_ptr0);
                            assert(self.landed_store_lsn() == landed_store_lsn0);
                            assert(self.store.next_alloc_page() == store_next_alloc_page0);
                            assert(self.state().cache == self.cache@);
                            assert(self.state().store == self.i_ephemeral_store());
                            assert(self.state().persistent_store_ptr == self.store.persistent_store_ptr_view());
                            assert(self.state().prepared_store_ptr == pre_state.state.prepared_store_ptr);
                            assert(self.state().prepared_store_lsn == pre_state.state.prepared_store_lsn);
                            self.store.prepared_store_ptr_view_ensures();
                            self.store.prepared_store_lsn_nat_ensures();
                            assert(self.prepared_store_ptr_view() == iaddr_view(prepared_store_ptr0));
                            assert(self.prepared_store_lsn_nat() == prepared_store_lsn0 as nat);
                            assert(self.state().prepared_store_ptr == self.prepared_store_ptr_view());
                            assert(self.state().prepared_store_lsn == self.prepared_store_lsn_nat());
                            assert(self.state().journal == self.journal@);
                            assert(self.outstanding_requests_wf());
                            assert(self.outstanding_requests_match_cache_reqs());
                            assert(self.store.persistent_store_ptr_matches_alloc_au());
                            self.store.prepared_store_ptr_has_alloc_au();
                            self.store.prepared_store_ptr_before_next_alloc();
                            self.store.persistent_store_ptr_has_alloc_au();
                            self.store.persistent_store_ptr_before_next_alloc();
                            self.store.store_addrs_are_alloc_au(None);
                            self.state_store_addrs_match();
                            assert(self.inv_applying_journal());
                            assert(self.inv());
                            assert(self.inv_api(api));
                        }
                        return true;
                    }
                }
            }
        }
        let exec_seq_end = self.journal.exec_seq_end();
        if self.store.exec_store_lsn() < exec_seq_end {
            proof {
                assert(self.inv_applying_journal());
                assert(self.inv_api(api));
            }
            return true;
        }
        proof {
            assert(self.inv_applying_journal());
        }
        let ghost pre_state = self.state();
        proof {
            assert(pre_state == self.state());
            assert(self.store_initialized);
            self.journal.view_seq_end_ensures();
            assert(pre_state.store == self.i_ephemeral_store());
            assert(pre_state.persistent_store_ptr == self.store.persistent_store_ptr_view());
            assert(pre_state.prepared_store_ptr == prepared_store_ptr_view0);
            assert(pre_state.prepared_store_lsn == prepared_store_lsn_nat0);
        }

        {
            self.recovery_phase = RecoveryPhase::ReadyForUserOperation;

            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

            let ghost post_state = ConcreteProgramModel{
                state: AtomicState {
                    recovery_state: RecoveryState::RecoveryComplete,
                    journal: pre_state.journal,
                    persistent_journal_seq_end: pre_state.ephemeral_map().seq_end,
                    ..pre_state
                }
            };

            proof {
                assert(ConcreteProgramModel::valid_internal_transition(
                    ConcreteProgramModel { state: pre_state }, post_state
                )) by {
                    assert(AtomicState::internal_transitions(
                        pre_state,
                        post_state.state,
                        InternalEvent::RecoveryComplete{}
                    )) by {
                        let end_lsn = pre_state.ephemeral_map().seq_end;
                        let journal_lbl = CachedJournal::Label::QueryEndLsn{end_lsn};
                        reveal(CachedJournal::State::next_by);
                        reveal(CachedJournal::State::next);
                        assert(CachedJournal::State::next_by(
                            pre_state.journal,
                            post_state.state.journal,
                            journal_lbl,
                            CachedJournal::Step::query_end_lsn()
                        )); // witness
                    };
                }
            }

            let tracked new_reply_token = self.instance.borrow().internal(
                KVStoreTokenized::Label::InternalOp{},
                post_state,
                &mut model,
            );
            self.model = Tracked(model);
            proof {
                self.system_inv_implies_atomic_state_wf();
                assert(self.prepared_store_ptr() == prepared_store_ptr0);
                assert(self.prepared_store_lsn() == prepared_store_lsn0);
                assert(self.landed_store_ptr() == landed_store_ptr0);
                assert(self.landed_store_lsn() == landed_store_lsn0);
                assert(self.store.next_alloc_page() == store_next_alloc_page0);
                assert(self.state() == post_state.state);
                assert(self.store_initialized);
                assert(post_state.state.store == self.i_ephemeral_store());
                assert(self.store.persistent_store_ptr_matches_alloc_au());
                assert(self.state().prepared_store_ptr == pre_state.prepared_store_ptr);
                assert(self.state().prepared_store_lsn == pre_state.prepared_store_lsn);
                assert(pre_state.prepared_store_ptr == prepared_store_ptr_view0);
                assert(pre_state.prepared_store_lsn == prepared_store_lsn_nat0);
                self.store.prepared_store_ptr_view_ensures();
                self.store.prepared_store_lsn_nat_ensures();
                assert(self.prepared_store_ptr_view() == iaddr_view(prepared_store_ptr0));
                assert(self.prepared_store_lsn_nat() == prepared_store_lsn0 as nat);
                assert(self.state().prepared_store_ptr == self.prepared_store_ptr_view());
                assert(self.state().prepared_store_lsn == self.prepared_store_lsn_nat());
                self.store.prepared_store_ptr_has_alloc_au();
                self.store.prepared_store_ptr_before_next_alloc();
                self.store.persistent_store_ptr_has_alloc_au();
                self.store.persistent_store_ptr_before_next_alloc();
                self.store.store_addrs_are_alloc_au(None);
                assert(self.in_flight is None);
                assert(self.store_addrs() == self.store.store_addrs(None));
                assert(self.state().cache == self.cache@);
                assert(self.state().store == self.i_ephemeral_store());
                assert(self.state().persistent_store_ptr == pre_state.persistent_store_ptr);
                assert(pre_state.persistent_store_ptr == self.store.persistent_store_ptr_view());
                assert(self.state().prepared_store_ptr == pre_state.prepared_store_ptr);
                assert(self.state().prepared_store_lsn == pre_state.prepared_store_lsn);
                assert(self.state().journal == self.journal@);
                assert(self.cache.wf());
                assert(self.store.wf());
                assert(self.journal.alloc_au() == journal_alloc_au0);
                assert(self.store_alloc_au() == store_alloc_au0);
                assert(self.journal.alloc_au() != self.store_alloc_au());
                assert(self.outstanding_requests_match_cache_reqs());
                assert(self.outstanding_requests_wf());
                assert(self.journal.seq_end() == self.store.store_lsn_nat());
                assert(self.state().recovery_state is RecoveryComplete);
                assert(self.state().in_flight is None);
                assert(!self.sync_requests.in_flight());
                self.store.store_addrs_none_matches_persistent_view();
                self.state_store_addrs_match();
                assert(self.inv_running());
                assert(self.inv_api(api));
            }
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

    fn should_do_background_marshall(&self) -> (out: bool)
    {
        self.outstanding_requests.len() == 0
    }

    fn maybe_marshall_journal(&mut self, api: &mut ClientAPI<ConcreteProgramModel>, background: bool) -> (out: JournalMarshalStepResult)
        requires
            old(self).inv_api(old(api)),
            old(self).ready_for_user_operation(),
        ensures
            self.inv_api(api),
            self.ready_for_user_operation(),
            self.sync_requests == old(self).sync_requests,
            self.in_flight == old(self).in_flight,
            self.store == old(self).store,
            self.store_initialized == old(self).store_initialized,
            self.prepared_store_ptr() == old(self).prepared_store_ptr(),
            self.prepared_store_lsn() == old(self).prepared_store_lsn(),
            self.landed_store_ptr() == old(self).landed_store_ptr(),
            self.landed_store_lsn() == old(self).landed_store_lsn(),
            self.outstanding_requests@ == old(self).outstanding_requests@,
    {
        let ghost pre_journal_view = self.journal@;
        let marshalled_end = self.journal.exec_marshaled_seq_end();
        let seq_end = self.journal.exec_seq_end();

        if marshalled_end >= seq_end {
            return JournalMarshalStepResult::Done{};
        }

        // NOTE: temporary heuristics that only marshall journal once a threshold of unmarshalled
        // records have been reached, do this only for background tasks
        if background {
            let marshall_batch_size = 20; // NOTE: testing
            if seq_end - marshalled_end < marshall_batch_size {
                return JournalMarshalStepResult::Done{};
            }
        }
        
        let ghost pre_state = self.model@.value();
        let ghost pre_cache = self.cache;
        let ghost journal_alloc_au0 = self.journal.alloc_au();
        let ghost store_alloc_au0 = self.store_alloc_au();
        let addr = self.journal.peek_next_addr();
        proof {
            assert(self.journal@ == pre_journal_view);
            assert(addr.au as nat == self.journal.alloc_au());
            assert(self.journal.alloc_au() != self.store_alloc_au());
            assert(!self.store_addrs().contains(addr@)) by {
                if self.store_addrs().contains(addr@) {
                    assert(addr@.au == self.store_alloc_au());
                    assert(addr@.au == addr.au as nat);
                    assert(false);
                }
            }
            assert(pre_state.state.store_addrs() == self.store_addrs());
            assert(!pre_state.state.store_addrs().contains(addr@));
            assume(!self.journal@.status.unwrap().lsn_addr_index.values().contains(addr@));
            assume(!pre_cache.entry_fetched(&addr));
        }

        let reserve_result = self.cache.reserve_for_write_absent(&addr);
        match reserve_result {
            ReserveWriteResult::CacheFull => {
                JournalMarshalStepResult::CacheFull{}
            }
            ReserveWriteResult::Reserved{slot_handle} => {
                let ghost cache_after_reserve = self.cache;
                let ghost post_reserve_state = ConcreteProgramModel{
                    state: AtomicState{
                        cache: self.cache@,
                        journal: self.journal@,
                        ..pre_state.state
                    }
                };
                let tracked mut model0 = KVStoreTokenized::model::arbitrary();
                // cache reserve internal transition
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model0);
                    assert(AtomicState::internal_transitions(
                            pre_state.state,
                            post_reserve_state.state,
                            InternalEvent::CacheInternal{}
                    )); // witness
                    self.instance.borrow().internal(
                        KVStoreTokenized::Label::InternalOp{},
                        post_reserve_state,
                        &mut model0,
                    );
                }
                self.model = Tracked(model0);

                // journal marshall step internal transition
                self.journal.advance_next_addr();

                proof {
                    assert(self.journal@ == pre_journal_view);
                    assert(!self.journal@.status.unwrap().lsn_addr_index.values().contains(addr@));
                    self.system_inv_implies_atomic_state_wf();
                }

                let marshalled_end_now = self.journal.exec_marshaled_seq_end();
                let seq_end_now = self.journal.exec_seq_end();
                proof {
                    assert(marshalled_end_now as nat == self.journal.marshalled_seq_end());
                    assert(seq_end_now as nat == self.journal.seq_end());
                }
                if marshalled_end_now == seq_end_now {
                    Self::todo_placeholder();
                }

                let Ghost(raw_page) =
                    self.journal.internal_journal_marshall_commit_reserved(&mut self.cache, addr, slot_handle);

                let ghost post_commit_state = ConcreteProgramModel{
                    state: AtomicState{
                        cache: self.cache@,
                        journal: self.journal@,
                        ..post_reserve_state.state
                    }
                };
                let tracked mut model1 = KVStoreTokenized::model::arbitrary();
                proof {
                    let ghost pre_commit_state = self.model@.value();
                    tracked_swap(self.model.borrow_mut(), &mut model1);
                    assert(pre_commit_state.state == post_reserve_state.state);
                    let event = InternalEvent::JournalMarshallStep{addr: addr@, raw_page};
                    assert(pre_commit_state.state.store_addrs() == pre_state.state.store_addrs());
                    assert(!pre_commit_state.state.store_addrs().contains(addr@));
                    assert(AtomicState::internal_transitions(
                        pre_commit_state.state,
                        post_commit_state.state,
                        event,
                    ));
                    self.instance.borrow().internal(
                        KVStoreTokenized::Label::InternalOp{},
                        post_commit_state,
                        &mut model1,
                    );
                }
                self.model = Tracked(model1);

                proof {
                    self.system_inv_implies_atomic_state_wf();
                    assert(self.state() == post_commit_state.state);
                    assert(self.state().cache == self.cache@);
                    assert(self.state().store == self.i_ephemeral_store());
                    assert(self.state().persistent_store_ptr == pre_state.state.persistent_store_ptr);
                    assert(pre_state.state.persistent_store_ptr == self.store.persistent_store_ptr_view());
                    assert(self.state().journal == self.journal@);
                    assert(self.cache.wf());
                    assert(self.store.wf());
                    assert(self.journal.alloc_au() == journal_alloc_au0);
                    assert(self.store_alloc_au() == store_alloc_au0);
                    assert(self.journal.alloc_au() != self.store_alloc_au());
                    assert(self.store_initialized);
                    assert(self.store.persistent_store_ptr_matches_alloc_au());
                    self.store.prepared_store_ptr_has_alloc_au();
                    self.store.prepared_store_ptr_before_next_alloc();
                    self.store.persistent_store_ptr_has_alloc_au();
                    self.store.persistent_store_ptr_before_next_alloc();
                    let inflight_store_ptr = if self.in_flight is Some { self.in_flight.unwrap().store_ptr } else { None };
                    if inflight_store_ptr is Some {
                        assert(inflight_store_ptr.unwrap().au as nat == self.store_alloc_au());
                        assert((inflight_store_ptr.unwrap().page as nat) < self.store.next_alloc_page());
                    }
                    self.store.store_addrs_are_alloc_au(inflight_store_ptr);
                    self.state_store_addrs_match();
                    assert(self.journal.index_ready());
                    assert(self.state().recovery_state is RecoveryComplete);
                    assert(self.journal.seq_end() == self.store.store_lsn_nat());
                    assert(self.state().wf());
                    assert(self.state().in_flight is Some <==> self.sync_requests.in_flight());
                    assert(self.state().in_flight is Some <==> self.in_flight is Some);
                    if self.state().in_flight is Some {
                        assert(self.in_flight is Some);
                        assert(self.sync_requests.in_flight());
                        let sync_version = self.state().in_flight.unwrap().journal_version;
                        let new_persistent_map_version = self.in_flight.unwrap().new_boundary_lsn as nat;
                        assert(self.journal.seq_start() <= new_persistent_map_version);
                        assert(new_persistent_map_version <= sync_version);
                        self.journal.view_marshaled_seq_end_ensures();
                        self.journal.view_seq_end_ensures();
                        assert(sync_version <= self.state().journal.marshalled_seq_end());
                        assert(sync_version <= self.state().journal.seq_end());
                        assert(self.state().journal.marshalled_seq_end() == self.journal.marshalled_seq_end());
                        assert(self.state().journal.seq_end() == self.journal.seq_end());
                        assert(sync_version <= self.journal.marshalled_seq_end());
                        assert(sync_version <= self.journal.seq_end());
                        assert(self.sync_reqs_in_version(self.sync_requests.superblocking_reqs@, sync_version));
                        assert(self.in_flight.unwrap().new_boundary_lsn as nat == self.state().in_flight.unwrap().boundary_lsn);
                        assert(self.in_flight.unwrap().new_persistent_lsn as nat == self.state().in_flight.unwrap().journal_version);
                        assert(iaddr_view(self.in_flight.unwrap().store_ptr) == self.state().in_flight.unwrap().store_ptr);
                        if self.in_flight.unwrap().store_ptr is Some {
                            assert(self.in_flight.unwrap().store_ptr.unwrap().au as nat == self.store_alloc_au());
                            assert((self.in_flight.unwrap().store_ptr.unwrap().page as nat) < self.store.next_alloc_page());
                        }
                    }
                    assert(self.sync_requests.wf(self.instance@.id()));
                    assert(self.sync_reqs_in_version(self.sync_requests.buffered_reqs@, self.version()));
                    assert(self.sync_requests.sync_target_lsn <= self.version());
                    assert(self.sync_reqs_in_version(
                        self.sync_requests.journal_cleaning_reqs@,
                        self.sync_requests.sync_target_lsn as nat,
                    ));
                    assert(Self::three_sync_req_lists_mutually_unique(
                        self.sync_requests.superblocking_reqs@,
                        self.sync_requests.journal_cleaning_reqs@,
                        self.sync_requests.buffered_reqs@,
                    ));
                    assert(old(self).inv_running());
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        pre_cache,
                        cache_after_reserve,
                        self.cache,
                    );
                    FracCacheImpl::valid_writeback_handles_preserved_transitive(
                        pre_cache,
                        cache_after_reserve,
                        self.cache,
                    );
                    Implementation::outstanding_requests_wf_map_preserved_by_cache(
                        old(self).outstanding_requests@,
                        pre_cache,
                        self.cache,
                    );
                    assert(self.outstanding_requests_match_cache_reqs());
                    assert(self.outstanding_requests_wf());
                    assert(self.inv_running());
                    assert(self.inv());
                    assert(self.inv_api(api));
                    assert(self.ready_for_user_operation());
                }
                JournalMarshalStepResult::Success{}
            }
        }
    }

    fn do_background_work(&mut self, api: &mut ClientAPI<ConcreteProgramModel>) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).ready_for_user_operation(),
        ensures
            self.inv_api(api),
            self.ready_for_user_operation(),
    {
        api.log("background: consider tail marshalling");
        if !self.should_do_background_marshall() {
            api.log("background: skip marshalling (outstanding requests present)");
            return false;
        }

        match self.maybe_marshall_journal(api, true) {
            JournalMarshalStepResult::Success{} => { 
                self.should_retry_superblock_launch = true;
                api.log("background: marshalling frontier advanced");
                return true 
            },
            _ => { 
                api.log("background: no marshalling progress");
                return false 
            },
        }
    }
}

impl KVStoreTrait for Implementation {
    type ProgramModel = ConcreteProgramModel;
    type Proof = RefinementProof;

    closed spec fn wf_init(self) -> bool {
        &&& self.inv()
        &&& self.recovery_phase is FetchingSuperblock
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
            journal_flush_accumulator: 0,
            current_sync_motivation: None,
            store: StoreImpl::new(None, 2),
            store_initialized: false,
            journal: JournalImpl::new(placeholder_snapshot, 1),
            cache,
            in_flight: None,
            // persistent_version: 0,
            model: Tracked(model),
            instance: Tracked(instance),
            sync_requests: SyncRequestBuffer::new_empty(),
            outstanding_requests: HashMapWithView::new(),
            should_retry_superblock_launch: false,
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
                }
                RecoveryPhase::ReadingJournalIndex => {
                    progress = self.recover_read_map(&mut api) || progress;
                    match self.recovery_phase {
                        RecoveryPhase::ReadingJournalIndex => {
                            progress = self.recover_read_journal_index(&mut api) || progress;
                        }
                        _ => {}
                    }
                }
                RecoveryPhase::ApplyingJournalToRecoverEphemeralMap => {
                    progress = self.recover_apply_journal_to_recover_ephemeral_map(&mut api);
                }
                RecoveryPhase::ReadyForUserOperation => {
                    if self.should_retry_superblock_launch {
                        if self.outstanding_requests.len() == 0 {
                            self.should_retry_superblock_launch = false;
                            self.maybe_launch_superblock(&mut api);
                            progress = true;
                        }
                    }
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
                    // Internal/background maintenance work for the ready state.
                    let bg_progress = self.do_background_work(&mut api);
                    progress = progress || bg_progress;
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

} // verus!
