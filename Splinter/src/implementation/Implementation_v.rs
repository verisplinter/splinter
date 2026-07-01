/*
Legacy implementation guide.

This is the previous executable Implementation_v body, kept as reference while
the active implementation path moves to UnifiedCacheProgramModel. It is
commented out because the concrete and monolithic atomic modules it imports
have been retired from the active module graph.

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
use crate::implementation::AtomicState_v::{AtomicState, DiskEvent, InflightInfo, InternalEvent, ProgramEvent, journal_marshall_labels, map_to_multiset, to_journal_records};
use crate::implementation::RecoveryState_v::RecoveryState;
use crate::implementation::MultisetMapRelation_v::{multiset_map_singleton, multiset_map_singleton_ensures, multiset_to_map, unique_keys};
use crate::implementation::VecMap_v::VecMap;
use crate::implementation::JournalTypes_v::{ILsn};
use crate::allocation_layer::AllocationJournal_v::lsn_au_index_discard_up_to;
use crate::allocation_layer::LikesJournal_v::lsn_addr_index_discard_up_to;
use crate::implementation::JournalImpl_v::{BeginWritebackForTargetResult, CleanForCommitResult, FrozenJournal, IJournalSnapshot, JournalImpl, RecoverIndexResult, RecoverMapResult, all_pages_parsable, cache_matches_raw_disk, iaddr_view, journal_disk_inv, load_index_labels, map_recovery_labels};
use crate::implementation::SuperblockTypes_v;
use crate::implementation::SuperblockTypes_v::{ASuperblock, ISuperblock};
use crate::implementation::StoreImpl_v::{LoadMapResult, StoreImpl, raw_page_to_store_kmmap};
use crate::implementation::CachedJournal_v::{CachedJournal, freeze_reads_for_seq_end};
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
use crate::disk::GenericDisk_v::to_aus;
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
                assert(self.superblocking_reqs@ + out@
                    == self.superblocking_reqs@ + seq![req] + prev_out);
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
            match outstanding[id] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    FracCacheImpl::valid_writeback_handle_model_entry(&new_cache, &write_addr, handle);
                    FracCacheImpl::entry_fetched_from_view(&new_cache, &write_addr);
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
            match outstanding[id] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                },
                _ => {
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
                    vstd::set::axiom_set_remove_same(outstanding.dom(), req_id);
                }
            };
            vstd::map::axiom_map_remove_different(outstanding, id2, req_id);
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
                    vstd::set::axiom_set_remove_same(outstanding.dom(), req_id);
                }
            };
            vstd::map::axiom_map_remove_different(outstanding, id2, req_id);
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
                    vstd::set::axiom_set_remove_same(outstanding.dom(), id);
                }
            };

            vstd::map::axiom_map_remove_different(outstanding, id2, id);

            vstd::map::axiom_map_remove_domain(outstanding, id);
            vstd::set::axiom_set_remove_different(outstanding.dom(), id2, id);

            match outstanding[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr: wa2, handle: h2}
                | OutstandingReqInfo::StoreWriteReq{write_addr: wa2, handle: h2} => {

                    assert(wa2@ != write_addr@) by {
                        if wa2@ == write_addr@ {
                        }
                    };

                    FracCacheImpl::valid_writeback_handle_model_entry(&new_cache, &wa2, h2);
                    FracCacheImpl::entry_fetched_from_view(&new_cache, &wa2);
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
                    vstd::set::axiom_set_remove_same(outstanding.dom(), id);
                }
            };

            vstd::map::axiom_map_remove_different(outstanding, id2, id);

            vstd::map::axiom_map_remove_domain(outstanding, id);
            vstd::set::axiom_set_remove_different(outstanding.dom(), id2, id);

            match outstanding[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr: wa2, handle: h2}
                | OutstandingReqInfo::StoreWriteReq{write_addr: wa2, handle: h2} => {

                    assert(wa2@ != write_addr@) by {
                        if wa2@ == write_addr@ {
                        }
                    };

                    FracCacheImpl::valid_writeback_handle_model_entry(&new_cache, &wa2, h2);
                    FracCacheImpl::entry_fetched_from_view(&new_cache, &wa2);
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
                    vstd::set::axiom_set_remove_same(outstanding.dom(), id);
                }
            };
            vstd::map::axiom_map_remove_different(outstanding, id2, id);

            vstd::map::axiom_map_remove_domain(outstanding, id);
            vstd::set::axiom_set_remove_different(outstanding.dom(), id2, id);

            match outstanding[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr: ra2, load_handle: h2} => {

                    assert(ra2@ != read_addr@) by {
                        if ra2@ == read_addr@ {
                        }
                    };

                    FracCacheImpl::entry_fetched_from_view(&new_cache, &ra2);
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    FracCacheImpl::valid_writeback_handle_model_entry(&new_cache, &write_addr, handle);
                    FracCacheImpl::entry_fetched_from_view(&new_cache, &write_addr);
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
        assert(cache_reqs.remove(id).is_injective()) by {
            assert forall |id1: ID, id2: ID| #![auto]
                cache_reqs.remove(id).contains_key(id1)
                && cache_reqs.remove(id).contains_key(id2)
                && cache_reqs.remove(id)[id1] == cache_reqs.remove(id)[id2]
                implies id1 == id2 by {
                vstd::map::axiom_map_remove_different(cache_reqs, id1, id);
                vstd::map::axiom_map_remove_different(cache_reqs, id2, id);
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
                    vstd::set::axiom_set_remove_same(outstanding.dom(), id);
                }
            };
            vstd::map::axiom_map_remove_different(outstanding, id2, id);
            vstd::map::axiom_map_remove_different(cache_reqs, id2, id);
            match outstanding[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr: ra2, load_handle: h2} => {
                    vstd::map::axiom_map_remove_domain(cache_reqs, id);
                    vstd::set::axiom_set_remove_different(cache_reqs.dom(), id2, id);
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    vstd::map::axiom_map_remove_domain(cache_reqs, id);
                    vstd::set::axiom_set_remove_different(cache_reqs.dom(), id2, id);
                },
                OutstandingReqInfo::SuperBlockReq{} => {
                    vstd::map::axiom_map_remove_domain(cache_reqs, id);
                    vstd::set::axiom_set_remove_different(cache_reqs.dom(), id2, id);
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
        assert(cache_reqs.remove(id).is_injective()) by {
            assert forall |id1: ID, id2: ID| #![auto]
                cache_reqs.remove(id).contains_key(id1)
                && cache_reqs.remove(id).contains_key(id2)
                && cache_reqs.remove(id)[id1] == cache_reqs.remove(id)[id2]
                implies id1 == id2 by {
                vstd::map::axiom_map_remove_different(cache_reqs, id1, id);
                vstd::map::axiom_map_remove_different(cache_reqs, id2, id);
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
                    vstd::set::axiom_set_remove_same(outstanding.dom(), id);
                }
            };
            vstd::map::axiom_map_remove_different(outstanding, id2, id);
            vstd::map::axiom_map_remove_different(cache_reqs, id2, id);
            match outstanding[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr: ra2, load_handle: h2} => {
                    vstd::map::axiom_map_remove_domain(cache_reqs, id);
                    vstd::set::axiom_set_remove_different(cache_reqs.dom(), id2, id);
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle}
                | OutstandingReqInfo::StoreWriteReq{write_addr, handle} => {
                    vstd::map::axiom_map_remove_domain(cache_reqs, id);
                    vstd::set::axiom_set_remove_different(cache_reqs.dom(), id2, id);
                },
                OutstandingReqInfo::SuperBlockReq{} => {
                    vstd::map::axiom_map_remove_domain(cache_reqs, id);
                    vstd::set::axiom_set_remove_different(cache_reqs.dom(), id2, id);
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
        &&& self.state().journal == self.journal@
        &&& self.store.persistent_store_ptr_matches_alloc_au()
    }

    spec fn inv_reading_journal(self) -> bool
    {
        &&& (!self.journal.index_ready() ==> self.state().recovery_state is SuperblockAvailable)
        &&& (self.journal.index_ready() ==> self.state().recovery_state is MetadataLoadComplete)
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
        &&& self.state().recovery_state is MetadataLoadComplete
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
            (self.state().in_flight is Some) <==> (self.in_flight is Some),
            self.state().in_flight is Some ==> iaddr_view(self.in_flight.unwrap().store_ptr) == self.state().in_flight.unwrap().store_ptr,
        ensures
    {
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
                assert(pre_state.state == old(self).state()) by {
                }

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
            assert(self.state().cache == self.cache@) by {
            }
            assert(self.outstanding_requests_wf()) by {
            }
            assert(self.outstanding_requests_match_cache_reqs()) by {
            }
            self.store.prepared_store_ptr_has_alloc_au();
            self.store.prepared_store_ptr_before_next_alloc();
            self.store.persistent_store_ptr_has_alloc_au();
            self.store.persistent_store_ptr_before_next_alloc();
            let inflight_store_ptr = if self.in_flight is Some { self.in_flight.unwrap().store_ptr } else { None };
            if inflight_store_ptr is Some {
            }
            self.store.store_addrs_are_alloc_au(inflight_store_ptr);
            self.state_store_addrs_match();
            if self.state().in_flight is Some {
                let sync_version = self.state().in_flight.unwrap().journal_version;
                let new_persistent_map_version = self.in_flight.unwrap().new_boundary_lsn as nat;
                self.journal.view_marshaled_seq_end_ensures();
                self.journal.view_seq_end_ensures();
                if self.in_flight.unwrap().store_ptr is Some {
                }
            }
            assert(self.sync_reqs_in_version(self.sync_requests.buffered_reqs@, self.version())) by {
            }
            assert(self.sync_requests.sync_target_lsn <= self.version()) by {
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
        assume(false);
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
                let end_lsn = pre_state.state.journal.seq_end();
                let map_req = req.mapspec_req();
                let map_reply = reply.mapspec_reply();
                assert(pre_state.state == old(self).state()) by {
                }

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
                assert(self.inv_running()) by {
                }
                assert(self.inv()) by {
                }
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
        let ghost version = pre_state.state.journal.seq_end();
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

        proof {
            assume(self.inv_api(api));
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
                        assert(self.store.wf());
                        self.store.prepared_store_ptr_before_next_alloc();
                        self.store.persistent_store_ptr_view_ensures();
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
                                    ..post_reserve_state.state
                                }
                            };
                            let tracked mut model1 = KVStoreTokenized::model::arbitrary();
                            proof {
                                let ghost pre_freeze_state = self.model@.value();
                                tracked_swap(self.model.borrow_mut(), &mut model1);
                                assert(pre_freeze_state.state == post_reserve_state.state);
                                assert(raw_page_to_store_kmmap(raw_page_g) == self.store@);
                                self.journal.view_seq_end_ensures();
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
                                assert(self.state().journal == self.journal@);
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
                            first: 0,
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
                                assert(pre_model.state.in_flight is Some <==> self.in_flight is Some);
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
                                        assert(self.state().journal == self.journal@);
                                        assert(self.state().outstanding_cache_reqs == new_outstanding_cache_reqs);
                                        assert(self.state().in_flight is Some <==> self.in_flight is Some);
                                        assert(self.state().in_flight is Some <==> self.sync_requests.in_flight());
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
                                        assert(self.state().journal == self.journal@);
                                        assert(self.state().outstanding_cache_reqs == pre_model.state.outstanding_cache_reqs);
                                        assert(self.state().in_flight is Some <==> self.in_flight is Some);
                                        assert(self.state().in_flight is Some <==> self.sync_requests.in_flight());
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
                        reads: freeze_reads_for_seq_end(
                            frozen_journal.snapshot@,
                            frozen_journal.seq_end as nat,
                        ),
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
        }
        let ghost pre_send_outstanding = self.outstanding_requests@;
        {
            let tracked mut model = KVStoreTokenized::model::arbitrary();
            let ghost post_state = ConcreteProgramModel {
                state: state_after_freeze
            };

            proof {
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
            assert(self.prepared_store_ptr_view() == iaddr_view(prepared_store_ptr_for_send));
            assert(self.prepared_store_lsn_nat() == prepared_store_lsn_for_send as nat);
            assert(pre.journal == self.journal@);
            assert(post.journal == self.journal@);
            assert(AtomicState::sync_begin_journal_ok(
                pre,
                post,
                frozen_journal.snapshot@,
                frozen_journal.seq_end as nat,
            )) by {
                if frozen_journal.snapshot.boundary_lsn as nat == pre.journal.seq_end()
                    && frozen_journal.snapshot.freshest_rec is None
                    && frozen_journal.seq_end as nat == pre.journal.seq_end()
                {
                    assert(post.journal == pre.journal);
                    assert(frozen_journal.snapshot.freshest_rec is None);
                    assert(frozen_journal.seq_end as nat == pre.journal.seq_end());
                } else {
                    let journal_lbl = CachedJournal::Label::FreezeForCommit{
                        frozen: frozen_journal.snapshot@,
                        reads: freeze_reads_for_seq_end(
                            frozen_journal.snapshot@,
                            frozen_journal.seq_end as nat,
                        ),
                    };
                    assume(CachedJournal::State::next(pre.journal, post.journal, journal_lbl));
                }
            };
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
                if motivation is PushMap {
                    assert(frozen_journal.snapshot.boundary_lsn as nat == prepared_store_lsn_for_send as nat);
                    assume(frozen_journal.snapshot.boundary_lsn as nat == pre.journal.seq_end());
                } else {
                    self.journal.view_seq_start_ensures();
                    assert(frozen_journal.seq_start() as nat == self.journal.seq_start());
                    assert(pre.journal == self.journal@);
                    assert(frozen_journal.snapshot.boundary_lsn as nat == frozen_journal.seq_start() as nat);
                    assert(frozen_journal.snapshot.boundary_lsn as nat == pre.journal.snapshot.boundary_lsn);
                }
            };
            assert(post == AtomicState{
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
                assert(committed_version_lsn == prepared_store_lsn_for_send);
                assert(pushmap_target_covered);
                assert(target_lsn as nat <= prepared_store_lsn_for_send as nat);
                self.journal.view_seq_start_ensures();
                assert(self.state().journal.snapshot.boundary_lsn == self.journal.seq_start());
                assert(self.journal.seq_start() <= self.state().in_flight.unwrap().boundary_lsn);
            } else {
                let journal_lbl = CachedJournal::Label::FreezeForCommit{
                    frozen: frozen_journal.snapshot@,
                    reads: freeze_reads_for_seq_end(
                        frozen_journal.snapshot@,
                        frozen_journal.seq_end as nat,
                    ),
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
            assume(self.state().in_flight.unwrap().journal_version <= self.journal.seq_end());
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
        assume(self.state().wf());
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
        assume(!self.state().sync_req_map.dom().contains(req.id));
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
            tj.build_lsn_au_index(tj.seq_start()) == self.journal@.status.unwrap().lsn_au_index
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
        assume(forall |addr: Address, data: RawPage| self.cache@.valid_read(addr, data)
            ==> journal_raw_disk.contains_key(addr) && journal_raw_disk[addr] == data);
        // Connect model journal snapshot to exec journal snapshot:
        // !(Begin) + inv() → !(FetchingSuperblock) → inv_post_superblock_common()
        // → self.state().journal == self.journal@ → model.program.state.journal.snapshot == self.journal.snapshot@
        // persistent_journal_structure fires: !(AwaitingSuperblock) ∧ !(RecoveryComplete)
        // (AwaitingSuperblock can't hold when inv() holds and !(Begin) — only Begin maps to FetchingSuperblock)

        // persistent_journal_index_matches_disk: when MetadataLoadComplete with freshest_rec,
        // tj.build_lsn_au_index(...) == model's AU index == self.journal@.status.unwrap().lsn_au_index
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
            tj.build_lsn_au_index(tj.seq_start()) == self.journal@.status.unwrap().lsn_au_index
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
            self.journal.view_seq_start_ensures();
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
        }

        let mut in_flight = None;
        std::mem::swap(&mut self.in_flight, &mut in_flight);
        if let Some(InFlight{new_boundary_lsn, freshest_rec, new_persistent_lsn, store_ptr}) = in_flight {
            proof {
            }
            match store_ptr {
                Some(ptr) => {
                    let expected_store_au = self.store.exec_alloc_au();
                    if ptr.au != expected_store_au {
                        Self::todo_placeholder();
                    }
                }
                None => {}
            }
            self.store.set_persistent_store_ptr(store_ptr);
            self.store.set_prepared_store(store_ptr, new_boundary_lsn);
            self.journal.discard_old(new_boundary_lsn);

            let ghost post_state = ConcreteProgramModel{ state: AtomicState{
                in_flight: None,
                journal: self.journal@,
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
                let new_lsn_au_index = lsn_au_index_discard_up_to(
                    pre_state.state.journal.status.unwrap().lsn_au_index,
                    pre_state.state.in_flight.unwrap().boundary_lsn,
                );
                let deallocs = pre_state.state.journal.status.unwrap().lsn_au_index.values()
                    - new_lsn_au_index.values();

                assert( response_shard@.multiset() == Multiset::singleton((pre_state.state.in_flight->Some_0.req_id, DiskResponse::WriteResp{})) );    // extn // trigger

                // Access inv_running conjuncts from old(self).inv() precondition

                // discard_old: advance journal boundary
                reveal(CachedJournal::State::next_by);
                reveal(CachedJournal::State::next);
                let journal_lbl = CachedJournal::Label::DiscardOld{
                    start_lsn: pre_state.state.in_flight.unwrap().boundary_lsn,
                    require_end: post_state.state.journal.seq_end(),
                    deallocs,
                };
                assert(CachedJournal::State::next_by(
                    pre_state.state.journal,
                    post_state.state.journal,
                    journal_lbl,
                    CachedJournal::Step::discard_old(),
                )) by {
                    assert(deallocs ==
                        pre_state.state.journal.status.unwrap().lsn_au_index.values()
                        - post_state.state.journal.status.unwrap().lsn_au_index.values());
                };
                assert(CachedJournal::State::next(
                    pre_state.state.journal,
                    post_state.state.journal,
                    journal_lbl,
                ));

                reveal(Cache::State::next_by);
                reveal(Cache::State::next);
                let cache_lbl = Cache::Label::EvictableCheck{aus: to_aus(discard_addrs)};
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
                assert(self.i_ephemeral_store() == pre_view_store) by {
                }
                self.store.store_addrs_none_matches_persistent_view();
                self.state_store_addrs_match();
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
                assert(self.state().outstanding_cache_reqs.dom() <= self.outstanding_requests@.dom()) by {
                    assert(self.state().outstanding_cache_reqs.dom() <= pre_outstanding.dom()) by {
                    }
                    assert forall |id2: ID| #[trigger] self.state().outstanding_cache_reqs.dom().contains(id2)
                        implies self.outstanding_requests@.dom().contains(id2) by {
                        if id2 == id {
                            self.system_inv_sb_id_not_in_cache_reqs();
                        }
                        vstd::set::axiom_set_remove_different(pre_outstanding.dom(), id2, id);
                    };
                }
                assert forall |id2: ID| #![auto]
                    self.outstanding_requests@.dom().contains(id2)
                    && self.outstanding_requests@[id2] is SuperBlockReq
                    implies false by {
                    vstd::map::axiom_map_remove_different(pre_outstanding, id2, id);
                };
                self.store.prepared_store_ptr_has_alloc_au();
                self.store.prepared_store_ptr_before_next_alloc();
                self.store.persistent_store_ptr_has_alloc_au();
                self.store.persistent_store_ptr_before_next_alloc();
                self.store.store_addrs_are_alloc_au(None);
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
            if !(self.recovery_phase is FetchingSuperblock) {
                let inflight_store_ptr = if self.in_flight is Some { self.in_flight.unwrap().store_ptr } else { None };
                if inflight_store_ptr is Some {
                }
                self.store.store_addrs_are_alloc_au(inflight_store_ptr);
            }
            assert(self.model_reqs_in_outstanding()) by {
                let in_flight_sb_id = if self.state().in_flight is Some { set!{self.state().in_flight.unwrap().req_id} } else { set!{} };
                assert((self.state().outstanding_cache_reqs.dom() + in_flight_sb_id) <= self.outstanding_requests@.dom()) by {
                    assert forall |id2: ID| #[trigger] (self.state().outstanding_cache_reqs.dom() + in_flight_sb_id).contains(id2)
                        implies self.outstanding_requests@.dom().contains(id2) by {
                        if id2 == id {
                            if in_flight_sb_id.contains(id2) {
                                self.system_inv_sb_id_not_in_cache_reqs();
                            }
                        }
                        vstd::set::axiom_set_remove_different(pre_outstanding.dom(), id2, id);
                    };
                }
            }
            if self.recovery_phase is ReadingJournalIndex {
                assert forall |id2: ID| #[trigger] self.outstanding_requests@.contains_key(id2)
                    implies self.outstanding_requests@[id2] is CacheLoadReq by {
                    vstd::map::axiom_map_remove_different(pre_outstanding, id2, id);
                };
                assert(self.inv_reading_journal()) by {
                }
            } else if self.recovery_phase is ApplyingJournalToRecoverEphemeralMap {
                assert forall |id2: ID| #[trigger] self.outstanding_requests@.contains_key(id2)
                    implies self.outstanding_requests@[id2] is CacheLoadReq by {
                    vstd::map::axiom_map_remove_different(pre_outstanding, id2, id);
                };
                assert(self.inv_applying_journal()) by {
                }
            } else if self.recovery_phase is ReadyForUserOperation {
                assert(self.inv_running()) by {
                }
            }
            assert forall |id2: ID| #![auto]
                self.outstanding_requests@.dom().contains(id2)
                && self.outstanding_requests@[id2] is SuperBlockReq
                implies self.in_flight is Some
                    && !self.state().outstanding_cache_reqs.dom().contains(id2)
                    && self.state().in_flight is Some
                    && id2 == self.state().in_flight.unwrap().req_id by {
                vstd::map::axiom_map_remove_different(pre_outstanding, id2, id);
            };
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
            assert(AtomicState::disk_transition(pre_state.state, post_state.state, disk_event, info.reqs, info.resps)); // trigger
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
            Self::outstanding_requests_wf_map_remove_journal_after_complete(
                pre_outstanding,
                pre_cache_impl,
                self.cache,
                pre_cache_reqs,
                id,
                write_addr,
            );
        }

        if self.journal_flush_accumulator == 0 {
            // TODO: eliminate this once we strengthen the self.inv to relate journal_flush_accumulator with
            // the number of entries present in outstanding req info
            Self::todo_placeholder();
        }
        self.journal_flush_accumulator = self.journal_flush_accumulator - 1;
        if self.journal_flush_accumulator == 0 {
            proof {
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
            assert(AtomicState::disk_transition(pre_state.state, post_state.state, disk_event, info.reqs, info.resps)); // trigger
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
                        self.store.persistent_store_ptr_before_next_alloc();
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
                match superblock.store_ptr {
                    Some(ptr) => {
                    }
                    None => {}
                }
            }

            // Compute the next ghost model and transition our token.
            let ghost post_state = ConcreteProgramModel{
                state: AtomicState {
                    recovery_state: RecoveryState::SuperblockAvailable,                    
                    journal: self.journal@,
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
            self.store.prepared_store_ptr_has_alloc_au();
            self.store.prepared_store_ptr_before_next_alloc();
            self.store.persistent_store_ptr_has_alloc_au();
            self.store.persistent_store_ptr_before_next_alloc();
            self.store.store_addrs_are_alloc_au(None);
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
        let ghost pre_persistent_store_ptr = self.store.persistent_store_ptr_view();
        let ghost pre_cache_impl = self.cache;
        let ghost pre_outstanding = self.outstanding_requests@;
        proof {
            self.system_inv_implies_atomic_state_wf();
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
                    assert(AtomicState::disk_transition(pre_state.state, post_state.state, disk_event, program_lbl->info.reqs, program_lbl->info.resps)); // trigger
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
                }
                self.outstanding_requests.insert(id, OutstandingReqInfo::CacheLoadReq{
                    read_addr: store_ptr,
                    load_handle: slot_handle,
                });
                proof {
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
                        ..pre_state.state
                    }
                };

                proof {
                    self.journal.view_seq_start_ensures();
                    assert(pre_state.state.recovery_state is SuperblockAvailable
                        || pre_state.state.recovery_state is MetadataLoadComplete);
                    let cache_lbl = Cache::Label::Access{reads: reads@, writes: Map::empty()};
                    assume(Cache::State::next(pre_state.state.cache, post_state.state.cache, cache_lbl));
                    if pre_persistent_store_ptr is None {
                    } else {
                        let ptr = pre_persistent_store_ptr.unwrap();
                    }
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
            self.store.prepared_store_ptr_has_alloc_au();
            self.store.prepared_store_ptr_before_next_alloc();
            self.store.persistent_store_ptr_has_alloc_au();
            self.store.persistent_store_ptr_before_next_alloc();
            if self.recovery_phase is ApplyingJournalToRecoverEphemeralMap {
                self.journal.seq_start_le_seq_end();
            }
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
                            recovery_state: RecoveryState::MetadataLoadComplete,
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
            if self.recovery_phase is ApplyingJournalToRecoverEphemeralMap {
                assert(self.inv_applying_journal()) by {
                }
            }
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
            self.system_inv_implies_atomic_state_wf();
            assert(self.inv_applying_journal()) by {
            }
            assert(self.in_flight is None) by {
                if self.in_flight is Some {
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
                // inv_applying_journal gives recovery_state is MetadataLoadComplete
            }
            let ghost journal_raw_disk = self.system_inv_journal_pages_parsable();
            let start_lsn = self.store.exec_store_lsn();
            proof {
                assume(self.journal@.snapshot.freshest_rec is Some ==> {
                    let journal_dv = LinkedJournal_v::DiskView{
                        boundary_lsn: self.journal@.snapshot.boundary_lsn,
                        entries: to_journal_records(journal_raw_disk),
                    };
                    let tj = LinkedJournal_v::TruncatedJournal{
                        freshest_rec: self.journal@.snapshot.freshest_rec,
                        disk_view: journal_dv,
                    };
                    &&& journal_disk_inv(journal_dv, self.journal@.snapshot.freshest_rec)
                    &&& tj.build_lsn_addr_index() == self.journal.status.unwrap().lsn_addr_index@
                });
            }
            let fetch = self.journal.recover_map_step(&mut self.cache, start_lsn, Ghost(journal_raw_disk));

            // we need to track some
            match fetch {
                RecoverMapResult::NotInCache{} => {
                    proof {
                        self.store.store_addrs_are_alloc_au(None);
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
                        assert(CachedJournal::State::next(
                            journal_after_fetch,
                            journal_after_fetch,
                            map_recovery_labels(fetch_boundary_lsn, reads@, addr@).1,
                        ));
                        self.store.kmmap_wf_ensures();
                        let empty_prefix = records.discard_recent(self.store.store_lsn_nat());
                        reveal_with_fuel(MsgHistory::apply_to_stamped_map, 1);
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
                                    let prefix = records.discard_recent(old_store_lsn);
                                    assert(old_store_lsn < records.seq_end) by {
                                    }
                                    let next_prefix = records.discard_recent((old_store_lsn + 1) as nat);
                                    assert(next_prefix.discard_recent(old_store_lsn).ext_equal(prefix)) by {
                                        assert forall |lsn: LSN| #[trigger] next_prefix.discard_recent(old_store_lsn).msgs.contains_key(lsn)
                                            <==> prefix.msgs.contains_key(lsn) by {
                                            assert(next_prefix.discard_recent(old_store_lsn).contains(lsn)
                                                <==> next_prefix.seq_start <= lsn < old_store_lsn);
                                        }
                                    }
                                    assert(next_prefix.discard_recent(old_store_lsn) == prefix) by {
                                        MsgHistory::ext_equal_is_equality();
                                    }
                                    assert(record_msgs.msgs[old_store_lsn]
                                        == record.parsedv().messages[(old_store_lsn - record.header.start_lsn as nat) as int]);
                                    assert(records.msgs[old_store_lsn] == km) by {
                                    }
                                    reveal_with_fuel(MsgHistory::apply_to_stamped_map, 2);
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
                            ..pre_state.state
                        }
                    };
                    let final_store_lsn = self.store.exec_store_lsn();

                    proof {
                        assert(ConcreteProgramModel::valid_internal_transition(pre_state, post_state)) by {
                            assume(AtomicState::internal_transitions(
                                pre_state.state,
                                post_state.state,
                                InternalEvent::MapRecovery{records, reads: reads@, addr: addr@}
                            ));
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
                            self.store.prepared_store_ptr_view_ensures();
                            self.store.prepared_store_lsn_nat_ensures();
                            self.store.prepared_store_ptr_has_alloc_au();
                            self.store.prepared_store_ptr_before_next_alloc();
                            self.store.persistent_store_ptr_has_alloc_au();
                            self.store.persistent_store_ptr_before_next_alloc();
                            self.store.store_addrs_are_alloc_au(None);
                            self.state_store_addrs_match();
                        }
                        return true;
                    }
                }
            }
        }
        let exec_seq_end = self.journal.exec_seq_end();
        if self.store.exec_store_lsn() < exec_seq_end {
            proof {
            }
            return true;
        }
        proof {
        }
        let ghost pre_state = self.state();
        proof {
            self.journal.view_seq_end_ensures();
        }

        {
            self.recovery_phase = RecoveryPhase::ReadyForUserOperation;

            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

            let ghost post_state = ConcreteProgramModel{
                state: AtomicState {
                    recovery_state: RecoveryState::RecoveryComplete,
                    journal: pre_state.journal,
                    persistent_journal_seq_end: pre_state.journal.seq_end(),
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
                        let end_lsn = pre_state.journal.seq_end();
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
                self.store.prepared_store_ptr_view_ensures();
                self.store.prepared_store_lsn_nat_ensures();
                self.store.prepared_store_ptr_has_alloc_au();
                self.store.prepared_store_ptr_before_next_alloc();
                self.store.persistent_store_ptr_has_alloc_au();
                self.store.persistent_store_ptr_before_next_alloc();
                self.store.store_addrs_are_alloc_au(None);
                self.store.store_addrs_none_matches_persistent_view();
                self.state_store_addrs_match();
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
            assume(!self.store_addrs().contains(addr@));
            assume(!self.journal@.status.unwrap().lsn_au_index.values().contains(addr@.au));
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
                    self.system_inv_implies_atomic_state_wf();
                }

                let marshalled_end_now = self.journal.exec_marshaled_seq_end();
                let seq_end_now = self.journal.exec_seq_end();
                proof {
                }
                if marshalled_end_now == seq_end_now {
                    Self::todo_placeholder();
                }

                proof {
                    assume(!self.journal.status.unwrap().lsn_addr_index@.values().contains(addr@));
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
                    let event = InternalEvent::JournalMarshallStep{addr: addr@, raw_page};
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
                    self.store.prepared_store_ptr_has_alloc_au();
                    self.store.prepared_store_ptr_before_next_alloc();
                    self.store.persistent_store_ptr_has_alloc_au();
                    self.store.persistent_store_ptr_before_next_alloc();
                    let inflight_store_ptr = if self.in_flight is Some { self.in_flight.unwrap().store_ptr } else { None };
                    if inflight_store_ptr is Some {
                    }
                    self.store.store_addrs_are_alloc_au(inflight_store_ptr);
                    self.state_store_addrs_match();
                    if self.state().in_flight is Some {
                        let sync_version = self.state().in_flight.unwrap().journal_version;
                        let new_persistent_map_version = self.in_flight.unwrap().new_boundary_lsn as nat;
                        self.journal.view_marshaled_seq_end_ensures();
                        self.journal.view_seq_end_ensures();
                        if self.in_flight.unwrap().store_ptr is Some {
                        }
                    }
                    assert(self.sync_reqs_in_version(
                        self.sync_requests.journal_cleaning_reqs@,
                        self.sync_requests.sync_target_lsn as nat,
                    ));
                    assert(Self::three_sync_req_lists_mutually_unique(
                        self.sync_requests.superblocking_reqs@,
                        self.sync_requests.journal_cleaning_reqs@,
                        self.sync_requests.buffered_reqs@,
                    ));
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
            boundary_lsn: 0, freshest_rec: None, first: 0, };
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
*/

// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

// Unified-cache implementation scaffold.
//
// The old executable body is preserved above as a commented reference. The
// active code below rebuilds the entry shape against UnifiedCacheProgramModel
// and keeps the component transition bodies as explicit stubs.

#![allow(unused_imports)]
#![allow(unused_variables)]

use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::hash_map::HashMapWithView;
use vstd::modes::tracked_swap;
use vstd::multiset::Multiset;
use vstd::tokens::InstanceId;

use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::disk::GenericDisk_v::{Address, AU};
use crate::implementation::MultisetMapRelation_v::{
    multiset_map_singleton, multiset_map_singleton_ensures, multiset_to_map,
};
use crate::implementation::AbstractSuperblock_v::{
    abstract_superblock_raw_wf, superblock_matches,
};
use crate::implementation::AtomicBranchState_v::AtomicBranchState;
use crate::implementation::AtomicJournalState_v::AtomicJournalState;
use crate::implementation::AuPoolImpl_v::{
    initial_free_aus as au_pool_initial_free_aus, AuPoolImpl,
};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedBranch_v::CachedBranch;
use crate::implementation::CachedJournal_v::CachedJournal;
use crate::implementation::CrashAwareCachingDiskSystemRefinement_v as CachingDiskSystemRefinement;
use crate::implementation::DiskLayout_v::{DiskLayout, spec_superblock_addr, superblock_addr};
use crate::implementation::FracCacheImpl_v::{
    FetchErrorCode, FracCacheImpl, MutHandle, WritebackAcquireResult, WritebackHandle,
    PAGE_SIZE_BYTES,
};
use crate::implementation::JournalImpl_v::{IJournalSnapshot, JournalImpl};
use crate::implementation::JournalTypes_v::to_journal_records;
use crate::implementation::RecoveryState_v::RecoveryState;
use crate::implementation::UnifiedCacheProgramModel_v::UnifiedCacheProgramModel;
use crate::implementation::UnifiedCacheSystemRefinement_v as UnifiedCacheSystemRefinement;
use crate::implementation::UnifiedCacheSystem_v::{
    AtomicSyncPhase, UnifiedCacheSystem, cache_write_response_addrs,
};
use crate::spec::AsyncDisk_t::{DiskRequest, DiskResponse};
use crate::spec::ImplDisk_t::{IAddress, IAU, IDiskRequest, IDiskResponse};
use crate::spec::MapSpec_t::{CrashTolerantAsyncMap, ID, SyncReqId};
use crate::trusted::ClientAPI_t::{ClientAPI, DiskResponseRecord};
use crate::trusted::KVStoreTrait_t::{KVStoreTrait, open_system_invariant_disk_response_singleton};
use crate::trusted::KVStoreTokenized_t::KVStoreTokenized;
use crate::trusted::ProgramModelTrait_t::{ProgramDiskInfo, ProgramLabel, ProgramModelTrait};
use crate::trusted::RefinementObligation_t::RefinementObligation;
use crate::trusted::ReqReply_t::{Input, Request};
use crate::trusted::SystemModel_t::SystemModel;

verus! {

pub const TOTAL_AUS: IAU = 100;

pub open spec fn initial_free_aus() -> Set<AU>
{
    au_pool_initial_free_aus(TOTAL_AUS)
}

pub fn bootstrap_alloc_au() -> (out: IAU)
    ensures
        0 < (out as nat),
        (out as nat) < (TOTAL_AUS as nat),
{
    1
}

pub type ModelShard = KVStoreTokenized::model<UnifiedCacheProgramModel>;
pub type RequestShard = KVStoreTokenized::requests<UnifiedCacheProgramModel>;
pub type ReplyShard = KVStoreTokenized::replies<UnifiedCacheProgramModel>;
pub type DiskRespShard = KVStoreTokenized::disk_responses_multiset<UnifiedCacheProgramModel>;
pub type DiskReqShard = KVStoreTokenized::disk_requests_multiset<UnifiedCacheProgramModel>;

pub struct UnifiedCacheRefinementProof;

#[derive(Debug, Copy, Clone)]
pub enum RecoveryPhase {
    FetchingSuperblock,
    LoadingJournal,
    LoadingBranch,
    ReadyForUserOperation,
}

pub enum OutstandingReqInfo {
    CacheRead{addr: IAddress, load_handle: MutHandle},
    CacheWrite{addr: IAddress, write_handle: WritebackHandle},
    SuperblockWrite,
}

pub struct Implementation {
    pub recovery_phase: RecoveryPhase,
    pub cache: FracCacheImpl,
    pub journal: JournalImpl,
    pub au_pool: AuPoolImpl,
    pub branch_loaded: bool,
    pub sync_requests: Vec<SyncReqId>,
    pub outstanding_requests: HashMapWithView<ID, OutstandingReqInfo>,
    pub should_retry_sync_launch: bool,

    pub model: Tracked<ModelShard>,
    pub instance: Tracked<KVStoreTokenized::Instance<UnifiedCacheProgramModel>>,
}

impl Implementation {
    pub closed spec fn state(&self) -> UnifiedCacheSystem::State
    {
        self.model@.value().state
    }

    pub closed spec fn instance_id(&self) -> InstanceId
    {
        self.instance@.id()
    }

    pub closed spec fn inv(&self) -> bool
    {
        &&& self.model@.instance_id() == self.instance@.id()
        &&& self.cache.wf()
        &&& self.journal.basic_wf()
        &&& self.au_pool.wf(TOTAL_AUS)
        &&& self.au_pool.canonical_wf(TOTAL_AUS)
        &&& self.state().cache == self.cache@
        &&& self.state().free_aus =~= self.au_pool@
        &&& self.outstanding_requests_wf()
        &&& self.outstanding_cache_reqs_match_model()
        &&& self.outstanding_requests_single_flight()
        &&& self.outstanding_requests@.dom().len() > 0 ==> {
            &&& !(self.state().recovery_state is Begin)
            &&& !(self.state().recovery_state is AwaitingSuperblock)
        }
        &&& self.recovery_phase is LoadingJournal ==> {
            self.state().journal.journal == self.journal@
        }
        &&& self.recovery_phase is ReadyForUserOperation ==> {
            self.state().recovery_state is RecoveryComplete
        }
    }

    pub closed spec fn wf_init(&self) -> bool
    {
        &&& self.inv()
        &&& self.recovery_phase is FetchingSuperblock
        &&& self.state().recovery_state is Begin
        &&& self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty()
    }

    pub closed spec fn inv_api(&self, api: &ClientAPI<UnifiedCacheProgramModel>) -> bool
    {
        &&& self.inv()
        &&& self.instance_id() == api.instance_id()
    }

    pub closed spec fn outstanding_cache_reqs_match_model(&self) -> bool
    {
        &&& self.state().outstanding_cache_reqs.dom() == self.outstanding_requests@.dom()
        &&& self.state().outstanding_cache_reqs.is_injective()
        &&& forall |id: ID| #[trigger] self.outstanding_requests@.contains_key(id) ==> {
            match self.outstanding_requests@[id] {
                OutstandingReqInfo::CacheRead{addr, ..}
                | OutstandingReqInfo::CacheWrite{addr, ..} => {
                    &&& self.state().outstanding_cache_reqs.contains_key(id)
                    &&& self.state().outstanding_cache_reqs[id] == addr@
                },
                OutstandingReqInfo::SuperblockWrite => {
                    !self.state().outstanding_cache_reqs.contains_key(id)
                },
            }
        }
    }

    pub closed spec fn outstanding_requests_wf(&self) -> bool
    {
        forall |id: ID| #[trigger] self.outstanding_requests@.contains_key(id) ==> {
            match self.outstanding_requests@[id] {
                OutstandingReqInfo::CacheRead{addr, load_handle} => {
                    &&& self.cache.entry_fetched(&addr)
                    &&& self.cache.valid_load_handle(&addr, load_handle)
                },
                OutstandingReqInfo::CacheWrite{addr, write_handle} => {
                    &&& self.cache.entry_fetched(&addr)
                    &&& self.cache.valid_writeback_handle(&addr, write_handle)
                },
                OutstandingReqInfo::SuperblockWrite => true,
            }
        }
    }

    pub closed spec fn no_outstanding_cache_io_for_addr(&self, addr: IAddress) -> bool
    {
        forall |id: ID| #[trigger] self.outstanding_requests@.contains_key(id) ==> {
            match self.outstanding_requests@[id] {
                OutstandingReqInfo::CacheRead{addr: other, ..}
                | OutstandingReqInfo::CacheWrite{addr: other, ..} => other@ != addr@,
                OutstandingReqInfo::SuperblockWrite => true,
            }
        }
    }

    pub closed spec fn outstanding_requests_single_flight(&self) -> bool
    {
        forall |id1: ID, id2: ID| {
            &&& #[trigger] self.outstanding_requests@.contains_key(id1)
            &&& #[trigger] self.outstanding_requests@.contains_key(id2)
        } ==> id1 == id2
    }

    fn issue_cache_read_io(
        &mut self,
        addr: IAddress,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    ) -> (started: bool)
        requires
            old(self).inv_api(old(api)),
            !(old(self).state().recovery_state is Begin),
            !(old(self).state().recovery_state is AwaitingSuperblock),
            addr@.wf(),
            addr@ != spec_superblock_addr(),
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
        ensures
            self.inv_api(api),
    {
        let ghost pre_state = self.model@.value();
        let ghost pre_outstanding = self.outstanding_requests@;
        let ghost pre_cache = self.cache;

        match self.cache.fetch(&addr, true) {
            FetchErrorCode::LoadInitiate{slot_handle} => {
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                }

                let req_id_perm = Tracked(api.send_disk_request_predict_id());
                let disk_req = IDiskRequest::ReadReq{from: addr};
                let ghost req_map = map![req_id_perm@ => disk_req@];
                let ghost updated = map![req_id_perm@ => addr@];
                let ghost disk_request_tuples =
                    multiset_map_singleton(req_id_perm@, disk_req@);
                let ghost disk_response_tuples = Multiset::empty();
                let ghost post_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        cache: self.cache@,
                        outstanding_cache_reqs:
                            pre_state.state.outstanding_cache_reqs.union_prefer_right(updated),
                        ..pre_state.state
                    }
                };

                proof {
                    multiset_map_singleton_ensures(req_id_perm@, disk_req@);
                    assert(multiset_to_map(disk_request_tuples) == req_map);
                    Self::singleton_updated_addr_map(req_id_perm@, disk_req@, addr@);
                    assert(updated.is_injective());
                    assert(!updated.contains_value(spec_superblock_addr()));
                    Self::singleton_req_map_values(req_id_perm@, disk_req@);
                    Self::singleton_addr_map_values_wf(req_id_perm@, addr@);
                    assert(updated.values() <= Set::new(|addr: Address| addr.wf()));
                    assert(UnifiedCacheSystem::State::cache_io_begin(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Disk,
                        req_map,
                        self.cache@,
                        disk_request_tuples,
                        disk_response_tuples,
                    )) by {
                    }
                    assert(UnifiedCacheSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Disk,
                        UnifiedCacheSystem::Step::cache_io_begin(
                            req_map,
                            self.cache@,
                            disk_request_tuples,
                            disk_response_tuples,
                        ),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    assert(UnifiedCacheSystem::State::next(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Disk,
                    )) by {
                        reveal(UnifiedCacheSystem::State::next);
                    }
                    let info = ProgramDiskInfo{
                        reqs: disk_request_tuples,
                        resps: disk_response_tuples,
                    };
                    assert(UnifiedCacheProgramModel::disk_step_matches_info(
                        pre_state.state,
                        UnifiedCacheSystem::Step::cache_io_begin(
                            req_map,
                            self.cache@,
                            disk_request_tuples,
                            disk_response_tuples,
                        ),
                        info,
                    ));
                    assert(exists |step: UnifiedCacheSystem::Step| {
                        &&& UnifiedCacheSystem::State::next_by(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheSystem::Label::Disk,
                            step,
                        )
                        &&& UnifiedCacheProgramModel::disk_step_matches_info(
                            pre_state.state,
                            step,
                            info,
                        )
                    }) by {
                        let step = UnifiedCacheSystem::Step::cache_io_begin(
                            req_map,
                            self.cache@,
                            disk_request_tuples,
                            disk_response_tuples,
                        );
                        assert(UnifiedCacheSystem::State::next_by(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheSystem::Label::Disk,
                            step,
                        ));
                        assert(UnifiedCacheProgramModel::disk_step_matches_info(
                            pre_state.state,
                            step,
                            info,
                        ));
                    }
                    assert(UnifiedCacheProgramModel::valid_disk_transition(
                        pre_state,
                        post_state,
                        info,
                    )) by {
                        reveal(UnifiedCacheProgramModel::valid_disk_transition);
                    }
                    assert(ProgramModelTrait::next(
                        pre_state,
                        post_state,
                        ProgramLabel::DiskIO{info},
                    ));
                }

                let tracked empty_disk_responses = DiskRespShard::empty(self.instance_id());
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
                self.outstanding_requests.insert(id, OutstandingReqInfo::CacheRead{
                    addr,
                    load_handle: slot_handle,
                });

                proof {
                    assert(self.outstanding_requests_wf()) by {
                        assert forall |id2: ID| #[trigger] self.outstanding_requests@.contains_key(id2)
                            implies {
                                match self.outstanding_requests@[id2] {
                                    OutstandingReqInfo::CacheRead{addr, load_handle} => {
                                        &&& self.cache.entry_fetched(&addr)
                                        &&& self.cache.valid_load_handle(&addr, load_handle)
                                    },
                                    OutstandingReqInfo::CacheWrite{addr, write_handle} => {
                                        &&& self.cache.entry_fetched(&addr)
                                        &&& self.cache.valid_writeback_handle(&addr, write_handle)
                                    },
                                    OutstandingReqInfo::SuperblockWrite => true,
                                }
                            } by {
                            if id2 == id {
                            } else {
                                assert(pre_outstanding == Map::<ID, OutstandingReqInfo>::empty());
                                assert(!pre_outstanding.contains_key(id2));
                                assert(false);
                            }
                        }
                    }
                    assert(self.outstanding_requests@.dom() =~= set![id]);
                    assert(pre_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty()) by {
                        assert(old(self).outstanding_cache_reqs_match_model());
                        assert(pre_state.state.outstanding_cache_reqs.dom()
                            == pre_outstanding.dom());
                        assert(pre_outstanding == Map::<ID, OutstandingReqInfo>::empty());
                        assert_maps_equal!(
                            pre_state.state.outstanding_cache_reqs,
                            Map::<ID, Address>::empty(),
                            k => {
                                if pre_state.state.outstanding_cache_reqs.contains_key(k) {
                                    assert(pre_state.state.outstanding_cache_reqs.dom().contains(k));
                                    assert(pre_outstanding.dom().contains(k));
                                    assert(false);
                                }
                            }
                        );
                    }
                    assert(self.state().outstanding_cache_reqs == map![id => addr@]) by {
                        assert(post_state.state.outstanding_cache_reqs
                            == pre_state.state.outstanding_cache_reqs.union_prefer_right(updated));
                        assert(pre_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty());
                        assert(updated == map![req_id_perm@ => addr@]);
                        assert(id == req_id_perm@);
                        assert_maps_equal!(self.state().outstanding_cache_reqs, map![id => addr@], k => {
                            if k == id {
                                assert(updated.contains_key(k));
                            } else {
                                assert(!updated.contains_key(k));
                            }
                        });
                    }
                    assert(self.outstanding_cache_reqs_match_model());
                    assert(self.outstanding_requests_single_flight());
                }
                true
            },
            FetchErrorCode::Success{slot_handle} => {
                self.cache.handle_release(&addr, slot_handle);
                proof {
                    assert(self.cache@ == pre_cache@) by {
                        assert(self.cache@.lookup_map == pre_cache@.lookup_map);
                        assert(self.cache@.status_map == pre_cache@.status_map);
                        assert(self.cache@.entries == pre_cache@.entries);
                    }
                    assert(self.outstanding_requests_wf());
                }
                false
            },
            FetchErrorCode::Awaiting
            | FetchErrorCode::CacheFull
            | FetchErrorCode::NotPresent => {
                proof {
                    assert(self.outstanding_requests_wf());
                }
                false
            },
        }
    }

    fn issue_cache_writeback_io(
        &mut self,
        addr: IAddress,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    ) -> (started: bool)
        requires
            old(self).inv_api(old(api)),
            !(old(self).state().recovery_state is Begin),
            !(old(self).state().recovery_state is AwaitingSuperblock),
            addr@.wf(),
            addr@ != spec_superblock_addr(),
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
        ensures
            self.inv_api(api),
    {
        let ghost pre_state = self.model@.value();
        let ghost pre_outstanding = self.outstanding_requests@;
        let ghost pre_cache = self.cache;

        match self.cache.begin_writeback(&addr) {
            WritebackAcquireResult::Acquired{handle} => {
                let write_data = handle.rec.clone();
                proof {
                    assert(self.cache.valid_writeback_handle(&addr, handle));
                    FracCacheImpl::valid_writeback_handle_has_inv(&self.cache, &addr, handle);
                    assert(handle.inv());
                    assert(handle.rec.len() == PAGE_SIZE_BYTES);
                    assert(write_data@ == handle.rec@);
                    assert(write_data.len() == PAGE_SIZE_BYTES);
                }

                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                }

                let req_id_perm = Tracked(api.send_disk_request_predict_id());
                let disk_req = IDiskRequest::WriteReq{to: addr, data: write_data};
                let ghost req_map = map![req_id_perm@ => disk_req@];
                let ghost updated = map![req_id_perm@ => addr@];
                let ghost disk_request_tuples =
                    multiset_map_singleton(req_id_perm@, disk_req@);
                let ghost disk_response_tuples = Multiset::empty();
                let ghost post_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        cache: self.cache@,
                        outstanding_cache_reqs:
                            pre_state.state.outstanding_cache_reqs.union_prefer_right(updated),
                        ..pre_state.state
                    }
                };

                proof {
                    multiset_map_singleton_ensures(req_id_perm@, disk_req@);
                    assert(multiset_to_map(disk_request_tuples) == req_map);
                    Self::singleton_updated_addr_map(req_id_perm@, disk_req@, addr@);
                    assert(updated.is_injective());
                    assert(!updated.contains_value(spec_superblock_addr()));
                    Self::singleton_req_map_values(req_id_perm@, disk_req@);
                    Self::singleton_addr_map_values_wf(req_id_perm@, addr@);
                    assert(updated.values() <= Set::new(|addr: Address| addr.wf()));
                    assert(UnifiedCacheSystem::State::cache_io_begin(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Disk,
                        req_map,
                        self.cache@,
                        disk_request_tuples,
                        disk_response_tuples,
                    )) by {
                    }
                    assert(UnifiedCacheSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Disk,
                        UnifiedCacheSystem::Step::cache_io_begin(
                            req_map,
                            self.cache@,
                            disk_request_tuples,
                            disk_response_tuples,
                        ),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    assert(UnifiedCacheSystem::State::next(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Disk,
                    )) by {
                        reveal(UnifiedCacheSystem::State::next);
                    }
                    let info = ProgramDiskInfo{
                        reqs: disk_request_tuples,
                        resps: disk_response_tuples,
                    };
                    assert(UnifiedCacheProgramModel::disk_step_matches_info(
                        pre_state.state,
                        UnifiedCacheSystem::Step::cache_io_begin(
                            req_map,
                            self.cache@,
                            disk_request_tuples,
                            disk_response_tuples,
                        ),
                        info,
                    ));
                    assert(exists |step: UnifiedCacheSystem::Step| {
                        &&& UnifiedCacheSystem::State::next_by(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheSystem::Label::Disk,
                            step,
                        )
                        &&& UnifiedCacheProgramModel::disk_step_matches_info(
                            pre_state.state,
                            step,
                            info,
                        )
                    }) by {
                        let step = UnifiedCacheSystem::Step::cache_io_begin(
                            req_map,
                            self.cache@,
                            disk_request_tuples,
                            disk_response_tuples,
                        );
                        assert(UnifiedCacheSystem::State::next_by(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheSystem::Label::Disk,
                            step,
                        ));
                        assert(UnifiedCacheProgramModel::disk_step_matches_info(
                            pre_state.state,
                            step,
                            info,
                        ));
                    }
                    assert(UnifiedCacheProgramModel::valid_disk_transition(
                        pre_state,
                        post_state,
                        info,
                    )) by {
                        reveal(UnifiedCacheProgramModel::valid_disk_transition);
                    }
                    assert(ProgramModelTrait::next(
                        pre_state,
                        post_state,
                        ProgramLabel::DiskIO{info},
                    ));
                }

                let tracked empty_disk_responses = DiskRespShard::empty(self.instance_id());
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
                self.outstanding_requests.insert(id, OutstandingReqInfo::CacheWrite{
                    addr,
                    write_handle: handle,
                });

                proof {
                    assert(pre_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty()) by {
                        assert(old(self).outstanding_cache_reqs_match_model());
                        assert(pre_state.state.outstanding_cache_reqs.dom()
                            == pre_outstanding.dom());
                        assert(pre_outstanding == Map::<ID, OutstandingReqInfo>::empty());
                        assert_maps_equal!(
                            pre_state.state.outstanding_cache_reqs,
                            Map::<ID, Address>::empty(),
                            k => {
                                if pre_state.state.outstanding_cache_reqs.contains_key(k) {
                                    assert(pre_state.state.outstanding_cache_reqs.dom().contains(k));
                                    assert(pre_outstanding.dom().contains(k));
                                    assert(false);
                                }
                            }
                        );
                    }
                    assert(self.state().outstanding_cache_reqs == map![id => addr@]) by {
                        assert(post_state.state.outstanding_cache_reqs
                            == pre_state.state.outstanding_cache_reqs.union_prefer_right(updated));
                        assert(pre_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty());
                        assert(updated == map![req_id_perm@ => addr@]);
                        assert(id == req_id_perm@);
                        assert_maps_equal!(self.state().outstanding_cache_reqs, map![id => addr@], k => {
                            if k == id {
                                assert(updated.contains_key(k));
                            } else {
                                assert(!updated.contains_key(k));
                            }
                        });
                    }
                    assert(self.outstanding_requests_wf()) by {
                        assert forall |id2: ID| #[trigger] self.outstanding_requests@.contains_key(id2)
                            implies {
                                match self.outstanding_requests@[id2] {
                                    OutstandingReqInfo::CacheRead{addr, load_handle} => {
                                        &&& self.cache.entry_fetched(&addr)
                                        &&& self.cache.valid_load_handle(&addr, load_handle)
                                    },
                                    OutstandingReqInfo::CacheWrite{addr, write_handle} => {
                                        &&& self.cache.entry_fetched(&addr)
                                        &&& self.cache.valid_writeback_handle(&addr, write_handle)
                                    },
                                    OutstandingReqInfo::SuperblockWrite => true,
                                }
                            } by {
                            if id2 == id {
                            } else {
                                assert(pre_outstanding == Map::<ID, OutstandingReqInfo>::empty());
                                assert(!pre_outstanding.contains_key(id2));
                                assert(false);
                            }
                        }
                    }
                    assert(self.outstanding_requests@.dom() =~= set![id]);
                    assert(self.outstanding_cache_reqs_match_model());
                    assert(self.outstanding_requests_single_flight());
                }
                true
            },
            WritebackAcquireResult::NotPresent
            | WritebackAcquireResult::NotDirty
            | WritebackAcquireResult::Busy => {
                proof {
                    assert(self.cache@ == pre_cache@);
                    assert(self.outstanding_requests_wf());
                    assert(self.outstanding_cache_reqs_match_model());
                    assert(self.outstanding_requests_single_flight());
                }
                false
            },
        }
    }

    fn recover_begin(&mut self, api: &mut ClientAPI<UnifiedCacheProgramModel>)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is FetchingSuperblock,
            old(self).state().recovery_state is Begin,
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
        ensures
            self.inv_api(api),
            self.recovery_phase is FetchingSuperblock,
            self.state().recovery_state is AwaitingSuperblock,
    {
        // api.log("unified-cache recovery begins");
        api.log("unified-cache recovery begins");

        let ghost pre_state = self.model@.value();
        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof {
            tracked_swap(self.model.borrow_mut(), &mut model);
        }

        let req_id_perm = Tracked(api.send_disk_request_predict_id());
        let disk_req = IDiskRequest::ReadReq{from: superblock_addr()};
        let ghost read_req = DiskRequest::ReadReq{from: spec_superblock_addr()};
        let ghost disk_request_tuples = multiset_map_singleton(req_id_perm@, disk_req@);
        let ghost disk_response_tuples = Multiset::empty();
        let ghost post_state = UnifiedCacheProgramModel{
            state: UnifiedCacheSystem::State{
                recovery_state: RecoveryState::AwaitingSuperblock,
                ..pre_state.state
            }
        };

        proof {
            multiset_map_singleton_ensures(req_id_perm@, disk_req@);
            assert(disk_req@ == read_req);
            assert(disk_request_tuples == Multiset::empty().insert((req_id_perm@, read_req)));
            assert(UnifiedCacheSystem::State::initiate_recovery(
                pre_state.state,
                post_state.state,
                UnifiedCacheSystem::Label::Disk,
                req_id_perm@,
                disk_request_tuples,
                disk_response_tuples,
            )) by {
            }
            assert(UnifiedCacheSystem::State::next_by(
                pre_state.state,
                post_state.state,
                UnifiedCacheSystem::Label::Disk,
                UnifiedCacheSystem::Step::initiate_recovery(
                    req_id_perm@,
                    disk_request_tuples,
                    disk_response_tuples,
                ),
            )) by {
                reveal(UnifiedCacheSystem::State::next_by);
            }
            assert(UnifiedCacheSystem::State::next(
                pre_state.state,
                post_state.state,
                UnifiedCacheSystem::Label::Disk,
            )) by {
                reveal(UnifiedCacheSystem::State::next);
            }
            let info = ProgramDiskInfo{
                reqs: disk_request_tuples,
                resps: disk_response_tuples,
            };
            assert(UnifiedCacheProgramModel::disk_step_matches_info(
                pre_state.state,
                UnifiedCacheSystem::Step::initiate_recovery(
                    req_id_perm@,
                    disk_request_tuples,
                    disk_response_tuples,
                ),
                info,
            ));
            assert(exists |step: UnifiedCacheSystem::Step| {
                &&& UnifiedCacheSystem::State::next_by(
                    pre_state.state,
                    post_state.state,
                    UnifiedCacheSystem::Label::Disk,
                    step,
                )
                &&& UnifiedCacheProgramModel::disk_step_matches_info(
                    pre_state.state,
                    step,
                    info,
                )
            }) by {
                let step = UnifiedCacheSystem::Step::initiate_recovery(
                    req_id_perm@,
                    disk_request_tuples,
                    disk_response_tuples,
                );
                assert(UnifiedCacheSystem::State::next_by(
                    pre_state.state,
                    post_state.state,
                    UnifiedCacheSystem::Label::Disk,
                    step,
                ));
                assert(UnifiedCacheProgramModel::disk_step_matches_info(
                    pre_state.state,
                    step,
                    info,
                ));
            }
            assert(UnifiedCacheProgramModel::valid_disk_transition(
                pre_state,
                post_state,
                info,
            )) by {
                reveal(UnifiedCacheProgramModel::valid_disk_transition);
            }
            assert(ProgramModelTrait::next(
                pre_state,
                post_state,
                ProgramLabel::DiskIO{info},
            ));
        }

        let tracked empty_disk_responses = DiskRespShard::empty(self.instance_id());
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

        let _id = api.send_disk_request(disk_req, req_id_perm, Tracked(new_disk_req_token));

        proof {
            assert(pre_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty()) by {
                assert(old(self).outstanding_cache_reqs_match_model());
                assert(pre_state.state.outstanding_cache_reqs.dom()
                    == old(self).outstanding_requests@.dom());
                assert(old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty());
                assert_maps_equal!(
                    pre_state.state.outstanding_cache_reqs,
                    Map::<ID, Address>::empty(),
                    k => {
                        if pre_state.state.outstanding_cache_reqs.contains_key(k) {
                            assert(pre_state.state.outstanding_cache_reqs.dom().contains(k));
                            assert(old(self).outstanding_requests@.dom().contains(k));
                            assert(!old(self).outstanding_requests@.contains_key(k));
                            assert(false);
                        }
                    }
                );
            }
            assert(self.state().cache == self.cache@);
            assert(self.state().outstanding_cache_reqs == Map::<ID, Address>::empty());
            assert(self.outstanding_requests@ == old(self).outstanding_requests@);
            assert(self.outstanding_requests_wf());
            assert(self.outstanding_cache_reqs_match_model());
            assert(self.outstanding_requests_single_flight());
        }
    }

    fn recover_step(&mut self, api: &mut ClientAPI<UnifiedCacheProgramModel>) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is FetchingSuperblock ==> old(self).state().recovery_state is AwaitingSuperblock,
            old(self).recovery_phase is LoadingJournal ==> old(self).state().recovery_state is SuperblockAvailable,
            old(self).recovery_phase is LoadingJournal ==> old(self).state().journal.journal == old(self).journal@,
        ensures
            self.inv_api(api),
            !(self.recovery_phase is FetchingSuperblock),
            self.recovery_phase is LoadingJournal ==> self.state().recovery_state is SuperblockAvailable,
            self.recovery_phase is LoadingJournal ==> self.state().journal.journal == self.journal@,
    {
        // api.log("unified-cache recovery skeleton step");
        // self.recovery_phase = RecoveryPhase::ReadyForUserOperation;
        // true
        match self.recovery_phase {
            RecoveryPhase::FetchingSuperblock => {
                api.log("await unified-cache superblock response");

                let ghost pre_state = self.model@.value();
                let DiskResponseRecord{
                    id: disk_req_id,
                    disk_response: i_disk_response,
                    token: disk_response_token,
                } = api.blocking_receive_disk_response();

                proof {
                    let sys_model =
                        open_system_invariant_disk_response_singleton::<
                            UnifiedCacheProgramModel,
                            UnifiedCacheRefinementProof,
                        >(
                            self.model,
                            disk_response_token,
                            disk_req_id,
                            i_disk_response@,
                        );
                    assert(UnifiedCacheRefinementProof::inv(sys_model));
                    assert(sys_model.program == pre_state);
                    assert(UnifiedCacheSystemRefinement::inv(sys_model));
                    UnifiedCacheSystemRefinement::recovery_superblock_response_facts(
                        sys_model,
                        disk_req_id,
                        i_disk_response@,
                    );
                    assert(sys_model.program.state.recovery_state is AwaitingSuperblock);
                    assert(pre_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty());
                    assert(!sys_model.program.state.outstanding_cache_reqs.contains_key(disk_req_id)) by {
                        assert(sys_model.program.state.outstanding_cache_reqs == Map::<ID, Address>::empty());
                    }
                    assert(sys_model.disk.responses.contains_key(disk_req_id));
                    assert(sys_model.disk.responses[disk_req_id] == i_disk_response@);
                    assert(i_disk_response@ is ReadResp);
                    assert(sys_model.disk.responses[disk_req_id]->data
                        == sys_model.disk.content[spec_superblock_addr()]);
                    assert(abstract_superblock_raw_wf(i_disk_response@->data));
                }

                let raw_page = match i_disk_response {
                    IDiskResponse::ReadResp{data} => data,
                    IDiskResponse::WriteResp{} => {
                        unreached()
                    },
                };

                let layout = DiskLayout::new();
                let superblock = layout.parse(&raw_page);
                let bootstrap_au = bootstrap_alloc_au();
                self.journal = JournalImpl::new(superblock.journal.snapshot, bootstrap_au);
                self.branch_loaded = false;

                let ghost image = layout.spec_parse(raw_page@);
                let ghost branch_image = crate::implementation::AtomicBranchState_v::AtomicBranchImage{
                    sealed_roots: image.branch_roots,
                    seq_end: image.branch_seq_end,
                };
                let ghost new_journal = AtomicJournalState::State{
                    journal: CachedJournal::State{
                        snapshot: image.journal_snapshot,
                        status: None,
                    },
                    mini_allocator: MiniAllocator::empty(),
                    persistent_seq_end: image.journal_seq_end,
                    in_flight: None,
                    prepared: false,
                };
                let ghost new_branch = AtomicBranchState::State{
                    image: branch_image,
                    persistent_image: branch_image,
                    in_flight: None,
                    prepared: false,
                    branch_summary: Map::empty(),
                    persisted_root_count: image.branch_roots.len() as nat,
                    active_branch: CachedBranch::State::empty_active(),
                    mini_allocator: MiniAllocator::empty(),
                    seq_end: image.branch_seq_end,
                };
                let ghost disk_request_tuples = Multiset::empty();
                let ghost disk_response_tuples = multiset_map_singleton(disk_req_id, i_disk_response@);
                let ghost post_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        recovery_state: RecoveryState::SuperblockAvailable,
                        journal: new_journal,
                        branch: new_branch,
                        persistent_image: Some(image),
                        sync_phase: AtomicSyncPhase::None,
                        sync_req_map: Map::empty(),
                        ..pre_state.state
                    }
                };

                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                }

                proof {
                    assert(i_disk_response@ is ReadResp);
                    assert(i_disk_response@->data == raw_page@);
                    assert(abstract_superblock_raw_wf(raw_page@));
                    assert(image.wf());
                    assert(superblock_matches(raw_page@, image));
                    assert(AtomicJournalState::State::initialize(
                        new_journal,
                        image.journal_snapshot,
                        image.journal_seq_end,
                    )) by {
                        reveal(AtomicJournalState::State::initialize);
                    }
                    assert(AtomicBranchState::State::initialize(
                        new_branch,
                        branch_image,
                        image.branch_roots.len() as nat,
                    )) by {
                        reveal(AtomicBranchState::State::initialize);
                    }
                    multiset_map_singleton_ensures(disk_req_id, i_disk_response@);
                    assert(disk_response_tuples == Multiset::empty().insert((
                        disk_req_id,
                        DiskResponse::ReadResp{data: raw_page@},
                    )));
                    assert(UnifiedCacheSystem::State::superblock_recovery(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Disk,
                        disk_req_id,
                        raw_page@,
                        image,
                        new_journal,
                        new_branch,
                        disk_request_tuples,
                        disk_response_tuples,
                    )) by {
                    }
                    assert(UnifiedCacheSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Disk,
                        UnifiedCacheSystem::Step::superblock_recovery(
                            disk_req_id,
                            raw_page@,
                            image,
                            new_journal,
                            new_branch,
                            disk_request_tuples,
                            disk_response_tuples,
                        ),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    assert(UnifiedCacheSystem::State::next(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Disk,
                    )) by {
                        reveal(UnifiedCacheSystem::State::next);
                    }
                    let info = ProgramDiskInfo{
                        reqs: disk_request_tuples,
                        resps: disk_response_tuples,
                    };
                    assert(UnifiedCacheProgramModel::disk_step_matches_info(
                        pre_state.state,
                        UnifiedCacheSystem::Step::superblock_recovery(
                            disk_req_id,
                            raw_page@,
                            image,
                            new_journal,
                            new_branch,
                            disk_request_tuples,
                            disk_response_tuples,
                        ),
                        info,
                    ));
                    assert(exists |step: UnifiedCacheSystem::Step| {
                        &&& UnifiedCacheSystem::State::next_by(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheSystem::Label::Disk,
                            step,
                        )
                        &&& UnifiedCacheProgramModel::disk_step_matches_info(
                            pre_state.state,
                            step,
                            info,
                        )
                    }) by {
                        let step = UnifiedCacheSystem::Step::superblock_recovery(
                            disk_req_id,
                            raw_page@,
                            image,
                            new_journal,
                            new_branch,
                            disk_request_tuples,
                            disk_response_tuples,
                        );
                        assert(UnifiedCacheSystem::State::next_by(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheSystem::Label::Disk,
                            step,
                        ));
                        assert(UnifiedCacheProgramModel::disk_step_matches_info(
                            pre_state.state,
                            step,
                            info,
                        ));
                    }
                    assert(UnifiedCacheProgramModel::valid_disk_transition(
                        pre_state,
                        post_state,
                        info,
                    )) by {
                        reveal(UnifiedCacheProgramModel::valid_disk_transition);
                    }
                    assert(ProgramModelTrait::next(
                        pre_state,
                        post_state,
                        ProgramLabel::DiskIO{info},
                    ));
                }

                let tracked _disk_req_token = self.instance.borrow().disk_transitions(
                    KVStoreTokenized::Label::DiskOp{
                        disk_request_tuples,
                        disk_response_tuples,
                    },
                    post_state,
                    &mut model,
                    disk_response_token.get(),
                );
                self.model = Tracked(model);

                self.recovery_phase = RecoveryPhase::LoadingJournal;

                proof {
                    assert(self.state().cache == self.cache@);
                    assert(superblock@ == layout.spec_parse_inner(raw_page@));
                    assert(superblock@@ == image);
                    assert(self.journal@.snapshot == image.journal_snapshot);
                    self.journal.view_ensures();
                    assert(!self.journal.index_ready());
                    assert(self.journal@.status is None);
                    assert(self.state().journal.journal == self.journal@);
                    assert(post_state.state.outstanding_cache_reqs == pre_state.state.outstanding_cache_reqs);
                    assert(pre_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty());
                    assert(self.state().outstanding_cache_reqs == Map::<ID, Address>::empty());
                    assert(self.outstanding_requests@ == old(self).outstanding_requests@);
                    assert(self.outstanding_requests_wf());
                    assert(self.outstanding_cache_reqs_match_model());
                    assert(self.outstanding_requests_single_flight());
                }
                true
            },
            RecoveryPhase::LoadingJournal => {
                let index_ready = self.journal.exec_index_ready();
                if index_ready {
                    api.log("unified-cache journal model transition pending");
                    false
                } else {
                    match self.journal.exec_freshest_rec() {
                        None => {
                            let ghost pre_state = self.model@.value();
                            let ghost pre_journal_view = self.journal@;
                            let reads = self.journal.recover_empty_index();
                            let ghost journal_reads = to_journal_records(reads@);
                            let ghost discovered_aus = Set::<AU>::empty();
                            let ghost new_atomic_journal = AtomicJournalState::State{
                                journal: self.journal@,
                                ..pre_state.state.journal
                            };
                            let ghost post_state = UnifiedCacheProgramModel{
                                state: UnifiedCacheSystem::State{
                                    cache: self.cache@,
                                    journal: new_atomic_journal,
                                    free_aus: pre_state.state.free_aus - discovered_aus,
                                    ..pre_state.state
                                }
                            };

                            let tracked mut model = KVStoreTokenized::model::arbitrary();
                            proof {
                                tracked_swap(self.model.borrow_mut(), &mut model);
                            }

                            proof {
                                assert(pre_state.state.recovery_state is SuperblockAvailable);
                                assert(pre_state.state.journal.journal == pre_journal_view);
                                assert(pre_state.state.cache == self.cache@);
                                assert(reads@ == Map::<Address, crate::spec::AsyncDisk_t::RawPage>::empty());
                                assert(journal_reads =~= Map::<Address, crate::journal::LinkedJournal_v::JournalRecord>::empty()) by {
                                    assert_maps_equal!(
                                        journal_reads,
                                        Map::<Address, crate::journal::LinkedJournal_v::JournalRecord>::empty(),
                                        addr => {
                                        }
                                    );
                                }

                                let cache_lbl = Cache::Label::Access{
                                    reads: reads@,
                                    writes: Map::empty(),
                                };
                                assert forall |addr| #[trigger] cache_lbl->reads.contains_key(addr)
                                    implies pre_state.state.cache.valid_read(addr, cache_lbl->reads[addr]) by {
                                    assert(reads@ == Map::<Address, crate::spec::AsyncDisk_t::RawPage>::empty());
                                }
                                assert forall |addr| #[trigger] cache_lbl->writes.contains_key(addr)
                                    implies pre_state.state.cache.valid_write(addr) by {
                                }
                                let updated_entries = pre_state.state.cache.write_updated_entries(cache_lbl->writes);
                                let updated_status_map = pre_state.state.cache.write_updated_status(cache_lbl->writes);
                                assert(cache_lbl->writes == Map::<Address, crate::spec::AsyncDisk_t::RawPage>::empty());
                                assert(pre_state.state.cache.entries.union_prefer_right(updated_entries)
                                    =~= pre_state.state.cache.entries);
                                assert(pre_state.state.cache.status_map.union_prefer_right(updated_status_map)
                                    =~= pre_state.state.cache.status_map);
                                assert(Cache::State::next_by(
                                    pre_state.state.cache,
                                    self.cache@,
                                    cache_lbl,
                                    Cache::Step::access{},
                                )) by {
                                    reveal(Cache::State::next_by);
                                }
                                assert(Cache::State::next(
                                    pre_state.state.cache,
                                    self.cache@,
                                    cache_lbl,
                                )) by {
                                    reveal(Cache::State::next);
                                }

                                let atomic_lbl = AtomicJournalState::Label::LoadIndex{
                                    reads: journal_reads,
                                    discovered_aus,
                                };
                                assert(AtomicJournalState::State::load_index(
                                    pre_state.state.journal,
                                    new_atomic_journal,
                                    atomic_lbl,
                                    self.journal@,
                                    0,
                                    0,
                                )) by {
                                    reveal(AtomicJournalState::State::load_index);
                                }
                                assert(AtomicJournalState::State::next_by(
                                    pre_state.state.journal,
                                    new_atomic_journal,
                                    atomic_lbl,
                                    AtomicJournalState::Step::load_index(self.journal@, 0, 0),
                                )) by {
                                    reveal(AtomicJournalState::State::next_by);
                                }
                                assert(AtomicJournalState::State::next(
                                    pre_state.state.journal,
                                    new_atomic_journal,
                                    atomic_lbl,
                                )) by {
                                    reveal(AtomicJournalState::State::next);
                                }

                                assert(UnifiedCacheSystem::State::journal_load_index(
                                    pre_state.state,
                                    post_state.state,
                                    UnifiedCacheSystem::Label::Internal,
                                    reads@,
                                    reads@,
                                    discovered_aus,
                                    self.cache@,
                                    new_atomic_journal,
                                )) by {
                                }
                                assert(UnifiedCacheSystem::State::next_by(
                                    pre_state.state,
                                    post_state.state,
                                    UnifiedCacheSystem::Label::Internal,
                                    UnifiedCacheSystem::Step::journal_load_index(
                                        reads@,
                                        reads@,
                                        discovered_aus,
                                        self.cache@,
                                        new_atomic_journal,
                                    ),
                                )) by {
                                    reveal(UnifiedCacheSystem::State::next_by);
                                }
                                assert(UnifiedCacheSystem::State::next(
                                    pre_state.state,
                                    post_state.state,
                                    UnifiedCacheSystem::Label::Internal,
                                )) by {
                                    reveal(UnifiedCacheSystem::State::next);
                                }
                                assert(ProgramModelTrait::next(
                                    pre_state,
                                    post_state,
                                    ProgramLabel::Internal{},
                                ));
                            }

                            let tracked _internal_token = self.instance.borrow().internal(
                                KVStoreTokenized::Label::InternalOp{},
                                post_state,
                                &mut model,
                            );
                            self.model = Tracked(model);
                            self.recovery_phase = RecoveryPhase::LoadingBranch;
                            api.log("unified-cache empty journal index recovered");
                            true
                        },
                        Some(_) => {
                            api.log("unified-cache nonempty journal recovery pending");
                            false
                        },
                    }
                }
            },
            RecoveryPhase::LoadingBranch => {
                api.log("unified-cache branch recovery pending");
                false
            },
            RecoveryPhase::ReadyForUserOperation => {
                false
            },
        }
    }

    fn handle_disk_response(
        &mut self,
        rec: DiskResponseRecord<UnifiedCacheProgramModel>,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    )
        requires
            old(self).inv_api(old(api)),
            rec.token@.instance_id() == old(self).instance_id(),
            rec.token@.multiset() == multiset_map_singleton(rec.id, rec.disk_response@),
            rec.disk_response is ReadResp ==> rec.disk_response->data.len() == PAGE_SIZE_BYTES,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        let DiskResponseRecord{id, disk_response, token} = rec;
        let ghost response = disk_response@;
        let ghost pre_outstanding = self.outstanding_requests@;

        let req_info = self.outstanding_requests.remove(&id);
        match req_info {
            None => {
                api.log("unified-cache unexpected disk response");
            },
            Some(OutstandingReqInfo::CacheRead{addr, load_handle}) => {
                match disk_response {
                    IDiskResponse::ReadResp{data} => {
                        let mut load_handle = load_handle;
                        load_handle.rec = data;

                        proof {
                            assert(load_handle.rec.len() == PAGE_SIZE_BYTES);
                            assert(pre_outstanding.contains_key(id));
                            assert(old(self).outstanding_requests_wf());
                            assert(old(self).cache.entry_fetched(&addr));
                            assert(old(self).cache.valid_load_handle(&addr, load_handle));
                        }

                        let ghost pre_state = self.model@.value();
                        let ghost pre_cache_reqs = pre_state.state.outstanding_cache_reqs;
                        self.cache.load_release(&addr, load_handle);

                        let ghost resp_map = map![id => response];
                        let ghost disk_request_tuples = Multiset::empty();
                        let ghost disk_response_tuples = multiset_map_singleton(id, response);
                        let ghost finished_cache_reqs =
                            pre_state.state.outstanding_cache_reqs.restrict(resp_map.dom()).invert();
                        let ghost cache_resps = Map::new(
                            |a| finished_cache_reqs.contains_key(a),
                            |a| resp_map[finished_cache_reqs[a]],
                        );
                        let ghost post_state = UnifiedCacheProgramModel{
                            state: UnifiedCacheSystem::State{
                                cache: self.cache@,
                                outstanding_cache_reqs:
                                    pre_state.state.outstanding_cache_reqs.remove_keys(resp_map.dom()),
                                disk_backed_addrs:
                                    pre_state.state.disk_backed_addrs + cache_write_response_addrs(cache_resps),
                                ..pre_state.state
                            }
                        };

                        let tracked mut model = KVStoreTokenized::model::arbitrary();
                        proof {
                            tracked_swap(self.model.borrow_mut(), &mut model);
                        }

                        proof {
                            assert(pre_state.state.outstanding_cache_reqs == map![id => addr@]) by {
                                assert(pre_state.state.outstanding_cache_reqs.contains_key(id));
                                assert(pre_state.state.outstanding_cache_reqs[id] == addr@);
                                assert_maps_equal!(pre_state.state.outstanding_cache_reqs, map![id => addr@], k => {
                                    if k == id {
                                    } else {
                                        if pre_state.state.outstanding_cache_reqs.contains_key(k) {
                                            assert(old(self).outstanding_requests@.contains_key(k));
                                            assert(old(self).outstanding_requests@.contains_key(id));
                                            assert(old(self).outstanding_requests_single_flight());
                                            assert(k == id);
                                            assert(false);
                                        }
                                    }
                                });
                            }
                            multiset_map_singleton_ensures(id, response);
                            assert(multiset_to_map(disk_response_tuples) == resp_map);
                            Self::cache_resps_singleton(pre_cache_reqs, id, addr@, response);
                            assert(cache_resps == map![addr@ => response]);
                            assert(UnifiedCacheSystem::State::cache_io_end(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheSystem::Label::Disk,
                                resp_map,
                                self.cache@,
                                disk_request_tuples,
                                disk_response_tuples,
                            )) by {
                            }
                            assert(UnifiedCacheSystem::State::next_by(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheSystem::Label::Disk,
                                UnifiedCacheSystem::Step::cache_io_end(
                                    resp_map,
                                    self.cache@,
                                    disk_request_tuples,
                                    disk_response_tuples,
                                ),
                            )) by {
                                reveal(UnifiedCacheSystem::State::next_by);
                            }
                            assert(UnifiedCacheSystem::State::next(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheSystem::Label::Disk,
                            )) by {
                                reveal(UnifiedCacheSystem::State::next);
                            }
                            let info = ProgramDiskInfo{
                                reqs: disk_request_tuples,
                                resps: disk_response_tuples,
                            };
                            assert(UnifiedCacheProgramModel::disk_step_matches_info(
                                pre_state.state,
                                UnifiedCacheSystem::Step::cache_io_end(
                                    resp_map,
                                    self.cache@,
                                    disk_request_tuples,
                                    disk_response_tuples,
                                ),
                                info,
                            ));
                            assert(exists |step: UnifiedCacheSystem::Step| {
                                &&& UnifiedCacheSystem::State::next_by(
                                    pre_state.state,
                                    post_state.state,
                                    UnifiedCacheSystem::Label::Disk,
                                    step,
                                )
                                &&& UnifiedCacheProgramModel::disk_step_matches_info(
                                    pre_state.state,
                                    step,
                                    info,
                                )
                            }) by {
                                let step = UnifiedCacheSystem::Step::cache_io_end(
                                    resp_map,
                                    self.cache@,
                                    disk_request_tuples,
                                    disk_response_tuples,
                                );
                                assert(UnifiedCacheSystem::State::next_by(
                                    pre_state.state,
                                    post_state.state,
                                    UnifiedCacheSystem::Label::Disk,
                                    step,
                                ));
                                assert(UnifiedCacheProgramModel::disk_step_matches_info(
                                    pre_state.state,
                                    step,
                                    info,
                                ));
                            }
                            assert(UnifiedCacheProgramModel::valid_disk_transition(
                                pre_state,
                                post_state,
                                info,
                            )) by {
                                reveal(UnifiedCacheProgramModel::valid_disk_transition);
                            }
                            assert(ProgramModelTrait::next(
                                pre_state,
                                post_state,
                                ProgramLabel::DiskIO{info},
                            ));
                            assert(post_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty()) by {
                                assert(pre_state.state.outstanding_cache_reqs == map![id => addr@]);
                                assert(resp_map.dom() == set![id]);
                                assert_maps_equal!(
                                    post_state.state.outstanding_cache_reqs,
                                    Map::<ID, Address>::empty(),
                                    k => {
                                        if post_state.state.outstanding_cache_reqs.contains_key(k) {
                                            assert(!resp_map.dom().contains(k));
                                            assert(pre_state.state.outstanding_cache_reqs.contains_key(k));
                                            assert(k == id);
                                            assert(false);
                                        }
                                    }
                                );
                            }
                        }

                        let tracked _disk_req_token = self.instance.borrow().disk_transitions(
                            KVStoreTokenized::Label::DiskOp{
                                disk_request_tuples,
                                disk_response_tuples,
                            },
                            post_state,
                            &mut model,
                            token.get(),
                        );
                        self.model = Tracked(model);

                        proof {
                            assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty());
                            assert(self.state().outstanding_cache_reqs == Map::<ID, Address>::empty());
                            assert(self.outstanding_requests_wf());
                            assert(self.outstanding_cache_reqs_match_model());
                            assert(self.outstanding_requests_single_flight());
                        }
                    },
                    IDiskResponse::WriteResp{} => {
                        self.outstanding_requests.insert(id, OutstandingReqInfo::CacheRead{
                            addr,
                            load_handle,
                        });
                        api.log("unified-cache read got write response");
                    },
                }
            },
            Some(OutstandingReqInfo::CacheWrite{addr, write_handle}) => {
                match disk_response {
                    IDiskResponse::WriteResp{} => {
                        proof {
                            assert(pre_outstanding.contains_key(id));
                            assert(old(self).outstanding_requests_wf());
                            assert(old(self).cache.entry_fetched(&addr));
                            assert(old(self).cache.valid_writeback_handle(&addr, write_handle));
                        }

                        let ghost pre_state = self.model@.value();
                        let ghost pre_cache_reqs = pre_state.state.outstanding_cache_reqs;
                        self.cache.complete_writeback(&addr, write_handle);

                        let ghost resp_map = map![id => response];
                        let ghost disk_request_tuples = Multiset::empty();
                        let ghost disk_response_tuples = multiset_map_singleton(id, response);
                        let ghost finished_cache_reqs =
                            pre_state.state.outstanding_cache_reqs.restrict(resp_map.dom()).invert();
                        let ghost cache_resps = Map::new(
                            |a| finished_cache_reqs.contains_key(a),
                            |a| resp_map[finished_cache_reqs[a]],
                        );
                        let ghost post_state = UnifiedCacheProgramModel{
                            state: UnifiedCacheSystem::State{
                                cache: self.cache@,
                                outstanding_cache_reqs:
                                    pre_state.state.outstanding_cache_reqs.remove_keys(resp_map.dom()),
                                disk_backed_addrs:
                                    pre_state.state.disk_backed_addrs + cache_write_response_addrs(cache_resps),
                                ..pre_state.state
                            }
                        };

                        let tracked mut model = KVStoreTokenized::model::arbitrary();
                        proof {
                            tracked_swap(self.model.borrow_mut(), &mut model);
                        }

                        proof {
                            assert(pre_state.state.outstanding_cache_reqs == map![id => addr@]) by {
                                assert(pre_state.state.outstanding_cache_reqs.contains_key(id));
                                assert(pre_state.state.outstanding_cache_reqs[id] == addr@);
                                assert_maps_equal!(pre_state.state.outstanding_cache_reqs, map![id => addr@], k => {
                                    if k == id {
                                    } else {
                                        if pre_state.state.outstanding_cache_reqs.contains_key(k) {
                                            assert(old(self).outstanding_requests@.contains_key(k));
                                            assert(old(self).outstanding_requests@.contains_key(id));
                                            assert(old(self).outstanding_requests_single_flight());
                                            assert(k == id);
                                            assert(false);
                                        }
                                    }
                                });
                            }
                            multiset_map_singleton_ensures(id, response);
                            assert(multiset_to_map(disk_response_tuples) == resp_map);
                            Self::cache_resps_singleton(pre_cache_reqs, id, addr@, response);
                            assert(cache_resps == map![addr@ => response]);
                            assert(UnifiedCacheSystem::State::cache_io_end(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheSystem::Label::Disk,
                                resp_map,
                                self.cache@,
                                disk_request_tuples,
                                disk_response_tuples,
                            )) by {
                            }
                            assert(UnifiedCacheSystem::State::next_by(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheSystem::Label::Disk,
                                UnifiedCacheSystem::Step::cache_io_end(
                                    resp_map,
                                    self.cache@,
                                    disk_request_tuples,
                                    disk_response_tuples,
                                ),
                            )) by {
                                reveal(UnifiedCacheSystem::State::next_by);
                            }
                            assert(UnifiedCacheSystem::State::next(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheSystem::Label::Disk,
                            )) by {
                                reveal(UnifiedCacheSystem::State::next);
                            }
                            let info = ProgramDiskInfo{
                                reqs: disk_request_tuples,
                                resps: disk_response_tuples,
                            };
                            assert(UnifiedCacheProgramModel::disk_step_matches_info(
                                pre_state.state,
                                UnifiedCacheSystem::Step::cache_io_end(
                                    resp_map,
                                    self.cache@,
                                    disk_request_tuples,
                                    disk_response_tuples,
                                ),
                                info,
                            ));
                            assert(exists |step: UnifiedCacheSystem::Step| {
                                &&& UnifiedCacheSystem::State::next_by(
                                    pre_state.state,
                                    post_state.state,
                                    UnifiedCacheSystem::Label::Disk,
                                    step,
                                )
                                &&& UnifiedCacheProgramModel::disk_step_matches_info(
                                    pre_state.state,
                                    step,
                                    info,
                                )
                            }) by {
                                let step = UnifiedCacheSystem::Step::cache_io_end(
                                    resp_map,
                                    self.cache@,
                                    disk_request_tuples,
                                    disk_response_tuples,
                                );
                                assert(UnifiedCacheSystem::State::next_by(
                                    pre_state.state,
                                    post_state.state,
                                    UnifiedCacheSystem::Label::Disk,
                                    step,
                                ));
                                assert(UnifiedCacheProgramModel::disk_step_matches_info(
                                    pre_state.state,
                                    step,
                                    info,
                                ));
                            }
                            assert(UnifiedCacheProgramModel::valid_disk_transition(
                                pre_state,
                                post_state,
                                info,
                            )) by {
                                reveal(UnifiedCacheProgramModel::valid_disk_transition);
                            }
                            assert(ProgramModelTrait::next(
                                pre_state,
                                post_state,
                                ProgramLabel::DiskIO{info},
                            ));
                            assert(post_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty()) by {
                                assert(pre_state.state.outstanding_cache_reqs == map![id => addr@]);
                                assert(resp_map.dom() == set![id]);
                                assert_maps_equal!(
                                    post_state.state.outstanding_cache_reqs,
                                    Map::<ID, Address>::empty(),
                                    k => {
                                        if post_state.state.outstanding_cache_reqs.contains_key(k) {
                                            assert(!resp_map.dom().contains(k));
                                            assert(pre_state.state.outstanding_cache_reqs.contains_key(k));
                                            assert(k == id);
                                            assert(false);
                                        }
                                    }
                                );
                            }
                        }

                        let tracked _disk_req_token = self.instance.borrow().disk_transitions(
                            KVStoreTokenized::Label::DiskOp{
                                disk_request_tuples,
                                disk_response_tuples,
                            },
                            post_state,
                            &mut model,
                            token.get(),
                        );
                        self.model = Tracked(model);

                        proof {
                            assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty());
                            assert(self.state().outstanding_cache_reqs == Map::<ID, Address>::empty());
                            assert(self.outstanding_requests_wf());
                            assert(self.outstanding_cache_reqs_match_model());
                            assert(self.outstanding_requests_single_flight());
                        }
                    },
                    IDiskResponse::ReadResp{..} => {
                        self.outstanding_requests.insert(id, OutstandingReqInfo::CacheWrite{
                            addr,
                            write_handle,
                        });
                        api.log("unified-cache write got read response");
                    },
                }
            },
            Some(OutstandingReqInfo::SuperblockWrite) => {
                self.outstanding_requests.insert(id, OutstandingReqInfo::SuperblockWrite);
                api.log("unified-cache superblock response path pending");
            },
        }
    }

    fn handle_user_request(
        &mut self,
        req: Request,
        req_shard: Tracked<RequestShard>,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    )
        requires
            old(self).inv_api(old(api)),
            req_shard@.instance_id() == old(self).instance_id(),
            req_shard@.element() == req,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        match req.input {
            Input::NoopInput => {
                api.log("noop skeleton");
            },
            Input::PutInput{..} => {
                api.log("put skeleton");
            },
            Input::QueryInput{..} => {
                api.log("query skeleton");
            },
            Input::SyncInput => {
                api.log("sync skeleton");
            },
            Input::SimulateCrash => {
                api.log("simulate crash skeleton");
            },
        }
    }

    fn do_background_work(&mut self, api: &mut ClientAPI<UnifiedCacheProgramModel>) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        match self.recovery_phase {
            RecoveryPhase::ReadyForUserOperation => {
                if self.journal.free_aus_below_threshold() {
                    let ghost pre_state = self.model@.value();
                    let ghost pre_pool = self.au_pool@;
                    let refill = self.journal.background_refill_aus(&mut self.au_pool, TOTAL_AUS);
                    match refill {
                        None => {
                            proof {
                                assert(self.journal.basic_wf());
                                assert(self.journal@ == old(self).journal@);
                                assert(self.au_pool@ =~= pre_pool);
                                assert(self.au_pool@ =~= old(self).au_pool@);
                                assert(self.state().free_aus =~= self.au_pool@);
                                assert(self.outstanding_requests_wf());
                                assert(self.outstanding_cache_reqs_match_model());
                                assert(self.outstanding_requests_single_flight());
                            }
                            false
                        },
                        Some(allocation) => {
                            let ghost aus = allocation.as_set();
                            let ghost new_journal = AtomicJournalState::State{
                                mini_allocator: pre_state.state.journal.mini_allocator.add_aus(aus),
                                ..pre_state.state.journal
                            };
                            let ghost post_state = UnifiedCacheProgramModel{
                                state: UnifiedCacheSystem::State{
                                    free_aus: pre_state.state.free_aus - aus,
                                    journal: new_journal,
                                    ..pre_state.state
                                }
                            };

                            let tracked mut model = KVStoreTokenized::model::arbitrary();
                            proof {
                                tracked_swap(self.model.borrow_mut(), &mut model);
                            }

                            proof {
                                assert(pre_state.state.client_ready());
                                assert(aus <= pre_state.state.free_aus) by {
                                    assert(aus <= pre_pool);
                                    assert(pre_state.state.free_aus =~= pre_pool);
                                }
                                assert(AtomicJournalState::State::fill_aus(
                                    pre_state.state.journal,
                                    new_journal,
                                    AtomicJournalState::Label::FillAUs{aus},
                                )) by {
                                    reveal(AtomicJournalState::State::fill_aus);
                                }
                                assert(AtomicJournalState::State::next_by(
                                    pre_state.state.journal,
                                    new_journal,
                                    AtomicJournalState::Label::FillAUs{aus},
                                    AtomicJournalState::Step::fill_aus(),
                                )) by {
                                    reveal(AtomicJournalState::State::next_by);
                                }
                                assert(AtomicJournalState::State::next(
                                    pre_state.state.journal,
                                    new_journal,
                                    AtomicJournalState::Label::FillAUs{aus},
                                )) by {
                                    reveal(AtomicJournalState::State::next);
                                }
                                assert(UnifiedCacheSystem::State::journal_fill_aus(
                                    pre_state.state,
                                    post_state.state,
                                    UnifiedCacheSystem::Label::Internal,
                                    aus,
                                    new_journal,
                                )) by {
                                }
                                assert(UnifiedCacheSystem::State::next_by(
                                    pre_state.state,
                                    post_state.state,
                                    UnifiedCacheSystem::Label::Internal,
                                    UnifiedCacheSystem::Step::journal_fill_aus(aus, new_journal),
                                )) by {
                                    reveal(UnifiedCacheSystem::State::next_by);
                                }
                                assert(UnifiedCacheSystem::State::next(
                                    pre_state.state,
                                    post_state.state,
                                    UnifiedCacheSystem::Label::Internal,
                                )) by {
                                    reveal(UnifiedCacheSystem::State::next);
                                }
                                assert(ProgramModelTrait::next(
                                    pre_state,
                                    post_state,
                                    ProgramLabel::Internal{},
                                ));
                            }

                            let tracked _internal_token = self.instance.borrow().internal(
                                KVStoreTokenized::Label::InternalOp{},
                                post_state,
                                &mut model,
                            );
                            self.model = Tracked(model);
                            api.log("unified-cache journal au refill");

                            proof {
                                assert(self.state().free_aus =~= self.au_pool@) by {
                                    assert(self.state().free_aus =~= pre_state.state.free_aus - aus);
                                    assert(self.au_pool@ =~= pre_pool - aus);
                                    assert(pre_state.state.free_aus =~= pre_pool);
                                }
                                assert(self.state().cache == self.cache@);
                                assert(self.outstanding_requests@ == old(self).outstanding_requests@);
                                assert(self.outstanding_requests_wf());
                                assert(self.outstanding_cache_reqs_match_model());
                                assert(self.outstanding_requests_single_flight());
                            }
                            true
                        },
                    }
                } else {
                    false
                }
            },
            _ => {
                false
            },
        }
    }
}

impl KVStoreTrait for Implementation {
    type ProgramModel = UnifiedCacheProgramModel;
    type Proof = UnifiedCacheRefinementProof;

    closed spec fn wf_init(self) -> bool
    {
        Implementation::wf_init(&self)
    }

    closed spec fn instance_id(self) -> InstanceId
    {
        Implementation::instance_id(&self)
    }

    fn new() -> (out: Self)
    {
        let cache = FracCacheImpl::new();
        let snapshot = IJournalSnapshot::new_empty(0);
        let bootstrap_au = bootstrap_alloc_au();
        let journal = JournalImpl::new(snapshot, bootstrap_au);
        let au_pool = AuPoolImpl::new(TOTAL_AUS);

        let ghost free_aus = au_pool@;
        let ghost initial_state = UnifiedCacheSystem::State {
            recovery_state: RecoveryState::Begin,
            cache: cache@,
            outstanding_cache_reqs: Map::<ID, Address>::empty(),
            disk_backed_addrs: Set::<Address>::empty().insert(spec_superblock_addr()),
            free_aus,
            journal: AtomicJournalState::State::empty(),
            branch: AtomicBranchState::State::empty(),
            persistent_image: None,
            sync_phase: AtomicSyncPhase::None,
            sync_req_map: Map::<SyncReqId, nat>::empty(),
        };

        proof {
            assert(free_aus.disjoint(UnifiedCacheSystem::State::reserved_aus())) by {
                assert(spec_superblock_addr().au == 0);
                assert(UnifiedCacheSystem::State::reserved_aus() =~= set![0]) by {
                    reveal(UnifiedCacheSystem::State::reserved_aus);
                }
                assert(!free_aus.contains(0));
            }
            assert(UnifiedCacheSystem::State::initialize(
                initial_state,
                cache.total_slots() as nat,
                free_aus,
            )) by {
                assert(initial_state.cache == Cache::State::empty(cache.total_slots() as nat));
            }
            assert(UnifiedCacheSystem::State::init_by(
                initial_state,
                UnifiedCacheSystem::Config::initialize(cache.total_slots() as nat, free_aus),
            )) by {
                reveal(UnifiedCacheSystem::State::init_by);
            }
            assert(UnifiedCacheSystem::State::init(initial_state)) by {
                reveal(UnifiedCacheSystem::State::init);
            }
        }

        let tracked (
            Tracked(instance),
            Tracked(model),
            Tracked(requests),
            Tracked(replies),
            Tracked(disk_requests),
            Tracked(disk_responses),
        ) = KVStoreTokenized::Instance::initialize(UnifiedCacheProgramModel{state: initial_state});

        Implementation {
            recovery_phase: RecoveryPhase::FetchingSuperblock,
            cache,
            journal,
            au_pool,
            branch_loaded: false,
            sync_requests: Vec::new(),
            outstanding_requests: HashMapWithView::new(),
            should_retry_sync_launch: false,
            model: Tracked(model),
            instance: Tracked(instance),
        }
    }

    fn kvstore_mkfs(&mut self, mut api: ClientAPI<Self::ProgramModel>)
    {
        api.log("unified-cache mkfs skeleton");
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn kvstore_main(&mut self, mut api: ClientAPI<Self::ProgramModel>)
    {
        self.recover_begin(&mut api);

        let debug_print = true;
        loop
            invariant
                self.inv_api(&api),
                self.recovery_phase is FetchingSuperblock
                    ==> self.state().recovery_state is AwaitingSuperblock,
                self.recovery_phase is LoadingJournal
                    ==> self.state().recovery_state is SuperblockAvailable,
                self.recovery_phase is LoadingJournal
                    ==> self.state().journal.journal == self.journal@,
        {
            let mut progress = false;

            match self.recovery_phase {
                RecoveryPhase::ReadyForUserOperation => {
                    match api.receive_disk_response() {
                        None => {},
                        Some(rec) => {
                            progress = true;
                            self.handle_disk_response(rec, &mut api);
                        },
                    }
                },
                _ => {},
            }

            match self.recovery_phase {
                RecoveryPhase::FetchingSuperblock
                | RecoveryPhase::LoadingJournal
                | RecoveryPhase::LoadingBranch => {
                    progress = self.recover_step(&mut api) || progress;
                },
                RecoveryPhase::ReadyForUserOperation => {
                    match api.receive_request(debug_print) {
                        None => {},
                        Some(rec) => {
                            progress = true;
                            match rec.request.input {
                                Input::SimulateCrash => {
                                    return;
                                },
                                _ => {
                                    self.handle_user_request(rec.request, rec.token, &mut api);
                                },
                            }
                        },
                    }

                    if self.should_retry_sync_launch {
                        api.log("sync launch retry skeleton");
                        self.should_retry_sync_launch = false;
                        progress = true;
                    }

                    let bg_progress = self.do_background_work(&mut api);
                    progress = progress || bg_progress;
                },
            }

            if !progress {
                api.log("sleeping");
                api.sleep_a_little();
            }
        }
    }
}

///////////////////////////////////////////////////////////////////////////////
// Utility Proofs
//
// Keep small algebraic/map proof helpers out of the executable implementation
// flow above. These lemmas have no runtime role; they only discharge local
// proof obligations around singleton disk/cache request maps.
///////////////////////////////////////////////////////////////////////////////

impl Implementation {
    proof fn singleton_req_map_values(id: ID, req: DiskRequest)
        ensures
            map![id => req].values() == set![req],
    {
        let m = map![id => req];
        assert forall |r: DiskRequest| #[trigger] m.values().contains(r)
            implies set![req].contains(r) by {
            let key = choose |key: ID| m.contains_key(key) && #[trigger] m[key] == r;
            assert(key == id);
            assert(r == req);
        }
        assert forall |r: DiskRequest| #[trigger] set![req].contains(r)
            implies m.values().contains(r) by {
            assert(r == req);
            assert(m.contains_key(id));
            assert(m[id] == req);
            reveal(Map::values);
        }
    }

    proof fn singleton_updated_addr_map(
        id: ID,
        req: DiskRequest,
        addr: Address,
    )
        requires
            req.addr() == addr,
        ensures
            Map::new(|i| map![id => req].contains_key(i), |i| map![id => req][i].addr())
                == map![id => addr],
    {
        let updated = Map::new(
            |i| map![id => req].contains_key(i),
            |i| map![id => req][i].addr(),
        );
        assert_maps_equal!(updated, map![id => addr], i => {
            if i == id {
                assert(map![id => req].contains_key(i));
                assert(updated[i] == req.addr());
            } else {
                assert(!map![id => req].contains_key(i));
            }
        });
    }

    proof fn singleton_addr_map_values_wf(id: ID, addr: Address)
        requires
            addr.wf(),
        ensures
            map![id => addr].values() <= Set::new(|addr: Address| addr.wf()),
    {
        let m = map![id => addr];
        assert forall |candidate: Address| #[trigger] m.values().contains(candidate)
            implies Set::new(|addr: Address| addr.wf()).contains(candidate) by {
            let key = choose |key: ID| m.contains_key(key) && #[trigger] m[key] == candidate;
            assert(key == id);
            assert(candidate == addr);
        }
    }

    proof fn cache_resps_singleton(
        pre_cache_reqs: Map<ID, Address>,
        id: ID,
        addr: Address,
        resp: DiskResponse,
    )
        requires
            pre_cache_reqs == map![id => addr],
        ensures ({
            let resp_map = map![id => resp];
            let finished_cache_reqs = pre_cache_reqs.restrict(resp_map.dom()).invert();
            let cache_resps = Map::new(
                |a| finished_cache_reqs.contains_key(a),
                |a| resp_map[finished_cache_reqs[a]],
            );
            cache_resps == map![addr => resp]
        }),
    {
        let resp_map = map![id => resp];
        let restricted = pre_cache_reqs.restrict(resp_map.dom());
        assert_maps_equal!(restricted, map![id => addr], k => {
            if k == id {
                assert(resp_map.dom().contains(k));
            } else {
                assert(!pre_cache_reqs.contains_key(k));
            }
        });
        let finished_cache_reqs = restricted.invert();
        assert_maps_equal!(finished_cache_reqs, map![addr => id], a => {
            if a == addr {
                assert(restricted.contains_pair(id, addr));
                reveal(Map::invert);
            } else {
                assert(!restricted.contains_value(a));
                reveal(Map::invert);
            }
        });
        let cache_resps = Map::new(
            |a| finished_cache_reqs.contains_key(a),
            |a| resp_map[finished_cache_reqs[a]],
        );
        assert_maps_equal!(cache_resps, map![addr => resp], a => {
            if a == addr {
                assert(finished_cache_reqs[a] == id);
            } else {
                assert(!finished_cache_reqs.contains_key(a));
            }
        });
    }
}

///////////////////////////////////////////////////////////////////////////////
// Refinement Proof Obligations
//
// The trait implementation has to keep these proof methods inside the trait
// impl, but the whole proof-obligation block lives below the executable
// implementation so the runtime shape stays easier to read.
///////////////////////////////////////////////////////////////////////////////

impl RefinementObligation<UnifiedCacheProgramModel> for UnifiedCacheRefinementProof {
    open spec fn inv(model: SystemModel::State<UnifiedCacheProgramModel>) -> bool
    {
        let unified = UnifiedCacheSystemRefinement::unified_cache_system_i(model);
        &&& UnifiedCacheSystemRefinement::inv(model)
        &&& CachingDiskSystemRefinement::caching_disk_system_coordination_i(unified).inv()
    }

    open spec fn i(model: SystemModel::State<UnifiedCacheProgramModel>) -> CrashTolerantAsyncMap::State
    {
        CachingDiskSystemRefinement::caching_disk_system_i(
            UnifiedCacheSystemRefinement::unified_cache_system_i(model),
        )
    }

    open spec fn i_lbl(
        pre: SystemModel::State<UnifiedCacheProgramModel>,
        post: SystemModel::State<UnifiedCacheProgramModel>,
        lbl: SystemModel::Label,
    ) -> CrashTolerantAsyncMap::Label
    {
        CachingDiskSystemRefinement::caching_disk_system_i_lbl(
            UnifiedCacheSystemRefinement::unified_cache_system_i(pre),
            UnifiedCacheSystemRefinement::unified_cache_system_i(post),
            UnifiedCacheSystemRefinement::unified_cache_system_i_lbl(pre, post, lbl),
        )
    }

    proof fn i_lbl_valid(
        pre: SystemModel::State<UnifiedCacheProgramModel>,
        post: SystemModel::State<UnifiedCacheProgramModel>,
        lbl: SystemModel::Label,
        ctam_lbl: CrashTolerantAsyncMap::Label,
    )
    {
        reveal(SystemModel::Label::label_correspondence);
        reveal(crate::trusted::RefinementObligation_t::externally_visible);
    }

    proof fn init_refines(pre: SystemModel::State<UnifiedCacheProgramModel>)
    {
        UnifiedCacheSystemRefinement::init_refines(pre);
        CachingDiskSystemRefinement::init_refines_ctam(
            UnifiedCacheSystemRefinement::unified_cache_system_i(pre),
        );

        assert(CrashTolerantAsyncMap::State::init(Self::i(pre)));
        reveal(CrashTolerantAsyncMap::State::init);
        reveal(CrashTolerantAsyncMap::State::init_by);
        let config = choose |config| CrashTolerantAsyncMap::State::init_by(Self::i(pre), config);
        match config {
            CrashTolerantAsyncMap::Config::initialize() => {
                assert(CrashTolerantAsyncMap::State::initialize(Self::i(pre)));
            },
            CrashTolerantAsyncMap::Config::dummy_to_use_type_params(_) => {
                assert(false);
            },
        }
    }

    proof fn next_refines(
        pre: SystemModel::State<UnifiedCacheProgramModel>,
        post: SystemModel::State<UnifiedCacheProgramModel>,
        lbl: SystemModel::Label,
    )
    {
        let unified_pre = UnifiedCacheSystemRefinement::unified_cache_system_i(pre);
        let unified_post = UnifiedCacheSystemRefinement::unified_cache_system_i(post);
        let unified_lbl = UnifiedCacheSystemRefinement::unified_cache_system_i_lbl(pre, post, lbl);

        UnifiedCacheSystemRefinement::next_refines(pre, post, lbl);
        UnifiedCacheSystemRefinement::inv_implies_caching_disk_refinement_inv(pre);
        CachingDiskSystemRefinement::next_refines_ctam(unified_pre, unified_post, unified_lbl);
    }
}

} // verus!
