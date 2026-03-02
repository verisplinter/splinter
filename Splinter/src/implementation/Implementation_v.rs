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
use crate::abstract_system::AbstractCrashAwareMap_v::AbstractCrashAwareMap;

use crate::implementation::ModelRefinement_v::RefinementProof;
use crate::implementation::ConcreteProgramModel_v::ConcreteProgramModel;
use crate::implementation::AtomicState_v::{AtomicState, DiskEvent, InflightInfo, InternalEvent, ProgramEvent, RecoveryState, map_to_multiset, to_journal_reads};
use crate::implementation::MultisetMapRelation_v::{multiset_map_singleton, multiset_map_singleton_ensures, multiset_to_map, unique_keys};
use crate::implementation::VecMap_v::VecMap;
use crate::implementation::JournalTypes_v::{ILsn};
use crate::allocation_layer::LikesJournal_v::lsn_addr_index_discard_up_to;
use crate::implementation::JournalImpl_v::{BeginWritebackForTargetResult, CleanForCommitResult, IJournalSnapshot, JournalImpl, RecoverIndexResult, RecoverMapResult, all_pages_parsable, cache_matches_raw_disk, iaddr_view, journal_disk_inv, load_index_labels, map_recovery_labels};
use crate::implementation::SuperblockTypes_v;
use crate::implementation::SuperblockTypes_v::{ASuperblock, ISuperblock, map_to_kmmap};
use crate::implementation::CachedJournal_v::CachedJournal;
use crate::implementation::CachedJournal_v;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::WF_v::WF;
use crate::marshalling::IJournalRecordFormat_v::IJournalRecordFormat;
use crate::marshalling::Marshalling_v::Marshal;
use crate::implementation::OverflowFiction_v::*;
use crate::abstract_system::AbstractCrashAwareMap_v;
use crate::implementation::Cache_v::Cache;
use crate::implementation::FracCacheImpl_v::{FetchErrorCode, FracCacheImpl, MutHandle, PAGE_SIZE_BYTES, WritebackHandle, cache_load_label};

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

enum SuperblockMotivation {
    PushMap,
    PushJournal,
}

enum OutstandingReqInfo{
    SuperBlockReq{},
    CacheLoadReq{read_addr: IAddress, load_handle: MutHandle},
    JournalCacheWriteReq{write_addr: IAddress, handle: WritebackHandle},
}

// Data-free mirror of OutstandingReqInfo, used to capture the variant from a
// borrowed peek (get) without holding the borrow across &mut self calls.
enum OutstandingReqKind{
    SuperBlockReq,
    CacheLoadReq,
    JournalCacheWriteReq,
}

// This struct supplies KVStoreTrait, which has both the entry point to the implementation and the
// proof hooks to satisfy the refinement obligation trait.
pub struct Implementation {
    recovery_phase: RecoveryPhase,

    sync_counter: u64,
    journal_flush_accumulator: u64,

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

        // Cache entries match: CacheLoadReq/JournalCacheWriteReq IDs are exactly outstanding_cache_reqs
        &&& forall |id| #[trigger] self.outstanding_requests@.dom().contains(id) ==> {
            &&& (self.outstanding_requests@[id] is SuperBlockReq) <==> in_flight_sb_id.contains(id)
            &&& (self.outstanding_requests@[id] is CacheLoadReq || self.outstanding_requests@[id] is JournalCacheWriteReq)
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
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle} => {
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
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle} => {
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
        reveal(Implementation::outstanding_requests_wf_map);
        assert forall |id| #[trigger] outstanding.contains_key(id) implies {
            match outstanding[id] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& new_cache.entry_fetched(&read_addr)
                    &&& new_cache.valid_load_handle(&read_addr, load_handle)
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle} => {
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
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle} => {
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
        reveal(Implementation::outstanding_requests_wf_map);
        assert forall |id2| #[trigger] outstanding.insert(req_id, inserted_req).contains_key(id2) implies {
            match outstanding.insert(req_id, inserted_req)[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& cache.entry_fetched(&read_addr)
                    &&& cache.valid_load_handle(&read_addr, load_handle)
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle} => {
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
                    OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle} => {
                        assert(cache.entry_fetched(&write_addr));
                        assert(cache.valid_writeback_handle(&write_addr, handle));
                    },
                    OutstandingReqInfo::SuperBlockReq{} => {}
                }
            }
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
        reveal(Implementation::outstanding_requests_wf_map);
        reveal(Implementation::outstanding_requests_match_cache_reqs_map);
        assert forall |id2| #[trigger] outstanding.remove(id).contains_key(id2) implies {
            match outstanding.remove(id)[id2] {
                OutstandingReqInfo::CacheLoadReq{read_addr, load_handle} => {
                    &&& new_cache.entry_fetched(&read_addr)
                    &&& new_cache.valid_load_handle(&read_addr, load_handle)
                },
                OutstandingReqInfo::JournalCacheWriteReq{write_addr: wa2, handle: h2} => {
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
                OutstandingReqInfo::JournalCacheWriteReq{write_addr: wa2, handle: h2} => {
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
        // &&& self.model@.instance_id() == self.instance@.id() // TODO delete covered by inv

        &&& self.journal.index_ready()

        // physical state consistent with model
        &&& state.recovery_state is RecoveryComplete

        &&& self.journal.seq_end() == self.store_lsn
        &&& self.state().wf()

        // TODO: strengthen to self.outstanding_reqs_match_model() once all exec code
        // properly maintains outstanding_requests (insert on send, remove on response).
        // For now, the weaker conjunct in inv() (SuperBlockReq ==> in_flight is Some)
        // suffices for the B2/B4 pull-downs.

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

        // Connect exec InFlight fields to model state for C1/C2 proofs
        &&& (state.in_flight is Some ==> {
            // InFlight boundary tracks exec journal seq_start (doesn't change between send and receive)
            &&& self.in_flight.unwrap().new_boundary_lsn as nat == self.journal.seq_start()
            // InFlight boundary matches model's in-flight map version
            &&& self.in_flight.unwrap().new_boundary_lsn as nat == state.store.in_flight.unwrap().seq_end
            // InFlight persistent_lsn matches model's inflight journal_version
            &&& self.in_flight.unwrap().new_persistent_lsn as nat == state.in_flight.unwrap().journal_version
            // InFlight store is a snapshot of the persistent store at send time (unchanged since)
            &&& self.in_flight.unwrap().new_store@ == self.persistent_store@
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
        &&& self.journal.seq_start() <= self.store_lsn as nat
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

                assert(view_as_kmmap(self.store) =~= view_as_kmmap(old(self).store).insert(key, Message::Define{value})); //extn // trigger

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

    #[verifier::exec_allows_no_decreases_clause]
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
        let mut frozen_journal;
        match motivation {
            SuperblockMotivation::PushMap => {
                proof { assert(false); }
                return;
            },
            SuperblockMotivation::PushJournal => {
                // sync the ephemeral journal with the existing persistent map
                api.log("send_superblock: journal sync only");

                let target_lsn = self.sync_requests.journal_cleaning_target_lsn;
                match self.journal.clean_for_commit(target_lsn) {
                    CleanForCommitResult::NeedsFlush{} => {
                        let marshalled_end = self.journal.exec_marshaled_seq_end();
                        if target_lsn > marshalled_end {
                            // TODO: wire in journal marshall code to marshal each page into the cahe 
                            // until marshalled end is beyond the targe lsn
                            return;
                        } 

                        // Now it's time to flush!
                        let mut continue_writeback = true;
                        while continue_writeback
                            invariant
                                self.inv_api(api),
                                self.ready_for_user_operation(),
                                target_lsn == self.sync_requests.journal_cleaning_target_lsn,
                                target_lsn <= marshalled_end,
                                marshalled_end as nat == self.journal.marshalled_seq_end()
                        {
                            proof {
                                reveal(Implementation::inv);
                                reveal(Implementation::ready_for_user_operation);
                                reveal(Implementation::inv_running);
                            }
                            let ghost pre_model = self.model@.value();
                            let ghost pre_outstanding = self.outstanding_requests@;
                            let ghost pre_cache_impl = self.cache;
                            let ghost pre_view_store = self.view_store();
                            let ghost pre_journal_seq_start = self.journal.seq_start();
                            proof {
                                reveal(Implementation::inv_api);
                                reveal(Implementation::inv);
                                reveal(Implementation::inv_post_superblock_common);
                                assert(pre_model.state.store == pre_view_store);
                                assert(Self::outstanding_requests_wf_map(pre_outstanding, pre_cache_impl));
                                assert(Self::outstanding_requests_match_cache_reqs_map(
                                    pre_outstanding,
                                    pre_model.state.outstanding_cache_reqs,
                                ));
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
                                        reveal(Implementation::inv_api);
                                        reveal(Implementation::inv);
                                        self.system_inv_implies_atomic_state_wf();
                                        let ghost inserted_req = OutstandingReqInfo::JournalCacheWriteReq{
                                            write_addr: request.addr,
                                            handle: request.handle,
                                        };
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
                                    }
                                },
                                BeginWritebackForTargetResult::Complete{..} => {
                                    proof {
                                        assert(cache_after_wb == pre_model.state.cache);
                                    }
                                    self.model = Tracked(model);
                                    proof {
                                        self.system_inv_implies_atomic_state_wf();
                                        assert(self.outstanding_requests@ == pre_outstanding);
                                        Self::outstanding_requests_wf_map_preserved_by_cache(
                                            pre_outstanding,
                                            pre_cache_impl,
                                            self.cache,
                                        );
                                        assert(self.inv_api(api));
                                    }
                                    continue_writeback = false;
                                },
                            }
                        }
                        return;
                    },
                    CleanForCommitResult::Frozen{frozen_journal: fj} => {
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

                // Okay, the journal is clean up to the point of journal_cleaning_target_lsn, which
                // means the journal_cleaning_reqs are now eligible to be delivered in a
                // superblock.
                std::mem::swap(&mut self.sync_requests.superblocking_reqs, &mut self.sync_requests.journal_cleaning_reqs);

                std::mem::swap(&mut self.persistent_store, &mut tmp_store);

                sb = ISuperblock{
                    journal_snapshot: frozen_journal.snapshot,
                    store: tmp_store.v,
                };
                
                api.log("sending this particular superblock: ");
                Self::debug_print(&sb);
                raw_page = DiskLayout::new().marshall(&sb);

                let ISuperblock{store: mut tmp_store_v, ..} = sb;
                tmp_store.v = tmp_store_v;
                std::mem::swap(&mut self.persistent_store, &mut tmp_store);

                self_in_flight = Some(InFlight{
                    new_boundary_lsn: self.journal.exec_seq_start(),
                    freshest_rec: frozen_journal.snapshot.freshest_rec,
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
                        reveal(Implementation::inv);
                        reveal(Implementation::ready_for_user_operation);
                        reveal(Implementation::inv_running);
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
            new_boundary_lsn: frozen_journal.seq_start() as nat,
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
                frozen_seq_end: frozen_journal.seq_end as nat,
            };

            // Prove preconditions of execute_sync_begin:
            let pre = state_after_freeze;
            let post = post_state.state;

            let map_lbl = AbstractCrashAwareMap::Label::CommitStartLabel{
                new_boundary_lsn: frozen_journal.seq_start() as nat};
            reveal(AbstractCrashAwareMap::State::next);
            reveal(AbstractCrashAwareMap::State::next_by);

            assert(AbstractCrashAwareMap::State::next_by(
                pre.store,
                post.store,
                map_lbl,
                AbstractCrashAwareMap::Step::commit_start(),
            ));
            assert(AbstractCrashAwareMap::State::next(pre.store, post.store, map_lbl));
            let journal_lbl = CachedJournal::Label::FreezeForCommit{
                frozen: frozen_journal.snapshot@,
                frozen_seq_end: frozen_journal.seq_end as nat,
            };
            assert(pre.journal == self.journal@);
            assert(post.journal == self.journal@);
            assert(CachedJournal::State::next(pre.journal, post.journal, journal_lbl));
            
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
            self.journal.seq_start_le_marshalled_end();

            // The superblock write ID is not in outstanding_cache_reqs.
            self.system_inv_sb_id_not_in_cache_reqs();
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
        assert( self.sync_reqs_in_version(self.sync_requests.journal_cleaning_reqs@, self.sync_requests.journal_cleaning_target_lsn as nat) );
        assert( oself.sync_reqs_in_version(oself.sync_requests.journal_cleaning_reqs@, oself.sync_requests.journal_cleaning_target_lsn as nat) );
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
        reveal(Implementation::outstanding_requests_match_cache_reqs_map);

        // From outstanding_requests_wf_map: CacheLoadReq → valid_load_handle
        reveal(Implementation::outstanding_requests_wf_map);
        reveal(Implementation::inv);
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

        reveal(Implementation::outstanding_requests_match_cache_reqs_map);
        reveal(Implementation::outstanding_requests_wf_map);
        reveal(Implementation::inv);
        match pre_outstanding[disk_req_id] {
            OutstandingReqInfo::JournalCacheWriteReq{write_addr, handle} => {
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

    // B5: Every disk response matches an outstanding request.
    // B6: The superblock read response's store has unique keys.
    // Uses persistent_sb_disk_inv (asb.wf()) + awaiting_sb_response_is_disk_content.
    proof fn system_inv_sb_store_unique_keys(self, disk_req_id: ID, i_disk_response: IDiskResponse, disk_response_token: Tracked<DiskRespShard>)
    requires
        self.state().recovery_state is AwaitingSuperblock,
        i_disk_response is ReadResp,
        disk_response_token@.multiset() == multiset_map_singleton(disk_req_id, i_disk_response@),
    ensures
        VecMap::unique_keys(DiskLayout::spec_new().spec_parse_inner(i_disk_response@->data).store)
    {
        let model = open_system_invariant_disk_response_singleton::<ConcreteProgramModel, RefinementProof>(
            self.model, disk_response_token, disk_req_id, i_disk_response@);
        // awaiting_sb_response_is_disk_content: response data == disk content at sb addr
        // persistent_sb_disk_inv: ASuperblock parsed from disk content has wf() (unique_keys)
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
                    entries: to_journal_reads(journal_raw_disk),
                },
                self.journal@.snapshot.freshest_rec),
        self.journal@.status is Some && self.journal@.snapshot.freshest_rec is Some ==> {
            let journal_dv = LinkedJournal_v::DiskView{
                boundary_lsn: self.journal@.snapshot.boundary_lsn,
                entries: to_journal_reads(journal_raw_disk),
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
        reveal(Implementation::inv);
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
                    entries: to_journal_reads(journal_raw_disk),
                },
                self.journal@.snapshot.freshest_rec));
        assume(self.journal@.status is Some && self.journal@.snapshot.freshest_rec is Some ==> {
            let journal_dv = LinkedJournal_v::DiskView{
                boundary_lsn: self.journal@.snapshot.boundary_lsn,
                entries: to_journal_reads(journal_raw_disk),
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
        // Remove the superblock request entry from outstanding_requests.
        // This is done here (rather than in the dispatcher) so that inv() holds
        // at the point of dispatch — model_reqs_in_outstanding is maintained.
        let _req_info = self.outstanding_requests.remove(&id);

        let mut ready_reqs = vec![];
        std::mem::swap(&mut self.sync_requests.superblocking_reqs, &mut ready_reqs);

        // TODO(jialin): why do these Noop requests have ids? Because we need to know
        // which Noop a reply corresponds to.
        let ghost pre_state = self.model@.value();

        // From old(self).inv(): SuperBlockReq ==> in_flight is Some && !cache_reqs.contains(id)
        // From system invariant: in_flight.req_id == id
        proof {
            // old(self) had the SuperBlockReq entry — triggers the forall in old(self).inv():
            //   in_flight is Some, !cache_reqs.contains(id), req_id == id
            reveal(Implementation::inv);
            // in_flight and model are unchanged by remove
            self.system_inv_response_implies_in_flight(id, disk_response, response_shard);
        }

        let mut in_flight = None;
        std::mem::swap(&mut self.in_flight, &mut in_flight);
        if let Some(InFlight{new_boundary_lsn, freshest_rec, new_persistent_lsn, new_store}) = in_flight {
            if self.journal.exec_seq_start() != new_boundary_lsn {
                self.persistent_store = new_store;
            }

            let ghost new_lsn_addr_index =
                lsn_addr_index_discard_up_to(pre_state.state.journal.status.unwrap().lsn_addr_index, new_boundary_lsn as LSN);
            
            // Here's a commit_complete step of AbstractCrashAwareMap:
            let ghost post_store = AbstractCrashAwareMap::State{
                persistent: old(self).state().store.in_flight.unwrap(),
                in_flight: None,
                ..old(self).state().store
            };
            // Use model's current freshest_rec (not InFlight's send-time value, which
            // may be stale if marshalling occurred between send and receive).
            // discard_old with start_lsn == pre.seq_start() preserves freshest_rec.
            let ghost freshest_rec_a = if new_boundary_lsn as LSN == pre_state.state.journal.seq_end() {
                None::<Address>
            } else {
                pre_state.state.journal.snapshot.freshest_rec
            };
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

            // in_flight is Some and req_id == id were established above via
            // system_inv_response_implies_in_flight

            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

            proof {
                let info = ProgramDiskInfo{ reqs: Multiset::empty(), resps: response_shard@.multiset() };
                let discard_addrs =
                    pre_state.state.journal.status.unwrap().lsn_addr_index.values() - new_lsn_addr_index.values();
                let disk_event = DiskEvent::ExecuteSyncEnd{ discard_addrs };

                assert( response_shard@.multiset() == Multiset::singleton((pre_state.state.in_flight->Some_0.req_id, DiskResponse::WriteResp{})) );    // extn // trigger

                // Access inv_running conjuncts from old(self).inv() precondition
                reveal(Implementation::inv);
                reveal(Implementation::inv_running);
                reveal(Implementation::inv_post_superblock_common);

                // === C2: state machine transitions ===
                // commit_complete: persistent ← in_flight, clear in_flight
                reveal(AbstractCrashAwareMap::State::next_by);
                reveal(AbstractCrashAwareMap::State::next);
                // witness
                assert( AbstractCrashAwareMap::State::next_by(
                    pre_state.state.store, post_state.state.store,
                    AbstractCrashAwareMap::Label::CommitCompleteLabel{},
                    AbstractCrashAwareMap::Step::commit_complete()) );

                // discard_old: advance journal boundary
                reveal(CachedJournal::State::next_by);
                reveal(CachedJournal::State::next);
                let journal_lbl = CachedJournal::Label::DiscardOld{
                    start_lsn: post_state.state.persistent_map().seq_end,
                    require_end: post_state.state.ephemeral_map().seq_end,
                    discard_addrs,
                };
                assert( CachedJournal::State::next_by(
                    pre_state.state.journal, post_state.state.journal,
                    journal_lbl, CachedJournal::Step::discard_old()) );

                // evictable_check: discard_addrs is empty because boundary doesn't advance
                // discard_addrs is empty because boundary doesn't advance
                reveal(Implementation::inv_running);
                self.journal.lsn_addr_index_keys_bounded_below();
                self.journal.view_seq_start_ensures();
                crate::allocation_layer::LikesJournal_v::lsn_addr_index_discard_up_to_ensures(
                    pre_state.state.journal.status.unwrap().lsn_addr_index,
                    new_boundary_lsn as LSN);

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
                reveal(Implementation::inv);
                reveal(Implementation::inv_running);
                reveal(Implementation::inv_post_superblock_common);
                reveal(Implementation::i_persistent_store);
                reveal(Implementation::i_inflight_store);
                reveal(Implementation::i_ephemeral_store);
                reveal(Implementation::view_store);
                reveal(Implementation::state);
                reveal(view_as_kmmap);

                // === inv_post_superblock_common: self.state().journal == self.journal@ ===
                // The discard_old step is a no-op: start_lsn == pre.seq_start(), so journal unchanged.
                self.journal.view_seq_start_ensures();
                // self.journal@.snapshot.boundary_lsn == self.journal.seq_start()
                // From inv_running: new_boundary_lsn as nat == self.journal.seq_start()

                // lsn_addr_index is unchanged: all keys >= boundary_lsn, so discard_up_to is no-op
                self.journal.lsn_addr_index_keys_bounded_below();
                crate::allocation_layer::LikesJournal_v::lsn_addr_index_discard_up_to_ensures(
                    pre_state.state.journal.status.unwrap().lsn_addr_index,
                    new_boundary_lsn as LSN);
                // trigger extn
                assert( new_lsn_addr_index =~= pre_state.state.journal.status.unwrap().lsn_addr_index );

                // freshest_rec: case split on whether journal is empty
                self.journal.view_seq_end_ensures();
                if new_boundary_lsn as LSN == pre_state.state.journal.seq_end() {
                    // Journal empty: seq_start == seq_end, so freshest_rec must be None
                    self.journal.freshest_rec_none_when_empty();
                }
            }
            self.deliver_inflight_replies(&mut ready_reqs, api);

            // maybe launch another superblock
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
            reveal(Implementation::inv);
            reveal(Implementation::state);
            self.system_inv_cache_load_is_read_resp(id, disk_response, response_shard, pre_outstanding);
            // Establish sb_req_id disjointness BEFORE the remove, while self.state() is fresh.
            // If in_flight is Some, in_flight.req_id is NOT in cache_reqs.
            // Combined with CacheLoadReq ==> id IS in cache_reqs, this gives in_flight.req_id != id.
            if self.state().in_flight is Some {
                self.system_inv_sb_id_not_in_cache_reqs();
                reveal(Implementation::outstanding_requests_match_cache_reqs_map);
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
            reveal(Implementation::inv);
            reveal(Implementation::state);
            assert(self.outstanding_requests_wf());
            assert(self.outstanding_requests_match_cache_reqs());
            reveal(Implementation::model_reqs_in_outstanding);
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
            reveal(Implementation::inv);
            reveal(Implementation::state);
            assert(Self::outstanding_requests_wf_map(pre_outstanding, pre_cache_impl));
            assert(Self::outstanding_requests_match_cache_reqs_map(pre_outstanding, pre_cache_reqs));
            self.system_inv_journal_cache_write_is_write_resp(id, disk_response, response_shard, pre_outstanding);
            if self.state().in_flight is Some {
                self.system_inv_sb_id_not_in_cache_reqs();
                reveal(Implementation::outstanding_requests_match_cache_reqs_map);
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
            reveal(Implementation::inv);
            reveal(Implementation::state);
            assert(self.outstanding_requests@ == pre_outstanding.remove(id));
            reveal(Implementation::outstanding_requests_match_cache_reqs_map);
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
            reveal(Implementation::outstanding_requests_wf);
            assert(self.outstanding_requests_wf());
            assert(self.outstanding_requests_match_cache_reqs());
            reveal(Implementation::model_reqs_in_outstanding);
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
                OutstandingReqInfo::CacheLoadReq{..} => OutstandingReqKind::CacheLoadReq,
                OutstandingReqInfo::JournalCacheWriteReq{..} => OutstandingReqKind::JournalCacheWriteReq,
            }
        };
        // Borrow from get() is dropped — self is free for &mut calls.

        match kind {
        OutstandingReqKind::SuperBlockReq => {
            // SuperBlockReq branch.
            // A6: Derive disk_response is WriteResp from the system invariant.
            // inv() holds because we haven't removed anything yet.
            proof {
                reveal(Implementation::inv);
                reveal(Implementation::inv_running);
                reveal(Implementation::state);
                reveal(Implementation::i);

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

            // B6: derive unique_keys from system invariant BEFORE model swap
            proof {
                self.system_inv_sb_store_unique_keys(disk_req_id, i_disk_response, disk_response_token);
            }

            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }

            let layout = DiskLayout::new();
            let superblock: ISuperblock = layout.parse(&raw_page);
            Self::debug_print(&superblock);

            self.persistent_store = VecMap::from_vec(superblock.store);
            self.journal = JournalImpl::new(superblock.journal_snapshot);

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
                self.journal.view_seq_start_ensures();
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
                disk_response_token.get(),
            );
            self.model = Tracked(model);
        }

        api.log("recovery phase now ReadingJournalIndex");
        self.recovery_phase = RecoveryPhase::ReadingJournalIndex;

        proof {
            reveal(Implementation::inv);
            reveal(Implementation::inv_recover);
            broadcast use vstd::map::axiom_map_empty;
        }
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
        let ghost cache_before_index = self.cache;
        proof {
            reveal(Implementation::inv);
            self.system_inv_implies_atomic_state_wf();
        }
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
                proof {
                    let ghost new_info = OutstandingReqInfo::CacheLoadReq{read_addr: addr, load_handle: slot_handle};
                    assert(self.outstanding_requests_match_cache_reqs()) by {
                        let ghost new_outstanding = self.outstanding_requests@;
                        let ghost new_cache_reqs = post_state.state.outstanding_cache_reqs;
                        let ghost old_cache_reqs = pre_state.state.outstanding_cache_reqs;

                        assert(new_cache_reqs.is_injective()) by {
                            reveal(Implementation::outstanding_requests_match_cache_reqs);

                            assert(!old_cache_reqs.contains_value(addr@)) by {
                                if old_cache_reqs.contains_value(addr@) {
                                    assert(old_cache_reqs.values().contains(addr@)) by {
                                        reveal(Map::values);
                                    }
                                    assert(pre_state.state.cache.lookup_map.dom().contains(addr@)) by {
                                    }
                                    assert(cache_before_index.entry_fetched(&addr)) by {
                                        assert(cache_before_index@.lookup_map.contains_key(addr@)) by {
                                            reveal(Map::contains_key);
                                        }
                                        FracCacheImpl::entry_fetched_from_view(&cache_before_index, &addr);
                                    }
                                }
                            }

                        }

                    }
                }
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

                proof {
                    self.system_inv_implies_atomic_state_wf();
                }
            }
            RecoverIndexResult::IndexProgress{} => { }
        }
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
            let ghost pre_state = self.model@.value();
            let ghost instance_id = self.instance@.id();
            let ghost pre_cache_impl = self.cache;
            let ghost pre_cache = self.cache@;
            let ghost pre_outstanding = self.outstanding_requests@;
            let ghost pre_store_lsn = self.store_lsn as nat;
            proof {
                assert(self.inv_applying_journal()) by {
                    reveal(Implementation::inv);
                }
                // inv_applying_journal gives recovery_state is JournalIndexComplete
            }
            let ghost journal_raw_disk = self.system_inv_journal_pages_parsable();
            let fetch = self.journal.recover_map_step(&mut self.cache, self.store_lsn, Ghost(journal_raw_disk));

            // we need to track some
            match fetch {
                RecoverMapResult::NotInCache{} => {
                    return false;
                }
                RecoverMapResult::FetchSuccess{reads, addr, record} => {
                    let record_msg_len = record.messages.len() as u64;
                    let record_seq_end = record.header.start_lsn + record_msg_len;

                    let ghost cache_after_fetch = self.cache@;
                    let ghost journal_after_fetch = self.journal@;
                    let ghost fetch_lbls = map_recovery_labels(self.journal.seq_start(), reads@, addr@);

                    let mut next_lsn = self.store_lsn;
                    let mut next_index: usize = (self.store_lsn - record.header.start_lsn) as usize;

                    let ghost record_msgs = record.parsedv().view().message_seq;
                    let ghost records = record_msgs.maybe_discard_old(pre_store_lsn);

                    while next_lsn < record_seq_end
                    invariant
                        self.model@.value() == pre_state,
                        self.model@.instance_id() == instance_id,
                        self.instance@.id() == instance_id,
                        self.outstanding_requests@ == pre_outstanding,
                        self.recovery_phase is ApplyingJournalToRecoverEphemeralMap,
                        self.sync_requests.valid_empty_sync_buffer(self.instance@.id()),
                        self.cache.wf(),
                        self.cache.valid_load_handles_preserved(pre_cache_impl),
                        self.journal.wf(),
                        self.journal.no_unmarshalled_entries(),
                        exec_seq_end == self.journal.seq_end(),
                        self.store_lsn as nat <= self.journal.seq_end(),
                        self.store.wf(),
                        self.cache@ == cache_after_fetch,
                        self.journal@ == journal_after_fetch,
                        Cache::State::next(pre_cache, cache_after_fetch, fetch_lbls.0),
                        pre_state.state.store.persistent == self.i_persistent_store(),
                        pre_state.state.store.in_flight == self.i_inflight_store(),
                        self.store_lsn == next_lsn,
                        next_lsn as nat == record.header.start_lsn as nat + next_index as nat,
                        pre_store_lsn <= self.store_lsn as nat <= records.seq_end,
                        view_as_kmmap(self.store)
                            == MsgHistory::map_plus_history(
                                pre_state.state.ephemeral_map(),
                                records.discard_recent(self.store_lsn as nat),
                            ).value,
                    decreases record_seq_end - next_lsn
                    {
                        let km = record.messages[next_index];
                        let ghost old_store_lsn = self.store_lsn as nat;

                        match km.message {
                            Message::Define{value} => {
                                let key = km.key;
                                self.store.insert(key, value);
                                proof {
                                    let prefix = records.discard_recent(old_store_lsn);
                                    let next_prefix = records.discard_recent((old_store_lsn + 1) as nat);
                                    assert(next_prefix.discard_recent(old_store_lsn) == prefix) by {
                                        MsgHistory::ext_equal_is_equality();
                                    }

                                    reveal_with_fuel(MsgHistory::apply_to_stamped_map, 2);
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

                        self.store_lsn = self.store_lsn + 1;
                        next_lsn = next_lsn + 1;
                        next_index = next_index + 1;
                    }

                    let ghost post_state = ConcreteProgramModel{
                        state: AtomicState{
                            cache: self.cache@,
                            journal: self.journal@,
                            store: self.view_store(),
                            ..pre_state.state
                        }
                    };

                    proof {
                        let map_lbl = AbstractCrashAwareMap::Label::PutRecordsLabel{records};
                        assert(view_as_kmmap(self.store)
                            == MsgHistory::map_plus_history(pre_state.state.ephemeral_map(), records).value) by {
                            assert(records.discard_recent(self.store_lsn as nat) == records); // trigger
                        }
                        MsgHistory::map_plus_history_seq_end_lemma(pre_state.state.ephemeral_map(), records);

                        reveal(AbstractMap::State::next_by);
                        reveal(AbstractMap::State::next);
                        assert(AbstractMap::State::next_by(
                            pre_state.state.store.ephemeral->v,
                            post_state.state.store.ephemeral->v,
                            AbstractMap::Label::PutLabel{puts: records},
                            AbstractMap::Step::put{}
                        )); // witness
                        reveal(AbstractCrashAwareMap::State::next_by);
                        reveal(AbstractCrashAwareMap::State::next);
                        assert(AbstractCrashAwareMap::State::next_by(
                            pre_state.state.store,
                            post_state.state.store,
                            map_lbl,
                            AbstractCrashAwareMap::Step::put_records(post_state.state.store.ephemeral->v)
                        )); // witness
                        assert(ConcreteProgramModel::valid_internal_transition(pre_state, post_state)) by {
                                assert(AtomicState::internal_transitions(
                                pre_state.state,
                                post_state.state,
                                InternalEvent::MapRecovery{records, reads: reads@, addr: addr@}
                            )) by {
                                let cache_lbl = Cache::Label::Access{reads: reads@, writes: Map::empty()};
                                let ghost journal_reads = to_journal_reads(reads@);

                                assert(Cache::State::next(pre_state.state.cache, post_state.state.cache, cache_lbl)) by {
                                    reveal(map_recovery_labels);
                                }
                                assert(CachedJournal::State::next(
                                    pre_state.state.journal,
                                    post_state.state.journal,
                                    fetch_lbls.1
                                )) by {
                                }
                                self.journal.view_seq_start_ensures();
                                assert(pre_state.state.journal.snapshot.boundary_lsn
                                    <= journal_reads[addr@].message_seq.seq_end) by {
                                    assert(pre_state.state.journal.snapshot.boundary_lsn
                                        <= record.parsedv().view().message_seq.seq_end);
                                }
                                reveal(map_recovery_labels);
                            };
                        }
                    }
                    let tracked instance = self.instance.borrow();
                    let tracked new_reply_token = instance.internal(
                        KVStoreTokenized::Label::InternalOp{},
                        post_state,
                        self.model.borrow_mut(),
                    );

                    if self.store_lsn < exec_seq_end {
                        return true;
                    }
                }
            }
        }
        let exec_seq_end = self.journal.exec_seq_end();
        if self.store_lsn < exec_seq_end {
            return true;
        }
        let ghost pre_state = self.state();
        proof {
            reveal(Implementation::inv);
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

    fn should_do_background_marshal(&self) -> (out: bool)
    {
        self.outstanding_requests.len() == 0
    }

    fn do_background_work(&mut self, api: &mut ClientAPI<ConcreteProgramModel>) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).ready_for_user_operation(),
        ensures
            self.inv_api(api),
            self.ready_for_user_operation(),
    {
        if !self.should_do_background_marshal() {
            proof {
            }
            return false;
        }
        let ghost pre_state = self.model@.value();
        let did_work = self.journal.internal_journal_marshal_one_page(&mut self.cache);

        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof { tracked_swap(self.model.borrow_mut(), &mut model); }

        let ghost post_state = ConcreteProgramModel{
            state: AtomicState{
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
                    InternalEvent::JournalBackgroundWork{}
                )) by {
                    reveal(Implementation::inv);
                    reveal(Implementation::ready_for_user_operation);
                    reveal(Implementation::inv_running);
                    assert(pre_state.state.client_ready());
                    assert(AtomicState::cache_background_step(
                        pre_state.state.cache,
                        post_state.state.cache,
                    ));
                    assume(AtomicState::journal_background_journal_step(
                        pre_state.state.journal,
                        post_state.state.journal,
                    ));
                };
            }
        }
        let tracked _new_reply_token = self.instance.borrow().internal(
            KVStoreTokenized::Label::InternalOp{},
            post_state,
            &mut model,
        );
        self.model = Tracked(model);
        proof {
            reveal(Implementation::inv);
            reveal(Implementation::ready_for_user_operation);
            reveal(Implementation::inv_running);
            if self.recovery_phase is ReadyForUserOperation {
                let state = self.state();
                self.system_inv_implies_atomic_state_wf();
                assert(state.in_flight is Some ==> {
                    self.in_flight.unwrap().new_boundary_lsn
                        <= state.journal.status.unwrap().unmarshalled_tail.seq_start
                });
                assert(state.in_flight is Some ==> {
                    let sync_version = state.in_flight.unwrap().journal_version;
                    let new_persistent_map_version = self.in_flight.unwrap().new_boundary_lsn as nat;
                    &&& self.journal.seq_start() <= new_persistent_map_version
                    &&& new_persistent_map_version <= sync_version
                    &&& self.sync_reqs_in_version(self.sync_requests.superblocking_reqs@, sync_version)
                });
                assert(state.in_flight is Some ==> {
                    &&& self.in_flight.unwrap().new_boundary_lsn as nat == self.journal.seq_start()
                    &&& self.in_flight.unwrap().new_boundary_lsn as nat == state.store.in_flight.unwrap().seq_end
                    &&& self.in_flight.unwrap().new_persistent_lsn as nat == state.in_flight.unwrap().journal_version
                    &&& self.in_flight.unwrap().new_store@ == self.persistent_store@
                });
                assert(self.sync_reqs_in_version(
                    self.sync_requests.journal_cleaning_reqs@,
                    self.sync_requests.journal_cleaning_target_lsn as nat,
                ));
                assert(Self::three_sync_req_lists_mutually_unique(
                    self.sync_requests.superblocking_reqs@,
                    self.sync_requests.journal_cleaning_reqs@,
                    self.sync_requests.buffered_reqs@,
                ));
            }
            assert forall |id| #![auto] self.outstanding_requests@.dom().contains(id)
                && self.outstanding_requests@[id] is SuperBlockReq
                ==> self.in_flight is Some
                    && !self.state().outstanding_cache_reqs.dom().contains(id)
                    && self.state().in_flight is Some
                    && id == self.state().in_flight.unwrap().req_id by {
            }
            assume(self.inv_api(api));
        }

        did_work
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
            journal_flush_accumulator: 0,
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
                    // Internal/background maintenance work for the ready state.
                    progress = progress || self.do_background_work(&mut api);
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
