// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use vstd::hash_map::HashMapWithView;
// use crate::abstract_system::MsgHistory_v::{MsgHistory, KeyedMessage};
// use crate::abstract_system::StampedMap_v::*;
// use crate::marshalling::IntegerMarshalling_v::IntFormat;
// use crate::marshalling::Marshalling_v::Parsedview;
// use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
// use crate::marshalling::KeyedMessageFormat_v::KeyedMessageFormat;
use crate::spec::MapSpec_t::{ID};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
// use crate::implementation::OverflowFiction_v::*;
// use crate::implementation::CachedJournal_v::CachedJournal;
use crate::disk::GenericDisk_v::{IAddress};
// use crate::implementation::CachedJournal_v;
// use crate::implementation::JournalTypes_v::AJournal;
// use crate::implementation::JournalTypes_v::ILsn;
// use crate::implementation::JournalModel_v::LsnAddrIndex;
use crate::spec::AsyncDisk_t::{RawPage, DiskRequest, DiskResponse};
use crate::implementation::Cache_v::*;
use vstd::std_specs::hash::obeys_key_model;

use vstd::prelude::*;
use vstd::pcm::Loc;
use vstd::tokens::frac::*;
use vstd::pervasive::unreached;

verus!{

pub const PAGE_SIZE_BYTES: usize = 4096;
pub const CACHE_SIZE_RECS: usize = 1000;

pub type IRawPage = Vec<u8>;
pub type Perm = Frac<Slot,2>;

// NOTE: not very modular as it exposes all the information to the caller
// these information leaks through the module boundary, we want the ability 
// to do partial pub fields, this is supported by rust just not verus
// is it possible for verus for verification purposes to view all fields as pub (as long as one field is marked so)
// regardless of the annotation?

#[derive(Clone,Copy)]
pub enum IEntry{
    Empty,
    Reserved{addr: IAddress},
    Loading{addr: IAddress}, 
    Filled{addr: IAddress},
}

struct Metadata {
    entry: IEntry,
    status: Status,
}

pub struct MutHandle {
    pub token: Tracked<Perm>,
    pub idx: Slot,
    pub rec: IRawPage,
}

impl MutHandle {
    pub open spec fn inv(&self) -> bool
    {
        &&& self.token@.resource() == self.idx
        &&& self.rec.len() == PAGE_SIZE_BYTES
    }
}

pub struct FracCacheImpl {
    perms: Tracked<Seq<Perm>>, // ghost permission tracking
    internal_slots: Vec<Option<IRawPage>>, // reserved cache memory
    metadata: Vec<Metadata>,
    lookup_map: HashMapWithView<IAddress, Slot>,
}

// release handle returns to specific slot

impl View for FracCacheImpl {
    type V = Cache::State;

    closed spec fn view(&self) -> Self::V
    {
        let entries = Map::new(|k: Slot| k < self.total_slots(), |k| self.view_entry_at(k));
        let status_map = Map::new(|k: Slot| k < self.total_slots(), |k| self.metadata[k as int].status);
        Cache::State{
            entries,
            status_map,
            lookup_map: self.lookup_map@,
        }
    }
}

pub enum FetchErrorCode {
    Success{slot_handle: MutHandle},
    CacheFull, // all slots are filled, no available entries to evict without writeback
    // WritebackEviction, // slots are filled, have to writeback to evict, require additional calls
    LoadInitiate{slot_handle: MutHandle},   // cache is asking caller to initiate the disk IO on cache's behalf
    Awaiting,   // IO request has been sent, haven't heard back yet.
}

pub open spec fn cache_load_label(addr: &IAddress) -> Cache::Label
{
    Cache::Label::DiskOps{requests: set!{DiskRequest::ReadReq{from: addr@}}, responses: map!{}}
}

impl FracCacheImpl {
    /// spec fns

    pub open spec fn total_slots(&self) -> Slot
    {
        CACHE_SIZE_RECS
    }

    closed spec fn entry_present(self, idx: Slot) -> bool
    {
        &&& idx < self.total_slots()
        &&& self.internal_slots[idx as int] is Some
    }

    closed spec fn perms_inv(self) -> bool
    {
        forall |i| 0 <= i < self.total_slots() ==> 
            #[trigger] self.perms@[i].resource() == i
    }

    closed spec fn slots_inv(self) -> bool
    {
        forall |i| 0 <= i < self.total_slots() && self.internal_slots[i] is Some
            ==> #[trigger] self.internal_slots[i].unwrap().len() == PAGE_SIZE_BYTES
    }

    closed spec fn perms_consistent_with_slots(self) -> bool
    {
        &&& forall |i: int| #![auto] 0 <= i < self.total_slots() ==> {
            &&& self.internal_slots[i] is Some <==> self.perms@[i].frac() == 2 // perm consistent
            &&& self.internal_slots[i] is None <==> self.perms@[i].frac() == 1 // perm consistent
        }
    }

    closed spec fn lookup_map_inv(self) -> bool
    {
        forall |slot| #[trigger] self.lookup_map@.contains_value(slot) 
            ==> slot < self.total_slots()
    }

    closed spec fn lookup_map_consistent_with_slots(self) -> bool
    {
        &&& forall |slot: Slot| #![auto] slot < self.total_slots() ==>
            (self.lookup_map@.contains_value(slot) <==> !(self.metadata[slot as int].entry is Empty))
    }
    
    closed spec fn lookup_map_bijection(self) -> bool
    {
        // If metadata[slot] is Filled{addr}, then lookup_map@[addr@] == slot
        forall |slot: Slot| slot < self.total_slots() ==> {
            match #[trigger] self.metadata[slot as int].entry {
                IEntry::Filled{addr} => {
                    self.lookup_map@.contains_key(addr@) && self.lookup_map@[addr@] == slot
                },
                _ => true,
            }
        }
    }

    // if these are things proven in the cache layer then we don't need to do this here
    closed spec fn metadata_consistent_with_slots(self) -> bool
        recommends self.lookup_map_consistent_with_slots()
    {
        forall |slot| 0 <= slot < self.total_slots()
        ==> match #[trigger] self.metadata[slot].entry {
            IEntry::Empty{} => { self.internal_slots[slot] is Some },
            IEntry::Filled{addr} => { true },
            _ => { self.internal_slots[slot] is None }
        }
        // // empty slots have valid internal buffers
        // &&&  && self.metadata[slot].entry is Empty
        //     ==> self.internal_slots[slot] is Some

        // // valid look up slots with loading has none
        // &&& forall |slot: int| #![auto] 0 <= slot < self.total_slots() && self.metadata[slot].entry is Loading || 
        //     ==> self.internal_slots[slot] is None

        // &&& forall |slot: int| #![auto] 0 <= slot < self.total_slots() && self.metadata[slot].entry is Filled
        //     ==> self.internal_slots[slot] is None

        // reserved are new pages that we write to directly
    }

    pub closed spec fn wf(self) -> bool
    {
        &&& self.internal_slots.len() == self.total_slots()
        &&& self.metadata.len() == self.total_slots()
        &&& self.perms@.len() == self.total_slots()

        &&& self.perms_inv()
        &&& self.slots_inv()
        &&& self.lookup_map_inv()
        &&& self.perms_consistent_with_slots()
        &&& self.metadata_consistent_with_slots()
        &&& self.lookup_map_consistent_with_slots()
        &&& self.lookup_map_bijection()
    }

    closed spec fn view_entry_at(self, k: Slot) -> Entry
        recommends self.wf(), k < self.total_slots()
    {
        match self.metadata[k as int].entry {
            IEntry::Empty => Entry::Empty,
            IEntry::Reserved{addr} => Entry::Reserved{addr: addr@},
            IEntry::Loading{addr} => Entry::Loading{addr: addr@},
            IEntry::Filled{addr} => Entry::Filled{
                addr: addr@,
                // NOTE: changed from empty_page to arbitrary because we want to 
                // support loading directly into the page
                data: if self.internal_slots[k as int] is None { Self::empty_page() } 
                        else { self.internal_slots[k as int].unwrap()@ }
            },
        }
    }

    pub open spec fn empty_page() -> RawPage
    {
        seq![0u8; PAGE_SIZE_BYTES as nat]
    }

    #[verifier::external_body]
    exec fn new_empty_page() -> (out: IRawPage)
        ensures out@ == Self::empty_page()
    {
        vec![0; PAGE_SIZE_BYTES]
    }

    spec fn empty_metadata() -> Metadata {
        Metadata{ entry: IEntry::Empty, status: Status::NotFilled, }
    }

    pub closed spec fn entry_fetched(self, addr: &IAddress) -> bool
    {
        self.lookup_map@.contains_key(addr@)
    }

    pub proof fn entry_fetched_lemma()
        ensures forall |slf: Self, addr: &IAddress| #![auto] slf.entry_fetched(addr) ==> slf@.lookup_map.contains_key(addr@)
    {
    }

    pub proof fn lookup_addr_slot_lemma()
        ensures forall |slf: Self, addr: &IAddress| #![auto]
            slf.entry_fetched(addr) ==> slf.lookup_addr_slot(addr) == slf@.lookup_map[addr@]
    {
        // lookup_addr_slot is defined as lookup_map@[addr@], so this is trivial
    }
    
    pub proof fn lookup_map_bijection_lemma()
        ensures forall |slf: Self, slot: Slot| #![auto]
            slf.wf() && slot < slf.total_slots() && slf@.entries[slot] is Filled ==> {
                let addr = slf@.entries[slot].get_addr();
                slf@.lookup_map.contains_key(addr) && slf@.lookup_map[addr] == slot
            }
    {
        // Follows from lookup_map_bijection invariant in wf()
        // slf@.entries[slot] is Filled iff slf.metadata[slot].entry is Filled (by view_entry_at definition)
        // When both are Filled, they have the same address
        // slf@.lookup_map == slf.lookup_map@ by definition of view
        // So the abstract property follows from the concrete invariant
    }

    pub closed spec fn lookup_addr_slot(self, addr: &IAddress) -> Slot
        recommends self.entry_fetched(addr)
    {
        self.lookup_map@[addr@]
    }

    pub closed spec(checked) fn entry_token_id(self, idx: usize) -> Loc
        recommends self.wf(), idx < self.total_slots(),
    {
        self.perms@[idx as int].id()
    }

    pub open spec(checked) fn valid_handle(self, handle: MutHandle) -> bool
        recommends self.wf()
    {
        &&& handle.inv()
        &&& handle.idx < self.total_slots()
        &&& handle.token@.frac() == 1
        &&& handle.token@.id() == self.entry_token_id(handle.idx)
    }

    pub closed spec fn slot_entry(self, slot: Slot) -> IEntry
    {
        self.metadata[slot as int].entry
    }

    // we require a load handle for a load_release?
    pub open spec fn valid_load_handle(self, addr: &IAddress, handle: MutHandle) -> bool
    {
        &&& self.valid_handle(handle)
        &&& self.lookup_addr_slot(addr) == handle.idx
        &&& self.slot_entry(handle.idx) == IEntry::Loading{addr: *addr}
    }

    pub open spec(checked) fn entry_token_unchanged(&self, other: Self) -> bool
        recommends self.wf(), other.wf(), self.total_slots() == other.total_slots()
    {
        forall |i| 0 <= i < self.total_slots() ==> 
            #[trigger] self.entry_token_id(i) == other.entry_token_id(i)
    }

    pub open spec(checked) fn entry_fetched_same_except(&self, other: Self, addr: &IAddress) -> bool
    {
        forall |addr2: IAddress| addr2 != *addr ==> {
            &&& #[trigger] self.entry_fetched(&addr2) == other.entry_fetched(&addr2)
            &&& self.entry_fetched(&addr2) ==> self.lookup_addr_slot(&addr2) == other.lookup_addr_slot(&addr2)
        }
    }

    pub closed spec(checked) fn entries_same_except(&self, other: Self, idx: usize) -> bool
        recommends self.wf(), other.wf(), idx < self.total_slots()
    {
        &&& forall |i| 0 <= i < self.total_slots() && i != idx 
            ==> {
                &&& #[trigger] self.perms@[i] == other.perms@[i] 
                &&& self.internal_slots[i] == other.internal_slots[i]
                &&& self.metadata[i] == other.metadata[i]
            }
    }

    /// exec fns

    pub exec fn new() -> (out: Self)
        ensures
            out.wf(),
            out@ == Cache::State::empty(out.total_slots() as nat)
    {
        let mut i = 0;
        let tracked mut perms = Seq::<Perm>::tracked_empty();
        let mut internal_slots = Vec::<Option<IRawPage>>::with_capacity(CACHE_SIZE_RECS);
        let mut metadata = Vec::<Metadata>::with_capacity(CACHE_SIZE_RECS);

        while i < CACHE_SIZE_RECS
        invariant 
            i <= CACHE_SIZE_RECS,
            internal_slots.len() == i,
            perms.len() == internal_slots.len(),
            metadata.len() == internal_slots.len(),
            forall |j: int| 0 <= j < i ==> {
                &&& #[trigger] internal_slots[j] is Some
                &&& internal_slots[j].unwrap()@ == Self::empty_page()
            },
            forall |j: int| 0 <= j < i ==> 
                #[trigger] metadata[j] == Self::empty_metadata(),
            forall |j: int| 0 <= j < i ==> 
                #[trigger] perms[j].resource() == j && perms[j].frac() == 2,
        decreases CACHE_SIZE_RECS - i,
        {
            internal_slots.push(Some(Self::new_empty_page()));
            metadata.push(Metadata{
                entry: IEntry::Empty,
                status: Status::NotFilled,
            });
            proof {
                let tracked(perm) = Frac::new(i);
                perms.tracked_push(perm);
            }
            i = i + 1;
        }

        assert forall |j| 0 <= j < internal_slots.len()
        implies #[trigger] perms[j].frac() == 2
        by {
            assert(perms[j].resource() == j) // trigger
        }

        assume( obeys_key_model::<IAddress>() );

        FracCacheImpl{
            perms: Tracked(perms),
            internal_slots,
            metadata,
            lookup_map: HashMapWithView::new(),
        }
    }

    pub exec fn evictable(self, addr: &IAddress) -> (out: bool)
    requires
        self.wf(),
    ensures
        out ==> Cache::State::evictable(self@, self@, Cache::Label::EvictableCheck{addrs: set![addr@]}),
    {
        match self.lookup_map.get(addr) {
            None => { true },
            Some(slot) => {
                assert( self.lookup_map@.contains_value(*slot) );   // trigger lookup_map_inv
                let meta = &self.metadata[*slot];
                if let IEntry::Filled{addr} = meta.entry {
                    match meta.status { Status::Clean => { true }, _ => { false }, }
                } else {
                    false
                }
            },
        }
    }

    // views might not work if it has to do with handle access
    pub exec fn fetch(&mut self, addr: &IAddress) -> (err: FetchErrorCode)
        requires old(self).wf()
        ensures 
            self.wf(),
            match err {
                FetchErrorCode::Awaiting => old(self)@ =~= self@,
                FetchErrorCode::Success{slot_handle} => {
                    &&& self.entry_fetched(addr)
                    &&& self.valid_handle(slot_handle)
                    &&& self.entry_token_unchanged(*old(self))
                    &&& self.entry_fetched_same_except(*old(self), addr)
                    &&& self.entries_same_except(*old(self), slot_handle.idx)
                    &&& old(self)@.entries == self@.entries.insert(slot_handle.idx, 
                            Entry::Filled{addr: addr@, data: slot_handle.rec@} ) // slot type
                    &&& old(self)@.lookup_map == self@.lookup_map
                    &&& old(self)@.status_map == self@.status_map
                },
                FetchErrorCode::CacheFull => old(self) == self,
                FetchErrorCode::LoadInitiate{slot_handle} => {
                    &&& self.entry_fetched(addr)
                    &&& self.valid_load_handle(addr, slot_handle)
                    &&& self.entry_token_unchanged(*old(self))
                    &&& self.entry_fetched_same_except(*old(self), addr)
                    &&& self.entries_same_except(*old(self), slot_handle.idx)
                    &&& Cache::State::next(old(self)@, self@, cache_load_label(addr))
                }
            }
    {
        if self.lookup_map.contains_key(addr) {
            let slot = *self.lookup_map.get(addr).unwrap();
            self.internal_slots.push(None);
            assert(self.lookup_map@.contains_value(slot)); // trigger

            let mut taken = self.internal_slots.swap_remove(slot);
            let mut slot_handle = match taken {
                None => { 
                    return FetchErrorCode::Awaiting;
                },
                Some(rec) => {
                    let tracked perm = self.perms.borrow_mut().tracked_remove(slot as int);
                    let tracked handle_perm = perm.split(1);
                    proof {
                        self.perms.borrow_mut().tracked_insert(slot as int, perm);
                    }
                    MutHandle{
                        token: Tracked(handle_perm),
                        idx: slot,
                        rec,
                    }
                }
            };
            assert(!(old(self).metadata[slot as int].entry is Empty));
            assert(old(self).internal_slots[slot as int] is Some);

            proof {
                let target_addr = addr@;
                match old(self).metadata[slot as int].entry {
                    IEntry::Empty{} => { assert(false); },
                    IEntry::Filled{addr} => {
                        // address if it was filled it must have this same address
                        assume(target_addr == addr@);
                        assert(old(self)@.entries[slot] == Entry::Filled{addr: addr@, data: slot_handle.rec@}); 
                    },
                    _ => {
                        assert(old(self).internal_slots[slot as int] is None); 
                        assert(false);
                    },
                }
            }
            return FetchErrorCode::Success{slot_handle};
        }

        let mut slot = 0;
        while slot < CACHE_SIZE_RECS
        invariant 
            old(self).wf(),
            self == old(self),
            slot <= self.total_slots(),
        decreases 
            self.total_slots() - slot,
        {
            if let IEntry::Empty = self.metadata[slot].entry {
                self.lookup_map.insert(*addr, slot);
                self.metadata[slot] = Metadata{
                    status: self.metadata[slot].status.clone(), 
                    entry: IEntry::Loading{addr: *addr}};

                assume(old(self).metadata[slot as int].status == self.metadata[slot as int].status);

                self.internal_slots.push(None);
                let mut taken = self.internal_slots.swap_remove(slot);
                let slot_handle = 
                    match taken {
                        None => { assert(false); unreached() },
                        Some(rec) => {
                            let tracked perm = self.perms.borrow_mut().tracked_remove(slot as int);
                            let tracked handle_perm = perm.split(1);
                            proof {
                                self.perms.borrow_mut().tracked_insert(slot as int, perm);
                            }
                            MutHandle{
                                token: Tracked(handle_perm),
                                idx: slot,
                                rec,
                            }
                        }
                    };

                assert(self.lookup_map_inv()) by {
                    assert forall |i| #[trigger] self.lookup_map@.contains_value(i) 
                    implies i < self.total_slots() by {
                        if i != slot {
                            assert(old(self).lookup_map@.contains_value(i)); // trigger
                        }
                    }
                }

                assert(self.lookup_map_consistent_with_slots()) by {
                    assert forall |i: Slot| #![auto] i < self.total_slots()
                    implies self.lookup_map@.contains_value(i) <==> !(self.metadata[i as int].entry is Empty)
                    by {
                        if self.lookup_map@.contains_value(i) && i != slot {
                            assert(old(self).lookup_map@.contains_value(i)); // trigger
                        }

                        if !(self.metadata[i as int].entry is Empty) {
                            if i == slot {
                                assert(self.lookup_map@.contains_pair(addr@, slot));
                                assert(self.lookup_map@.contains_value(i));
                            } else {
                                assert(old(self).lookup_map@.contains_value(i)); // trigger
                                let other_addr = choose |other_addr| #[trigger] old(self).lookup_map@.contains_key(other_addr)
                                    && old(self).lookup_map@[other_addr] == i;
                                assert(self.lookup_map@.contains_pair(other_addr, i));
                            }
                        }
                    }
                }

                let ghost load_request = DiskRequest::ReadReq{from: addr@};
                let ghost cache_lbl = cache_load_label(addr);

                proof {
                    let new_slots_mapping = map!{slot => addr@};
                    assume(new_slots_mapping.invert() =~= map!{addr@ => slot}); // TODO: don't want to prove this

                    assert forall |slot_addr| true
                    implies new_slots_mapping.contains_value(slot_addr) <==> 
                        exists |req| #[trigger] addr_maps_to_req(cache_lbl->requests, req, slot_addr)
                    by {
                        if new_slots_mapping.contains_value(slot_addr) {
                            assert(slot_addr == addr@);
                            assert(addr_maps_to_req(cache_lbl->requests, load_request, addr@));
                        }
                        if exists |req| addr_maps_to_req(cache_lbl->requests, req, slot_addr) {
                            let req = choose |req| #[trigger] addr_maps_to_req(cache_lbl->requests, req, slot_addr);
                            assert(req == load_request);
                            assert(slot_addr == addr@);
                            assert(new_slots_mapping.contains_pair(slot, slot_addr));
                        }
                    }
                    assert(Cache::State::valid_load_requests(cache_lbl->requests, new_slots_mapping));

                    let new_entry = Entry::Loading{addr: addr@};
                    let updated_entries = Map::new(
                        |slot| new_slots_mapping.contains_key(slot),
                        |slot| Entry::Loading{addr: new_slots_mapping[slot]}
                    );
                    assert(updated_entries =~= map!{slot => new_entry});
                    assert(self@.entries =~= old(self)@.entries.union_prefer_right(updated_entries)); // ext_eq
                    assert(self@.lookup_map =~= old(self)@.lookup_map.union_prefer_right(new_slots_mapping.invert())); // ext_eq
                    assert(self@.status_map.dom() =~= old(self)@.status_map.dom());
                    assert(self@.status_map =~= old(self)@.status_map);
                    assert(Cache::State::load_initiate(old(self)@, self@, cache_lbl, new_slots_mapping));

                    reveal(Cache::State::next_by);
                    assert(Cache::State::next_by(old(self)@, self@, cache_lbl, Cache::Step::load_initiate(new_slots_mapping)));
                    reveal(Cache::State::next);
                }
                
                assert(self.valid_load_handle(addr, slot_handle));
                return FetchErrorCode::LoadInitiate{slot_handle};
            }
            slot = slot+1;
        }
        return FetchErrorCode::CacheFull;
    }

    pub exec fn load_release(&mut self, addr: &IAddress, handle: MutHandle)
        requires 
            old(self).wf(),
            old(self).valid_load_handle(addr, handle),
            old(self).entry_fetched(addr),
        ensures ({
            let resp = DiskResponse::ReadResp{data: handle.rec@};
            let cache_lbl = Cache::Label::DiskOps{requests: set!{}, responses: map!{addr@ => resp}};
            &&& self.wf()
            &&& self.entry_token_unchanged(*old(self))
            &&& self.entry_fetched_same_except(*old(self), addr)
            &&& Cache::State::next(old(self)@, self@, cache_lbl)
        })
    {
        let MutHandle{token, idx, rec} = handle;
        proof {
            let tracked(handle_perm) = token.get();
            let tracked mut perm = self.perms.borrow_mut().tracked_remove(idx as int);
            perm.agree(&handle_perm);
            perm.combine(handle_perm);
            perm.bounded();
            assert(self.internal_slots[idx as int] is None);
            assert(perm.frac() == 2);
            self.perms.borrow_mut().tracked_insert(idx as int, perm);
        }

        self.internal_slots[idx] = Some(rec);
        self.metadata[idx] = Metadata{
            status: Status::Clean, 
            entry: IEntry::Filled{addr: *addr}};

        proof {
            let resp = DiskResponse::ReadResp{data: handle.rec@};
            let cache_lbl = Cache::Label::DiskOps{requests: set!{}, responses: map!{addr@ => resp}};

            assert(old(self)@.valid_load_responses(cache_lbl->responses));
            assert(old(self)@.lookup_map.restrict(cache_lbl->responses.dom()) =~= map!{addr@ => idx});
            let slot_addr_map = old(self)@.lookup_map.restrict(cache_lbl->responses.dom()).invert();
            assume(slot_addr_map =~= map!{idx => addr@});

            let updated_entries = Map::new(
                |slot| slot_addr_map.contains_key(slot),
                |slot| Entry::Filled{
                    addr: slot_addr_map[slot],
                    data: cache_lbl->responses[slot_addr_map[slot]]->data
                }
            );
            assert(updated_entries =~= map!{idx => Entry::Filled{addr: addr@, data: rec@}});

            let updated_status_map = Map::new(
                |slot| slot_addr_map.contains_key(slot),
                |slot| Status::Clean
            );
            assert(updated_status_map =~= map!{idx => Status::Clean});
            assert(self@.entries =~= old(self)@.entries.union_prefer_right(updated_entries));
            assert(self@.status_map =~= old(self)@.status_map.union_prefer_right(updated_status_map));
            assert(Cache::State::load_complete(old(self)@, self@, cache_lbl));
            reveal(Cache::State::next_by);
            assert(Cache::State::next_by(old(self)@, self@, cache_lbl, Cache::Step::load_complete()));
            reveal(Cache::State::next);
        }
    }

    pub exec fn handle_release(&mut self, addr: &IAddress, handle: MutHandle)
        requires 
            old(self).wf(),
            old(self).valid_handle(handle),
            old(self).entry_fetched(addr),
        ensures ({
            &&& self.wf()
            &&& self.entry_token_unchanged(*old(self))
            &&& self.entry_fetched_same_except(*old(self), addr)
            &&& self@.entries == old(self)@.entries.insert(handle.idx,
                Entry::Filled{addr: addr@, data: handle.rec@})
            &&& self@.lookup_map == old(self)@.lookup_map
            &&& self@.status_map == old(self)@.status_map
        })
    {
        let MutHandle{token, idx, rec} = handle;
        proof {
            let tracked(handle_perm) = token.get();
            let tracked mut perm = self.perms.borrow_mut().tracked_remove(idx as int);
            perm.agree(&handle_perm);
            perm.combine(handle_perm);
            perm.bounded();
            assert(self.internal_slots[idx as int] is None);
            assert(perm.frac() == 2);
            self.perms.borrow_mut().tracked_insert(idx as int, perm);
        }
        self.internal_slots[idx] = Some(rec);
        assume(false);
    }
}

}//verus!
