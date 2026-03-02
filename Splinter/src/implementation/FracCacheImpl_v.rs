// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use vstd::hash_map::HashMapWithView;
use crate::spec::MapSpec_t::{ID};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::disk::GenericDisk_v::{IAddress};
use crate::spec::AsyncDisk_t::{RawPage, DiskRequest, DiskResponse, Address};
use crate::implementation::Cache_v::{Cache, Entry, Slot, Status, addr_maps_to_req};
use vstd::std_specs::hash::obeys_key_model;
use vstd::prelude::*;
use vstd::pcm::Loc;
use vstd::tokens::frac::*;
use vstd::pervasive::unreached;
use crate::trusted::ClientAPI_t::BLOCK_SIZE;

verus!{

pub const PAGE_SIZE_BYTES: usize = BLOCK_SIZE;
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

pub struct WritebackHandle {
    pub token: Tracked<Perm>,
    pub idx: Slot,
    pub rec: IRawPage,
}

impl WritebackHandle {
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
    writeback_loans: Ghost<Map<Slot, RawPage>>,
}

// release handle returns to specific slot

impl View for FracCacheImpl {
    type V = Cache::State;

    closed spec fn view(&self) -> Self::V
    {
        self.view_state()
    }
}

pub enum FetchErrorCode {
    Success{slot_handle: MutHandle},
    CacheFull, // all slots are filled, no available entries to evict without writeback
    NotPresent, // address not present and caller requested no load initiation
    // WritebackEviction, // slots are filled, have to writeback to evict, require additional calls
    LoadInitiate{slot_handle: MutHandle},   // cache is asking caller to initiate the disk IO on cache's behalf
    Awaiting,   // IO request has been sent, haven't heard back yet.
}

pub enum WriteAcquireResult {
    Acquired{slot_handle: MutHandle},
    CacheFull,
    Awaiting,
}

pub enum WritebackAcquireResult {
    NotPresent,
    NotDirty,
    Busy, // page is dirty but currently borrowed by another handle
    Acquired{handle: WritebackHandle},
}

pub open spec fn cache_load_label(addr: &IAddress) -> Cache::Label
{
    Cache::Label::DiskOps{requests: set!{DiskRequest::ReadReq{from: addr@}}, responses: map!{}}
}

pub open spec fn cache_write_label(addr: &IAddress, data: RawPage) -> Cache::Label
{
    Cache::Label::Access{reads: map!{}, writes: map!{addr@ => data}}
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

    closed spec fn writeback_loans_inv(self) -> bool
    {
        &&& forall |slot: Slot| #[trigger] self.writeback_loans@.contains_key(slot) ==> {
            &&& slot < self.total_slots()
            &&& self.writeback_loans@[slot].len() == PAGE_SIZE_BYTES
            &&& self.metadata[slot as int].entry is Filled
            &&& self.metadata[slot as int].status is Writeback
            &&& self.internal_slots[slot as int] is None
        }
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
        let entries = self.view_entries();
        forall |slot| #[trigger] entries.contains_key(slot) ==> match entries[slot] {
            Entry::Filled{addr, ..} => {
                self.lookup_map@.contains_key(addr) && self.lookup_map@[addr] == slot
            },
            _ => true,
        }
    }

    closed spec fn lookup_map_injective(self) -> bool
    {
        self.lookup_map@.is_injective()
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
    }

    closed spec fn empty_entry_not_writeback(self) -> bool
    {
        forall |slot| #![auto] 0 <= slot < self.total_slots()
        ==> self.metadata[slot].entry is Empty ==> !(self.metadata[slot].status is Writeback)
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
        &&& self.empty_entry_not_writeback()
        &&& self.lookup_map_consistent_with_slots()
        &&& self.lookup_map_bijection()
        &&& self.lookup_map_injective()
        &&& self.writeback_loans_inv()
    }

    closed spec fn view_state(self) -> Cache::State
    {
        Cache::State{
            entries: self.view_entries(),
            status_map: Map::new(|k: Slot| k < self.total_slots(), |k| self.metadata[k as int].status),
            lookup_map: self.lookup_map@,
        }
    }

    closed spec fn view_entries(self) -> Map<Slot, Entry>
    {
        Map::new(|k: Slot| k < self.total_slots(), |k| {
            match self.metadata[k as int].entry {
                IEntry::Empty => Entry::Empty,
                IEntry::Reserved{addr} => Entry::Reserved{addr: addr@},
                IEntry::Loading{addr} => Entry::Loading{addr: addr@},
                IEntry::Filled{addr} => Entry::Filled{
                    addr: addr@,
                    data: if self.internal_slots[k as int] is Some {
                        self.internal_slots[k as int].unwrap()@
                    } else if self.metadata[k as int].status is Writeback
                        && self.writeback_loans@.contains_key(k) {
                        self.writeback_loans@[k]
                    } else {
                        Self::empty_page()
                    }
                },
            }
        })
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
                data: if self.internal_slots[k as int] is Some {
                    self.internal_slots[k as int].unwrap()@
                } else if self.metadata[k as int].status is Writeback
                    && self.writeback_loans@.contains_key(k) {
                    self.writeback_loans@[k]
                } else {
                    Self::empty_page()
                }
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

    pub proof fn entry_fetched_from_view(cache: &FracCacheImpl, addr: &IAddress)
    ensures
        cache.entry_fetched(addr) == cache@.lookup_map.contains_key(addr@)
    {
        reveal(FracCacheImpl::entry_fetched);
        reveal(FracCacheImpl::view_state);
    }

    // Connects valid_load_handle (exec level) to the model view:
    // the model entry at the handle's slot is Loading (not Filled),
    // and the model lookup_map maps the address to the handle's slot.
    pub proof fn valid_load_handle_model_entry(cache: &FracCacheImpl, addr: &IAddress, handle: MutHandle)
    requires
        cache.wf(),
        cache.entry_fetched(addr),
        cache.valid_load_handle(addr, handle),
    ensures
        cache@.entries.contains_key(handle.idx),
        cache@.entries[handle.idx] is Loading,
        !(cache@.entries[handle.idx] is Filled),
        cache@.lookup_map.contains_key(addr@),
        cache@.lookup_map[addr@] == handle.idx,
    {
        reveal(FracCacheImpl::entry_fetched);
        reveal(FracCacheImpl::slot_entry);
        reveal(FracCacheImpl::lookup_addr_slot);
        reveal(FracCacheImpl::view_state);
        reveal(FracCacheImpl::view_entries);
        reveal(FracCacheImpl::wf);
    }

    pub proof fn valid_writeback_handle_model_entry(cache: &FracCacheImpl, addr: &IAddress, handle: WritebackHandle)
    requires
        cache.wf(),
        cache.valid_writeback_handle(addr, handle),
    ensures
        cache@.entries.contains_key(handle.idx),
        cache@.entries[handle.idx] == (Entry::Filled{addr: addr@, data: handle.rec@}),
        cache@.lookup_map.contains_key(addr@),
        cache@.lookup_map[addr@] == handle.idx,
        cache@.status_map[handle.idx] is Writeback,
    {
        reveal(FracCacheImpl::valid_writeback_handle);
        reveal(FracCacheImpl::entry_fetched);
        reveal(FracCacheImpl::lookup_addr_slot);
        reveal(FracCacheImpl::slot_entry);
        reveal(FracCacheImpl::view_state);
        reveal(FracCacheImpl::view_entries);
        reveal(FracCacheImpl::wf);
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
        &&& !(self@.status_map[handle.idx] is Writeback)
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

    pub open spec fn valid_write_handle(self, addr: &IAddress, handle: MutHandle) -> bool
    {
        &&& self.valid_handle(handle)
        &&& self.lookup_addr_slot(addr) == handle.idx
        &&& !(self.slot_entry(handle.idx) is Empty)
        &&& !(self.slot_entry(handle.idx) is Loading)
    }

    pub closed spec fn valid_writeback_handle(self, addr: &IAddress, handle: WritebackHandle) -> bool
    {
        &&& handle.inv()
        &&& self.entry_fetched(addr)
        &&& handle.idx < self.total_slots()
        &&& handle.token@.frac() == 1
        &&& handle.token@.id() == self.entry_token_id(handle.idx)
        &&& self.lookup_addr_slot(addr) == handle.idx
        &&& self.slot_entry(handle.idx) == IEntry::Filled{addr: *addr}
        &&& self@.status_map[handle.idx] is Writeback
        &&& self.internal_slots[handle.idx as int] is None
        &&& self.writeback_loans@.contains_key(handle.idx)
        &&& self.writeback_loans@[handle.idx] == handle.rec@
    }

    pub open spec fn valid_writeback_handles_preserved(self, old: Self) -> bool
        recommends self.wf(), old.wf()
    {
        forall |addr: IAddress, handle: WritebackHandle|
            #![trigger old.valid_writeback_handle(&addr, handle)]
            old.valid_writeback_handle(&addr, handle)
            ==> self.valid_writeback_handle(&addr, handle)
    }

    pub open spec fn valid_writeback_handles_preserved_except(self, old: Self, except: IAddress) -> bool
        recommends self.wf(), old.wf()
    {
        forall |addr: IAddress, handle: WritebackHandle|
            #![trigger old.valid_writeback_handle(&addr, handle)]
            addr != except
            && old.valid_writeback_handle(&addr, handle)
            ==> self.valid_writeback_handle(&addr, handle)
    }

    pub open spec fn valid_load_handles_preserved(self, old: Self) -> bool
        recommends self.wf(), old.wf()
    {
        forall |addr: IAddress, handle: MutHandle|
            #![trigger old.valid_load_handle(&addr, handle)]
            old.entry_fetched(&addr) && old.valid_load_handle(&addr, handle)
            ==> self.entry_fetched(&addr) && self.valid_load_handle(&addr, handle)
    }

    pub open spec fn valid_load_handles_preserved_except(self, old: Self, except: IAddress) -> bool
        recommends self.wf(), old.wf()
    {
        forall |addr: IAddress, handle: MutHandle|
            #![trigger old.valid_load_handle(&addr, handle)]
            addr != except
            && old.entry_fetched(&addr)
            && old.valid_load_handle(&addr, handle)
            ==> self.entry_fetched(&addr) && self.valid_load_handle(&addr, handle)
    }

    proof fn valid_load_handles_preserved_if_maps_same(old: Self, new: Self)
        requires
            new.lookup_map@ == old.lookup_map@,
            new.metadata == old.metadata,
            new.entry_token_unchanged(old),
        ensures
            new.valid_load_handles_preserved(old),
    {
        assert forall |addr: IAddress, handle: MutHandle|
            old.entry_fetched(&addr) && old.valid_load_handle(&addr, handle)
            implies new.entry_fetched(&addr) && new.valid_load_handle(&addr, handle)
        by {
            assert(new.entry_fetched(&addr)) by {
            }
            assert(new.valid_handle(handle)) by {
            }
            assert(new.lookup_addr_slot(&addr) == old.lookup_addr_slot(&addr)) by {
            }
        }
    }

    pub proof fn valid_load_handles_preserved_transitive(old: Self, mid: Self, new: Self)
    requires
        old.wf(), mid.wf(), new.wf(),
        mid.valid_load_handles_preserved(old),
        new.valid_load_handles_preserved(mid),
        ensures
            new.valid_load_handles_preserved(old),
    {
        assert forall |addr: IAddress, handle: MutHandle|
            old.entry_fetched(&addr) && old.valid_load_handle(&addr, handle)
            implies new.entry_fetched(&addr) && new.valid_load_handle(&addr, handle)
        by {
        }
    }

    pub proof fn valid_writeback_handles_preserved_transitive(old: Self, mid: Self, new: Self)
    requires
        old.wf(), mid.wf(), new.wf(),
        mid.valid_writeback_handles_preserved(old),
        new.valid_writeback_handles_preserved(mid),
    ensures
        new.valid_writeback_handles_preserved(old),
    {
        assert forall |addr: IAddress, handle: WritebackHandle|
            old.valid_writeback_handle(&addr, handle)
            implies new.valid_writeback_handle(&addr, handle)
        by {
        }
    }

    pub proof fn valid_writeback_handles_preserved_if_same(old: Self, new: Self)
    requires
        old == new,
    ensures
        new.valid_writeback_handles_preserved(old),
    {
        assert forall |addr: IAddress, handle: WritebackHandle|
            old.valid_writeback_handle(&addr, handle)
            implies new.valid_writeback_handle(&addr, handle)
        by {
        }
    }

    pub proof fn valid_writeback_handles_preserved_except_if_same(old: Self, new: Self, except: IAddress)
    requires
        old == new,
    ensures
        new.valid_writeback_handles_preserved_except(old, except),
    {
        assert forall |addr: IAddress, handle: WritebackHandle|
            addr != except
            && old.valid_writeback_handle(&addr, handle)
            implies new.valid_writeback_handle(&addr, handle)
        by {
        }
    }

    proof fn slot_entry_same_except(old: Self, new: Self, except_idx: usize, idx: usize)
        requires
            old.wf(),
            new.wf(),
            except_idx < new.total_slots(),
            new.entries_same_except(old, except_idx),
            idx < new.total_slots(),
            idx != except_idx,
        ensures
            new.slot_entry(idx) == old.slot_entry(idx),
    {
        let i = idx as int;
        assert({
            &&& new.perms@[i] == old.perms@[i]
            &&& new.internal_slots[i] == old.internal_slots[i]
            &&& new.metadata[i] == old.metadata[i]
        }) by {
        }
    }

    proof fn valid_load_handles_preserved_except_from_same(old: Self, new: Self, except: IAddress, except_idx: usize)
        requires
            old.wf(),
            new.wf(),
            new.entry_fetched_same_except(old, &except),
            except_idx < new.total_slots(),
            new.entries_same_except(old, except_idx),
            new.entry_token_unchanged(old),
            forall |addr2: IAddress, handle2: MutHandle|
                addr2 != except
                && old.entry_fetched(&addr2)
                && old.valid_load_handle(&addr2, handle2)
                ==> handle2.idx != except_idx,
        ensures
            new.valid_load_handles_preserved_except(old, except),
    {
        assert forall |addr2: IAddress, handle2: MutHandle|
            addr2 != except
            && old.entry_fetched(&addr2)
            && old.valid_load_handle(&addr2, handle2)
            implies new.entry_fetched(&addr2) && new.valid_load_handle(&addr2, handle2)
        by {
            assert(new.entry_fetched(&addr2)) by {
            }
            assert(new.lookup_addr_slot(&addr2) == old.lookup_addr_slot(&addr2)) by {
            }
            assert(!(new@.status_map[handle2.idx] is Writeback)) by {
                let i = handle2.idx as int;
                assert(new.perms@[i] == old.perms@[i]) by {
                }
                reveal(FracCacheImpl::view_state);
            }
            assert(new.valid_handle(handle2)) by {
            }
            Self::slot_entry_same_except(old, new, except_idx, handle2.idx);
        }
    }

    proof fn valid_load_handles_preserved_from_except_if_missing(old: Self, new: Self, except: IAddress)
        requires
            old.wf(),
            new.wf(),
            new.valid_load_handles_preserved_except(old, except),
            !old.entry_fetched(&except),
        ensures
            new.valid_load_handles_preserved(old),
    {
        assert forall |addr2: IAddress, handle2: MutHandle|
            old.entry_fetched(&addr2) && old.valid_load_handle(&addr2, handle2)
            implies new.entry_fetched(&addr2) && new.valid_load_handle(&addr2, handle2)
        by {
            if addr2 == except {
            }
            assert(new.entry_fetched(&addr2) && new.valid_load_handle(&addr2, handle2)) by {
            }
        }
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

    pub open spec fn release_common_post(self, old: Self, addr: &IAddress) -> bool
        recommends self.wf(), old.wf()
    {
        &&& self.wf()
        &&& self.entry_token_unchanged(old)
        &&& self.entry_fetched_same_except(old, addr)
    }

    pub open spec fn filled_entry_restored_from_handle(
        self,
        old: Self,
        addr: &IAddress,
        idx: Slot,
        data: RawPage,
    ) -> bool
    {
        &&& self@.entries == old@.entries.insert(idx, Entry::Filled{addr: addr@, data})
        &&& self@.lookup_map == old@.lookup_map
        &&& self@.status_map == old@.status_map
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
            assert(perms[j].resource() == j)
        }

        assume( obeys_key_model::<IAddress>() );

        FracCacheImpl{
            perms: Tracked(perms),
            internal_slots,
            metadata,
            lookup_map: HashMapWithView::new(),
            writeback_loans: Ghost(Map::empty()),
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
                assert( self.lookup_map@.contains_value(*slot) );
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
    pub exec fn fetch(&mut self, addr: &IAddress, load: bool) -> (err: FetchErrorCode)
        requires old(self).wf()
        ensures 
            self.wf(),
            self.valid_load_handles_preserved(*old(self)),
            !load ==> !(err is LoadInitiate),
            match err {
                FetchErrorCode::Awaiting => old(self)@ =~= self@,
                FetchErrorCode::Success{slot_handle} => {
                    &&& self.entry_fetched(addr)
                    &&& self.valid_handle(slot_handle)
                    &&& self.entry_token_unchanged(*old(self))
                    &&& self.entry_fetched_same_except(*old(self), addr)
                    &&& self.entries_same_except(*old(self), slot_handle.idx)
                    &&& old(self).slot_entry(slot_handle.idx) == (IEntry::Filled{addr: *addr})
                    &&& self.slot_entry(slot_handle.idx) == (IEntry::Filled{addr: *addr})
                    &&& old(self)@.valid_read(addr@, slot_handle.rec@)
                    &&& old(self)@.entries == self@.entries.insert(slot_handle.idx, 
                            Entry::Filled{addr: addr@, data: slot_handle.rec@} ) // slot type
                    &&& old(self)@.lookup_map == self@.lookup_map
                    &&& old(self)@.status_map == self@.status_map
                },
                FetchErrorCode::CacheFull => *old(self) == *self,
                FetchErrorCode::NotPresent => *old(self) == *self,
                FetchErrorCode::LoadInitiate{slot_handle} => {
                    &&& self.entry_fetched(addr)
                    &&& !old(self).entry_fetched(addr)
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
            assert(self.lookup_map@.contains_value(slot));
            match self.metadata[slot].status {
                Status::Writeback => {
                    proof {
                        Self::valid_load_handles_preserved_if_maps_same(*old(self), *self);
                    }
                    return FetchErrorCode::Awaiting;
                },
                _ => {},
            }
            self.internal_slots.push(None);

            let taken = self.internal_slots.swap_remove(slot);
            let slot_handle = match taken {
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
            proof {
                match old(self).metadata[slot as int].entry {
                    IEntry::Empty{} => { },
                    IEntry::Filled{..} => {
                        // address if it was filled it must have this same address
                        reveal(FracCacheImpl::view_entries);
                        assert(old(self).view_entries().contains_key(slot)) by {
                            assert(slot < old(self).total_slots());
                        }
                    },
                    _ => {
                    },
                }
            }
            return FetchErrorCode::Success{slot_handle};
        }

        // TODO(codex): there's no way to get out of fetch(false) with a page
        // absent from the cache (the bypass write). We want to support this path!
        // It will need to refine Cache_v::reserve.

        // TODO(codex): discuss: Maybe we actually want two modes:
        // - bypass write: give me write on the page but don't load
        // - try-fetch: give me the page if it's in cache, if not, don't
        //   even bother reserving a cache slot.
        // How do we expose these variants? Yet another parameter mode? Or
        // should we split this into multiple entry points? What would that
        // look like?

        if !load {
            proof {
                Self::valid_load_handles_preserved_if_maps_same(*old(self), *self);
            }
            return FetchErrorCode::NotPresent;
        }

        let mut slot = 0;
        while slot < CACHE_SIZE_RECS
        invariant 
            old(self).wf(),
            *self == *old(self),
            slot <= self.total_slots(),
        decreases 
            self.total_slots() - slot,
        {
            if let IEntry::Empty = self.metadata[slot].entry {
                let status = self.metadata[slot].status;
                match status {
                    Status::Writeback => {
                        slot = slot + 1;
                        continue;
                    },
                    _ => {},
                }
                self.lookup_map.insert(*addr, slot);
                self.metadata[slot] = Metadata{
                    status, 
                    entry: IEntry::Loading{addr: *addr}};

                self.internal_slots.push(None);
                let taken = self.internal_slots.swap_remove(slot);
                let slot_handle = 
                    match taken {
                        None => { unreached() },
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
                            assert(old(self).lookup_map@.contains_value(i));
                        }
                    }
                }

                assert(self.lookup_map_consistent_with_slots()) by {
                    assert forall |i: Slot| #![auto] i < self.total_slots()
                    implies self.lookup_map@.contains_value(i) <==> !(self.metadata[i as int].entry is Empty)
                    by {
                        if self.lookup_map@.contains_value(i) && i != slot {
                            assert(old(self).lookup_map@.contains_value(i));
                        }

                        if !(self.metadata[i as int].entry is Empty) {
                            if i == slot {
                                assert(self.lookup_map@.contains_pair(addr@, slot));
                            } else {
                                assert(old(self).lookup_map@.contains_value(i));
                                let other_addr = choose |other_addr| #[trigger] old(self).lookup_map@.contains_key(other_addr)
                                    && old(self).lookup_map@[other_addr] == i;
                                assert(self.lookup_map@.contains_pair(other_addr, i));
                            }
                        }
                    }
                }
                assert(self.lookup_map_injective()) by {
                    assert forall |addr1: Address, addr2: Address| #![auto]
                        self.lookup_map@.contains_key(addr1)
                        && self.lookup_map@.contains_key(addr2)
                        && self.lookup_map@[addr1] == self.lookup_map@[addr2]
                        implies addr1 == addr2
                    by {
                        if addr1 == addr@ {
                            if addr2 == addr@ {
                            } else {
                                assert(old(self).lookup_map@.contains_value(slot));
                            }
                        } else if addr2 == addr@ {
                            assert(old(self).lookup_map@.contains_value(slot));
                        } else {
                        }
                    }
                }

                let ghost load_request = DiskRequest::ReadReq{from: addr@};
                let ghost cache_lbl = cache_load_label(addr);

                proof {
                    let new_slots_mapping = map!{slot => addr@};
                    assert(new_slots_mapping.invert() =~= map!{addr@ => slot}) by {
                        // show both maps contain exactly the pair (addr@, slot)
                        assert(new_slots_mapping.contains_pair(slot, addr@));
                    }

                    assert forall |slot_addr| true
                    implies new_slots_mapping.contains_value(slot_addr) <==> 
                        exists |req| #[trigger] addr_maps_to_req(cache_lbl->requests, req, slot_addr)
                    by {
                        if new_slots_mapping.contains_value(slot_addr) {
                            assert(slot_addr == addr@);
                            assert(addr_maps_to_req(cache_lbl->requests, load_request, slot_addr));
                        }
                        if exists |req| addr_maps_to_req(cache_lbl->requests, req, slot_addr) {
                            let req = choose |req| addr_maps_to_req(cache_lbl->requests, req, slot_addr);
                            assert(cache_lbl->requests.contains(req));
                            assert(req == load_request);
                            assert(slot_addr == addr@);
                            assert(new_slots_mapping.contains_pair(slot, addr@));
                            assert(new_slots_mapping.contains_value(slot_addr));
                        }
                    }
                    let updated_entries = Map::new(
                        |slot| new_slots_mapping.contains_key(slot),
                        |slot| Entry::Loading{addr: new_slots_mapping[slot]}
                    );
                    assert(self@.entries =~= old(self)@.entries.union_prefer_right(updated_entries));
                    assert(self@.lookup_map =~= old(self)@.lookup_map.union_prefer_right(new_slots_mapping.invert()));
                    assert(self@.status_map =~= old(self)@.status_map);
                    reveal(Cache::State::next_by);
                    assert(Cache::State::next_by(old(self)@, self@, cache_lbl, Cache::Step::load_initiate(new_slots_mapping)));
                    reveal(Cache::State::next);
                }
                
                proof {
                    Self::valid_load_handles_preserved_except_from_same(*old(self), *self, *addr, slot_handle.idx);
                    Self::valid_load_handles_preserved_from_except_if_missing(*old(self), *self, *addr);
                }
                return FetchErrorCode::LoadInitiate{slot_handle};
            }
            slot = slot+1;
        }
        proof {
            Self::valid_load_handles_preserved_if_maps_same(*old(self), *self);
        }
        return FetchErrorCode::CacheFull;
    }

    pub exec fn acquire_for_write(&mut self, addr: &IAddress) -> (result: WriteAcquireResult)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self.wf() ==> self.valid_load_handles_preserved(*old(self)),
            match result {
                WriteAcquireResult::Awaiting => old(self)@ =~= self@,
                WriteAcquireResult::CacheFull => *old(self) == *self,
                WriteAcquireResult::Acquired{slot_handle} => {
                    &&& self.entry_fetched(addr)
                    &&& self.valid_write_handle(addr, slot_handle)
                    &&& self@.valid_write(addr@)
                    &&& !old(self).entry_fetched(addr) ==> (exists |lbl: Cache::Label| Cache::State::next(old(self)@, self@, lbl))
                },
            },
    {
        if self.lookup_map.contains_key(addr) {
            let slot = *self.lookup_map.get(addr).unwrap();
            assert(self.lookup_map@.contains_value(slot));
            match self.metadata[slot].status {
                Status::Writeback => {
                    proof {
                        Self::valid_load_handles_preserved_if_maps_same(*old(self), *self);
                    }
                    return WriteAcquireResult::Awaiting;
                },
                _ => {},
            }
            let entry = self.metadata[slot].entry;
            match entry {
                IEntry::Loading{..} => {
                    proof {
                        Self::valid_load_handles_preserved_if_maps_same(*old(self), *self);
                    }
                    return WriteAcquireResult::Awaiting;
                },
                IEntry::Filled{..} => {
                },
                _ => {
                    proof {
                        Self::valid_load_handles_preserved_if_maps_same(*old(self), *self);
                    }
                    return WriteAcquireResult::Awaiting;
                },
            }

            self.internal_slots.push(None);
            let taken = self.internal_slots.swap_remove(slot);
            let slot_handle = match taken {
                None => {
                    proof {
                        Self::valid_load_handles_preserved_if_maps_same(*old(self), *self);
                    }
                    return WriteAcquireResult::Awaiting;
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

            proof {
                Self::valid_load_handles_preserved_if_maps_same(*old(self), *self);
                assert(self.entry_fetched(addr));
                assert(self.valid_write_handle(addr, slot_handle));
                reveal(FracCacheImpl::view_state);
                reveal(FracCacheImpl::view_entries);
                assert(self@.lookup_map.contains_key(addr@));
                assert(self@.lookup_map[addr@] == slot);
                match entry {
                    IEntry::Filled{addr: entry_addr} => {
                        assert(self@.entries[slot] is Filled);
                        assert(match self@.entries[slot] {
                            Entry::Filled{addr: a, ..} => a == entry_addr@,
                            _ => false,
                        });
                        assert(self.lookup_map_bijection());
                        assert(self.lookup_map_injective());
                        assert(self@.entries.contains_key(slot));
                        assert(self@.lookup_map.contains_key(entry_addr@) && self@.lookup_map[entry_addr@] == slot);
                        assert(entry_addr@ == addr@);
                        assert(!(self.metadata[slot as int].status is Writeback));
                        assert(!(self@.status_map[slot] is Writeback));
                    },
                    _ => {
                        assert(false);
                    }
                }
                assert(self@.valid_write(addr@));
            }
            return WriteAcquireResult::Acquired{slot_handle};
        }

        let mut slot = 0;
        while slot < CACHE_SIZE_RECS
            invariant
                old(self).wf(),
                *self == *old(self),
                slot <= self.total_slots(),
            decreases
                self.total_slots() - slot,
        {
            if let IEntry::Empty = self.metadata[slot].entry {
                let status = self.metadata[slot].status;
                match status {
                    Status::Writeback => {
                        slot = slot + 1;
                        continue;
                    },
                    _ => {},
                }
                self.lookup_map.insert(*addr, slot);
                self.metadata[slot] = Metadata{
                    status,
                    entry: IEntry::Reserved{addr: *addr},
                };

                self.internal_slots.push(None);
                let taken = self.internal_slots.swap_remove(slot);
                let slot_handle =
                    match taken {
                        None => { unreached() },
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
                            assert(old(self).lookup_map@.contains_value(i));
                        }
                    }
                }

                assert(self.lookup_map_consistent_with_slots()) by {
                    assert forall |i: Slot| #![auto] i < self.total_slots()
                    implies self.lookup_map@.contains_value(i) <==> !(self.metadata[i as int].entry is Empty)
                    by {
                        if self.lookup_map@.contains_value(i) && i != slot {
                            assert(old(self).lookup_map@.contains_value(i));
                        }

                        if !(self.metadata[i as int].entry is Empty) {
                            if i == slot {
                                assert(self.lookup_map@.contains_pair(addr@, slot));
                            } else {
                                assert(old(self).lookup_map@.contains_value(i));
                                let other_addr = choose |other_addr| #[trigger] old(self).lookup_map@.contains_key(other_addr)
                                    && old(self).lookup_map@[other_addr] == i;
                                assert(self.lookup_map@.contains_pair(other_addr, i));
                            }
                        }
                    }
                }
                assert(self.lookup_map_injective()) by {
                    assert forall |addr1: Address, addr2: Address| #![auto]
                        self.lookup_map@.contains_key(addr1)
                        && self.lookup_map@.contains_key(addr2)
                        && self.lookup_map@[addr1] == self.lookup_map@[addr2]
                        implies addr1 == addr2
                    by {
                        if addr1 == addr@ {
                            if addr2 == addr@ {
                            } else {
                                assert(old(self).lookup_map@.contains_value(slot));
                            }
                        } else if addr2 == addr@ {
                            assert(old(self).lookup_map@.contains_value(slot));
                        } else {
                        }
                    }
                }

                proof {
                    let new_slots_mapping = map!{slot => addr@};
                    let lbl = Cache::Label::Internal;
                    assert(new_slots_mapping.invert() =~= map!{addr@ => slot}) by {
                        assert(new_slots_mapping.contains_pair(slot, addr@));
                    }
                    let updated_entries = Map::new(
                        |s| new_slots_mapping.contains_key(s),
                        |s| Entry::Reserved{addr: new_slots_mapping[s]}
                    );
                    assert(self@.entries =~= old(self)@.entries.union_prefer_right(updated_entries));
                    assert(self@.lookup_map =~= old(self)@.lookup_map.union_prefer_right(new_slots_mapping.invert()));
                    assert(self@.status_map =~= old(self)@.status_map);
                    reveal(Cache::State::next_by);
                    assert(Cache::State::next_by(old(self)@, self@, lbl, Cache::Step::reserve(new_slots_mapping)));
                    reveal(Cache::State::next);
                    assert(exists |lbl2: Cache::Label| #[trigger] Cache::State::next(old(self)@, self@, lbl2)) by {
                        assert(Cache::State::next(old(self)@, self@, lbl));
                    }
                    assert(self.entry_fetched(addr));
                    assert(self.valid_write_handle(addr, slot_handle));
                    assert(self@.valid_write(addr@));

                    Self::valid_load_handles_preserved_except_from_same(*old(self), *self, *addr, slot_handle.idx);
                    Self::valid_load_handles_preserved_from_except_if_missing(*old(self), *self, *addr);
                }
                return WriteAcquireResult::Acquired{slot_handle};
            }
            slot = slot + 1;
        }

        proof {
            Self::valid_load_handles_preserved_if_maps_same(*old(self), *self);
        }
        WriteAcquireResult::CacheFull
    }

    pub exec fn load_release(&mut self, addr: &IAddress, handle: MutHandle)
        requires 
            old(self).wf(),
            old(self).valid_load_handle(addr, handle),
            old(self).entry_fetched(addr),
        ensures ({
            let resp = DiskResponse::ReadResp{data: handle.rec@};
            let cache_lbl = Cache::Label::DiskOps{requests: set!{}, responses: map!{addr@ => resp}};
            &&& self.release_common_post(*old(self), addr)
            &&& self.valid_load_handles_preserved_except(*old(self), *addr)
            &&& self.valid_writeback_handles_preserved(*old(self))
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
            self.perms.borrow_mut().tracked_insert(idx as int, perm);
        }

        self.internal_slots[idx] = Some(rec);
        self.metadata[idx] = Metadata{
            status: Status::Clean, 
            entry: IEntry::Filled{addr: *addr}};

        proof {
            let resp = DiskResponse::ReadResp{data: handle.rec@};
            let cache_lbl = Cache::Label::DiskOps{requests: set!{}, responses: map!{addr@ => resp}};

            let slot_addr_map = old(self)@.lookup_map.restrict(cache_lbl->responses.dom()).invert();
            assert(slot_addr_map =~= map!{idx => addr@}) by {
                // the restrict map has exactly the pair (addr@ -> idx), so its invert is (idx -> addr@)
                assert(old(self)@.lookup_map.restrict(cache_lbl->responses.dom()).contains_pair(addr@, idx));

                reveal(Map::invert);
                // show slot_addr_map maps idx to addr@
                // show there are no other keys
            }

            let updated_entries = Map::new(
                |slot| slot_addr_map.contains_key(slot),
                |slot| Entry::Filled{
                    addr: slot_addr_map[slot],
                    data: cache_lbl->responses[slot_addr_map[slot]]->data
                }
            );

            let updated_status_map = Map::new(
                |slot| slot_addr_map.contains_key(slot),
                |slot| Status::Clean
            );
            assert(self@.entries =~= old(self)@.entries.union_prefer_right(updated_entries));
            assert(self@.status_map =~= old(self)@.status_map.union_prefer_right(updated_status_map));
            reveal(Cache::State::next_by);
            assert(Cache::State::next_by(old(self)@, self@, cache_lbl, Cache::Step::load_complete()));
            reveal(Cache::State::next);
            assert(self.valid_writeback_handles_preserved(*old(self))) by {
                assert forall |addr2: IAddress, handle2: WritebackHandle|
                    old(self).valid_writeback_handle(&addr2, handle2)
                    implies self.valid_writeback_handle(&addr2, handle2)
                by {
                    reveal(FracCacheImpl::valid_writeback_handle);
                    reveal(FracCacheImpl::valid_load_handle);
                    assert(old(self).lookup_addr_slot(addr) == idx);
                    assert(old(self).slot_entry(idx) == IEntry::Loading{addr: *addr});
                    assert(old(self).lookup_addr_slot(&addr2) == handle2.idx);
                    if handle2.idx == idx {
                        assert(old(self).slot_entry(handle2.idx) == IEntry::Filled{addr: addr2});
                        assert(old(self).slot_entry(idx) == IEntry::Filled{addr: addr2});
                        assert(false);
                    }
                    let i = handle2.idx as int;
                    assert(self.metadata[i] == old(self).metadata[i]);
                    assert(self.internal_slots[i] == old(self).internal_slots[i]);
                    assert(self.perms@[i] == old(self).perms@[i]);
                    assert(self.lookup_map@ == old(self)@.lookup_map);
                    assert(self.writeback_loans@ == old(self).writeback_loans@);
                }
            }
        }
    }

    // Commits a write through the cache state machine:
    // releasing this handle emits an Access{writes} transition and marks the slot Dirty.
    // Use this when caller intent is "I modified page contents and want that modeled as a write."
    pub exec fn write_release(&mut self, addr: &IAddress, handle: MutHandle)
        requires
            old(self).wf(),
            old(self).entry_fetched(addr),
            old(self).valid_write_handle(addr, handle),
            old(self)@.valid_write(addr@),
        ensures ({
            let cache_lbl = cache_write_label(addr, handle.rec@);
            &&& self.release_common_post(*old(self), addr)
            &&& self.valid_load_handles_preserved(*old(self))
            &&& Cache::State::next(old(self)@, self@, cache_lbl)
        })
    {
        let ghost recv = handle.rec@;
        let MutHandle{token, idx, rec} = handle;
        proof {
            let tracked(handle_perm) = token.get();
            let tracked mut perm = self.perms.borrow_mut().tracked_remove(idx as int);
            perm.agree(&handle_perm);
            perm.combine(handle_perm);
            perm.bounded();
            self.perms.borrow_mut().tracked_insert(idx as int, perm);
        }
        match self.metadata[idx].status {
            Status::Writeback => {
                unreached::<()>();
            },
            _ => {},
        }

        self.internal_slots[idx] = Some(rec);
        self.metadata[idx] = Metadata{
            status: Status::Dirty,
            entry: IEntry::Filled{addr: *addr},
        };

        proof {
            let cache_lbl = cache_write_label(addr, recv);
            let updated_entries = old(self)@.write_updated_entries(cache_lbl->writes);
            let updated_status_map = old(self)@.write_updated_status(cache_lbl->writes);
            let slot_addr_map = old(self)@.lookup_map.restrict(cache_lbl->writes.dom()).invert();
            assert(slot_addr_map =~= map!{idx => addr@}) by {
                assert(old(self)@.lookup_map.restrict(cache_lbl->writes.dom()).contains_pair(addr@, idx));
                reveal(Map::invert);
            }
            let updated_entries2 = Map::new(
                |slot| slot_addr_map.contains_key(slot),
                |slot| Entry::Filled{
                    addr: slot_addr_map[slot],
                    data: cache_lbl->writes[slot_addr_map[slot]],
                }
            );
            let updated_status_map2 = Map::new(
                |slot| slot_addr_map.contains_key(slot),
                |slot| Status::Dirty
            );
            assert(updated_entries =~= updated_entries2);
            assert(updated_status_map =~= updated_status_map2);
            assert(self@.entries =~= old(self)@.entries.union_prefer_right(updated_entries));
            assert(self@.status_map =~= old(self)@.status_map.union_prefer_right(updated_status_map));
            assert(self@.lookup_map =~= old(self)@.lookup_map);
            reveal(Cache::State::next_by);
            assert(Cache::State::next_by(old(self)@, self@, cache_lbl, Cache::Step::access()));
            reveal(Cache::State::next);
        }
    }

    // Returns a borrowed filled-page handle without modeling a cache write transition.
    // This is the borrow/restore path used by read-style flows that may mutate bytes in exec code
    // but are not intended to count as an abstract cache Access{writes} step.
    pub exec fn handle_release(&mut self, addr: &IAddress, handle: MutHandle)
        requires 
            old(self).wf(),
            old(self).valid_handle(handle),
            old(self).entry_fetched(addr),
            old(self).slot_entry(handle.idx) == (IEntry::Filled{addr: *addr}),
        ensures ({
            &&& self.release_common_post(*old(self), addr)
            &&& self.valid_load_handles_preserved(*old(self))
            &&& self.filled_entry_restored_from_handle(*old(self), addr, handle.idx, handle.rec@)
        })
    {
        let MutHandle{token, idx, rec} = handle;
        proof {
            let tracked(handle_perm) = token.get();
            let tracked mut perm = self.perms.borrow_mut().tracked_remove(idx as int);
            perm.agree(&handle_perm);
            perm.combine(handle_perm);
            perm.bounded();
            self.perms.borrow_mut().tracked_insert(idx as int, perm);
            // relate perms view to the old one (remove + insert at same index)
        }
        match self.metadata[idx].status {
            Status::Writeback => {
                unreached::<()>();
            },
            _ => {},
        }
        self.internal_slots[idx] = Some(rec);
        proof {
            // vector update view for internal_slots
            // show view entries updated only at idx
            reveal(FracCacheImpl::view_entries);
            assert(self@.entries == old(self)@.entries.insert(idx, Entry::Filled{addr: addr@, data: rec@}));
            // wf follows since we only changed internal_slots at idx and restored the perm fraction
        }
    }

    pub exec fn begin_writeback(&mut self, addr: &IAddress) -> (result: WritebackAcquireResult)
        requires
            old(self).wf(),
        ensures ({
            &&& self.wf()
            &&& self.valid_load_handles_preserved(*old(self))
            &&& self.valid_writeback_handles_preserved(*old(self))
            &&& match result {
                WritebackAcquireResult::Acquired{handle} => {
                    &&& self.entry_fetched(addr)
                    &&& self.valid_writeback_handle(addr, handle)
                    &&& Cache::State::next(
                        old(self)@,
                        self@,
                        Cache::Label::DiskOps{
                            requests: set![DiskRequest::WriteReq{to: addr@, data: handle.rec@}],
                            responses: map!{},
                        },
                    )
                    &&& old(self).entry_fetched(addr)
                    &&& old(self)@.lookup_map == self@.lookup_map
                    &&& old(self)@.entries == self@.entries
                    &&& old(self)@.status_map[handle.idx] is Dirty
                    &&& self@.status_map == old(self)@.status_map.insert(handle.idx, Status::Writeback)
                },
                WritebackAcquireResult::NotPresent => {
                    &&& *old(self) == *self
                    &&& Cache::State::next(self@, self@, Cache::Label::EvictableCheck{addrs: set![addr@]})
                },
                WritebackAcquireResult::NotDirty => {
                    &&& *old(self) == *self
                    &&& Cache::State::next(self@, self@, Cache::Label::EvictableCheck{addrs: set![addr@]})
                },
                WritebackAcquireResult::Busy => {
                    &&& *old(self) == *self
                }
            }
        }),
    {
        if !self.lookup_map.contains_key(addr) {
            proof {
                reveal(Cache::State::next_by);
                reveal(Cache::State::next);
                let lbl = Cache::Label::EvictableCheck{addrs: set![addr@]};
                assert(!self.lookup_map@.contains_key(addr@));
                assert(Cache::State::next_by(self@, self@, lbl, Cache::Step::evictable()));
                Self::valid_writeback_handles_preserved_if_same(*old(self), *self);
            }
            return WritebackAcquireResult::NotPresent;
        }

        let slot = *self.lookup_map.get(addr).unwrap();
        assert(self.lookup_map@.contains_value(slot));
        assert(slot < self.total_slots());
        assert(slot < self.metadata.len());
        let status = self.metadata[slot].status;

        match status {
            Status::Dirty => {},
            Status::Clean => {
                match self.metadata[slot].entry {
                    IEntry::Filled{addr: entry_addr} => {
                        proof {
                            reveal(FracCacheImpl::view_entries);
                            let entries = self.view_entries();
                            assert(entries.contains_key(slot)) by {
                                assert(slot < self.total_slots());
                            }
                            assert(entries[slot] is Filled);
                            assert(entries[slot].get_addr() == entry_addr@);
                            assert(self.lookup_map_bijection());
                            assert(self.lookup_map@.contains_key(entry_addr@) && self.lookup_map@[entry_addr@] == slot);
                            assert(self.lookup_map@.contains_key(addr@));
                            assert(self.lookup_map@[addr@] == slot);
                            assert(self.lookup_map_injective());
                            assert(addr@ == entry_addr@);
                            assert(entry_addr == *addr);

                            reveal(Cache::State::next_by);
                            reveal(Cache::State::next);
                            let lbl = Cache::Label::EvictableCheck{addrs: set![addr@]};
                            assert(Cache::State::next_by(self@, self@, lbl, Cache::Step::evictable()));
                            Self::valid_writeback_handles_preserved_if_same(*old(self), *self);
                        }
                        return WritebackAcquireResult::NotDirty;
                    },
                    _ => {
                        proof {
                            Self::valid_writeback_handles_preserved_if_same(*old(self), *self);
                        }
                        return WritebackAcquireResult::Busy;
                    }
                }
            },
            Status::Writeback | Status::NotFilled => {
                proof {
                    Self::valid_writeback_handles_preserved_if_same(*old(self), *self);
                }
                return WritebackAcquireResult::Busy;
            }
        }
        match self.metadata[slot].entry {
            IEntry::Filled{addr: entry_addr} => {
                proof {
                    reveal(FracCacheImpl::view_entries);
                    let entries = self.view_entries();
                    assert(entries.contains_key(slot)) by {
                        assert(slot < self.total_slots());
                    }
                    assert(entries[slot] is Filled);
                    assert(entries[slot].get_addr() == entry_addr@);
                    assert(self.lookup_map_bijection());
                    assert(self.lookup_map@.contains_key(entry_addr@) && self.lookup_map@[entry_addr@] == slot);
                    assert(self.lookup_map@.contains_key(addr@));
                    assert(self.lookup_map@[addr@] == slot);
                    assert(self.lookup_map_injective());
                    assert(addr@ == entry_addr@);
                    assert(entry_addr == *addr);
                }
            },
            _ => {
                proof {
                    Self::valid_writeback_handles_preserved_if_same(*old(self), *self);
                }
                return WritebackAcquireResult::Busy;
            }
        }

        match &self.internal_slots[slot] {
            None => {
                proof {
                    Self::valid_writeback_handles_preserved_if_same(*old(self), *self);
                }
                return WritebackAcquireResult::Busy;
            },
            Some(_) => {},
        }

        self.internal_slots.push(None);
        assert(self.lookup_map@.contains_value(slot));
        let taken = self.internal_slots.swap_remove(slot);
        let rec = match taken {
            None => {
                unreached::<IRawPage>()
            },
            Some(rec) => {
                rec
            }
        };
        if rec.len() != PAGE_SIZE_BYTES {
            return unreached::<WritebackAcquireResult>();
        }

        let tracked perm = self.perms.borrow_mut().tracked_remove(slot as int);
        let tracked handle_perm = perm.split(1);
        proof {
            self.perms.borrow_mut().tracked_insert(slot as int, perm);
        }
        let ghost loans = self.writeback_loans@;
        self.writeback_loans = Ghost(loans.insert(slot, rec@));
        let handle = WritebackHandle{token: Tracked(handle_perm), idx: slot, rec};

        self.metadata[slot] = Metadata{
            entry: IEntry::Filled{addr: *addr},
            status: Status::Writeback
        };
        proof {
            reveal(Cache::State::next_by);
            reveal(Cache::State::next);
            let req = DiskRequest::WriteReq{to: addr@, data: rec@};
            let lbl = Cache::Label::DiskOps{requests: set![req], responses: map!{}};
            assert(handle.idx == slot);
            assert(lbl->requests.contains(req));
            assert(!lbl->requests.is_empty());
            assert(lbl->responses.is_empty());

            // Facts established by this acquired branch.
            assert(old(self)@.lookup_map == self@.lookup_map);
            assert(old(self)@.entries == self@.entries);
            assert(old(self)@.status_map[handle.idx] is Dirty);
            assert(self@.status_map == old(self)@.status_map.insert(handle.idx, Status::Writeback));
            FracCacheImpl::valid_writeback_handle_model_entry(self, addr, handle);
            assert(old(self)@.lookup_map.contains_key(addr@));
            assert(old(self)@.lookup_map[addr@] == handle.idx);
            assert(old(self)@.entries[old(self)@.lookup_map[addr@]] == Entry::Filled{addr: addr@, data: rec@});

            assert(old(self)@.valid_writeback_requests(lbl->requests)) by {
                assert forall |r: DiskRequest| #[trigger] lbl->requests.contains(r) implies {
                    &&& r is WriteReq
                    &&& old(self)@.lookup_map.contains_key(r->to)
                    &&& old(self)@.entries[old(self)@.lookup_map[r->to]] == Entry::Filled{addr: r->to, data: r->data}
                    &&& old(self)@.status_map[old(self)@.lookup_map[r->to]] is Dirty
                } by {
                    assert(r == req);
                };
            }
            let req_slot_map = Map::new(
                |r: DiskRequest| lbl->requests.contains(r),
                |r: DiskRequest| old(self)@.lookup_map[r->to]
            );
            let writeback_slots = req_slot_map.values();
            assert(writeback_slots =~= set![slot]) by {
                assert forall |s: Slot| #[trigger] writeback_slots.contains(s) <==> set![slot].contains(s) by {
                    if writeback_slots.contains(s) {
                        let r = choose |r: DiskRequest|
                            #[trigger] lbl->requests.contains(r)
                            && old(self)@.lookup_map[r->to] == s;
                        assert(lbl->requests.contains(r));
                        assert(r == req);
                        assert(old(self)@.lookup_map[addr@] == slot);
                        assert(s == slot);
                    }
                    if s == slot {
                        assert(req_slot_map.contains_key(req));
                        assert(req_slot_map[req] == slot);
                        assert(req_slot_map.values().contains(slot)) by {
                            reveal(Map::values);
                        }
                        assert(writeback_slots.contains(s));
                        reveal(Map::values);
                    }
                };
            };
            let updated_status_map = Map::new(
                |s: Slot| writeback_slots.contains(s),
                |s: Slot| Status::Writeback,
            );
            let singleton_update = Map::<Slot, Status>::empty().insert(slot, Status::Writeback);
            assert(updated_status_map =~= singleton_update) by {
                assert forall |s: Slot| #[trigger] updated_status_map.contains_key(s) <==> singleton_update.contains_key(s) by {
                    assert(updated_status_map.contains_key(s) <==> writeback_slots.contains(s));
                    assert(singleton_update.contains_key(s) <==> s == slot);
                };
                assert forall |s: Slot| #[trigger] updated_status_map.contains_key(s) implies updated_status_map[s] == singleton_update[s] by {
                    assert(updated_status_map[s] == Status::Writeback);
                    assert(singleton_update[s] == Status::Writeback);
                };
            };
            vstd::map_lib::lemma_union_insert_right(old(self)@.status_map, Map::<Slot, Status>::empty(), slot, Status::Writeback);
            assert(old(self)@.status_map.union_prefer_right(updated_status_map)
                =~= old(self)@.status_map.insert(slot, Status::Writeback));
            assert(Cache::State::next_by(old(self)@, self@, lbl, Cache::Step::writeback_initiate())) by {
            }
            assert(self.valid_writeback_handles_preserved(*old(self))) by {
                assert forall |addr2: IAddress, handle2: WritebackHandle|
                    old(self).valid_writeback_handle(&addr2, handle2)
                    implies self.valid_writeback_handle(&addr2, handle2)
                by {
                    reveal(FracCacheImpl::valid_writeback_handle);
                    assert(old(self)@.status_map[handle2.idx] is Writeback);
                    assert(!(old(self)@.status_map[slot] is Writeback));
                    assert(handle2.idx != slot);
                    let i = handle2.idx as int;
                    assert(self.metadata[i] == old(self).metadata[i]);
                    assert(self.internal_slots[i] == old(self).internal_slots[i]);
                    assert(self.perms@[i] == old(self).perms@[i]);
                    assert(self.lookup_map@ == old(self)@.lookup_map);
                    assert(self.writeback_loans@.contains_key(handle2.idx) == old(self).writeback_loans@.contains_key(handle2.idx));
                    if old(self).writeback_loans@.contains_key(handle2.idx) {
                        assert(self.writeback_loans@[handle2.idx] == old(self).writeback_loans@[handle2.idx]);
                    }
                }
            }
        }
        WritebackAcquireResult::Acquired{handle}
    }

    pub exec fn complete_writeback(&mut self, addr: &IAddress, handle: WritebackHandle)
        requires
            old(self).wf(),
            old(self).entry_fetched(addr),
            old(self).valid_writeback_handle(addr, handle),
        ensures ({
            let resp = DiskResponse::WriteResp{};
            let cache_lbl = Cache::Label::DiskOps{requests: set!{}, responses: map!{addr@ => resp}};
            &&& self.wf()
            &&& self.valid_load_handles_preserved(*old(self))
            &&& self.valid_writeback_handles_preserved_except(*old(self), *addr)
            &&& Cache::State::next(old(self)@, self@, cache_lbl)
        })
    {
        let WritebackHandle{token, idx, rec} = handle;
        proof {
            let tracked(handle_perm) = token.get();
            let tracked mut perm = self.perms.borrow_mut().tracked_remove(idx as int);
            perm.agree(&handle_perm);
            perm.combine(handle_perm);
            perm.bounded();
            self.perms.borrow_mut().tracked_insert(idx as int, perm);
        }
        let ghost loans = self.writeback_loans@;
        self.writeback_loans = Ghost(loans.remove(idx));
        self.internal_slots[idx] = Some(rec);
        self.metadata[idx] = Metadata{
            status: Status::Clean,
            entry: IEntry::Filled{addr: *addr},
        };

        proof {
            let resp = DiskResponse::WriteResp{};
            let cache_lbl = Cache::Label::DiskOps{requests: set!{}, responses: map!{addr@ => resp}};

            let slot_addr_map = old(self)@.lookup_map.restrict(cache_lbl->responses.dom()).invert();
            assert(slot_addr_map =~= map!{idx => addr@}) by {
                assert(old(self)@.lookup_map.restrict(cache_lbl->responses.dom()).contains_pair(addr@, idx));
                reveal(Map::invert);
            }

            let updated_status_map = Map::new(
                |slot| slot_addr_map.contains_key(slot),
                |slot| Status::Clean
            );
            assert(self@.entries =~= old(self)@.entries);
            assert(self@.status_map =~= old(self)@.status_map.union_prefer_right(updated_status_map));
            reveal(Cache::State::next_by);
            assert(Cache::State::next_by(old(self)@, self@, cache_lbl, Cache::Step::writeback_complete()));
            reveal(Cache::State::next);
            assert(self.valid_load_handles_preserved(*old(self))) by {
                assert forall |addr2: IAddress, handle2: MutHandle|
                    old(self).entry_fetched(&addr2) && old(self).valid_load_handle(&addr2, handle2)
                    implies self.entry_fetched(&addr2) && self.valid_load_handle(&addr2, handle2)
                by {
                    reveal(FracCacheImpl::valid_load_handle);
                    reveal(FracCacheImpl::valid_handle);
                    assert(!(old(self)@.status_map[handle2.idx] is Writeback));
                    assert(old(self)@.status_map[idx] is Writeback);
                    assert(handle2.idx != idx);
                    let i = handle2.idx as int;
                    assert(self.metadata[i] == old(self).metadata[i]);
                    assert(self.internal_slots[i] == old(self).internal_slots[i]);
                    assert(self.perms@[i] == old(self).perms@[i]);
                    assert(self.lookup_map@ == old(self)@.lookup_map);
                }
            }
            assert(self.valid_writeback_handles_preserved_except(*old(self), *addr)) by {
                assert forall |addr2: IAddress, handle2: WritebackHandle|
                    addr2 != *addr
                    && old(self).valid_writeback_handle(&addr2, handle2)
                    implies self.valid_writeback_handle(&addr2, handle2)
                by {
                    reveal(FracCacheImpl::valid_writeback_handle);
                    assert(old(self).lookup_addr_slot(addr) == idx);
                    assert(old(self).lookup_addr_slot(&addr2) == handle2.idx);
                    assert(old(self).lookup_map_injective());
                    assert(handle2.idx != idx);
                    let i = handle2.idx as int;
                    assert(self.metadata[i] == old(self).metadata[i]);
                    assert(self.internal_slots[i] == old(self).internal_slots[i]);
                    assert(self.perms@[i] == old(self).perms@[i]);
                    assert(self.lookup_map@ == old(self)@.lookup_map);
                    assert(self.writeback_loans@.contains_key(handle2.idx) == old(self).writeback_loans@.contains_key(handle2.idx));
                    if old(self).writeback_loans@.contains_key(handle2.idx) {
                        assert(self.writeback_loans@[handle2.idx] == old(self).writeback_loans@[handle2.idx]);
                    }
                }
            }
        }
    }
}

}//verus!
