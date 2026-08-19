// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::assert_sets_equal;
use vstd::hash_map::HashMapWithView;
use crate::spec::MapSpec_t::{ID};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::disk::GenericDisk_v::{IAddress};
use crate::spec::ImplDisk_t::IAU;
use crate::spec::AsyncDisk_t::{RawPage, DiskRequest, DiskResponse, Address};
use crate::implementation::Cache_v::{Cache, Entry, Slot, Status, addr_maps_to_req};
use crate::implementation::AuPoolImpl_v::iau_vec_set;
use vstd::std_specs::hash::obeys_key_model;
use vstd::pcm::Loc;
use vstd::tokens::frac::*;
use vstd::pervasive::unreached;
use crate::trusted::ClientAPI_t::BLOCK_SIZE;

verus!{

pub const PAGE_SIZE_BYTES: usize = BLOCK_SIZE;
pub const CACHE_SIZE_RECS: usize = 1000;

pub type IRawPage = Vec<u8>;
pub type Perm = Frac<Slot,2>;

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

pub enum ReserveWriteResult {
    Reserved{slot_handle: MutHandle},
    CacheFull,
}

pub enum ReserveTwoWriteResult {
    Reserved {
        first_handle: MutHandle,
        second_handle: MutHandle,
    },
    CacheFull,
}

pub enum PrepareTwoWriteResult {
    Ready {
        first_handle: MutHandle,
        second_handle: MutHandle,
        prepared_cache: Ghost<Cache::State>,
    },
    CacheFull,
    Blocked,
}

pub enum WritebackAcquireResult {
    NotPresent,
    NotDirty,
    Busy, // page is dirty but currently borrowed by another handle
    Acquired{handle: WritebackHandle},
}

pub enum AuSetWritebackResult {
    Acquired { addr: IAddress, handle: WritebackHandle },
    Complete,
    Busy,
}

fn iau_vec_contains(aus: &Vec<IAU>, target: IAU) -> (out: bool)
    ensures
        out <==> iau_vec_set(aus@).contains(target as nat),
{
    let mut index = 0usize;
    while index < aus.len()
        invariant
            index <= aus.len(),
            forall |i: int| 0 <= i < index ==> {
                #[trigger] aus@[i] != target
            },
        decreases aus.len() - index,
    {
        if aus[index] == target {
            return true;
        }
        index += 1;
    }
    false
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

    pub open spec fn restored_write_entry(
        &self,
        addr: &IAddress,
        handle: MutHandle,
    ) -> Entry
        recommends self.valid_write_handle(addr, handle)
    {
        if self.slot_entry(handle.idx) is Reserved {
            Entry::Reserved { addr: addr@ }
        } else {
            Entry::Filled { addr: addr@, data: handle.rec@ }
        }
    }

    pub open spec fn restored_two_write_state(
        &self,
        first_addr: &IAddress,
        first_handle: MutHandle,
        second_addr: &IAddress,
        second_handle: MutHandle,
    ) -> Cache::State
        recommends
            self.valid_write_handle(first_addr, first_handle),
            self.valid_write_handle(second_addr, second_handle),
            first_handle.idx != second_handle.idx,
    {
        Cache::State {
            entries: self@.entries
                .insert(
                    first_handle.idx,
                    self.restored_write_entry(first_addr, first_handle),
                )
                .insert(
                    second_handle.idx,
                    self.restored_write_entry(second_addr, second_handle),
                ),
            status_map: self@.status_map,
            lookup_map: self@.lookup_map,
        }
    }

    pub open spec fn prepared_two_write_state_matches(
        &self,
        prepared: Cache::State,
        first_addr: &IAddress,
        first_slot: Slot,
        second_addr: &IAddress,
        second_slot: Slot,
    ) -> bool {
        &&& first_addr != second_addr
        &&& first_slot != second_slot
        &&& prepared.lookup_map == self@.lookup_map
        &&& prepared.status_map == self@.status_map
        &&& prepared.lookup_map.contains_key(first_addr@)
        &&& prepared.lookup_map[first_addr@] == first_slot
        &&& prepared.lookup_map.contains_key(second_addr@)
        &&& prepared.lookup_map[second_addr@] == second_slot
        &&& prepared.entries.contains_key(first_slot)
        &&& prepared.entries.contains_key(second_slot)
        &&& prepared.entries == self@.entries
            .insert(first_slot, prepared.entries[first_slot])
            .insert(second_slot, prepared.entries[second_slot])
        &&& prepared.entries[first_slot].get_addr()
            == self@.entries[first_slot].get_addr()
        &&& prepared.entries[second_slot].get_addr()
            == self@.entries[second_slot].get_addr()
        &&& (prepared.entries[first_slot] is Filled)
            == (self@.entries[first_slot] is Filled)
        &&& (prepared.entries[second_slot] is Filled)
            == (self@.entries[second_slot] is Filled)
        &&& (prepared.entries[first_slot] is Empty)
            == (self@.entries[first_slot] is Empty)
        &&& (prepared.entries[second_slot] is Empty)
            == (self@.entries[second_slot] is Empty)
    }

    proof fn restored_two_write_state_matches(
        &self,
        first_addr: &IAddress,
        first_handle: MutHandle,
        second_addr: &IAddress,
        second_handle: MutHandle,
    )
        requires
            self.wf(),
            self.entry_fetched(first_addr),
            self.entry_fetched(second_addr),
            self.valid_write_handle(first_addr, first_handle),
            self.valid_write_handle(second_addr, second_handle),
            first_addr != second_addr,
            first_handle.idx != second_handle.idx,
        ensures
            self.prepared_two_write_state_matches(
                self.restored_two_write_state(
                    first_addr,
                    first_handle,
                    second_addr,
                    second_handle,
                ),
                first_addr,
                first_handle.idx,
                second_addr,
                second_handle.idx,
            ),
    {


        Self::valid_write_handle_model_valid_write(
            self,
            first_addr,
            first_handle,
        );
        Self::valid_write_handle_model_valid_write(
            self,
            second_addr,
            second_handle,
        );
        assert(self.prepared_two_write_state_matches(
            self.restored_two_write_state(
                first_addr,
                first_handle,
                second_addr,
                second_handle,
            ),
            first_addr,
            first_handle.idx,
            second_addr,
            second_handle.idx,
        )) by {

            assert_maps_equal!(
                self.restored_two_write_state(
                    first_addr,
                    first_handle,
                    second_addr,
                    second_handle,
                ).entries,
                self@.entries.insert(
                    first_handle.idx,
                    self.restored_write_entry(first_addr, first_handle),
                ).insert(
                    second_handle.idx,
                    self.restored_write_entry(second_addr, second_handle),
                ),
                slot => {}
            );
        }
    }

    pub closed spec fn entry_available_for_fetch(self, addr: &IAddress) -> bool
    {
        &&& self.entry_fetched(addr)
        &&& self.lookup_addr_slot(addr) < self.total_slots()
        &&& self.internal_slots[self.lookup_addr_slot(addr) as int] is Some
        &&& !(self.metadata[self.lookup_addr_slot(addr) as int].status is Writeback)
    }

    pub proof fn entry_available_preserved_except(
        old: Self,
        new: Self,
        except: &IAddress,
        except_slot: Slot,
        addr: &IAddress,
    )
        requires
            old.wf(),
            new.wf(),
            old.entry_available_for_fetch(addr),
            *addr != *except,
            new.entry_fetched(except),
            new.lookup_addr_slot(except) == except_slot,
            new.entry_fetched_same_except(old, except),
            new.entries_same_except(old, except_slot),
        ensures
            new.entry_available_for_fetch(addr),
    {
        assert(old.entry_fetched(addr)) by {

            reveal(FracCacheImpl::lookup_addr_slot);
        }
        assert(new.entry_fetched(addr) == old.entry_fetched(addr)) by {

            assert(*addr != *except);
        }
        assert(new.entry_fetched(addr));
        assert(new.lookup_addr_slot(addr) == old.lookup_addr_slot(addr));
        assert(new.lookup_addr_slot(addr) != except_slot) by {
            reveal(FracCacheImpl::lookup_addr_slot);
            reveal(FracCacheImpl::entry_fetched);
            assert(new.lookup_map@.is_injective());
        }
        let slot = new.lookup_addr_slot(addr);
        assert(slot < new.total_slots()) by {
            reveal(FracCacheImpl::wf);
            reveal(FracCacheImpl::lookup_map_inv);
            reveal(FracCacheImpl::entry_fetched);
            reveal(FracCacheImpl::lookup_addr_slot);
        }
        assert(new.total_slots() == old.total_slots());
        assert(except_slot < new.total_slots()) by {
            reveal(FracCacheImpl::wf);
            reveal(FracCacheImpl::lookup_map_inv);
            reveal(FracCacheImpl::entry_fetched);
            reveal(FracCacheImpl::lookup_addr_slot);
            assert(new.lookup_map_inv());
            assert(new.lookup_map@.contains_key(except@));
            assert(new.lookup_map@[except@] == except_slot);
            assert(new.lookup_map@.contains_value(except_slot));
        }
        assert(0 <= slot < new.total_slots() && slot != except_slot);
        assert(0 <= slot as int);
        assert((slot as int) < (new.total_slots() as int));
        assert(slot as int != except_slot as int);
        reveal(FracCacheImpl::entries_same_except);
        assert(forall |i: int| 0 <= i < new.total_slots() && i != except_slot ==> {
            &&& new.perms@[i] == old.perms@[i]
            &&& new.internal_slots[i] == old.internal_slots[i]
            &&& new.metadata[i] == old.metadata[i]
        });
        assert(new.perms@[slot as int].resource() == slot as int) by {
            reveal(FracCacheImpl::wf);
            reveal(FracCacheImpl::perms_inv);
        }
        assert(new.internal_slots[slot as int] == old.internal_slots[slot as int]);
        assert(new.metadata[slot as int] == old.metadata[slot as int]);
    }

    pub proof fn valid_write_handle_preserved_except(
        old: Self,
        new: Self,
        addr: &IAddress,
        handle: MutHandle,
        except: &IAddress,
        except_slot: Slot,
    )
        requires
            old.wf(),
            new.wf(),
            old.entry_fetched(addr),
            old.valid_write_handle(addr, handle),
            *addr != *except,
            new.entry_fetched(except),
            new.lookup_addr_slot(except) == except_slot,
            new.entry_fetched_same_except(old, except),
            except_slot < new.total_slots(),
            new.entries_same_except(old, except_slot),
            new.entry_token_unchanged(old),
        ensures
            new.valid_write_handle(addr, handle),
    {

        assert(new.entry_fetched(addr) == old.entry_fetched(addr));
        assert(new.entry_fetched(addr));
        assert(new.lookup_addr_slot(addr) == old.lookup_addr_slot(addr));
        assert(handle.idx == old.lookup_addr_slot(addr));
        assert(handle.idx != except_slot) by {
            reveal(FracCacheImpl::lookup_map_injective);
            assert(new.lookup_map@.is_injective());
        }
        Self::slot_entry_same_except(old, new, except_slot, handle.idx);
        assert(new.metadata@[handle.idx as int]
            == old.metadata@[handle.idx as int]) by {
            reveal(FracCacheImpl::entries_same_except);
            assert(0 <= (handle.idx as int));
            assert((handle.idx as int) < (new.total_slots() as int));
            assert((handle.idx as int) != (except_slot as int));
            assert(new.perms@[handle.idx as int]
                == old.perms@[handle.idx as int]);
            assert(new.internal_slots[handle.idx as int]
                == old.internal_slots[handle.idx as int]);
            assert(new.metadata[handle.idx as int]
                == old.metadata[handle.idx as int]);
        }
        assert(new.valid_handle(handle)) by {

            assert(new.entry_token_id(handle.idx)
                == old.entry_token_id(handle.idx));
            assert(new@.status_map[handle.idx]
                == old@.status_map[handle.idx]) by {
                reveal(FracCacheImpl::view_state);
            }
        }

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

    proof fn slots_inv_preserved_except(
        old: Self,
        new: Self,
        slot: Slot,
    )
        requires
            old.slots_inv(),
            new.total_slots() == old.total_slots(),
            slot < new.total_slots(),
            forall |i: int| 0 <= i < new.total_slots() && i != slot as int
                ==> new.internal_slots[i] == old.internal_slots[i],
            new.internal_slots[slot as int] is Some
                ==> new.internal_slots[slot as int].unwrap().len()
                    == PAGE_SIZE_BYTES,
        ensures
            new.slots_inv(),
    {
        reveal(FracCacheImpl::slots_inv);
        assert forall |i: int|
            0 <= i < new.total_slots()
                && new.internal_slots[i] is Some
            implies #[trigger] new.internal_slots[i].unwrap().len()
                == PAGE_SIZE_BYTES by {
            if i != slot as int {
                assert(new.internal_slots[i] == old.internal_slots[i]);
            }
        }
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
            Entry::Reserved{addr}
            | Entry::Loading{addr}
            | Entry::Filled{addr, ..} => {
                self.lookup_map@.contains_key(addr) && self.lookup_map@[addr] == slot
            },
            Entry::Empty => true,
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

    closed spec fn slot_evictable_for_au(self, slot: Slot, au: IAU) -> bool
        recommends
            slot < self.total_slots(),
    {
        match self.metadata[slot as int].entry {
            IEntry::Empty => true,
            IEntry::Reserved{addr} | IEntry::Loading{addr} => addr.au != au,
            IEntry::Filled{addr} => {
                addr.au != au || self.metadata[slot as int].status is Clean
            },
        }
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

    pub open spec fn empty_page() -> RawPage
    {
        seq![0u8; PAGE_SIZE_BYTES as nat]
    }

    exec fn new_empty_page() -> (out: IRawPage)
        ensures out@ == Self::empty_page()
    {
        let mut out = Vec::with_capacity(PAGE_SIZE_BYTES);
        while out.len() < PAGE_SIZE_BYTES
            invariant
                out.len() <= PAGE_SIZE_BYTES,
                forall |i: int| 0 <= i < out.len() ==> #[trigger] out@[i] == 0u8,
            decreases PAGE_SIZE_BYTES - out.len(),
        {
            out.push(0u8);
        }

        assert(out@ =~= Self::empty_page());
        out
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

    pub exec fn contains_addr(&self, addr: &IAddress) -> (out: bool)
        requires
            self.wf(),
        ensures
            out == self.entry_fetched(addr),
            out == self@.lookup_map.contains_key(addr@),
    {
        let out = self.lookup_map.contains_key(addr);
        proof {
            reveal(FracCacheImpl::entry_fetched);
            reveal(FracCacheImpl::view_state);
        }
        out
    }

    pub exec fn available_for_fetch(&self, addr: &IAddress) -> (out: bool)
        requires self.wf(),
        ensures out == self.entry_available_for_fetch(addr),
    {
        if !self.lookup_map.contains_key(addr) {
            proof {
                reveal(FracCacheImpl::entry_available_for_fetch);
                reveal(FracCacheImpl::entry_fetched);
            }
            return false;
        }
        let slot = *self.lookup_map.get(addr).unwrap();
        proof {
            reveal(FracCacheImpl::wf);
            assert(self.metadata.len() == self.total_slots());
            assert(self.internal_slots.len() == self.total_slots());
            reveal(FracCacheImpl::entry_fetched);
            reveal(FracCacheImpl::lookup_map_inv);
            assert(self.lookup_map@.contains_value(slot));
            assert(slot < self.total_slots());
        }
        if slot >= self.metadata.len() || slot >= self.internal_slots.len() {
            proof { assert(false); }
            return false;
        }
        let available_status = match self.metadata[slot].status {
            Status::Writeback => false,
            _ => true,
        };
        let out = slot < CACHE_SIZE_RECS
            && self.internal_slots[slot].is_some()
            && available_status;
        proof {
            reveal(FracCacheImpl::entry_available_for_fetch);
            reveal(FracCacheImpl::entry_fetched);
            reveal(FracCacheImpl::lookup_addr_slot);
        }
        out
    }

    pub proof fn valid_write_handle_model_entry(cache: &FracCacheImpl, addr: &IAddress, handle: MutHandle)
    requires
        cache.wf(),
        cache.entry_fetched(addr),
        cache.valid_write_handle(addr, handle),
        cache.slot_entry(handle.idx) == (IEntry::Filled{addr: *addr}),
    ensures
        cache@.lookup_map.contains_key(addr@),
        cache@.lookup_map[addr@] == handle.idx,
        cache@.valid_write(addr@),
    {
        reveal(FracCacheImpl::entry_fetched);
        reveal(FracCacheImpl::lookup_addr_slot);
        reveal(FracCacheImpl::slot_entry);
        reveal(FracCacheImpl::view_state);
        reveal(FracCacheImpl::view_entries);
        reveal(FracCacheImpl::wf);
    }

    pub proof fn valid_write_handle_model_valid_write(
        cache: &FracCacheImpl,
        addr: &IAddress,
        handle: MutHandle,
    )
        requires
            cache.wf(),
            cache.entry_fetched(addr),
            cache.valid_write_handle(addr, handle),
        ensures
            cache@.lookup_map.contains_key(addr@),
            cache@.lookup_map[addr@] == handle.idx,
            cache@.valid_write(addr@),
    {


        reveal(FracCacheImpl::entry_fetched);
        reveal(FracCacheImpl::lookup_addr_slot);
        reveal(FracCacheImpl::slot_entry);
        reveal(FracCacheImpl::view_state);
        reveal(FracCacheImpl::view_entries);
        reveal(FracCacheImpl::wf);
        match cache.metadata@[handle.idx as int].entry {
            IEntry::Reserved { addr: entry_addr }
            | IEntry::Filled { addr: entry_addr } => {
                assert(entry_addr == *addr) by {
                    reveal(FracCacheImpl::lookup_map_bijection);
                    reveal(FracCacheImpl::lookup_map_injective);
                    assert(cache@.entries.contains_key(handle.idx));
                    assert(cache@.entries[handle.idx].get_addr()
                        == entry_addr@);
                    assert(match cache@.entries[handle.idx] {
                        Entry::Reserved { addr }
                        | Entry::Loading { addr }
                        | Entry::Filled { addr, .. } => {
                            cache.lookup_map@.contains_key(addr)
                                && cache.lookup_map@[addr] == handle.idx
                        },
                        Entry::Empty => true,
                    });
                    assert(cache.lookup_map@.contains_key(entry_addr@));
                    assert(cache.lookup_map@[entry_addr@] == handle.idx);
                    assert(cache.lookup_map@[addr@] == handle.idx);
                    assert(cache.lookup_map@.is_injective());
                }
            },
            _ => {},
        }
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

    pub proof fn valid_writeback_handle_has_inv(
        cache: &FracCacheImpl,
        addr: &IAddress,
        handle: WritebackHandle,
    )
        requires
            cache.wf(),
            cache.valid_writeback_handle(addr, handle),
        ensures
            handle.inv(),
            cache.entry_fetched(addr),
    {
        reveal(FracCacheImpl::valid_writeback_handle);
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

    spec fn single_slot_mapping(slot: Slot, addr: Address) -> Map<Slot, Address>
    {
        map!{slot => addr}
    }

    proof fn prove_lookup_props_after_single_slot_update(old: Self, new: Self, slot: Slot, addr: IAddress)
        requires
            old.wf(),
            slot < old.total_slots(),
            old.slot_entry(slot) is Empty,
            !old@.lookup_map.contains_value(slot),
            !old@.lookup_map.contains_key(addr@),
            new@.lookup_map == old@.lookup_map.insert(addr@, slot),
            forall |i: Slot| #![auto]
                i < old.total_slots()
                ==> if i == slot {
                    !(new.slot_entry(i) is Empty)
                } else {
                    new.slot_entry(i) == old.slot_entry(i)
                },
            new.total_slots() == old.total_slots(),
        ensures
            new.lookup_map_inv(),
            new.lookup_map_consistent_with_slots(),
            new.lookup_map_injective(),
    {
        assert(new.lookup_map_inv()) by {
            assert forall |i| #[trigger] new.lookup_map@.contains_value(i)
            implies i < new.total_slots() by {
                if i != slot {
                    assert(old.lookup_map@.contains_value(i));
                }
            }
        }

        assert(new.lookup_map_consistent_with_slots()) by {
            assert forall |i: Slot| #![auto] i < new.total_slots()
            implies new.lookup_map@.contains_value(i) <==> !(new.slot_entry(i) is Empty)
            by {
                if new.lookup_map@.contains_value(i) && i != slot {
                    assert(old.lookup_map@.contains_value(i));
                }

                if !(new.slot_entry(i) is Empty) {
                    if i == slot {
                        assert(new.lookup_map@.contains_pair(addr@, slot));
                    } else {
                        assert(new.slot_entry(i) == old.slot_entry(i));
                        assert(!(old.slot_entry(i) is Empty));
                        assert(old.lookup_map@.contains_value(i));
                        let other_addr = choose |other_addr| #[trigger] old.lookup_map@.contains_key(other_addr)
                            && old.lookup_map@[other_addr] == i;
                        assert(new.lookup_map@.contains_pair(other_addr, i));
                    }
                } else {
                    if i != slot {
                        assert(new.slot_entry(i) == old.slot_entry(i));
                    }
                }
            }
        }

        assert(new.lookup_map_injective()) by {
            assert forall |addr1: Address, addr2: Address| #![auto]
                new.lookup_map@.contains_key(addr1)
                && new.lookup_map@.contains_key(addr2)
                && new.lookup_map@[addr1] == new.lookup_map@[addr2]
                implies addr1 == addr2
            by {
                if addr1 == addr@ {
                    if addr2 == addr@ {
                    } else {
                        assert(old.lookup_map@.contains_value(slot));
                    }
                } else if addr2 == addr@ {
                    assert(old.lookup_map@.contains_value(slot));
                } else {
                }
            }
        }
    }

    proof fn prove_load_handle_preservation_after_new_mapping(old: Self, new: Self, addr: IAddress, slot: Slot)
        requires
            old.wf(),
            new.wf(),
            !old.entry_fetched(&addr),
            new.entry_fetched_same_except(old, &addr),
            new.entry_token_unchanged(old),
            slot < new.total_slots(),
            new.entries_same_except(old, slot),
            forall |addr2: IAddress, handle2: MutHandle|
                addr2 != addr
                && old.entry_fetched(&addr2)
                && old.valid_load_handle(&addr2, handle2)
                ==> handle2.idx != slot,
        ensures
            new.valid_load_handles_preserved(old),
    {
        Self::valid_load_handles_preserved_except_from_same(old, new, addr, slot);
        Self::valid_load_handles_preserved_from_except_if_missing(old, new, addr);
    }

    proof fn prove_reserve_transition_single_slot(old: Self, new: Self, slot: Slot, addr: IAddress)
        requires
            old.wf(),
            slot < old.total_slots(),
            old.slot_entry(slot) is Empty,
            !old@.lookup_map.contains_value(slot),
            !old@.lookup_map.contains_key(addr@),
            new@.lookup_map == old@.lookup_map.insert(addr@, slot),
            new@.entries == old@.entries.union_prefer_right(
                Map::new(
                    |s| Self::single_slot_mapping(slot, addr@).contains_key(s),
                    |s| Entry::Reserved{addr: Self::single_slot_mapping(slot, addr@)[s]}
                )
            ),
            new@.status_map == old@.status_map,
        ensures
            Cache::State::next(old@, new@, Cache::Label::Internal),
    {
        let new_slots_mapping = Self::single_slot_mapping(slot, addr@);
        let lbl = Cache::Label::Internal;
        assert(new_slots_mapping.invert() =~= map!{addr@ => slot}) by {
            assert(new_slots_mapping.contains_pair(slot, addr@));
        }
        assert(old@.lookup_map.union_prefer_right(new_slots_mapping.invert()) =~= old@.lookup_map.insert(addr@, slot));
        let updated_entries = Map::new(
            |s| new_slots_mapping.contains_key(s),
            |s| Entry::Reserved{addr: new_slots_mapping[s]}
        );
        assert(new@.entries =~= old@.entries.union_prefer_right(updated_entries));
        assert(new@.lookup_map =~= old@.lookup_map.union_prefer_right(new_slots_mapping.invert()));
        assert(new@.status_map =~= old@.status_map);
        reveal(Cache::State::next_by);
        assert(Cache::State::next_by(old@, new@, lbl, Cache::Step::reserve(new_slots_mapping)));
        reveal(Cache::State::next);
    }

    proof fn prove_load_initiate_transition_single_slot(old: Self, new: Self, slot: Slot, addr: IAddress)
        requires
            old.wf(),
            slot < old.total_slots(),
            old.slot_entry(slot) is Empty,
            !old@.lookup_map.contains_value(slot),
            !old@.lookup_map.contains_key(addr@),
            new@.lookup_map == old@.lookup_map.insert(addr@, slot),
            new@.entries == old@.entries.union_prefer_right(
                Map::new(
                    |s| Self::single_slot_mapping(slot, addr@).contains_key(s),
                    |s| Entry::Loading{addr: Self::single_slot_mapping(slot, addr@)[s]}
                )
            ),
            new@.status_map == old@.status_map,
        ensures
            Cache::State::next(old@, new@, cache_load_label(&addr)),
    {
        let load_request = DiskRequest::ReadReq{from: addr@};
        let cache_lbl = cache_load_label(&addr);
        let new_slots_mapping = Self::single_slot_mapping(slot, addr@);
        assert(new_slots_mapping.invert() =~= map!{addr@ => slot}) by {
            assert(new_slots_mapping.contains_pair(slot, addr@));
        }
        assert(old@.lookup_map.union_prefer_right(new_slots_mapping.invert()) =~= old@.lookup_map.insert(addr@, slot));

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
            |s| new_slots_mapping.contains_key(s),
            |s| Entry::Loading{addr: new_slots_mapping[s]}
        );
        assert(new@.entries =~= old@.entries.union_prefer_right(updated_entries));
        assert(new@.lookup_map =~= old@.lookup_map.union_prefer_right(new_slots_mapping.invert()));
        assert(new@.status_map =~= old@.status_map);
        reveal(Cache::State::next_by);
        assert(Cache::State::next_by(old@, new@, cache_lbl, Cache::Step::load_initiate(new_slots_mapping)));
        reveal(Cache::State::next);
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

    pub exec fn evictable(&self, addr: &IAddress) -> (out: bool)
    requires
        self.wf(),
    ensures
        out ==> {
            let lbl = Cache::Label::EvictableCheck{aus: set![addr@.au]};
            &&& Cache::State::evictable(self@, self@, lbl)
            &&& Cache::State::next(self@, self@, lbl)
        },
    {
        let mut slot: Slot = 0;
        while slot < CACHE_SIZE_RECS
            invariant
                self.wf(),
                slot <= self.total_slots(),
                forall |s: Slot| s < slot ==> self.slot_evictable_for_au(s, addr.au),
            decreases CACHE_SIZE_RECS - slot,
        {
            let entry = self.metadata[slot].entry;
            let status = self.metadata[slot].status;
            let slot_ok = match entry {
                IEntry::Empty => true,
                IEntry::Reserved{addr: entry_addr}
                | IEntry::Loading{addr: entry_addr} => entry_addr.au != addr.au,
                IEntry::Filled{addr: entry_addr} => {
                    let clean = match status {
                        Status::Clean => true,
                        _ => false,
                    };
                    entry_addr.au != addr.au || clean
                },
            };
            if !slot_ok {
                return false;
            }
            proof {
                assert(self.slot_evictable_for_au(slot, addr.au));
            }
            slot = slot + 1;
        }

        proof {
            let lbl = Cache::Label::EvictableCheck{aus: set![addr@.au]};
            reveal(FracCacheImpl::wf);
            reveal(FracCacheImpl::lookup_map_bijection);
            reveal(FracCacheImpl::lookup_map_injective);
            reveal(FracCacheImpl::view_state);
            reveal(FracCacheImpl::view_entries);
            assert forall |model_addr: Address| lbl->aus.contains(model_addr.au)
                && #[trigger] self@.lookup_map.contains_key(model_addr)
                implies {
                    &&& self@.entries[self@.lookup_map[model_addr]] is Filled
                    &&& self@.status_map[self@.lookup_map[model_addr]] is Clean
                } by {
                let mapped_slot = self@.lookup_map[model_addr];
                assert(self.lookup_map@.contains_key(model_addr));
                assert(self.lookup_map@.contains_value(mapped_slot));
                assert(mapped_slot < self.total_slots());
                assert(self.view_entries().contains_key(mapped_slot));
                assert(self.slot_evictable_for_au(mapped_slot, addr.au));
                assert(model_addr.au == addr@.au);
                match self.metadata[mapped_slot as int].entry {
                    IEntry::Empty => {
                        assert(!self.lookup_map@.contains_value(mapped_slot));
                        assert(false);
                    },
                    IEntry::Reserved{addr: entry_addr}
                    | IEntry::Loading{addr: entry_addr} => {
                        assert(self.lookup_map@.contains_key(entry_addr@));
                        assert(self.lookup_map@[entry_addr@] == mapped_slot);
                        assert(entry_addr@ == model_addr);
                        assert(entry_addr.au == addr.au);
                        assert(false);
                    },
                    IEntry::Filled{addr: entry_addr} => {
                        assert(self.lookup_map@.contains_key(entry_addr@));
                        assert(self.lookup_map@[entry_addr@] == mapped_slot);
                        assert(entry_addr@ == model_addr);
                        assert(entry_addr.au == addr.au);
                        assert(self.metadata[mapped_slot as int].status is Clean);
                    },
                }
            }
            reveal(Cache::State::next_by);
            reveal(Cache::State::next);
            assert(Cache::State::next_by(self@, self@, lbl, Cache::Step::evictable()));
        }
        true
    }

    pub exec fn evictable_aus(&self, aus: &Vec<IAU>) -> (out: bool)
        requires
            self.wf(),
        ensures
            out ==> {
                let lbl = Cache::Label::EvictableCheck{aus: iau_vec_set(aus@)};
                &&& Cache::State::evictable(self@, self@, lbl)
                &&& Cache::State::next(self@, self@, lbl)
            },
    {
        let mut idx = 0usize;
        while idx < aus.len()
            invariant
                self.wf(),
                idx <= aus.len(),
                forall |i: int| 0 <= i < idx ==> {
                    let au = #[trigger] aus@[i];
                    let lbl = Cache::Label::EvictableCheck{aus: set![au as nat]};
                    &&& Cache::State::evictable(self@, self@, lbl)
                    &&& Cache::State::next(self@, self@, lbl)
                },
            decreases aus.len() - idx,
        {
            let addr = IAddress{au: aus[idx], page: 0};
            if !self.evictable(&addr) {
                return false;
            }
            idx += 1;
        }
        proof {
            let lbl = Cache::Label::EvictableCheck{aus: iau_vec_set(aus@)};
            reveal(Cache::State::next);
            reveal(Cache::State::next_by);
            assert forall |addr: Address| lbl->aus.contains(addr.au)
                && #[trigger] self@.lookup_map.contains_key(addr)
                implies {
                    &&& self@.entries[self@.lookup_map[addr]] is Filled
                    &&& self@.status_map[self@.lookup_map[addr]] is Clean
                } by {
                let i = choose |i: int| 0 <= i < aus@.len()
                    && #[trigger] aus@[i] as nat == addr.au;
                let single = Cache::Label::EvictableCheck{aus: set![aus@[i] as nat]};
                assert(Cache::State::evictable(self@, self@, single));
            }
            assert(Cache::State::evictable(self@, self@, lbl));
            assert(Cache::State::next_by(self@, self@, lbl, Cache::Step::evictable()));
            assert(Cache::State::next(self@, self@, lbl));
        }
        true
    }

    pub exec fn begin_writeback_for_aus(
        &mut self,
        aus: &Vec<IAU>,
    ) -> (out: AuSetWritebackResult)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self.valid_load_handles_preserved(*old(self)),
            self.valid_writeback_handles_preserved(*old(self)),
            match out {
                AuSetWritebackResult::Acquired { addr, handle } => {
                    &&& iau_vec_set(aus@).contains(addr@.au)
                    &&& self.entry_fetched(&addr)
                    &&& self.valid_writeback_handle(&addr, handle)
                    &&& Cache::State::next(
                        old(self)@,
                        self@,
                        Cache::Label::DiskOps {
                            requests: set![DiskRequest::WriteReq {
                                to: addr@,
                                data: handle.rec@,
                            }],
                            responses: Map::empty(),
                        },
                    )
                },
                AuSetWritebackResult::Complete => {
                    &&& *self == *old(self)
                    &&& Cache::State::next(
                        self@,
                        self@,
                        Cache::Label::EvictableCheck {
                            aus: iau_vec_set(aus@),
                        },
                    )
                },
                AuSetWritebackResult::Busy => *self == *old(self),
            },
    {
        let mut slot: Slot = 0;
        while slot < CACHE_SIZE_RECS
            invariant
                self.wf(),
                *self == *old(self),
                slot <= CACHE_SIZE_RECS,
            decreases CACHE_SIZE_RECS - slot,
        {
            let entry = self.metadata[slot].entry;
            let status = self.metadata[slot].status;
            match entry {
                IEntry::Reserved { addr }
                | IEntry::Loading { addr } => {
                    if iau_vec_contains(aus, addr.au) {
                        proof {
                            Self::valid_writeback_handles_preserved_if_same(
                                *old(self),
                                *self,
                            );
                        }
                        return AuSetWritebackResult::Busy;
                    }
                },
                IEntry::Filled { addr } => {
                    if iau_vec_contains(aus, addr.au) {
                        match status {
                            Status::Dirty => {
                                match self.begin_writeback(&addr) {
                                    WritebackAcquireResult::Acquired {
                                        handle,
                                    } => {
                                        return AuSetWritebackResult::Acquired {
                                            addr,
                                            handle,
                                        };
                                    },
                                    WritebackAcquireResult::NotPresent
                                    | WritebackAcquireResult::NotDirty
                                    | WritebackAcquireResult::Busy => {
                                        return AuSetWritebackResult::Busy;
                                    },
                                }
                            },
                            Status::Clean => {},
                            Status::Writeback | Status::NotFilled => {
                                proof {
                                    Self::valid_writeback_handles_preserved_if_same(
                                        *old(self),
                                        *self,
                                    );
                                }
                                return AuSetWritebackResult::Busy;
                            },
                        }
                    }
                },
                IEntry::Empty => {},
            }
            slot += 1;
        }

        if self.evictable_aus(aus) {
            proof {
                Self::valid_writeback_handles_preserved_if_same(
                    *old(self),
                    *self,
                );
            }
            AuSetWritebackResult::Complete
        } else {
            proof {
                Self::valid_writeback_handles_preserved_if_same(
                    *old(self),
                    *self,
                );
            }
            AuSetWritebackResult::Busy
        }
    }

    pub exec fn find_unmapped_empty_slot(&self) -> (out: Option<Slot>)
        requires
            self.wf(),
        ensures
            out is Some ==> {
                let slot = out.unwrap();
                &&& slot < self.total_slots()
                &&& self.slot_entry(slot) is Empty
                &&& !self@.lookup_map.contains_value(slot)
            },
            out is None ==> forall |slot: Slot| #![auto] slot < self.total_slots()
                ==> !(self.slot_entry(slot) is Empty && !self@.lookup_map.contains_value(slot)),
    {
        let mut slot: Slot = 0;
        while slot < CACHE_SIZE_RECS
            invariant
                self.wf(),
                slot <= self.total_slots(),
                forall |s: Slot| #![auto] s < slot ==> !(self.slot_entry(s) is Empty),
            decreases
                self.total_slots() - slot,
        {
            if let IEntry::Empty = self.metadata[slot].entry {
                proof {
                    assert(!self.lookup_map@.contains_value(slot));
                }
                return Some(slot);
            }
            slot = slot + 1;
        }
        None
    }

    pub exec fn find_unmapped_empty_slot_except(
        &self,
        excluded: Slot,
    ) -> (out: Option<Slot>)
        requires
            self.wf(),
        ensures
            out is Some ==> {
                let slot = out.unwrap();
                &&& slot < self.total_slots()
                &&& slot != excluded
                &&& self.slot_entry(slot) is Empty
                &&& !self@.lookup_map.contains_value(slot)
            },
            out is None ==> forall |slot: Slot| #![auto]
                slot < self.total_slots() && slot != excluded
                ==> !(self.slot_entry(slot) is Empty),
    {
        let mut slot: Slot = 0;
        while slot < CACHE_SIZE_RECS
            invariant
                self.wf(),
                slot <= self.total_slots(),
                forall |candidate: Slot| #![auto]
                    candidate < slot && candidate != excluded
                    ==> !(self.slot_entry(candidate) is Empty),
            decreases CACHE_SIZE_RECS - slot,
        {
            if slot != excluded {
                if let IEntry::Empty = self.metadata[slot].entry {
                    proof {
                        reveal(FracCacheImpl::lookup_map_consistent_with_slots);
                        assert(!self.lookup_map@.contains_value(slot));
                    }
                    return Some(slot);
                }
            }
            slot = slot + 1;
        }
        None
    }

    // views might not work if it has to do with handle access
    pub exec fn fetch(&mut self, addr: &IAddress, load: bool) -> (err: FetchErrorCode)
        requires old(self).wf()
        ensures 
            self.wf(),
            self.valid_load_handles_preserved(*old(self)),
            !load ==> !(err is LoadInitiate),
            old(self).entry_available_for_fetch(addr) ==> err is Success,
            (err is Success) ==> old(self).entry_available_for_fetch(addr),
            match err {
                FetchErrorCode::Awaiting => *old(self) == *self,
                FetchErrorCode::Success{slot_handle} => {
                    &&& self.entry_fetched(addr)
                    &&& self.valid_handle(slot_handle)
                    &&& self.lookup_addr_slot(addr) == slot_handle.idx
                    &&& self.valid_write_handle(addr, slot_handle)
                    &&& self@.valid_write(addr@)
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
                FetchErrorCode::NotPresent => {
                    &&& *old(self) == *self
                    &&& !self.entry_fetched(addr)
                },
                FetchErrorCode::LoadInitiate{slot_handle} => {
                    &&& self.entry_fetched(addr)
                    &&& !old(self).entry_fetched(addr)
                    &&& self.valid_load_handle(addr, slot_handle)
                    &&& self.entry_token_unchanged(*old(self))
                    &&& self.entry_fetched_same_except(*old(self), addr)
                    &&& self.entries_same_except(*old(self), slot_handle.idx)
                    &&& forall |read_addr: Address, data: RawPage|
                        old(self)@.valid_read(read_addr, data)
                        ==> self@.valid_read(read_addr, data)
                    &&& forall |read_addr: Address, data: RawPage|
                        self@.valid_read(read_addr, data)
                        ==> old(self)@.valid_read(read_addr, data)
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
                        assert(!old(self).entry_available_for_fetch(addr));
                        Self::valid_load_handles_preserved_if_maps_same(*old(self), *self);
                    }
                    return FetchErrorCode::Awaiting;
                },
                _ => {},
            }
            match &self.internal_slots[slot] {
                None => {
                    proof {
                        assert(!old(self).entry_available_for_fetch(addr));
                        Self::valid_load_handles_preserved_if_maps_same(
                            *old(self),
                            *self,
                        );
                    }
                    return FetchErrorCode::Awaiting;
                },
                Some(_) => {},
            }
            self.internal_slots.push(None);

            let taken = self.internal_slots.swap_remove(slot);
            let slot_handle = match taken {
                /* Old post-mutation path retained for reference:
                None => { 
                    proof {
                        assert(!old(self).entry_available_for_fetch(addr));
                    }
                    return FetchErrorCode::Awaiting;
                },
                */
                None => unreached::<MutHandle>(),
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
                assert(self.internal_slots[slot as int] is None);
                assert forall |i: int|
                    0 <= i < self.total_slots() && i != slot as int
                    implies self.internal_slots[i]
                        == old(self).internal_slots[i] by {}
                Self::slots_inv_preserved_except(
                    *old(self),
                    *self,
                    slot,
                );
                match old(self).metadata[slot as int].entry {
                    IEntry::Empty{} => { },
                    IEntry::Filled{..} => {
                        reveal(FracCacheImpl::view_entries);
                        assert(old(self).view_entries().contains_key(slot)) by {
                            assert(slot < old(self).total_slots());
                        }
                    },
                    _ => {
                    },
                }
                reveal(FracCacheImpl::entry_fetched);
                reveal(FracCacheImpl::lookup_addr_slot);
                reveal(FracCacheImpl::slot_entry);
                reveal(FracCacheImpl::view_state);
                reveal(FracCacheImpl::view_entries);
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
                reveal(FracCacheImpl::entry_fetched);
            }
            return FetchErrorCode::NotPresent;
        }

        match self.find_unmapped_empty_slot() {
            None => {
                proof {
                    Self::valid_load_handles_preserved_if_maps_same(*old(self), *self);
                }
                return FetchErrorCode::CacheFull;
            },
            Some(slot) => {
                    let status = self.metadata[slot].status;
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

                proof {
                    assert(self.internal_slots[slot as int] is None);
                    assert forall |i: int|
                        0 <= i < self.total_slots() && i != slot as int
                        implies self.internal_slots[i]
                            == old(self).internal_slots[i] by {}
                    Self::slots_inv_preserved_except(
                        *old(self),
                        *self,
                        slot,
                    );
                    let ghost new_slots_mapping = Self::single_slot_mapping(slot, addr@);
                    let ghost updated_entries = Map::new(
                        |s| new_slots_mapping.contains_key(s),
                        |s| Entry::Loading{addr: new_slots_mapping[s]}
                    );
                    assert(self@.entries == old(self)@.entries.union_prefer_right(updated_entries));
                    assert(self@.status_map =~= old(self)@.status_map);
                    Self::prove_lookup_props_after_single_slot_update(
                        *old(self), *self, slot, *addr
                    );
                    Self::prove_load_initiate_transition_single_slot(
                        *old(self), *self, slot, *addr
                    );
                    Self::prove_load_handle_preservation_after_new_mapping(
                        *old(self), *self, *addr, slot_handle.idx
                    );
                    assert forall |read_addr: Address, data: RawPage|
                        old(self)@.valid_read(read_addr, data)
                        implies self@.valid_read(read_addr, data) by {
                        let read_slot = old(self)@.lookup_map[read_addr];
                        assert(read_slot < old(self).total_slots()) by {
                            assert(old(self).lookup_map_inv());
                            assert(old(self).lookup_map@.contains_value(read_slot));
                        }
                        assert(read_slot < self.total_slots());
                        assert(old(self)@.entries[read_slot] is Filled);
                        assert(data == old(self)@.entries[read_slot]->data);
                        assert(read_slot != slot) by {
                            if read_slot == slot {
                                assert(old(self)@.lookup_map.contains_value(slot));
                                assert(false);
                            }
                        }
                        assert(self@.lookup_map[read_addr] == read_slot);
                        assert(!new_slots_mapping.contains_key(read_slot));
                        assert(!updated_entries.contains_key(read_slot));
                        assert(self.entries_same_except(*old(self), slot));
                        Self::slot_entry_same_except(
                            *old(self),
                            *self,
                            slot,
                            read_slot,
                        );
                        reveal(FracCacheImpl::view_entries);
                        assert(self@.entries[read_slot]
                            == old(self)@.entries[read_slot]);
                    }
                    assert forall |read_addr: Address, data: RawPage|
                        self@.valid_read(read_addr, data)
                        implies old(self)@.valid_read(read_addr, data) by {
                        let read_slot = self@.lookup_map[read_addr];
                        assert(read_slot < self.total_slots()) by {
                            assert(self.lookup_map_inv());
                            assert(self.lookup_map@.contains_value(read_slot));
                        }
                        if read_addr == addr@ {
                            assert(self@.lookup_map[read_addr] == slot);
                            assert(self@.entries[slot] is Loading);
                            assert(false);
                        }
                        assert(old(self)@.lookup_map.contains_key(read_addr));
                        assert(old(self)@.lookup_map[read_addr] == read_slot);
                        assert(read_slot != slot) by {
                            if read_slot == slot {
                                assert(self@.lookup_map[addr@] == slot);
                                assert(self@.lookup_map.is_injective());
                                assert(false);
                            }
                        }
                        assert(self.entries_same_except(*old(self), slot));
                        Self::slot_entry_same_except(
                            *old(self),
                            *self,
                            slot,
                            read_slot,
                        );
                        reveal(FracCacheImpl::view_entries);
                        assert(self@.entries[read_slot]
                            == old(self)@.entries[read_slot]);
                    }
                }
                return FetchErrorCode::LoadInitiate{slot_handle};
            },
        }
    }

    pub exec fn reserve_for_write_absent(&mut self, addr: &IAddress) -> (result: ReserveWriteResult)
        requires
            old(self).wf(),
            !old(self).entry_fetched(addr),
        ensures
            self.wf(),
            self.valid_load_handles_preserved(*old(self)),
            self.valid_writeback_handles_preserved(*old(self)),
            match result {
                ReserveWriteResult::Reserved{slot_handle} => {
                    let mapping = map![slot_handle.idx => addr@];
                    let updated_entries = Map::new(
                        |slot| mapping.contains_key(slot),
                        |slot| Entry::Reserved { addr: mapping[slot] },
                    );
                    &&& self.entry_fetched(addr)
                    &&& old(self).slot_entry(slot_handle.idx) is Empty
                    &&& self.slot_entry(slot_handle.idx) is Reserved
                    &&& self.valid_write_handle(addr, slot_handle)
                    &&& self@.valid_write(addr@)
                    &&& self.entry_fetched_same_except(*old(self), addr)
                    &&& self.entries_same_except(*old(self), slot_handle.idx)
                    &&& self.entry_token_unchanged(*old(self))
                    &&& self@.lookup_map
                        == old(self)@.lookup_map.insert(
                            addr@,
                            slot_handle.idx,
                        )
                    &&& self@.entries == old(self)@.entries
                        .union_prefer_right(updated_entries)
                    &&& self@.status_map == old(self)@.status_map
                    &&& forall |read_addr: Address, data: RawPage|
                        read_addr != addr@
                        && old(self)@.valid_read(read_addr, data)
                        ==> self@.valid_read(read_addr, data)
                    &&& Cache::State::next(old(self)@, self@, Cache::Label::Internal)
                },
                ReserveWriteResult::CacheFull => {
                    &&& *old(self) == *self
                    &&& forall |slot: Slot| #![auto]
                        slot < old(self).total_slots()
                        ==> !(old(self).slot_entry(slot) is Empty)
                },
            },
    {
        match self.find_unmapped_empty_slot() {
            None => {
                proof {
                    Self::valid_load_handles_preserved_if_maps_same(*old(self), *self);
                    Self::valid_writeback_handles_preserved_if_same(*old(self), *self);
                    reveal(FracCacheImpl::lookup_map_consistent_with_slots);
                    assert forall |slot: Slot| #![auto]
                        slot < old(self).total_slots()
                        implies !(old(self).slot_entry(slot) is Empty) by {
                        if old(self).slot_entry(slot) is Empty {
                            assert(!old(self)@.lookup_map.contains_value(slot));
                            assert(false);
                        }
                    }
                }
                ReserveWriteResult::CacheFull
            },
            Some(slot) => {
                let status = self.metadata[slot].status;
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

                proof {
                    assert(self.internal_slots[slot as int] is None);
                    assert forall |i: int|
                        0 <= i < self.total_slots() && i != slot as int
                        implies self.internal_slots[i]
                            == old(self).internal_slots[i] by {}
                    Self::slots_inv_preserved_except(
                        *old(self),
                        *self,
                        slot,
                    );
                    let ghost new_slots_mapping = Self::single_slot_mapping(slot, addr@);
                    let ghost updated_entries = Map::new(
                        |s| new_slots_mapping.contains_key(s),
                        |s| Entry::Reserved{addr: new_slots_mapping[s]}
                    );
                    assert(self@.entries == old(self)@.entries.union_prefer_right(updated_entries));
                    assert(self@.status_map =~= old(self)@.status_map);
                    Self::prove_lookup_props_after_single_slot_update(
                        *old(self), *self, slot, *addr
                    );
                    Self::prove_reserve_transition_single_slot(
                        *old(self), *self, slot, *addr
                    );
                    assert forall |read_addr: Address, data: RawPage|
                        read_addr != addr@
                        && old(self)@.valid_read(read_addr, data)
                        implies self@.valid_read(read_addr, data) by {
                        let read_slot = old(self)@.lookup_map[read_addr];
                        assert(read_slot < old(self).total_slots()) by {
                            assert(old(self).lookup_map_inv());
                            assert(old(self).lookup_map@.contains_value(read_slot));
                        }
                        assert(read_slot < self.total_slots());
                        assert(old(self)@.entries[read_slot] is Filled);
                        assert(data == old(self)@.entries[read_slot]->data);
                        assert(read_slot != slot) by {
                            if read_slot == slot {
                                assert(old(self)@.lookup_map.contains_value(slot));
                                assert(false);
                            }
                        }
                        assert(self@.lookup_map[read_addr] == read_slot);
                        assert(!new_slots_mapping.contains_key(read_slot));
                        assert(!updated_entries.contains_key(read_slot));
                        assert(self.entries_same_except(*old(self), slot));
                        Self::slot_entry_same_except(*old(self), *self, slot, read_slot);
                        reveal(FracCacheImpl::view_entries);
                        assert(self@.entries[read_slot] == old(self)@.entries[read_slot]);
                    }
                }
                ReserveWriteResult::Reserved{slot_handle}
            },
        }
    }

    pub exec fn reserve_two_for_write_absent(
        &mut self,
        first_addr: &IAddress,
        second_addr: &IAddress,
    ) -> (result: ReserveTwoWriteResult)
        requires
            old(self).wf(),
            first_addr != second_addr,
            !old(self).entry_fetched(first_addr),
            !old(self).entry_fetched(second_addr),
        ensures
            self.wf(),
            self.valid_load_handles_preserved(*old(self)),
            match result {
                ReserveTwoWriteResult::Reserved {
                    first_handle,
                    second_handle,
                } => {
                    &&& first_handle.idx != second_handle.idx
                    &&& self.slot_entry(first_handle.idx) is Reserved
                    &&& self.slot_entry(second_handle.idx) is Reserved
                    &&& self.valid_write_handle(first_addr, first_handle)
                    &&& self.valid_write_handle(second_addr, second_handle)
                    &&& self@.valid_write(first_addr@)
                    &&& self@.valid_write(second_addr@)
                    &&& forall |read_addr: Address, data: RawPage|
                        read_addr != first_addr@
                        && read_addr != second_addr@
                        && old(self)@.valid_read(read_addr, data)
                        ==> self@.valid_read(read_addr, data)
                    &&& Cache::State::next(
                        old(self)@,
                        self@,
                        Cache::Label::Internal,
                    )
                },
                ReserveTwoWriteResult::CacheFull => {
                    *self == *old(self)
                },
            },
    {
        let first_slot = match self.find_unmapped_empty_slot() {
            Some(slot) => slot,
            None => return ReserveTwoWriteResult::CacheFull,
        };
        let second_slot = match self.find_unmapped_empty_slot_except(
            first_slot,
        ) {
            Some(slot) => slot,
            None => return ReserveTwoWriteResult::CacheFull,
        };
        let ghost cache0 = *self;
        let first_handle = match self.reserve_for_write_absent(first_addr) {
            ReserveWriteResult::Reserved { slot_handle } => {
                proof {
                    assert(self.entries_same_except(
                        cache0,
                        slot_handle.idx,
                    ));
                    assert(self.entry_token_unchanged(cache0));
                    assert(cache0.slot_entry(slot_handle.idx) is Empty);
                }
                slot_handle
            },
            ReserveWriteResult::CacheFull => {
                proof {
                    assert(cache0.slot_entry(first_slot) is Empty);
                    assert(false);
                }
                return ReserveTwoWriteResult::CacheFull;
            },
        };
        let ghost cache1 = *self;
        proof {
            assert(cache1.entries_same_except(
                cache0,
                first_handle.idx,
            ));
            assert(cache1.entry_token_unchanged(cache0));
        }
        let remaining_slot = if first_handle.idx == first_slot {
            second_slot
        } else {
            first_slot
        };
        proof {
            assert(remaining_slot != first_handle.idx);
            assert(cache0.slot_entry(remaining_slot) is Empty);
            assert(cache1.entries_same_except(
                cache0,
                first_handle.idx,
            ));
            assert(first_handle.idx < cache1.total_slots());
            assert(remaining_slot < cache1.total_slots());
            Self::slot_entry_same_except(
                cache0,
                cache1,
                first_handle.idx,
                remaining_slot,
            );
            assert(cache1.slot_entry(remaining_slot) is Empty);
        }
        let second_handle = match self.reserve_for_write_absent(second_addr) {
            ReserveWriteResult::Reserved { slot_handle } => {
                proof {
                    assert(self.entries_same_except(
                        cache1,
                        slot_handle.idx,
                    ));
                    assert(self.entry_token_unchanged(cache1));
                    assert(cache1.slot_entry(slot_handle.idx) is Empty);
                }
                slot_handle
            },
            ReserveWriteResult::CacheFull => {
                proof {
                    assert(cache1.slot_entry(remaining_slot) is Empty);
                    assert(false);
                }
                return ReserveTwoWriteResult::CacheFull;
            },
        };
        proof {
            assert(self.entries_same_except(cache1, second_handle.idx));
            assert(self.entry_token_unchanged(cache1));
            let first_slot = first_handle.idx;
            let second_slot = second_handle.idx;
            assert(cache0.slot_entry(first_slot) is Empty);
            assert(cache1.slot_entry(second_slot) is Empty);
            assert(first_slot != second_slot) by {
                if first_slot == second_slot {
                    assert(self.lookup_addr_slot(first_addr) == first_slot);
                    assert(self.lookup_addr_slot(second_addr) == second_slot);
                    reveal(FracCacheImpl::lookup_map_injective);
                    assert(self.lookup_map@.is_injective());
                    assert(first_addr@ != second_addr@);
                }
            }
            assert(self.entry_token_unchanged(cache1));
            assert(self.entries_same_except(cache1, second_slot));
            assert(self.entry_fetched_same_except(cache1, second_addr));
            assert(self.entry_fetched(first_addr));
            assert(self.lookup_addr_slot(first_addr) == first_slot);
            assert(second_slot < self.total_slots());
            assert(first_slot < self.total_slots());
            Self::slot_entry_same_except(
                cache1,
                *self,
                second_slot,
                first_slot,
            );
            assert(self.valid_handle(first_handle)) by {

                assert(self.entry_token_id(first_slot)
                    == cache1.entry_token_id(first_slot));
            }
            assert(self.valid_write_handle(first_addr, first_handle));
            assert(cache0.slot_entry(second_slot) is Empty) by {
                assert(cache1.entries_same_except(cache0, first_slot));
                Self::slot_entry_same_except(
                    cache0,
                    cache1,
                    first_slot,
                    second_slot,
                );
            }

            let first_mapping = map![first_slot => first_addr@];
            let second_mapping = map![second_slot => second_addr@];
            let mapping = map![
                first_slot => first_addr@,
                second_slot => second_addr@
            ];
            let updated_entries = Map::new(
                |slot| mapping.contains_key(slot),
                |slot| Entry::Reserved { addr: mapping[slot] },
            );
            assert(cache0@.valid_new_slots_mapping(mapping)) by {

                assert(mapping.is_injective()) by {
                    assert forall |left: Slot, right: Slot|
                        mapping.contains_key(left)
                        && mapping.contains_key(right)
                        && #[trigger] mapping[left]
                            == #[trigger] mapping[right]
                        implies left == right by {}
                }
                assert(mapping.dom() <= cache0@.entries.dom());
                assert(mapping.values().disjoint(
                    cache0@.lookup_map.dom(),
                ));
                assert forall |slot: Slot|
                    #[trigger] mapping.contains_key(slot)
                    implies cache0@.entries[slot] is Empty by {
                    reveal(FracCacheImpl::view_entries);
                    if slot == first_slot {
                        assert(cache0.slot_entry(first_slot) is Empty);
                    } else {
                        assert(slot == second_slot);
                        assert(cache0.slot_entry(second_slot) is Empty);
                    }
                }
            }
            assert(self@.status_map == cache0@.status_map);
            assert(self@.entries
                == cache0@.entries.union_prefer_right(updated_entries)) by {
                assert_maps_equal!(
                    self@.entries,
                    cache0@.entries.union_prefer_right(updated_entries),
                    slot => {}
                );
            }
            assert(self@.lookup_map
                == cache0@.lookup_map.union_prefer_right(
                    mapping.invert(),
                )) by {
                assert(mapping.invert()
                    == map![
                        first_addr@ => first_slot,
                        second_addr@ => second_slot
                    ]) by {

                    assert(mapping.is_injective());
                    assert(mapping.contains_pair(
                        first_slot,
                        first_addr@,
                    ));
                    assert(mapping.contains_pair(
                        second_slot,
                        second_addr@,
                    ));
                    assert_maps_equal!(
                        mapping.invert(),
                        map![
                            first_addr@ => first_slot,
                            second_addr@ => second_slot
                        ],
                        addr => {}
                    );
                }
                assert_maps_equal!(
                    self@.lookup_map,
                    cache0@.lookup_map.union_prefer_right(
                        mapping.invert(),
                    ),
                    addr => {}
                );
            }
            reveal(Cache::State::next);
            reveal(Cache::State::next_by);
            assert(Cache::State::next_by(
                cache0@,
                self@,
                Cache::Label::Internal,
                Cache::Step::reserve(mapping),
            ));
            Self::valid_load_handles_preserved_transitive(
                cache0,
                cache1,
                *self,
            );
            assert forall |read_addr: Address, data: RawPage|
                read_addr != first_addr@
                && read_addr != second_addr@
                && cache0@.valid_read(read_addr, data)
                implies self@.valid_read(read_addr, data) by {
                assert(cache1@.valid_read(read_addr, data));
            }
        }
        ReserveTwoWriteResult::Reserved {
            first_handle,
            second_handle,
        }
    }

    proof fn prove_prepared_single_reserve(
        pre: Cache::State,
        post: Cache::State,
        addr: Address,
        slot: Slot,
    )
        requires
            pre.entries.contains_key(slot),
            pre.entries[slot] is Empty,
            !pre.lookup_map.contains_key(addr),
            post.entries == pre.entries.insert(
                slot,
                Entry::Reserved { addr },
            ),
            post.status_map == pre.status_map,
            post.lookup_map == pre.lookup_map.insert(addr, slot),
        ensures
            post.valid_write(addr),
            Cache::State::next(pre, post, Cache::Label::Internal),
            forall |read_addr: Address, data: RawPage|
                read_addr != addr
                && pre.valid_read(read_addr, data)
                ==> post.valid_read(read_addr, data),
    {
        let mapping = map![slot => addr];
        let updated_entries = Map::new(
            |candidate: Slot| mapping.contains_key(candidate),
            |candidate: Slot| Entry::Reserved {
                addr: mapping[candidate],
            },
        );
        assert(pre.valid_new_slots_mapping(mapping)) by {
            assert(mapping.is_injective());
        }
        assert(post.entries
            == pre.entries.union_prefer_right(updated_entries)) by {
            assert_maps_equal!(
                post.entries,
                pre.entries.union_prefer_right(updated_entries),
                candidate => {}
            );
        }
        assert(mapping.invert() == map![addr => slot]) by {

            assert(mapping.is_injective());
            assert(mapping.contains_pair(slot, addr));
            assert_maps_equal!(mapping.invert(), map![addr => slot], candidate => {});
        }
        assert(post.lookup_map
            == pre.lookup_map.union_prefer_right(mapping.invert())) by {
            assert_maps_equal!(
                post.lookup_map,
                pre.lookup_map.union_prefer_right(mapping.invert()),
                candidate => {}
            );
        }
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        assert(Cache::State::next_by(
            pre,
            post,
            Cache::Label::Internal,
            Cache::Step::reserve(mapping),
        ));
        assert(post.valid_write(addr));
        assert forall |read_addr: Address, data: RawPage|
            read_addr != addr
            && pre.valid_read(read_addr, data)
            implies post.valid_read(read_addr, data) by {
            assert(pre.lookup_map[read_addr] != slot) by {
                if pre.lookup_map[read_addr] == slot {
                    assert(pre.entries[slot] is Filled);
                    assert(false);
                }
            }
        }
    }

    pub exec fn prepare_two_for_write(
        &mut self,
        first_addr: &IAddress,
        second_addr: &IAddress,
    ) -> (result: PrepareTwoWriteResult)
        requires
            old(self).wf(),
            old(self)@.inv(),
            first_addr != second_addr,
        ensures
            self.wf(),
            self.valid_load_handles_preserved(*old(self)),
            match result {
                PrepareTwoWriteResult::Ready {
                    first_handle,
                    second_handle,
                    prepared_cache,
                } => {
                    &&& first_handle.idx != second_handle.idx
                    &&& self.entry_fetched(first_addr)
                    &&& self.entry_fetched(second_addr)
                    &&& self.valid_write_handle(first_addr, first_handle)
                    &&& self.valid_write_handle(second_addr, second_handle)
                    &&& prepared_cache@ == self.restored_two_write_state(
                        first_addr,
                        first_handle,
                        second_addr,
                        second_handle,
                    )
                    &&& prepared_cache@.valid_write(first_addr@)
                    &&& prepared_cache@.valid_write(second_addr@)
                    &&& prepared_cache@.inv()
                    &&& self.prepared_two_write_state_matches(
                        prepared_cache@,
                        first_addr,
                        first_handle.idx,
                        second_addr,
                        second_handle.idx,
                    )
                    &&& Cache::State::next(
                        old(self)@,
                        prepared_cache@,
                        Cache::Label::Internal,
                    )
                    &&& forall |read_addr: Address, data: RawPage|
                        read_addr != first_addr@
                        && read_addr != second_addr@
                        && old(self)@.valid_read(read_addr, data)
                        ==> prepared_cache@.valid_read(read_addr, data)
                },
                PrepareTwoWriteResult::CacheFull
                | PrepareTwoWriteResult::Blocked => {
                    self@ == old(self)@
                },
            },
    {
        let ghost cache0 = *self;
        let first_present = self.contains_addr(first_addr);
        let second_present = self.contains_addr(second_addr);

        if !first_present && !second_present {
            return match self.reserve_two_for_write_absent(
                first_addr,
                second_addr,
            ) {
                ReserveTwoWriteResult::Reserved {
                    first_handle,
                    second_handle,
                } => {
                    let ghost prepared = self.restored_two_write_state(
                        first_addr,
                        first_handle,
                        second_addr,
                        second_handle,
                    );
                    proof {
                        Self::restored_two_write_state_matches(
                            self,
                            first_addr,
                            first_handle,
                            second_addr,
                            second_handle,
                        );
                        assert(prepared == self@) by {
                            assert(self.slot_entry(first_handle.idx)
                                is Reserved);
                            assert(self.slot_entry(second_handle.idx)
                                is Reserved);
                            assert_maps_equal!(prepared.entries, self@.entries, slot => {});
                        }
                        Cache::State::inv_next(
                            cache0@,
                            prepared,
                            Cache::Label::Internal,
                        );
                    }
                    PrepareTwoWriteResult::Ready {
                        first_handle,
                        second_handle,
                        prepared_cache: Ghost(prepared),
                    }
                },
                ReserveTwoWriteResult::CacheFull => {
                    PrepareTwoWriteResult::CacheFull
                },
            };
        }

        if first_present {
            let first_handle = match self.fetch(first_addr, false) {
                FetchErrorCode::Success { slot_handle } => slot_handle,
                FetchErrorCode::CacheFull => {
                    return PrepareTwoWriteResult::CacheFull;
                },
                FetchErrorCode::Awaiting
                | FetchErrorCode::NotPresent => {
                    return PrepareTwoWriteResult::Blocked;
                },
                FetchErrorCode::LoadInitiate { slot_handle: _ } => {
                    proof { assert(false); }
                    return PrepareTwoWriteResult::Blocked;
                },
            };
            let ghost cache1 = *self;
            if second_present {
                let second_handle = match self.fetch(second_addr, false) {
                    FetchErrorCode::Success { slot_handle } => slot_handle,
                    FetchErrorCode::CacheFull => {
                        self.handle_release(first_addr, first_handle);
                        proof { assert(self@ == cache0@); }
                        return PrepareTwoWriteResult::CacheFull;
                    },
                    FetchErrorCode::Awaiting
                    | FetchErrorCode::NotPresent => {
                        self.handle_release(first_addr, first_handle);
                        proof { assert(self@ == cache0@); }
                        return PrepareTwoWriteResult::Blocked;
                    },
                    FetchErrorCode::LoadInitiate { slot_handle: _ } => {
                        proof { assert(false); }
                        self.handle_release(first_addr, first_handle);
                        return PrepareTwoWriteResult::Blocked;
                    },
                };
                proof {
                    Self::valid_write_handle_preserved_except(
                        cache1,
                        *self,
                        first_addr,
                        first_handle,
                        second_addr,
                        second_handle.idx,
                    );
                }
                let ghost prepared = self.restored_two_write_state(
                    first_addr,
                    first_handle,
                    second_addr,
                    second_handle,
                );
                proof {
                    assert(first_handle.idx != second_handle.idx);
                    Self::restored_two_write_state_matches(
                        self,
                        first_addr,
                        first_handle,
                        second_addr,
                        second_handle,
                    );
                    assert(prepared == cache0@) by {
                        assert_maps_equal!(prepared.entries, cache0@.entries, slot => {});
                    }
                    reveal(Cache::State::next);
                    reveal(Cache::State::next_by);
                    assert(Cache::State::next_by(
                        cache0@,
                        prepared,
                        Cache::Label::Internal,
                        Cache::Step::noop(),
                    ));
                    Cache::State::inv_next(
                        cache0@,
                        prepared,
                        Cache::Label::Internal,
                    );
                    Self::valid_load_handles_preserved_transitive(
                        cache0,
                        cache1,
                        *self,
                    );
                }
                return PrepareTwoWriteResult::Ready {
                    first_handle,
                    second_handle,
                    prepared_cache: Ghost(prepared),
                };
            } else {
                let second_handle = match self.reserve_for_write_absent(
                    second_addr,
                ) {
                    ReserveWriteResult::Reserved { slot_handle } => slot_handle,
                    ReserveWriteResult::CacheFull => {
                        self.handle_release(first_addr, first_handle);
                        proof { assert(self@ == cache0@); }
                        return PrepareTwoWriteResult::CacheFull;
                    },
                };
                proof {
                    Self::valid_write_handle_preserved_except(
                        cache1,
                        *self,
                        first_addr,
                        first_handle,
                        second_addr,
                        second_handle.idx,
                    );
                }
                let ghost prepared = self.restored_two_write_state(
                    first_addr,
                    first_handle,
                    second_addr,
                    second_handle,
                );
                proof {
                    Self::restored_two_write_state_matches(
                        self,
                        first_addr,
                        first_handle,
                        second_addr,
                        second_handle,
                    );
                    assert(cache0@.entries.contains_key(second_handle.idx));
                    assert(cache0@.entries[second_handle.idx] is Empty) by {
                        assert(cache1.slot_entry(second_handle.idx) is Empty);
                        assert(second_handle.idx != first_handle.idx);
                        assert(cache1.entries_same_except(
                            cache0,
                            first_handle.idx,
                        ));
                        Self::slot_entry_same_except(
                            cache0,
                            cache1,
                            first_handle.idx,
                            second_handle.idx,
                        );
                        reveal(FracCacheImpl::view_entries);
                    }
                    assert(!cache0@.lookup_map.contains_key(second_addr@));
                    assert(prepared.entries == cache0@.entries.insert(
                        second_handle.idx,
                        Entry::Reserved { addr: second_addr@ },
                    )) by {
                        assert_maps_equal!(
                            prepared.entries,
                            cache0@.entries.insert(
                                second_handle.idx,
                                Entry::Reserved { addr: second_addr@ },
                            ),
                            slot => {}
                        );
                    }
                    assert(prepared.status_map == cache0@.status_map);
                    assert(prepared.lookup_map == cache0@.lookup_map.insert(
                        second_addr@,
                        second_handle.idx,
                    ));
                    Self::prove_prepared_single_reserve(
                        cache0@,
                        prepared,
                        second_addr@,
                        second_handle.idx,
                    );
                    Cache::State::inv_next(
                        cache0@,
                        prepared,
                        Cache::Label::Internal,
                    );
                    Self::valid_load_handles_preserved_transitive(
                        cache0,
                        cache1,
                        *self,
                    );
                }
                return PrepareTwoWriteResult::Ready {
                    first_handle,
                    second_handle,
                    prepared_cache: Ghost(prepared),
                };
            }
        }

        let second_handle = match self.fetch(second_addr, false) {
            FetchErrorCode::Success { slot_handle } => slot_handle,
            FetchErrorCode::CacheFull => {
                return PrepareTwoWriteResult::CacheFull;
            },
            FetchErrorCode::Awaiting | FetchErrorCode::NotPresent => {
                return PrepareTwoWriteResult::Blocked;
            },
            FetchErrorCode::LoadInitiate { slot_handle: _ } => {
                proof { assert(false); }
                return PrepareTwoWriteResult::Blocked;
            },
        };
        let ghost cache1 = *self;
        let first_handle = match self.reserve_for_write_absent(first_addr) {
            ReserveWriteResult::Reserved { slot_handle } => slot_handle,
            ReserveWriteResult::CacheFull => {
                self.handle_release(second_addr, second_handle);
                proof { assert(self@ == cache0@); }
                return PrepareTwoWriteResult::CacheFull;
            },
        };
        proof {
            Self::valid_write_handle_preserved_except(
                cache1,
                *self,
                second_addr,
                second_handle,
                first_addr,
                first_handle.idx,
            );
        }
        let ghost prepared = self.restored_two_write_state(
            first_addr,
            first_handle,
            second_addr,
            second_handle,
        );
        proof {
            Self::restored_two_write_state_matches(
                self,
                first_addr,
                first_handle,
                second_addr,
                second_handle,
            );
            assert(cache0@.entries.contains_key(first_handle.idx));
            assert(cache0@.entries[first_handle.idx] is Empty) by {
                assert(cache1.slot_entry(first_handle.idx) is Empty);
                assert(first_handle.idx != second_handle.idx);
                assert(cache1.entries_same_except(
                    cache0,
                    second_handle.idx,
                ));
                Self::slot_entry_same_except(
                    cache0,
                    cache1,
                    second_handle.idx,
                    first_handle.idx,
                );
                reveal(FracCacheImpl::view_entries);
            }
            assert(!cache0@.lookup_map.contains_key(first_addr@));
            assert(prepared.entries == cache0@.entries.insert(
                first_handle.idx,
                Entry::Reserved { addr: first_addr@ },
            )) by {
                assert_maps_equal!(
                    prepared.entries,
                    cache0@.entries.insert(
                        first_handle.idx,
                        Entry::Reserved { addr: first_addr@ },
                    ),
                    slot => {}
                );
            }
            assert(prepared.status_map == cache0@.status_map);
            assert(prepared.lookup_map == cache0@.lookup_map.insert(
                first_addr@,
                first_handle.idx,
            ));
            Self::prove_prepared_single_reserve(
                cache0@,
                prepared,
                first_addr@,
                first_handle.idx,
            );
            Cache::State::inv_next(
                cache0@,
                prepared,
                Cache::Label::Internal,
            );
            Self::valid_load_handles_preserved_transitive(
                cache0,
                cache1,
                *self,
            );
        }
        PrepareTwoWriteResult::Ready {
            first_handle,
            second_handle,
            prepared_cache: Ghost(prepared),
        }
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
            &&& forall |read_addr: Address, data: RawPage|
                old(self)@.valid_read(read_addr, data)
                ==> self@.valid_read(read_addr, data)
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
            assert(rec@.len() == PAGE_SIZE_BYTES);
            assert forall |i: int|
                0 <= i < self.total_slots() && i != idx as int
                implies self.internal_slots[i]
                    == old(self).internal_slots[i] by {}
            Self::slots_inv_preserved_except(
                *old(self),
                *self,
                idx,
            );
            let resp = DiskResponse::ReadResp{data: handle.rec@};
            let cache_lbl = Cache::Label::DiskOps{requests: set!{}, responses: map!{addr@ => resp}};

            let slot_addr_map = old(self)@.lookup_map.restrict(cache_lbl->responses.dom()).invert();
            assert(slot_addr_map =~= map!{idx => addr@}) by {
                // the restrict map has exactly the pair (addr@ -> idx), so its invert is (idx -> addr@)
                assert(old(self)@.lookup_map.restrict(cache_lbl->responses.dom()).contains_pair(addr@, idx));

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
            assert(self@.entries
                == old(self)@.entries.union_prefer_right(updated_entries)) by {
                assert_maps_equal!(
                    self@.entries,
                    old(self)@.entries.union_prefer_right(updated_entries),
                    slot => {}
                );
            }
            assert(self@.status_map =~= old(self)@.status_map.union_prefer_right(updated_status_map));
            assert(self@.lookup_map == old(self)@.lookup_map);
            reveal(FracCacheImpl::wf);
            reveal(FracCacheImpl::lookup_map_inv);
            reveal(FracCacheImpl::view_state);
            reveal(FracCacheImpl::view_entries);
            assert forall |read_addr: Address, data: RawPage|
                old(self)@.valid_read(read_addr, data)
                implies self@.valid_read(read_addr, data) by {
                let read_slot = old(self)@.lookup_map[read_addr];
                assert(old(self)@.lookup_map.contains_key(read_addr));
                assert(old(self)@.lookup_map.contains_value(read_slot));
                assert(old(self).lookup_map_inv());
                assert(read_slot < old(self).total_slots());
                if read_addr == addr@ {

                    reveal(FracCacheImpl::entry_fetched);
                    reveal(FracCacheImpl::lookup_addr_slot);
                    assert(read_slot == idx);
                    assert(old(self)@.entries[read_slot] is Loading);
                    assert(false);
                } else {
                    assert(old(self)@.entries.contains_key(read_slot));
                    assert(read_slot != idx) by {
                        assert(old(self)@.lookup_map.is_injective());
                    }
                    assert(self.internal_slots[read_slot as int]
                        == old(self).internal_slots[read_slot as int]);
                    assert(self.metadata[read_slot as int]
                        == old(self).metadata[read_slot as int]);
                    assert(self@.entries[read_slot]
                        == old(self)@.entries[read_slot]);
                }
            }
            reveal(Cache::State::next_by);
            assert(Cache::State::next_by(old(self)@, self@, cache_lbl, Cache::Step::load_complete()));
            reveal(Cache::State::next);
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
            &&& self.entry_fetched(addr)
            &&& self.lookup_addr_slot(addr) == handle.idx
            &&& self.valid_load_handles_preserved(*old(self))
            &&& self.valid_writeback_handles_preserved(*old(self))
            &&& self.entries_same_except(*old(self), handle.idx)
            &&& self@.lookup_map == old(self)@.lookup_map
            &&& self@.valid_read(addr@, handle.rec@)
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
            assert(rec@.len() == PAGE_SIZE_BYTES);
            assert forall |i: int|
                0 <= i < self.total_slots() && i != idx as int
                implies self.internal_slots[i]
                    == old(self).internal_slots[i] by {}
            Self::slots_inv_preserved_except(
                *old(self),
                *self,
                idx,
            );
            let cache_lbl = cache_write_label(addr, recv);
            let updated_entries = old(self)@.write_updated_entries(cache_lbl->writes);
            let updated_status_map = old(self)@.write_updated_status(cache_lbl->writes);
            let slot_addr_map = old(self)@.lookup_map.restrict(cache_lbl->writes.dom()).invert();
            assert(slot_addr_map =~= map!{idx => addr@}) by {
                assert(old(self)@.lookup_map.restrict(cache_lbl->writes.dom()).contains_pair(addr@, idx));
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
            assert(self@.lookup_map == old(self)@.lookup_map) by {
                assert_maps_equal!(
                    self@.lookup_map,
                    old(self)@.lookup_map,
                    candidate => {}
                );
            }
            assert(self@.lookup_map[addr@] == idx);
            assert(self@.entries[idx]
                == Entry::Filled { addr: addr@, data: recv });
            assert(self@.valid_read(addr@, recv));
            reveal(Cache::State::next_by);
            assert(Cache::State::next_by(old(self)@, self@, cache_lbl, Cache::Step::access()));
            reveal(Cache::State::next);
        }
    }

    pub proof fn two_write_releases_refine_access(
        prepared_cache: Cache::State,
        borrowed_cache: Self,
        after_first: Self,
        after_second: Self,
        first_addr: &IAddress,
        first_slot: Slot,
        first_data: RawPage,
        second_addr: &IAddress,
        second_slot: Slot,
        second_data: RawPage,
    )
        requires
            borrowed_cache.wf(),
            first_addr != second_addr,
            first_slot != second_slot,
            borrowed_cache.prepared_two_write_state_matches(
                prepared_cache,
                first_addr,
                first_slot,
                second_addr,
                second_slot,
            ),
            prepared_cache.valid_write(first_addr@),
            prepared_cache.valid_write(second_addr@),
            prepared_cache.inv(),
            borrowed_cache@.valid_write(first_addr@),
            borrowed_cache@.valid_write(second_addr@),
            Cache::State::next(
                borrowed_cache@,
                after_first@,
                Cache::Label::Access {
                    reads: Map::empty(),
                    writes: map![first_addr@ => first_data],
                },
            ),
            Cache::State::next(
                after_first@,
                after_second@,
                Cache::Label::Access {
                    reads: Map::empty(),
                    writes: map![second_addr@ => second_data],
                },
            ),
        ensures
            Cache::State::next(
                prepared_cache,
                after_second@,
                Cache::Label::Access {
                    reads: Map::empty(),
                    writes: map![
                        first_addr@ => first_data,
                        second_addr@ => second_data
                    ],
                },
            ),
            after_second@.valid_read(first_addr@, first_data),
            after_second@.valid_read(second_addr@, second_data),
    {
        reveal(FracCacheImpl::view_state);
        reveal(FracCacheImpl::view_entries);
        assert(prepared_cache.lookup_map == borrowed_cache@.lookup_map);
        assert(prepared_cache.status_map == borrowed_cache@.status_map);
        assert(prepared_cache.entries == borrowed_cache@.entries
            .insert(first_slot, prepared_cache.entries[first_slot])
            .insert(second_slot, prepared_cache.entries[second_slot])) by {
            assert_maps_equal!(
                prepared_cache.entries,
                borrowed_cache@.entries.insert(
                    first_slot,
                    prepared_cache.entries[first_slot],
                ).insert(
                    second_slot,
                    prepared_cache.entries[second_slot],
                ),
                slot => {}
            );
        }
        assert(prepared_cache.entries[first_slot].get_addr()
            == borrowed_cache@.entries[first_slot].get_addr());
        assert(prepared_cache.entries[second_slot].get_addr()
            == borrowed_cache@.entries[second_slot].get_addr());
        assert((prepared_cache.entries[first_slot] is Filled)
            == (borrowed_cache@.entries[first_slot] is Filled));
        assert((prepared_cache.entries[second_slot] is Filled)
            == (borrowed_cache@.entries[second_slot] is Filled));
        assert((prepared_cache.entries[first_slot] is Empty)
            == (borrowed_cache@.entries[first_slot] is Empty));
        assert((prepared_cache.entries[second_slot] is Empty)
            == (borrowed_cache@.entries[second_slot] is Empty));
        Cache::State::two_borrowed_write_slots_preserve_inv(
            prepared_cache,
            borrowed_cache@,
            first_slot,
            second_slot,
        );
        let first_write = map![first_addr@ => first_data];
        let second_write = map![second_addr@ => second_data];
        let writes = map![
            first_addr@ => first_data,
            second_addr@ => second_data
        ];
        assert(first_write.union_prefer_right(second_write) == writes) by {
            assert_maps_equal!(
                first_write.union_prefer_right(second_write),
                writes,
                addr => {}
            );
        }
        Cache::State::access_compose_disjoint_writes(
            borrowed_cache@,
            after_first@,
            after_second@,
            first_write,
            second_write,
        );
        assert(Cache::State::next(
            borrowed_cache@,
            after_second@,
            Cache::Label::Access {
                reads: Map::empty(),
                writes,
            },
        ));
        Cache::State::access_from_two_borrowed_write_slots(
            prepared_cache,
            borrowed_cache@,
            after_second@,
            first_addr@,
            first_slot,
            first_data,
            second_addr@,
            second_slot,
            second_data,
        );
        Cache::State::access_write_valid(
            prepared_cache,
            after_second@,
            Map::empty(),
            writes,
            first_addr@,
        );
        Cache::State::access_write_valid(
            prepared_cache,
            after_second@,
            Map::empty(),
            writes,
            second_addr@,
        );
    }

    // Returns a borrowed filled-page handle without modeling a cache write transition.
    // This is the borrow/restore path used by read-style flows that may mutate bytes in exec code
    // but are not intended to count as an abstract cache Access{writes} step.
    pub exec fn handle_release(&mut self, addr: &IAddress, handle: MutHandle)
        requires 
            old(self).wf(),
            old(self).valid_handle(handle),
            old(self).entry_fetched(addr),
            old(self).lookup_addr_slot(addr) == handle.idx,
            old(self).slot_entry(handle.idx) == (IEntry::Filled{addr: *addr}),
        ensures ({
            &&& self.release_common_post(*old(self), addr)
            &&& self.valid_load_handles_preserved(*old(self))
            &&& self.filled_entry_restored_from_handle(*old(self), addr, handle.idx, handle.rec@)
            &&& self.entry_available_for_fetch(addr)
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
            assert(rec@.len() == PAGE_SIZE_BYTES);
            assert forall |i: int|
                0 <= i < self.total_slots() && i != idx as int
                implies self.internal_slots[i]
                    == old(self).internal_slots[i] by {}
            Self::slots_inv_preserved_except(
                *old(self),
                *self,
                idx,
            );
            reveal(FracCacheImpl::view_entries);
            assert(self@.entries == old(self)@.entries.insert(idx, Entry::Filled{addr: addr@, data: rec@}));
            reveal(FracCacheImpl::entry_available_for_fetch);
            reveal(FracCacheImpl::lookup_addr_slot);
            assert(self.lookup_map@ == old(self).lookup_map@);
            assert(self.lookup_addr_slot(addr) == idx);
            assert(self.internal_slots[idx as int] is Some);
            assert(!(self.metadata[idx as int].status is Writeback));
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
                    &&& Cache::State::next(self@, self@, Cache::Label::EvictableCheck{aus: set![addr@.au]})
                },
                WritebackAcquireResult::NotDirty => {
                    &&& *old(self) == *self
                    &&& Cache::State::next(self@, self@, Cache::Label::EvictableCheck{aus: set![addr@.au]})
                },
                WritebackAcquireResult::Busy => {
                    &&& *old(self) == *self
                }
            }
        }),
    {
        if !self.lookup_map.contains_key(addr) {
            if !self.evictable(addr) {
                proof {
                    Self::valid_writeback_handles_preserved_if_same(*old(self), *self);
                }
                return WritebackAcquireResult::Busy;
            }
            proof {
                let lbl = Cache::Label::EvictableCheck{aus: set![addr@.au]};
                assert(!self.lookup_map@.contains_key(addr@));
                assert(Cache::State::evictable(self@, self@, lbl));
                assert(Cache::State::next(self@, self@, lbl));
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
                        if entry_addr != *addr {
                            proof {
                                Self::valid_writeback_handles_preserved_if_same(*old(self), *self);
                            }
                            return WritebackAcquireResult::Busy;
                        }
                        if !self.evictable(addr) {
                            proof {
                                Self::valid_writeback_handles_preserved_if_same(*old(self), *self);
                            }
                            return WritebackAcquireResult::Busy;
                        }
                        proof {
                            let lbl = Cache::Label::EvictableCheck{aus: set![addr@.au]};
                            assert(Cache::State::evictable(self@, self@, lbl));
                            assert(Cache::State::next(self@, self@, lbl));
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
                if entry_addr != *addr {
                    proof {
                        Self::valid_writeback_handles_preserved_if_same(*old(self), *self);
                    }
                    return WritebackAcquireResult::Busy;
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
            assert(self.internal_slots[slot as int] is None);
            assert forall |i: int|
                0 <= i < self.total_slots() && i != slot as int
                implies self.internal_slots[i]
                    == old(self).internal_slots[i] by {}
            Self::slots_inv_preserved_except(
                *old(self),
                *self,
                slot,
            );
            reveal(Cache::State::next_by);
            reveal(Cache::State::next);
            let req = DiskRequest::WriteReq{to: addr@, data: rec@};
            let lbl = Cache::Label::DiskOps{requests: set![req], responses: map!{}};

            // Facts established by this acquired branch.
            assert(old(self)@.lookup_map == self@.lookup_map);
            assert(old(self)@.entries == self@.entries);
            assert(old(self)@.status_map[handle.idx] is Dirty);
            assert(self@.status_map == old(self)@.status_map.insert(handle.idx, Status::Writeback));
            FracCacheImpl::valid_writeback_handle_model_entry(self, addr, handle);

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
                        }
                        assert(writeback_slots.contains(s));
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
            &&& forall |read_addr: Address, data: RawPage|
                old(self)@.valid_read(read_addr, data)
                ==> self@.valid_read(read_addr, data)
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
            assert(rec@.len() == PAGE_SIZE_BYTES);
            assert forall |i: int|
                0 <= i < self.total_slots() && i != idx as int
                implies self.internal_slots[i]
                    == old(self).internal_slots[i] by {}
            Self::slots_inv_preserved_except(
                *old(self),
                *self,
                idx,
            );
            let resp = DiskResponse::WriteResp{};
            let cache_lbl = Cache::Label::DiskOps{requests: set!{}, responses: map!{addr@ => resp}};

            let slot_addr_map = old(self)@.lookup_map.restrict(cache_lbl->responses.dom()).invert();
            assert(slot_addr_map =~= map!{idx => addr@}) by {
                assert(old(self)@.lookup_map.restrict(cache_lbl->responses.dom()).contains_pair(addr@, idx));
            }

            let updated_status_map = Map::new(
                |slot| slot_addr_map.contains_key(slot),
                |slot| Status::Clean
            );
            assert(self@.entries =~= old(self)@.entries);
            assert(self@.lookup_map == old(self)@.lookup_map);
            assert forall |read_addr: Address, data: RawPage|
                old(self)@.valid_read(read_addr, data)
                implies self@.valid_read(read_addr, data) by {}
            assert(self@.status_map =~= old(self)@.status_map.union_prefer_right(updated_status_map));
            reveal(Cache::State::next_by);
            assert(Cache::State::next_by(old(self)@, self@, cache_lbl, Cache::Step::writeback_complete()));
            reveal(Cache::State::next);
        }
    }
}

}//verus!
