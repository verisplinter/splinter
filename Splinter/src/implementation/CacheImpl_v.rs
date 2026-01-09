// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use vstd::hash_map::HashMapWithView;
use crate::abstract_system::MsgHistory_v::{MsgHistory, KeyedMessage};
use crate::abstract_system::StampedMap_v::*;
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::marshalling::KeyedMessageFormat_v::KeyedMessageFormat;
use crate::spec::MapSpec_t::{ID};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::implementation::OverflowFiction_v::*;
use crate::implementation::CachedJournal_v::CachedJournal;
use crate::disk::GenericDisk_v::{Address, IAddress};
use crate::implementation::CachedJournal_v;
use crate::implementation::JournalTypes_v::AJournal;
use crate::implementation::JournalTypes_v::ILsn;
use crate::implementation::JournalModel_v::LsnAddrIndex;
use crate::spec::AsyncDisk_t::RawPage;
use crate::implementation::Cache_v::*;
use vstd::std_specs::hash::obeys_key_model;
use vstd::cell::{PCell, PointsTo};

verus!{

pub const PAGE_SIZE_BYTES: usize = 4096;
pub const CACHE_SIZE_PAGES: usize = 1000;

pub type IRawPage = Vec<u8>;

pub struct Handle {
    slot: Slot,
    page: IRawPage,
    _releasable: Ghost<bool>,
}

impl Handle {
    pub closed spec fn inv(self) -> bool {
        &&& self.slot < CACHE_SIZE_PAGES
        &&& self._releasable@ ==> self.page.len() == PAGE_SIZE_BYTES
    }

    pub closed spec fn releasable(self) -> bool {
        &&& self._releasable@
    }

    pub closed spec fn value(self) -> RawPage
    recommends 
        self.inv(),
        self.releasable(),
    {
        self.page@
    }

    pub closed spec fn slot(self) -> Slot
    {
        self.slot
    }

    // Immutable access

    pub fn borrow(&self) -> (page: &IRawPage)
    requires
        self.inv(),
        self.releasable(),
    ensures
        page.len() == PAGE_SIZE_BYTES,
        page@ == self.value(),
    {
        &self.page
    }

    // Mutable access

    pub fn take(&mut self) -> (page: IRawPage)
        requires
            old(self).inv(),
            old(self).releasable(),
        ensures page.len() == PAGE_SIZE_BYTES,
            self.inv(),
            !self.releasable(),
            page@ == old(self).value(),
            self.slot() == old(self).slot(),
    {
        let mut dummy = vec![];
        std::mem::swap(&mut dummy, &mut self.page);
        self._releasable = Ghost(false);
        assert( dummy.len() == old(self).page.len() );
        dummy
    }

    pub fn replace(&mut self, page: IRawPage)
    requires
        page.len() == PAGE_SIZE_BYTES,
        old(self).inv(),
        !old(self).releasable(),
    ensures
        self.inv(),
        self.releasable(),
        self.value() == page@,
        self.slot() == old(self).slot(),
    {
        self.page = page;
        self._releasable = Ghost(true);
    }
}

#[derive(Clone, Copy)]
pub enum IEntry{
    Empty,
    Reserved{addr: IAddress},
    Loading{addr: IAddress}, 
    Filled{addr: IAddress},
}

pub struct Metadata {
    entry: IEntry,
    status: Status,
}

pub struct CacheImpl {
    lookup_map: HashMapWithView<IAddress, Slot>,
    pages: Vec<Option<IRawPage>>,
    metadata: Vec<Metadata>,
}

impl View for CacheImpl {
    type V = Cache::State;

    closed spec fn view(&self) -> Self::V 
    {
        let entries = Map::new(|k: Slot| k < CACHE_SIZE_PAGES, |k| self.view_entry_at(k));
        let status_map = Map::new(|k: Slot| k < CACHE_SIZE_PAGES, |k| self.metadata[k as int].status);

        Cache::State{
            entries,
            status_map,
            lookup_map: self.lookup_map@,
        }
    }
}

impl CacheImpl {
    pub open spec fn empty_page() -> RawPage
    {
        Seq::new(PAGE_SIZE_BYTES as nat, |i| 0)
    }
    
    pub closed spec fn inv(self) -> bool
    {
        // Lookup map invariants
        // not sure we need this, but ... we only deal in wf addrs
        &&& forall |addr| #![auto] self.lookup_map@.contains_key(addr) ==> addr.wf()

        // all slot pointers are in range
        &&& forall |slot| self.lookup_map@.contains_value(slot) ==> 0 <= slot < CACHE_SIZE_PAGES

        &&& self.lookup_map@.is_injective()

        // Slots named in lookup_map are in the non-Empty state
        &&& forall |slot: Slot| #![auto] slot < CACHE_SIZE_PAGES ==>
            (self.lookup_map@.contains_value(slot) <==> !(self.metadata[slot as int].entry is Empty))

        // Filled slots' addresses match lookup_map
        &&& forall |slot: Slot| slot < CACHE_SIZE_PAGES ==>
            match #[trigger] self.metadata[slot as int].entry {
                IEntry::Filled{addr} => { self.lookup_map@.contains_key(addr@) && self.lookup_map@[addr@] == slot },
                _ => { true }
            }
        // Opposite implication.
        &&& forall |iaddr: IAddress| #![auto] self.lookup_map@.contains_key(iaddr@) ==>
            self.metadata[self.lookup_map@[iaddr@] as int].entry == IEntry::Filled{addr: iaddr}

        // Page & metadata tables are correctly sized
        &&& self.pages.len() == CACHE_SIZE_PAGES
        &&& self.metadata.len() == CACHE_SIZE_PAGES

        // Each page is correctly sized.
        &&& forall |i| #![auto] 0<=i<CACHE_SIZE_PAGES && self.pages[i] is Some
            ==> self.pages[i].unwrap().len() == PAGE_SIZE_BYTES
        
        // probably add invariants connecting outstanding handle to allowed
        // Entry/Status states.
    }

    pub closed spec fn slot_has_oustanding_handle(self, slot: Slot) -> bool {
        &&& 0<=slot<CACHE_SIZE_PAGES
        &&& self.metadata[slot as int].entry is Filled
        &&& self.pages[slot as int] is None
    }

    pub closed spec fn outstanding_handle_slots(self) -> Set<Slot>
    {
        Set::new(|slot: Slot| self.slot_has_oustanding_handle(slot))
    }

    closed spec fn addr_to_oslot(self, iaddr: IAddress) -> Option<Slot>
    {
        self.lookup_map@.get(iaddr@)
    }

    closed spec fn addr_to_slot(self, iaddr: IAddress) -> Slot
    recommends self.addr_to_oslot(iaddr) is Some
    {
        self.addr_to_oslot(iaddr).unwrap()
    }

    closed spec fn slot_to_oaddr(self, slot: Slot) -> Option<IAddress>
    {
        match self.metadata[slot as int].entry {
            IEntry::Filled{addr} => Some(addr),
            _ => None,
        }
    }

    closed spec fn slot_to_addr(self, slot: Slot) -> IAddress
    recommends self.slot_to_oaddr(slot) is Some
    {
        self.slot_to_oaddr(slot).unwrap()
    }

    pub closed spec fn addr_to_page(self, iaddr: IAddress) -> Option<Option<IRawPage>>
    {
        match self.addr_to_oslot(iaddr) {
            None => None,
            Some(slot) => Some(self.pages[slot as int])
        }
    }

    pub closed spec fn outstanding_handle_addresses(self) -> Set<IAddress>
    {
        Set::new(|iaddr: IAddress| (self.addr_to_page(iaddr) == Some(None::<IRawPage>)))
    }

    pub closed spec fn value_at_slot(self, slot: Slot) -> RawPage
        recommends self.inv(), !self.outstanding_handle_slots().contains(slot)
    {
        match self.pages[slot as int] {
            None => arbitrary(),
            Some(page) => page@,
        }
    }

    pub closed spec fn value_at_addr(self, iaddr: IAddress) -> RawPage
    {
        match self.addr_to_oslot(iaddr)
        {
            None => arbitrary(),
            Some(slot) => self.value_at_slot(slot),
        }
    }

    // NB view is ill-defined when handle is outstanding for k.
    closed spec fn view_entry_at(self, k: Slot) -> Entry
        recommends self.inv(), !self.outstanding_handle_slots().contains(k)
    {
        match self.metadata[k as int].entry {
            IEntry::Empty => Entry::Empty,
            IEntry::Reserved{addr} => Entry::Reserved{addr: addr@},
            IEntry::Loading{addr} => Entry::Loading{addr: addr@},
            IEntry::Filled{addr} => Entry::Filled{
                addr: addr@,
                // NB when handles are outstanding, value_at_slot is undefined.
                data: self.value_at_slot(k),
            },
        }
    }

    spec fn empty_metadata() -> Metadata {
        Metadata{ entry: IEntry::Empty, status: Status::NotFilled, }
    }

    #[verifier::external_body]
    exec fn new_empty_page() -> (out: IRawPage)
        ensures out@ == Self::empty_page()
    {
        vec![0; PAGE_SIZE_BYTES]
    }

    pub exec fn new(/*total_slots: usize*/) -> (out: Self)
    ensures
        out.inv(),
        out.outstanding_handle_slots().is_empty(),
    {
        let mut pages: Vec<Option<IRawPage>> = vec![];
        let mut metadata = vec![];
        let mut i = 0usize;
        while i < CACHE_SIZE_PAGES
        invariant
            i <= CACHE_SIZE_PAGES,
            pages.len() == i,
            metadata.len() == i,
            forall |j| #![auto] 0 <= j < i ==> pages[j] is Some && pages[j].unwrap().len() == PAGE_SIZE_BYTES,
            forall |j| #![auto] 0 <= j < i ==> metadata[j] == Self::empty_metadata(),
        decreases CACHE_SIZE_PAGES - i,
        {
            pages.push(Some(Self::new_empty_page()));
            metadata.push(Metadata{
                entry: IEntry::Empty,
                status: Status::NotFilled,
            });
            i += 1;
        }

        assume( obeys_key_model::<IAddress>() );

        Self {
            pages: pages,
            metadata: metadata,
            lookup_map: HashMapWithView::new(),
        }
    }

    // TODO add get-by-address fetch with option
    pub fn read_or_fetch(&mut self, addr: &IAddress) -> (ohdl: Option<Handle>)
    requires
        old(self).inv(),
    ensures
        self.inv(),
        match ohdl {
            None => {
                &&& self.outstanding_handle_addresses() == old(self).outstanding_handle_addresses()
                &&& forall |i| 0<=i<CACHE_SIZE_PAGES ==>
                    self.value_at_slot(i) == old(self).value_at_slot(i)
            },
            Some(hdl) => {
                &&& hdl.inv()
                &&& hdl.releasable()
                &&& hdl.value() == old(self).value_at_slot(hdl.slot())
                &&& self.outstanding_handle_addresses() == old(self).outstanding_handle_addresses().insert(*addr)
                &&& forall |a| a != addr ==> self.value_at_addr(a) == old(self).value_at_addr(a)
            },
        },
    {
        let out = match self.lookup_map.get(addr) {
            None => {
                // TODO: start fetch
                assert( self.outstanding_handle_addresses() == old(self).outstanding_handle_addresses() );
                None
            },
            Some(slot) => {
                assert( self.lookup_map@.contains_value(*slot) );   // trigger lookup_map invariant
                match self.metadata[*slot].entry {
                    // inv violation
                    IEntry::Empty => { assert( false ); None }
                    // Waiting for a load. Or whatever reserved means.
                    IEntry::Reserved{addr} | IEntry::Loading{addr} => { None },
                    IEntry::Filled{addr: faddr} => {
                        // TODO Do we need to check the status? Hmm.
                        self.maybe_get(*slot)
                    },
                }
            }
        };
        out
    }

//     pub fn get(&mut self, slot: Slot) -> (hdl: Handle)
//     requires
//         old(self).inv(),
//         0 <= slot < CACHE_SIZE_PAGES,
//         !old(self).outstanding_handle_slots().contains(slot),
//     ensures
//         self.inv(),
//         hdl.releasable(),
//         hdl.slot() == slot,
//         hdl.value() == old(self).value_at_slot(slot),
//         self.outstanding_handle_slots() == old(self).outstanding_handle_slots().insert(hdl.slot()),
//         forall |i| 0<=i<CACHE_SIZE_PAGES && i != slot as int ==>
//             self.value_at_slot(i) == old(self).value_at_slot(i),
//     {
//         match self.maybe_get(slot) {
//             None => { assert(false); unreached() }
//             Some(hdl) => hdl,
//         }
//     }

    proof fn thingy(self)
    requires
        self.inv(),
    ensures
        true,
    {
    }

    proof fn handle_slots_to_addrs(self)
    requires
        self.inv(),
    ensures
        self.outstanding_handle_addresses() == self.outstanding_handle_slots().map(|slot| self.slot_to_addr(slot)),
    {
        assert forall |a|
            self.outstanding_handle_addresses().contains(a)
            implies
            self.outstanding_handle_slots().map(|slot| self.slot_to_addr(slot)).contains(a)
        by {
            let slot = self.addr_to_slot(a);
            assert( self.lookup_map@.contains_value(slot) );    // trigger inv
            assert( self.outstanding_handle_slots().contains(slot) );   // trigger
        }
    }

    // None means the slot is already outstanding in another handle.
    // I don't think our actual code will need this path.
    fn maybe_get(&mut self, slot: Slot) -> (res: Option<Handle>)
    requires
        old(self).inv(),
        old(self).metadata[slot as int].entry is Filled,
        0 <= slot < CACHE_SIZE_PAGES,
    ensures
        self.inv(),
        self.metadata == old(self).metadata,
        match res {
            None => {
                &&& old(self).outstanding_handle_slots().contains(slot)
                &&& self.outstanding_handle_slots() == old(self).outstanding_handle_slots()
                &&& self.outstanding_handle_addresses() == old(self).outstanding_handle_addresses()
                &&& forall |i| 0<=i<CACHE_SIZE_PAGES ==>
                    self.value_at_slot(i) == old(self).value_at_slot(i)
            },
            Some(hdl) => {
                &&& hdl.inv()
                &&& hdl.releasable()
                &&& hdl.slot() == slot
                &&& hdl.value() == old(self).value_at_slot(slot)
                &&& self.outstanding_handle_slots() == old(self).outstanding_handle_slots().insert(hdl.slot())
                &&& self.outstanding_handle_addresses() == old(self).outstanding_handle_addresses().insert(self.slot_to_oaddr(hdl.slot()).unwrap())
                &&& forall |i| 0<=i<CACHE_SIZE_PAGES && i != slot as int ==>
                    self.value_at_slot(i) == old(self).value_at_slot(i)
                &&& forall |a| a != self.slot_to_addr(slot) ==> self.value_at_addr(a) == old(self).value_at_addr(a)
            },
        },
    {
        self.pages.push(None);
        let mut taken = self.pages.swap_remove(slot);
        let out = match taken {
            // Somebody beat you to it
            None => { None },
            Some(page) => { Some(Handle{ slot, page, _releasable: Ghost(true) }) },
        };

        proof {
            self.handle_slots_to_addrs();
            old(self).handle_slots_to_addrs();
            let out = out;
            match out {
                None => { }
                Some(hdl) => {
                    assert forall |a| a != self.slot_to_addr(slot) implies self.value_at_addr(a) == old(self).value_at_addr(a) by {
                        match self.addr_to_oslot(a) {
                            None => {},
                            // trigger inv
                            Some(s) => { assert( self.lookup_map@.contains_value(s) ); }
                        }
                    }
                }
            }
        }

        out
    }

    pub fn release(&mut self, hdl: Handle)
    requires
        old(self).inv(),
        hdl.inv(),
        hdl.releasable(),
    ensures
        self.inv(),
        self.outstanding_handle_slots() == old(self).outstanding_handle_slots().remove(hdl.slot()),
        self.value_at_slot(hdl.slot()) == hdl.value(),
        forall |i| 0<=i<CACHE_SIZE_PAGES && i != hdl.slot() as int ==>
            self.value_at_slot(i) == old(self).value_at_slot(i),
    {
        self.pages[hdl.slot] = Some(hdl.page)
    }

    // #[verifier::external_body]
    // pub fn u32_to_usize(x: u32) -> (out: usize)
    // ensures x == out
    // {
    //     x.try_into().unwrap()
    // }
}

}//verus!
