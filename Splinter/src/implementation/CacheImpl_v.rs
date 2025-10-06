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

verus!{

pub type IRawPage = Vec<u8>;

#[derive(Clone)]
pub enum IEntry{
    Empty,
    Reserved{addr: IAddress},
    Loading{addr: IAddress}, 
    Filled{addr: IAddress, data: IRawPage},
}

impl View for IEntry {
    type V = Entry;

    open spec fn view(&self) -> Self::V
    {
        match self {
            IEntry::Empty => Entry::Empty,
            IEntry::Reserved{addr} => Entry::Reserved{addr: addr@},
            IEntry::Loading{addr} => Entry::Loading{addr: addr@},
            IEntry::Filled{addr, data} => Entry::Filled{addr: addr@, data: data@},
        }
    }
}

pub struct CacheImpl {
    entries: Vec<IEntry>,
    status_table: Vec<Status>,
    lookup_map: HashMapWithView<IAddress, Slot>,
    outstanding_reqs: HashMapWithView<ID, Slot>,
}

impl View for CacheImpl {
    type V = Cache::State;

    closed spec fn view(&self) -> Self::V 
    {
        let entries = Map::new(|k: Slot| k < self.entries.len(), |k| self.entries[k as int]@);
        let status_map = Map::new(|k: Slot| k < self.status_table.len(), |k| self.status_table[k as int]);

        Cache::State{
            entries,
            status_map,
            lookup_map: self.lookup_map@,
            outstanding_reqs: self.outstanding_reqs@,
        }
    }
}

impl CacheImpl {
    pub exec fn new(total_slots: usize) -> (out: Self)
        ensures out@ == Cache::State::empty(total_slots as nat)
    {
        let mut entries = Vec::<IEntry>::with_capacity(total_slots);
        let mut status_table = Vec::<Status>::with_capacity(total_slots);
        let mut i = 0;

        while i < total_slots
        invariant 
            i <= total_slots,
            entries.len() == i,
            status_table.len() == i,
            forall |j| 0 <= j < i ==> #[trigger] entries[j] is Empty,
            forall |j| 0 <= j < i ==> #[trigger] status_table[j] is NotFilled,
        decreases total_slots - i,
        {
            entries.push(IEntry::Empty);
            status_table.push(Status::NotFilled);
            i = i+1;
        }

        assume( obeys_key_model::<IAddress>() );

        CacheImpl{
            entries,
            status_table,
            lookup_map: HashMapWithView::new(),
            outstanding_reqs: HashMapWithView::new(),
        }
    }

    // Some => here's the page! Hooray! (borrow with lifetime?)
    // None => we've initiated the IO; try again later
    pub exec fn read_or_fetch(&self, addr: &IAddress) -> Option<Vec<u8>>
    {
        unreached()
    }
}

}//verus!
