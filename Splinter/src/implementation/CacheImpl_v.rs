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

// TODO(jonh): this can't be a vec, it needs to be a fixed-length array!
pub type IRawPage = Vec<u8>;

pub struct EntryLoan {
    data: IRawPage,
}

#[derive(Clone)]
pub enum IEntry{
    Empty,
    Reserved{addr: IAddress},
    Loading{addr: IAddress}, 
    Filled{addr: IAddress},
}

// impl View for IEntry {
//     type V = Entry;
// 
//     open spec fn view(&self) -> Self::V
//     {
//         match self {
//             IEntry::Empty => Entry::Empty,
//             IEntry::Reserved{addr} => Entry::Reserved{addr: addr@},
//             IEntry::Loading{addr} => Entry::Loading{addr: addr@},
//             IEntry::Filled{addr, data} => Entry::Filled{addr: addr@, data: data@},
//         }
//     }
// }

struct Metadata {
    entry: IEntry,
    status: Status,
    // The Option is exec (non-ghost) state that tells us at runtime whether we've
    // given out the handle.
    available: Option<Tracked<PointsTo<IRawPage>>>,
}

pub struct Handle<'a> {
    cell: &'a PCell<IRawPage>,
    perm: Tracked<&'a PointsTo<IRawPage>>,
}

impl<'a> Handle<'a> {
    pub fn borrow(&self) -> &IRawPage
    {
        self.cell.borrow(self.perm)
    }
}

impl<'a> View for Handle<'a> {
    type V = IRawPage;

    closed spec fn view(&self) -> Self::V 
    {
        self.perm@.mem_contents().value()
    }
}

pub const CACHE_COUNT: usize = 1000;

pub struct CacheImpl {
    pages: [PCell<IRawPage>; CACHE_COUNT],
//     perms: [Option<Tracked<PointsTo<IRawPage>>>; CACHE_COUNT],
    metadata: [Metadata; CACHE_COUNT],
    lookup_map: HashMapWithView<IAddress, Slot>,
}

impl View for CacheImpl {
    type V = Cache::State;

    closed spec fn view(&self) -> Self::V 
    {
        let entries = Map::new(|k: Slot| k < CACHE_COUNT, |k| self.view_entry_at(k));
        let status_map = Map::new(|k: Slot| k < CACHE_COUNT, |k| self.metadata[k as int].status);

        Cache::State{
            entries,
            status_map,
            lookup_map: self.lookup_map@,
        }
    }
}

impl CacheImpl {
    pub closed spec fn wf(self) -> bool
    {
        &&& forall |slot| self.lookup_map@.contains_value(slot) ==> slot < CACHE_COUNT
    }

    // Uhm, how are we going to answer this question when we don't have
    // perms for some handles we gave out?
    closed spec fn view_entry_at(self, k: Slot) -> Entry
    {
        match self.metadata[k as int].entry {
            IEntry::Empty => Entry::Empty,
            IEntry::Reserved{addr} => Entry::Reserved{addr: addr@},
            IEntry::Loading{addr} => Entry::Loading{addr: addr@},
            IEntry::Filled{addr} => Entry::Filled{
                addr: addr@,
                // TODO(jonh): what happens when the handle is outstanding?
//                 data: self.perms[k as int]@.unwrap().value()@
                data: self.metadata[k as int].available.unwrap()@.value()@
            },
        }
    }

    // TODO(verus): how should I populate an array [T; n]? can we spec from_fn?
    #[verifier::external_body]
    pub exec fn new(/*total_slots: usize*/) -> (out: Self)
        ensures
            out.wf(),
            out@ == Cache::State::empty(CACHE_COUNT as nat)
    {
        let pcell_pairs: [_; CACHE_COUNT] = std::array::from_fn(|k: usize| PCell::empty());
        let mut pages = std::array::from_fn(|k: usize| pcell_pairs[k].0);
//         let mut perms = std::array::from_fn(|k: usize| Some(pcell_pairs[k].1));
        let mut metadata = std::array::from_fn(|k: usize|
            Metadata{
                entry: IEntry::Empty,
                status: Status::NotFilled,
                available: Some(pcell_pairs[k].1)
            });
            
        assume( obeys_key_model::<IAddress>() );

        CacheImpl{
            pages,
//             perms,
            metadata,
            lookup_map: HashMapWithView::new(),
        }
    }

    // Some => here's the page! Hooray! (borrow with lifetime?)
    // None => we've initiated the IO; try again later

    // client api for request
    // mut self 
    pub exec fn read_or_fetch(&self, addr: &IAddress) -> (out: Option<Handle>)
        requires self.wf()
        ensures self.wf()
    {
        let slot = match self.lookup_map.get(addr)
        {
            None => {
                // Send a disk IO to fetch!
                return None;
            },
            Some(slot) => { slot },
        };

        let slot: usize = u32_to_usize(*slot);
        let available = None;
        std::mem::swap(&mut available, &mut self.metadata[slot].available);
//         let available = std::mem::take(&mut self.metadata[slot].available);
        match available {
            None => {
                // Somebody already has this handle, actually.
                None
            },
            Some(available) => {
                // by invariant, surely Status::Clean | Status::Dirty
                let perm = Tracked(available.borrow());
                Some(Handle{
                    cell: &self.pages[slot],
                    perm,
                })
            }
        }
    }
}

#[verifier::external_body]
pub fn u32_to_usize(x: u32) -> (out: usize)
ensures x == out
{
    x.try_into().unwrap()
}

}//verus!
