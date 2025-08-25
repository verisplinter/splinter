// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::spec::MapSpec_t::*;
use crate::spec::FloatingSeq_t::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::implementation::VecMap_v::*;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::WF_v::WF;
use crate::implementation::JournalTypes_v::*;
use crate::spec::TotalKMMap_t::*;
use crate::abstract_system::StampedMap_v::*;

verus! {

// Stores structured for easy marshalling. :v/
type ARawStore = Seq<(Key, Value)>;

pub type RawStore = Vec<(Key, Value)>;
// 
// pub fn vec_map_to_raw_store(vec_map: &VecMap<Key, Value>) -> RawStore {
//     vec_map.v
// }

pub struct Superblock {
    pub store: PersistentState, // mapspec
    // need version so recovery knows the shape of the (mostly-empty) history to reconstruct (the LSN)
    pub version_index: nat,
}

pub open spec(checked) fn singleton_floating_seq(at_index: nat, kmmap: TotalKMMap) -> FloatingSeq<Version>
{
    FloatingSeq::new(at_index, at_index+1,
          |i| Version{ appv: MapSpec::State{ kmmap } } )
}

impl Superblock {
    pub open spec fn initial_history(self) -> FloatingSeq<PersistentState>
    {
        singleton_floating_seq(self.version_index, self.store.appv.kmmap)
    }
}

pub struct ASuperblock {
    pub journal: AJournal,
    pub store: ARawStore,
    // need version so recovery knows the shape of the (mostly-empty) history to reconstruct (the LSN)
    // Wait no this is dumb; the journal contains its start LSN, which must match the store's LSN.
//     pub version_index: u64,
}

impl ASuperblock {
    pub open spec fn map_to_kmmap(m: Map<Key, Value>) -> TotalKMMap
    {
        TotalKMMap(
            Map::new(|k: Key| true,
                |k: Key| 
                    if m.contains_key(k) {
                        Message::Define{value: m[k]}
                    } else {
                        Message::empty()
                    }
            )
        )
    }

    pub open spec fn store_stamped_map(self) -> StampedMap
    {
        let value_map = VecMap::seq_to_map(self.store);
        let total_map = Self::map_to_kmmap(value_map);
        StampedMap{value: total_map, seq_end: self.journal@.seq_start}
    }

    pub open spec fn final_stamped_map(self) -> StampedMap
    {
        self.journal@.apply_to_stamped_map(self.store_stamped_map())
    }
}

impl View for ASuperblock {
    type V = Superblock;

    open spec fn view(&self) -> Self::V
    {
        let persistent_state = PersistentState{ appv: MapSpec::State{ kmmap: self.final_stamped_map().value}};
        Superblock{
            store: persistent_state,
            version_index: self.final_stamped_map().seq_end,
        }
    }
}

#[derive(Debug)]
pub struct ISuperblock {
    pub journal: Journal,
    pub store: RawStore,
    // need version so recovery knows the shape of the (mostly-empty) history to reconstruct (the LSN)
    // pub version_index: u64,
}

impl ISuperblock {
    pub open spec fn wf(self) -> bool {
        &&& self.store.wf()
        &&& self.journal.inv()
        &&& VecMap::unique_keys(self.store@)
    }
}

impl View for ISuperblock {
    type V = Superblock;

    open spec fn view(&self) -> Self::V
    {
        // promote to ASuperblock, thence to Superblock
        self.deepv()@
    }
}

}//verus!
