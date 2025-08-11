// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
// use vstd::hash_map::*;
use crate::spec::MapSpec_t::*;
// use crate::spec::AsyncDisk_t::*;
// use crate::spec::ImplDisk_t::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
// use crate::spec::TotalKMMap_t::*;
// use crate::spec::FloatingSeq_t::*;
use crate::implementation::VecMap_v::*;
use crate::marshalling::Marshalling_v::Deepview;
use crate::implementation::JournalTypes_v::*;
use crate::spec::TotalKMMap_t::*;
use crate::abstract_system::StampedMap_v::*;

verus! {

// Stores structured for easy marshalling. :v/
type ARawStore = Seq<(Key, Value)>;

type RawStore = Vec<(Key, Value)>;
// 
// pub fn vec_map_to_raw_store(vec_map: &VecMap<Key, Value>) -> RawStore {
//     vec_map.v
// }

pub struct Superblock {
    pub store: PersistentState, // mapspec
    // need version so recovery knows the shape of the (mostly-empty) history to reconstruct (the LSN)
    pub version_index: nat,
}

pub struct ASuperblock {
    pub journal: AJournal,
    pub store: ARawStore,
    // need version so recovery knows the shape of the (mostly-empty) history to reconstruct (the LSN)
    // Wait no this is dumb; the journal contains its start LSN, which must match the store's LSN.
//     pub version_index: u64,
}

impl View for ASuperblock {
    type V = Superblock;

    open spec fn view(&self) -> Self::V
    {
        let value_map = VecMap::seq_to_map(self.store);
        let message_map = Map::new(
                |k| value_map.contains_key(k),
                |k| Message::Define{value: value_map[k]});
        let total_map = TotalKMMap(message_map); 
//         assert( total_map.wf() );   // need to "totalize" the map
        let store_stamped_map = StampedMap{value: total_map, seq_end: 0};
        let msg_history = self.journal@; // convert AJournal into MsgHistory
        let final_stamped_map = msg_history.apply_to_stamped_map(store_stamped_map);
        let persistent_state = PersistentState{ appv: MapSpec::State{ kmmap: final_stamped_map.value}};
        Superblock{
            store: persistent_state,
            version_index: final_stamped_map.seq_end,
        }
    }
}

pub struct ISuperblock {
    pub journal: Journal,
    pub store: RawStore,
    // need version so recovery knows the shape of the (mostly-empty) history to reconstruct (the LSN)
    // pub version_index: u64,
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
