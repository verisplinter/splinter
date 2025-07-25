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
// use crate::marshalling::Marshalling_v::Deepview;
use crate::implementation::JournalTypes_v::*;

verus! {

pub struct Superblock {
    pub store: PersistentState, // mapspec
    // need version so recovery knows the shape of the (mostly-empty) history to reconstruct (the LSN)
    pub version_index: nat,
}

// Stores structured for easy marshalling. :v/
type ARawStore = VecMap<Key, Value>;

type RawStore = VecMap<Key, Value>;
// 
// pub fn vec_map_to_raw_store(vec_map: &VecMap<Key, Value>) -> RawStore {
//     vec_map.v
// }

pub struct ASuperblock {
    pub journal: AJournal,
    pub store: ARawStore,
    // need version so recovery knows the shape of the (mostly-empty) history to reconstruct (the LSN)
    // Wait no this is dumb; the journal contains its start LSN, which must match the store's LSN.
//     pub version_index: u64,
}

pub struct ISuperblock {
    pub journal: Journal,
    pub store: RawStore,
    // need version so recovery knows the shape of the (mostly-empty) history to reconstruct (the LSN)
//     pub version_index: u64,
}

impl View for ISuperblock {
    type V = Superblock;

    open spec fn view(&self) -> Self::V
    {
        let map = self.journal.to_stamped_map();
        Superblock{
            store: PersistentState{ appv: MapSpec::State{ kmmap: map.value}},
            version_index: map.seq_end
        }
    }
}

}//verus!
