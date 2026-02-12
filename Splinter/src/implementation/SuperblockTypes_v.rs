// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::spec::MapSpec_t::*;
use crate::spec::FloatingSeq_t::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::implementation::VecMap_v::*;
use crate::implementation::CachedJournal_v;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::WF_v::WF;
use crate::implementation::JournalTypes_v::*;
use crate::implementation::JournalImpl_v::IJournalSnapshot;
use crate::implementation::CachedJournal_v::JournalSnapshot;
use crate::spec::TotalKMMap_t::*;
use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::abstract_system::StampedMap_v::*;

verus! {

// Stores structured for easy marshalling. :v/
type ARawStore = Seq<(Key, Value)>;

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

pub open spec fn arawstore_as_stamped_map(selff: ARawStore, seq_end: LSN) -> StampedMap
{
    let value_map = VecMap::seq_to_map(selff);
    let total_map = map_to_kmmap(value_map);
    StampedMap{value: total_map, seq_end}
}

pub type RawStore = Vec<(Key, Value)>;
// 
// pub fn vec_map_to_raw_store(vec_map: &VecMap<Key, Value>) -> RawStore {
//     vec_map.v
// }

pub struct Superblock {
    pub store: StampedMap,
    pub journal: JournalSnapshot,
}

pub open spec(checked) fn singleton_floating_seq(at_index: nat, kmmap: TotalKMMap) -> FloatingSeq<Version>
{
    FloatingSeq::new(at_index, at_index+1,
          |i| Version{ appv: MapSpec::State{ kmmap } } )
}

impl Superblock {
    pub open spec fn wf(self) -> bool
    {
        &&& self.store.seq_end == self.journal.boundary_lsn
        // &&& self.journal.wf()
    }
}

pub struct ASuperblock {
    pub store: ARawStore,
    pub journal: JournalSnapshot,
    // need version so recovery knows the shape of the (mostly-empty) history to reconstruct (the LSN)
    // Wait no this is dumb; the journal contains its start LSN, which must match the store's LSN.
//     pub version_index: u64,
}

impl ASuperblock {
    pub open spec fn wf(self) -> bool {
        &&& VecMap::unique_keys(self.store)
    }
}

impl View for ASuperblock {
    type V = Superblock;

    open spec fn view(&self) -> Self::V
    {
        Superblock{
            store: arawstore_as_stamped_map(self.store, self.journal.boundary_lsn),
            journal: self.journal,
        }
    }
}

#[derive(Debug)]
pub struct ISuperblock {
    pub journal_snapshot: IJournalSnapshot,
    pub store: RawStore,  // TODO: try
    // need version so recovery knows the shape of the (mostly-empty) history to reconstruct (the LSN)
    // pub version_index: u64,
}

impl Parsedview<ASuperblock> for ISuperblock {
    open spec fn parsedv(&self) -> ASuperblock {
        ASuperblock{
            journal: self.journal_snapshot@,
            store: self.store@,
        }
    }
}

impl WF for ISuperblock {}

impl View for ISuperblock {
    type V = ASuperblock;

    open spec fn view(&self) -> Self::V
    {
        self.parsedv()
    }
}

}//verus!
