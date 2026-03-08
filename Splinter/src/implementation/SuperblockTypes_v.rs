// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::spec::MapSpec_t::{MapSpec, Version};
use crate::spec::FloatingSeq_t::FloatingSeq;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Message, Value};
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::WF_v::WF;
use crate::implementation::JournalImpl_v::IJournalSnapshot;
use crate::implementation::CachedJournal_v::JournalSnapshot;
use crate::spec::TotalKMMap_t::TotalKMMap;
use crate::spec::AsyncDisk_t::Address;
use crate::spec::ImplDisk_t::IAddress;

verus! {

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

pub struct Superblock {
    pub store_ptr: Option<Address>,
    pub journal: JournalSnapshot,
}

pub open spec(checked) fn singleton_floating_seq(at_index: nat, kmmap: TotalKMMap) -> FloatingSeq<Version>
{
    FloatingSeq::new(at_index, at_index + 1,
          |i| Version{ appv: MapSpec::State{ kmmap } } )
}

impl Superblock {
    pub open spec fn wf(self) -> bool
    {
        true
    }
}

pub struct ASuperblock {
    pub store_ptr: Option<Address>,
    pub journal: JournalSnapshot,
}

impl ASuperblock {
    pub open spec fn wf(self) -> bool {
        true
    }
}

impl View for ASuperblock {
    type V = Superblock;

    open spec fn view(&self) -> Self::V
    {
        Superblock{
            store_ptr: self.store_ptr,
            journal: self.journal,
        }
    }
}

#[derive(Debug)]
pub struct ISuperblock {
    pub journal_snapshot: IJournalSnapshot,
    pub store_ptr: Option<IAddress>,
}

impl Parsedview<ASuperblock> for ISuperblock {
    open spec fn parsedv(&self) -> ASuperblock {
        ASuperblock{
            journal: self.journal_snapshot@,
            store_ptr: match self.store_ptr {
                Some(addr) => Some(addr@),
                None => None,
            },
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
