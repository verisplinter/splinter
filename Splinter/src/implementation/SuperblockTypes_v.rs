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
use crate::abstract_system::StampedMap_v::LSN;
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
    pub journal_snapshot: JournalSnapshot,
    pub journal_seq_end: LSN,
    pub branch_roots: Seq<Address>,
    pub branch_seq_end: nat,
}

pub open spec(checked) fn singleton_floating_seq(at_index: nat, kmmap: TotalKMMap) -> FloatingSeq<Version>
{
    FloatingSeq::new(at_index, at_index + 1,
          |i| Version{ appv: MapSpec::State{ kmmap } } )
}

impl Superblock {
    pub open spec fn wf(self) -> bool
    {
        &&& self.branch_seq_end == self.journal_snapshot.boundary_lsn
        &&& self.journal_snapshot.boundary_lsn <= self.journal_seq_end
    }
}

pub struct ASuperblockJournalImage {
    pub snapshot: JournalSnapshot,
    pub seq_end: LSN,
}

impl ASuperblockJournalImage {
    pub open spec fn wf(self) -> bool {
        self.snapshot.boundary_lsn <= self.seq_end
    }
}

pub struct ASuperblockBranchImage {
    pub roots: Seq<Address>,
    pub seq_end: nat,
}

impl ASuperblockBranchImage {
    pub open spec fn wf(self, journal_snapshot: JournalSnapshot) -> bool {
        self.seq_end == journal_snapshot.boundary_lsn
    }
}

pub struct ASuperblock {
    pub journal: ASuperblockJournalImage,
    pub branch: ASuperblockBranchImage,
}

impl ASuperblock {
    pub open spec fn wf(self) -> bool {
        &&& self.journal.wf()
        &&& self.branch.wf(self.journal.snapshot)
    }
}

impl View for ASuperblock {
    type V = Superblock;

    open spec fn view(&self) -> Self::V
    {
        Superblock{
            journal_snapshot: self.journal.snapshot,
            journal_seq_end: self.journal.seq_end,
            branch_roots: self.branch.roots,
            branch_seq_end: self.branch.seq_end,
        }
    }
}

#[derive(Debug)]
pub struct ISuperblockJournalImage {
    pub snapshot: IJournalSnapshot,
    pub seq_end: u64,
}

impl Parsedview<ASuperblockJournalImage> for ISuperblockJournalImage {
    open spec fn parsedv(&self) -> ASuperblockJournalImage {
        ASuperblockJournalImage{
            snapshot: self.snapshot@,
            seq_end: self.seq_end as nat,
        }
    }
}

impl WF for ISuperblockJournalImage {}

impl View for ISuperblockJournalImage {
    type V = ASuperblockJournalImage;

    open spec fn view(&self) -> Self::V
    {
        self.parsedv()
    }
}

#[derive(Debug)]
pub struct ISuperblockBranchImage {
    pub roots: Vec<IAddress>,
    pub seq_end: u64,
}

impl Parsedview<ASuperblockBranchImage> for ISuperblockBranchImage {
    open spec fn parsedv(&self) -> ASuperblockBranchImage {
        ASuperblockBranchImage{
            roots: Parsedview::<Seq<Address>>::parsedv(&self.roots),
            seq_end: self.seq_end as nat,
        }
    }
}

impl WF for ISuperblockBranchImage {}

impl View for ISuperblockBranchImage {
    type V = ASuperblockBranchImage;

    open spec fn view(&self) -> Self::V
    {
        self.parsedv()
    }
}

#[derive(Debug)]
pub struct ISuperblock {
    pub journal: ISuperblockJournalImage,
    pub branch: ISuperblockBranchImage,
}

impl Parsedview<ASuperblock> for ISuperblock {
    open spec fn parsedv(&self) -> ASuperblock {
        ASuperblock{
            journal: self.journal@,
            branch: self.branch@,
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
