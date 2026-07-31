// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::WF_v::WF;
use crate::implementation::JournalImpl_v::IJournalSnapshot;
use crate::implementation::CachedJournal_v::JournalSnapshot;
use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::Pointer;
use crate::spec::AsyncDisk_t::page_count;
use crate::spec::ImplDisk_t::{IAddress, IAU, IPage};

verus! {

pub struct Superblock {
    pub journal_snapshot: JournalSnapshot,
    pub journal_seq_end: LSN,
    // Retired legacy branch-stack metadata:
    // pub branch_roots: Seq<Address>,
    pub betree_root: Pointer,
    // pub branch_seq_end: nat,
}

impl Superblock {
    pub open spec fn wf(self) -> bool
    {
        &&& self.journal_snapshot.boundary_lsn <= self.journal_seq_end
        &&& self.betree_root is Some
            ==> self.betree_root.unwrap().wf()
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

pub struct ASuperblock {
    pub geometry: ASuperblockGeometry,
    pub payload: ASuperblockPayload,
}

pub struct ASuperblockGeometry {
    pub pages_per_au: nat,
    pub formatted_au_count: nat,
}

impl ASuperblockGeometry {
    pub open spec fn wf(self) -> bool {
        &&& self.pages_per_au == page_count()
        &&& 1 < self.formatted_au_count
    }
}

pub struct ASuperblockPayload {
    pub journal: ASuperblockJournalImage,
    pub branch: Pointer,
}

impl ASuperblockPayload {
    pub open spec fn wf(self) -> bool {
        &&& self.journal.wf()
        &&& self.branch is Some ==> self.branch.unwrap().wf()
    }
}

impl ASuperblock {
    pub open spec fn addresses_bounded(self) -> bool {
        let bound = self.geometry.formatted_au_count;
        &&& self.payload.journal.snapshot.root is Some ==>
            self.payload.journal.snapshot.root.unwrap().freshest_rec.au < bound
        &&& self.payload.journal.snapshot.root is Some ==>
            self.payload.journal.snapshot.root.unwrap().first < bound
        &&& self.payload.branch is Some ==>
            self.payload.branch.unwrap().au < bound
    }

    pub open spec fn wf(self) -> bool {
        &&& self.geometry.wf()
        &&& self.payload.wf()
        &&& self.addresses_bounded()
    }
}

impl View for ASuperblockPayload {
    type V = Superblock;

    open spec fn view(&self) -> Self::V
    {
        Superblock{
            journal_snapshot: self.journal.snapshot,
            journal_seq_end: self.journal.seq_end,
            betree_root: self.branch,
        }
    }
}

impl View for ASuperblock {
    type V = Superblock;

    open spec fn view(&self) -> Self::V
    {
        self.payload@
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
pub struct ISuperblockGeometry {
    pub pages_per_au: IPage,
    pub formatted_au_count: IAU,
}

impl Parsedview<ASuperblockGeometry> for ISuperblockGeometry {
    open spec fn parsedv(&self) -> ASuperblockGeometry {
        ASuperblockGeometry {
            pages_per_au: self.pages_per_au as nat,
            formatted_au_count: self.formatted_au_count as nat,
        }
    }
}

impl WF for ISuperblockGeometry {}

impl View for ISuperblockGeometry {
    type V = ASuperblockGeometry;

    open spec fn view(&self) -> Self::V
    {
        self.parsedv()
    }
}

#[derive(Debug)]
pub struct ISuperblockPayload {
    pub journal: ISuperblockJournalImage,
    pub branch: Option<IAddress>,
}

impl Parsedview<ASuperblockPayload> for ISuperblockPayload {
    open spec fn parsedv(&self) -> ASuperblockPayload {
        ASuperblockPayload {
            journal: self.journal@,
            branch: Parsedview::<Pointer>::parsedv(&self.branch),
        }
    }
}

impl WF for ISuperblockPayload {}

impl View for ISuperblockPayload {
    type V = ASuperblockPayload;

    open spec fn view(&self) -> Self::V
    {
        self.parsedv()
    }
}

#[derive(Debug)]
pub struct ISuperblock {
    pub geometry: ISuperblockGeometry,
    pub payload: ISuperblockPayload,
}

impl Parsedview<ASuperblock> for ISuperblock {
    open spec fn parsedv(&self) -> ASuperblock {
        ASuperblock{
            geometry: self.geometry@,
            payload: self.payload@,
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
