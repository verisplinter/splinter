// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Shared abstract superblock image used by coordination-level and atomic-level
// models. The concrete raw-page encoding is intentionally staged behind an
// uninterpreted marshaller until the superblock format is wired in.

#![allow(unused_imports)]

use vstd::prelude::*;

use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::Address;
use crate::implementation::CachedJournal_v::JournalSnapshot;
use crate::spec::AsyncDisk_t::RawPage;

verus! {

pub struct AbstractSuperblockImage {
    pub journal_snapshot: JournalSnapshot,
    pub journal_seq_end: LSN,
    pub branch_roots: Seq<Address>,
    pub branch_seq_end: nat,
}

impl AbstractSuperblockImage {
    pub open spec fn wf(self) -> bool
    {
        &&& self.branch_seq_end == self.journal_snapshot.boundary_lsn
        &&& self.journal_snapshot.boundary_lsn <= self.journal_seq_end
    }
}

pub open spec fn abstract_superblock_image(
    journal_snapshot: JournalSnapshot,
    journal_seq_end: LSN,
    branch_roots: Seq<Address>,
    new_boundary_lsn: LSN,
) -> AbstractSuperblockImage
{
    AbstractSuperblockImage{
        journal_snapshot,
        journal_seq_end,
        branch_roots,
        branch_seq_end: new_boundary_lsn,
    }
}

pub open spec fn empty_abstract_superblock_image() -> AbstractSuperblockImage
{
    AbstractSuperblockImage{
        journal_snapshot: JournalSnapshot{boundary_lsn: 0, root: None},
        journal_seq_end: 0,
        branch_roots: Seq::empty(),
        branch_seq_end: 0,
    }
}

pub uninterp spec fn marshal_abstract_superblock(image: AbstractSuperblockImage) -> RawPage;

pub uninterp spec fn parse_abstract_superblock(raw: RawPage) -> AbstractSuperblockImage;

pub open spec fn superblock_matches(
    raw: RawPage,
    image: AbstractSuperblockImage,
) -> bool
{
    raw == marshal_abstract_superblock(image)
}

pub proof fn abstract_superblock_marshalling_matches(image: AbstractSuperblockImage)
    ensures
        superblock_matches(marshal_abstract_superblock(image), image),
{
}

// Placeholder until the concrete parser/marshaller are wired in.
// This is deliberately weaker than raw-wf: callers must prove well-formedness
// from the context that produced the raw superblock page.
#[verifier::external_body]
pub proof fn assumed_parse_marshalled_abstract_superblock(image: AbstractSuperblockImage)
    ensures
        parse_abstract_superblock(marshal_abstract_superblock(image)) == image,
{
}

// Placeholder until the concrete superblock marshaller/parser is wired in.
// This is the one trusted bridge that says a marshalled logical superblock
// parses back to the same well-formed image.
#[verifier::external_body]
pub proof fn marshalled_abstract_superblock_raw_wf(image: AbstractSuperblockImage)
    requires
        image.wf(),
    ensures
        parse_abstract_superblock(marshal_abstract_superblock(image)) == image,
        abstract_superblock_raw_wf(marshal_abstract_superblock(image)),
{
}

pub open spec fn abstract_superblock_raw_wf(raw: RawPage) -> bool
{
    let image = parse_abstract_superblock(raw);
    &&& image.wf()
    &&& superblock_matches(raw, image)
}

} // verus!
