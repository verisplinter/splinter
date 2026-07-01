// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Compatibility layer for the superblock image used by the unified-cache
// models. The image type and parser are now the concrete DiskLayout
// superblock; the public names remain while the surrounding refinement code is
// migrated.

#![allow(unused_imports)]

use vstd::prelude::*;

use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::Address;
use crate::implementation::CachedJournal_v::JournalSnapshot;
use crate::implementation::DiskLayout_v::DiskLayout;
use crate::implementation::SuperblockTypes_v::Superblock;
use crate::spec::AsyncDisk_t::RawPage;

verus! {

pub type AbstractSuperblockImage = Superblock;

pub open spec fn abstract_superblock_image(
    journal_snapshot: JournalSnapshot,
    journal_seq_end: LSN,
    branch_roots: Seq<Address>,
    new_boundary_lsn: LSN,
) -> AbstractSuperblockImage
{
    Superblock{
        journal_snapshot,
        journal_seq_end,
        branch_roots,
        branch_seq_end: new_boundary_lsn,
    }
}

pub open spec fn empty_abstract_superblock_image() -> AbstractSuperblockImage
{
    Superblock{
        journal_snapshot: JournalSnapshot{boundary_lsn: 0, root: None},
        journal_seq_end: 0,
        branch_roots: Seq::empty(),
        branch_seq_end: 0,
    }
}

pub uninterp spec fn marshal_abstract_superblock(image: AbstractSuperblockImage) -> RawPage;

pub open spec fn parse_abstract_superblock(raw: RawPage) -> AbstractSuperblockImage
{
    DiskLayout::spec_new().spec_parse(raw)
}

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

// Placeholder until the concrete marshaller/parser proof is connected. The
// parser side is concrete now; this trusted bridge remains only for the
// spec-level marshal used by state-machine write labels.
#[verifier::external_body]
pub proof fn assumed_parse_marshalled_abstract_superblock(image: AbstractSuperblockImage)
    ensures
        parse_abstract_superblock(marshal_abstract_superblock(image)) == image,
{
}

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
