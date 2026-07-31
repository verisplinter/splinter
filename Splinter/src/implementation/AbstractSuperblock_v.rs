// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Compatibility layer for the superblock image used by the unified-cache
// models. The image type and parser are now the concrete DiskLayout
// superblock; the public names remain while the surrounding refinement code is
// migrated.

#![allow(unused_imports)]

use vstd::prelude::*;

use crate::implementation::CachedJournal_v::JournalSnapshot;
use crate::implementation::DiskLayout_v::DiskLayout;
use crate::implementation::SuperblockTypes_v::Superblock;
use crate::marshalling::Marshalling_v::Marshal;
use crate::spec::AsyncDisk_t::RawPage;

verus! {

pub type AbstractSuperblockImage = Superblock;

pub open spec fn empty_abstract_superblock_image() -> AbstractSuperblockImage
{
    Superblock{
        journal_snapshot: JournalSnapshot{boundary_lsn: 0, root: None},
        journal_seq_end: 0,
        betree_root: None,
    }
}

// Legacy placeholder used before the concrete DiskLayout format was available:
// pub uninterp spec fn marshal_abstract_superblock(image: AbstractSuperblockImage) -> RawPage;

pub open spec fn parse_abstract_superblock(raw: RawPage) -> AbstractSuperblockImage
{
    DiskLayout::spec_new().spec_parse(raw)
}

pub open spec fn superblock_matches(
    raw: RawPage,
    image: AbstractSuperblockImage,
) -> bool
{
    &&& abstract_superblock_raw_wf(raw)
    &&& parse_abstract_superblock(raw) == image
}

pub open spec fn abstract_superblock_raw_wf(raw: RawPage) -> bool
{
    &&& DiskLayout::spec_new().fmt.parsable(raw)
    &&& DiskLayout::spec_new().spec_parse_inner(raw).wf()
}

pub proof fn superblock_matches_image_wf(
    raw: RawPage,
    image: AbstractSuperblockImage,
)
    requires
        superblock_matches(raw, image),
    ensures
        image.wf(),
{
    let parsed =
        DiskLayout::spec_new().spec_parse_inner(raw);
    assert(parsed.wf());
    assert(parsed@ == image);
    assert(image.wf());
}

} // verus!
