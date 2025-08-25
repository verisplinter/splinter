// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
// use vstd::hash_map::*;
use crate::spec::MapSpec_t::*;
use crate::spec::AsyncDisk_t::*;
use crate::spec::ImplDisk_t::*;
// use crate::spec::TotalKMMap_t::*;
// use crate::spec::FloatingSeq_t::*;
use crate::implementation::SuperblockTypes_v::*;
use crate::implementation::JournalTypes_v::*;
use crate::marshalling::ISuperblockFormat_v::*;
use crate::marshalling::Marshalling_v::*;
use crate::marshalling::Slice_v::*;
use crate::trusted::ClientAPI_t::BLOCK_SIZE;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::WF_v::WF;
use crate::marshalling::UniformPairFormat_v::uniform_size_matches_spec_size;

verus! {

pub open spec fn spec_superblock_addr() -> Address {
    Address{au: 0, page: 0}
}

pub fn superblock_addr() -> (out: IAddress)
ensures out@ == spec_superblock_addr()
{
    IAddress{au: 0, page: 0}
}

pub struct DiskLayout {
    pub fmt: ISuperblockFormat,
}

#[verifier::external_body]
pub fn empty_vec_u8_with_size(s: usize) -> (out: Vec<u8>)
ensures out.len() == s
{
    vec![0; s]
}

impl DiskLayout {
    pub closed spec fn wf(self) -> bool
    {
        &&& self.fmt.valid()
        &&& self.fmt.uniform_size() == BLOCK_SIZE
    }

    // LEFT OFF:
    // Problem is that, right now, I have a 'wf' feature on ISuperblock, but that's only
    // an exec type; we can't talk about it because the result of spec fn parse is a Superblock.
    // Okay, maybe we should add these features to 'parsable', and make them a condition
    // of ISuperblockFormat::marshall? Maybe a reasonable direction, but right now
    // ISuperblockFormat is a type synonym for PaddedFormat. I'll need to construct a wrapper.
    pub closed spec fn impl_inv(raw_page_0: RawPage) -> bool
    {
        true
//         let sb: ISuperblock = Self::spec_new().spec_parse(raw_page_0);
//         sb.wf()
    }

//     pub closed spec fn spec_marshall(self, superblock: Superblock) -> (out: RawPage)
//     {
//         choose |out| #![auto] self.fmt.parse(out)@ == superblock
//     }

    pub closed spec fn spec_parse(self, raw_page: RawPage) -> (out: Superblock)
    {
        self.fmt.parse(raw_page)@
    }

    // LEFT OFF: I think we need a proof obligation that all formatters are prefix-stable:
    // if you can parse a buffer, you can parse any extension of that buffer and get the
    // same thing back. NOPE, this eliminates vector formatters that unmarshall whatever you
    // give them. We should pad the block to block size.

    pub fn marshall(&self, sb: &ISuperblock) -> (out: IPageData)
    requires
        self.wf(),
    ensures
        sb@@ == self.spec_parse(out@),
    {
        assert( self.fmt.valid() );
        assume( self.fmt.marshallable(sb.parsedv()) );

        let ghost marshalled_size = self.fmt.uniform_size();
        assert( marshalled_size == BLOCK_SIZE );
//         assert( marshalled_size <= BLOCK_SIZE );
        let mut space = empty_vec_u8_with_size(BLOCK_SIZE);
        assert(0 as int + self.fmt.spec_size(sb.parsedv()) as int <= space.len() );
        let end = self.fmt.exec_marshall(sb, &mut space, 0);
        assert( end == self.fmt.spec_size(sb.parsedv()) );
        assert( self.fmt.parse(space@.subrange(0, end as int)) == sb.parsedv() );
        proof{ self.fmt.uniform_size_matches_spec_size() }
        assert( uniform_size_matches_spec_size(self.fmt) );
        assert( self.fmt.spec_size(sb.parsedv()) == self.fmt.uniform_size() );
        assert( end as int == marshalled_size as int );
        assert( self.fmt.parse(space@.subrange(0, marshalled_size as int)) == sb.parsedv() );
        assert( space@.subrange(0, BLOCK_SIZE as int) == space@ );
        space
    }

    pub fn parse(&self, raw_page: &IPageData) -> (out: ISuperblock)
    requires
        self.wf(),
    ensures
        out@@ == self.spec_parse(raw_page@)
    {
        // TODO carry in from disk invariant -- except it's physical, not represented at the model level
        assume( self.fmt.parsable(raw_page@) );

        let all_slice = Slice::all(raw_page);
        assert( all_slice@.i(raw_page@) == raw_page@ );
        let out = self.fmt.exec_parse(&all_slice, raw_page);
        assert( out@@ == self.spec_parse(raw_page@) );
        out
    }

    pub open spec fn mkfs(&self, disk: Disk) -> bool
    {
        &&& disk.contains_key(spec_superblock_addr())
        &&& Superblock{
                store: PersistentState{ appv: my_init() },
                version_index: 0,
            } == self.spec_parse(disk[spec_superblock_addr()])
    }

    pub exec fn exec_mkfs(&self) -> (out: Vec<u8>)
    requires self.wf()
    {
        let journal = Journal{ msg_history: vec![], seq_start: 0 };
        let sb = ISuperblock { journal, store: vec![] };
        self.marshall(&sb)
    }

    pub fn new() -> (out: Self)
    ensures out.wf(), out == Self::spec_new()
    {
        DiskLayout{
            fmt: ISuperblockFormat::new(),
        }
    }

    pub open spec fn spec_new() -> Self
    {
        DiskLayout{
            fmt: ISuperblockFormat::spec_new()
        }
    }
}

}//verus!
