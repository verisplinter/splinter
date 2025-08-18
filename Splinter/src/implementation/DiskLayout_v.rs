// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
// use vstd::hash_map::*;
use crate::spec::MapSpec_t::*;
use crate::spec::AsyncDisk_t::*;
use crate::spec::ImplDisk_t::*;
use crate::spec::TotalKMMap_t::*;
use crate::spec::FloatingSeq_t::*;
use crate::implementation::SuperblockTypes_v::*;
use crate::implementation::JournalTypes_v::*;
use crate::marshalling::ISuperblockFormat_v::*;
use crate::marshalling::Marshalling_v::*;
use crate::marshalling::Slice_v::*;
use crate::trusted::ClientAPI_t::BLOCK_SIZE;
use crate::marshalling::UniformSized_v::UniformSized;

verus! {

pub open spec fn spec_superblock_addr() -> Address {
    Address{au: 0, page: 0}
}

pub fn superblock_addr() -> (out: IAddress)
ensures out@ == spec_superblock_addr()
{
    IAddress{au: 0, page: 0}
}

pub open spec(checked) fn singleton_floating_seq(at_index: nat, kmmap: TotalKMMap) -> FloatingSeq<Version>
{
    FloatingSeq::new(at_index, at_index+1,
          |i| Version{ appv: MapSpec::State{ kmmap } } )
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
        self.fmt.valid()
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
    // same thing back.

    pub fn marshall(&self, sb: &ISuperblock) -> (out: IPageData)
    requires
        self.wf(),
    ensures
        sb@ == self.spec_parse(out@.subrange(0, self.fmt.uniform_size() as int))
    {
        assert( self.fmt.valid() );
        assume( self.fmt.marshallable(sb.deepv()) );
//         let mut space = empty_vec_u8_with_size(self.fmt.exec_size(sb));

        let ghost marshalled_size = self.fmt.uniform_size();
//         proof { self.fmt.size_is() }
        assert( marshalled_size == 408 );
        assert( marshalled_size <= BLOCK_SIZE );
        let mut space = empty_vec_u8_with_size(BLOCK_SIZE);
//         assert( self.fmt.spec_size(sb.deepv()) == space.len() );
        assert(0 as int + self.fmt.spec_size(sb.deepv()) as int <= space.len() );
        let end = self.fmt.exec_marshall(sb, &mut space, 0);
        assert( end == self.fmt.spec_size(sb.deepv()) );
//         assert( space@ == space@.subrange(0, end as int) );
        assert( self.fmt.parse(space@.subrange(0, marshalled_size as int)) == sb.deepv() );
        space
    }

    pub fn parse(&self, raw_page: &IPageData) -> (out: ISuperblock)
    requires
        self.wf(),
    ensures
        out@ == self.spec_parse(raw_page@)
    {
        assume( self.fmt.parsable(raw_page@) );  // TODO carry in from disk invariant
        let all_slice = Slice::all(raw_page);
        assert( all_slice@.i(raw_page@) == raw_page@ );
        let out = self.fmt.exec_parse(&all_slice, raw_page);
        assert( out@ == self.spec_parse(raw_page@) );
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
    ensures out.wf()
    {
        DiskLayout{
            fmt: ISuperblockFormat::new()
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
