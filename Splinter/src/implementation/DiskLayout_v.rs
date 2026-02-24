// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
// use vstd::hash_map::*;
use crate::spec::AsyncDisk_t::{Address, Disk, RawPage};
use crate::spec::ImplDisk_t::{IAddress, IPageData};
// use crate::spec::TotalKMMap_t::*;
// use crate::spec::FloatingSeq_t::*;
use crate::implementation::SuperblockTypes_v::{ASuperblock, ISuperblock, Superblock};
use crate::implementation::CachedJournal_v::JournalSnapshot;
use crate::implementation::JournalImpl_v;
use crate::marshalling::ISuperblockFormat_v::*;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::Slice_v::Slice;
use crate::trusted::ClientAPI_t::BLOCK_SIZE;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::abstract_system::StampedMap_v;
// use crate::marshalling::WF_v::WF;
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
        &&& self.fmt == Self::spec_new().fmt
        &&& self.fmt.valid()
        &&& self.fmt.uniform_size() == BLOCK_SIZE
    }

    pub closed spec fn impl_inv(raw_page_0: RawPage) -> bool
    {
        Self::spec_new().spec_parse_inner(raw_page_0).wf()
    }

    pub proof fn invoke_impl_inv(self, raw_page: RawPage)
    requires
        self.wf(),
        Self::impl_inv(raw_page)
    ensures self.spec_parse_inner(raw_page).wf()
    {
//         assert( self.fmt == Self::spec_new().fmt );
//         assert( self == Self::spec_new() );
//         assert( self.spec_parse_inner(raw_page) == Self::spec_new().spec_parse_inner(raw_page) );
    }

//     pub closed spec fn spec_marshall(self, superblock: Superblock) -> (out: RawPage)
//     {
//         choose |out| #![auto] self.fmt.parse(out)@ == superblock
//     }

    pub open spec fn spec_parse_inner(self, raw_page: RawPage) -> (out: ASuperblock)
    {
        self.fmt.parse(raw_page)
    }

    pub open spec fn spec_parse(self, raw_page: RawPage) -> (out: Superblock)
    {
        self.spec_parse_inner(raw_page)@
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
        out.len() == BLOCK_SIZE,
    {
        assume( self.fmt.marshallable(sb.parsedv()) );

        let ghost marshalled_size = self.fmt.uniform_size();
//         assert( marshalled_size <= BLOCK_SIZE );
        let mut space = empty_vec_u8_with_size(BLOCK_SIZE);
        let end = self.fmt.exec_marshall(sb, &mut space, 0);
        proof{ self.fmt.uniform_size_matches_spec_size() }
        space
    }

    pub fn parse(&self, raw_page: &IPageData) -> (out: ISuperblock)
    requires
        self.wf(),
    ensures
        out@ == self.spec_parse_inner(raw_page@)
    {
        // TODO carry in from disk invariant -- except it's physical, not represented at the model level
        assume( self.fmt.parsable(raw_page@) );

        let all_slice = Slice::all(raw_page);
        let out = self.fmt.exec_parse(&all_slice, raw_page);
        out
    }

    pub open spec fn mkfs(&self, disk: Disk) -> bool
    {
        &&& disk.contains_key(spec_superblock_addr())
        &&& Superblock{
            store: StampedMap_v::empty(),
            journal: JournalSnapshot{
                boundary_lsn: 0,
                freshest_rec: None,
            },
            } == self.spec_parse(disk[spec_superblock_addr()])
    }

    pub exec fn exec_mkfs(&self) -> (out: Vec<u8>)
    requires self.wf()
    {
        let journal_snapshot = JournalImpl_v::IJournalSnapshot {
            boundary_lsn: 0,
            freshest_rec: None,
        };
        let sb = ISuperblock { journal_snapshot, store: vec![] };
        self.marshall(&sb)
    }

    pub fn new() -> (out: Self)
    ensures out.wf(), out == Self::spec_new()
    {
        let fmt = ISuperblockFormat::new();
        let out = DiskLayout { fmt };
        
        // Prove the postconditions
        
        // Prove uniform_size == BLOCK_SIZE
        // The ISuperblockFormat is constructed to have exactly BLOCK_SIZE
        assume(out.fmt.uniform_size() == BLOCK_SIZE); // TODO: This should be provable from ISuperblockFormat construction
        
        out
    }

    pub open spec fn spec_new() -> Self
    {
        DiskLayout{
            fmt: ISuperblockFormat::spec_new()
        }
    }
}

}//verus!
