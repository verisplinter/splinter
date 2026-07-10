// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
// use vstd::hash_map::*;
use crate::spec::AsyncDisk_t::{Address, Disk, RawPage};
use crate::spec::ImplDisk_t::{IAddress, IAU, IPage, IPageData};
// use crate::spec::TotalKMMap_t::*;
// use crate::spec::FloatingSeq_t::*;
use crate::implementation::SuperblockTypes_v::{
    ASuperblock, ASuperblockGeometry, ASuperblockPayload, ISuperblock,
    ISuperblockBranchImage, ISuperblockGeometry, ISuperblockJournalImage,
    ISuperblockPayload, Superblock,
};
use crate::implementation::CachedJournal_v::JournalSnapshot;
use crate::implementation::JournalImpl_v;
use crate::marshalling::ISuperblockFormat_v::*;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::Slice_v::Slice;
use crate::trusted::ClientAPI_t::BLOCK_SIZE;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
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

pub fn empty_vec_u8_with_size(s: usize) -> (out: Vec<u8>)
ensures out.len() == s
{
    let mut out = Vec::with_capacity(s);
    while out.len() < s
        invariant
            out.len() <= s,
        decreases s - out.len(),
    {
        out.push(0);
    }
    out
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

    pub fn can_marshall(&self, sb: &ISuperblock) -> (out: bool)
        requires
            self.wf(),
        ensures
            out ==> self.fmt.marshallable(sb.parsedv()),
            out ==> self.fmt.impl_marshallable(*sb),
    {
        let roots_fit = sb.payload.branch.roots.len()
            <= self.fmt.field2_fmt.field2_fmt.field1_fmt.max_length;
        if !roots_fit {
            return false;
        }
        proof {
            assert(sb.payload.branch@.roots.len()
                <= self.fmt.field2_fmt.field2_fmt.field1_fmt.max_length);
            branch_roots_format_max_length_fits_u8(&self.fmt);
            assert(sb.payload.branch@.roots.len() <= u8::MAX as int);
            assert forall |i: int| 0 <= i < sb.payload.branch@.roots.len()
                implies self.fmt.field2_fmt.field2_fmt.field1_fmt.marshallable_at(
                    sb.payload.branch@.roots,
                    i,
                ) by {
            }
            assert(self.fmt.field2_fmt.field2_fmt.field1_fmt.marshallable(
                sb.payload.branch@.roots,
            ));
            assert(self.fmt.marshallable(sb.parsedv()));
            assert(self.fmt.impl_marshallable(*sb));
        }
        true
    }

    pub fn marshall(&self, sb: &ISuperblock) -> (out: IPageData)
    requires
        self.wf(),
        self.fmt.marshallable(sb.parsedv()),
        self.fmt.impl_marshallable(*sb),
    ensures
        sb@ == self.spec_parse_inner(out@),
        sb@@ == self.spec_parse(out@),
        self.fmt.parsable(out@),
        sb@.wf() ==> crate::implementation::AbstractSuperblock_v::superblock_matches(out@, sb@@),
        out.len() == BLOCK_SIZE,
    {
        proof {
            self.fmt.uniform_size_matches_spec_size();
            assert(self.fmt.spec_size(sb.parsedv()) == self.fmt.uniform_size());
            assert(self.fmt.spec_size(sb.parsedv()) == BLOCK_SIZE);
        }
        let mut space = empty_vec_u8_with_size(BLOCK_SIZE);
        let end = self.fmt.exec_marshall(sb, &mut space, 0);
        proof {
            assert(end == BLOCK_SIZE);
            assert(space@.subrange(0, end as int) =~= space@);
            assert(self.fmt.parsable(space@));
            assert(self.fmt.parse(space@) == sb.parsedv());
            assert(self.spec_parse_inner(space@) == sb.parsedv());
            assert(self.spec_parse(space@) == sb@@);
            if sb@.wf() {
                assert(crate::implementation::AbstractSuperblock_v::abstract_superblock_raw_wf(
                    space@,
                ));
                assert(crate::implementation::AbstractSuperblock_v::superblock_matches(
                    space@,
                    sb@@,
                ));
            }
        }
        space
    }

    pub fn parse(&self, raw_page: &IPageData) -> (out: ISuperblock)
    requires
        self.wf(),
        self.fmt.parsable(raw_page@),
    ensures
        out@ == self.spec_parse_inner(raw_page@)
    {
        let all_slice = Slice::all(raw_page);
        proof {
            crate::marshalling::Slice_v::SpecSlice::all_ensures::<u8>();
            assert(all_slice@.i(raw_page@) =~= raw_page@);
            assert(self.fmt.parsable(all_slice@.i(raw_page@)));
        }
        let out = self.fmt.exec_parse(&all_slice, raw_page);
        proof {
            assert(out.parsedv() == self.fmt.parse(all_slice@.i(raw_page@)));
            assert(out.parsedv() == self.fmt.parse(raw_page@));
            assert(out@ == self.spec_parse_inner(raw_page@));
        }
        out
    }

    pub open spec fn mkfs(&self, disk: Disk) -> bool
    {
        &&& disk.contains_key(spec_superblock_addr())
        &&& self.spec_parse_inner(disk[spec_superblock_addr()]).wf()
        &&& Superblock{
            journal_snapshot: JournalSnapshot{
                boundary_lsn: 0,
                root: None,
            },
            journal_seq_end: 0,
            branch_roots: Seq::empty(),
            branch_seq_end: 0,
            } == self.spec_parse(disk[spec_superblock_addr()])
    }

    pub exec fn exec_mkfs(
        &self,
        physical_au_count: IAU,
        pages_per_au: IPage,
    ) -> (out: Vec<u8>)
    requires
        self.wf(),
        1 < physical_au_count as nat,
        0 < pages_per_au as nat,
        pages_per_au as nat == crate::spec::AsyncDisk_t::page_count(),
    ensures
        out.len() == BLOCK_SIZE,
        self.spec_parse_inner(out@).wf(),
        self.spec_parse_inner(out@).geometry == (ASuperblockGeometry {
            pages_per_au: pages_per_au as nat,
            formatted_au_count: physical_au_count as nat,
        }),
        self.spec_parse(out@) == (Superblock{
            journal_snapshot: JournalSnapshot{
                boundary_lsn: 0,
                root: None,
            },
            journal_seq_end: 0,
            branch_roots: Seq::empty(),
            branch_seq_end: 0,
        }),
    {
        let journal_snapshot = JournalImpl_v::IJournalSnapshot {
            boundary_lsn: 0,
            freshest_rec: None,
            first: 0,
        };
        let journal = ISuperblockJournalImage {
            snapshot: journal_snapshot,
            seq_end: 0,
        };
        let roots = Vec::<IAddress>::new();
        proof {
            assert(Parsedview::<Seq<Address>>::parsedv(&roots) =~= Seq::<Address>::empty());
        }
        let branch = ISuperblockBranchImage {
            roots,
            seq_end: 0,
        };
        let geometry = ISuperblockGeometry {
            pages_per_au,
            formatted_au_count: physical_au_count,
        };
        let payload = ISuperblockPayload { journal, branch };
        let sb = ISuperblock { geometry, payload };
        let out = self.marshall(&sb);
        proof {
            assert(sb@@.branch_roots =~= Seq::<Address>::empty());
            assert(sb@.wf());
            assert(self.spec_parse_inner(out@) == sb@);
        }
        out
    }

    pub fn new() -> (out: Self)
    ensures out.wf(), out == Self::spec_new()
    {
        let fmt = ISuperblockFormat::new();
        let out = DiskLayout { fmt };
        
        // Prove the postconditions
        
        proof {
            isuperblock_format_uniform_size(&out.fmt);
        }
        
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
