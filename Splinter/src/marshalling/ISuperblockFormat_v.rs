// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

//! ISuperblockFormat_v - marshaller for the concrete unified-cache superblock.

use vstd::prelude::*;

use crate::disk::GenericDisk_v::Address;
use crate::implementation::CachedJournal_v::JournalSnapshot;
use crate::implementation::JournalImpl_v::IJournalSnapshot;
use crate::implementation::SuperblockTypes_v::{
    ASuperblock, ASuperblockBranchImage, ASuperblockJournalImage, ISuperblock,
    ISuperblockBranchImage, ISuperblockJournalImage,
};
use crate::marshalling::IAddressFormat_v::IAddressFormat;
use crate::marshalling::IJournalSnapshotFormat_v::IJournalSnapshotFormat;
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::NatFormat_v::NatFormat;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::WF_v::WF;

verus! {

pub const SUPERBLOCK_BRANCH_ROOTS_SIZE: usize = 512;

pub type IBranchRootsFormat = ResizableUniformSizedElementSeqFormat<IAddressFormat, u8>;

pub open spec fn branch_roots_format_spec_new() -> IBranchRootsFormat
{
    ResizableUniformSizedElementSeqFormat::spec_new(
        IAddressFormat::spec_new(),
        IntFormat::<u8>::spec_new(),
        SUPERBLOCK_BRANCH_ROOTS_SIZE,
    )
}

pub fn branch_roots_format_new() -> (out: IBranchRootsFormat)
    ensures
        out.valid(),
        out == branch_roots_format_spec_new(),
{
    ResizableUniformSizedElementSeqFormat::new(
        IAddressFormat::new(),
        IntFormat::<u8>::new(),
        SUPERBLOCK_BRANCH_ROOTS_SIZE,
    )
}

proof fn isuperblock_journal_wf_proof(
    snapshot: IJournalSnapshot,
    seq_end: u64,
    image: ISuperblockJournalImage,
)
    requires
        snapshot.wf(),
        seq_end.wf(),
        image.snapshot == snapshot,
        image.seq_end == seq_end,
    ensures
        image.wf(),
{
}

proof fn isuperblock_journal_postcondition_proof(
    fmt: &ISuperblockJournalFormat,
    slice: &Slice,
    data: &Vec<u8>,
    field1_slice: &Slice,
    field1_value: IJournalSnapshot,
    field2_slice: &Slice,
    field2_value: u64,
    result: ISuperblockJournalImage,
)
    requires
        fmt.valid(),
        slice@.valid(data@),
        result.snapshot == field1_value,
        result.seq_end == field2_value,
        field1_value.wf(),
        field2_value.wf(),
        fmt.parsable(slice@.i(data@)),
        Parsedview::<JournalSnapshot>::parsedv(&field1_value)
            == fmt.field1_fmt.parse(field1_slice@.i(data@)),
        Parsedview::<nat>::parsedv(&field2_value)
            == fmt.field2_fmt.parse(field2_slice@.i(data@)),
        field1_slice@.i(data@) == slice@.i(data@).subrange(0, fmt.field1_fmt.uniform_size() as int),
        field2_slice@.i(data@) == slice@.i(data@).subrange(
            fmt.field1_fmt.uniform_size() as int,
            fmt.field1_fmt.uniform_size() as int + fmt.field2_fmt.uniform_size() as int),
    ensures
        result.parsedv() == fmt.parse(slice@.i(data@)),
        result.wf(),
{
}

} // verus!

struct_marshaller_2! {
    format_name: ISuperblockJournalFormat,
    impl_type: ISuperblockJournalImage,
    spec_type: ASuperblockJournalImage,
    wf_proof: isuperblock_journal_wf_proof,
    postcondition_proof: isuperblock_journal_postcondition_proof,
    field1: {
        impl_field: snapshot,
        spec_field: snapshot,
        formatter_type: IJournalSnapshotFormat,
        formatter_spec_new: IJournalSnapshotFormat::spec_new(),
        formatter_new: IJournalSnapshotFormat::new(),
    },
    field2: {
        impl_field: seq_end,
        spec_field: seq_end,
        formatter_type: NatFormat<u64>,
        formatter_spec_new: NatFormat::spec_new(),
        formatter_new: NatFormat::new(),
    }
}

verus! {

proof fn isuperblock_branch_wf_proof(
    roots: Vec<crate::spec::ImplDisk_t::IAddress>,
    seq_end: u64,
    image: ISuperblockBranchImage,
)
    requires
        roots.wf(),
        seq_end.wf(),
        image.roots == roots,
        image.seq_end == seq_end,
    ensures
        image.wf(),
{
}

proof fn isuperblock_branch_postcondition_proof(
    fmt: &ISuperblockBranchFormat,
    slice: &Slice,
    data: &Vec<u8>,
    field1_slice: &Slice,
    field1_value: Vec<crate::spec::ImplDisk_t::IAddress>,
    field2_slice: &Slice,
    field2_value: u64,
    result: ISuperblockBranchImage,
)
    requires
        fmt.valid(),
        slice@.valid(data@),
        result.roots == field1_value,
        result.seq_end == field2_value,
        field1_value.wf(),
        field2_value.wf(),
        fmt.parsable(slice@.i(data@)),
        Parsedview::<Seq<Address>>::parsedv(&field1_value)
            == fmt.field1_fmt.parse(field1_slice@.i(data@)),
        Parsedview::<nat>::parsedv(&field2_value)
            == fmt.field2_fmt.parse(field2_slice@.i(data@)),
        field1_slice@.i(data@) == slice@.i(data@).subrange(0, fmt.field1_fmt.uniform_size() as int),
        field2_slice@.i(data@) == slice@.i(data@).subrange(
            fmt.field1_fmt.uniform_size() as int,
            fmt.field1_fmt.uniform_size() as int + fmt.field2_fmt.uniform_size() as int),
    ensures
        result.parsedv() == fmt.parse(slice@.i(data@)),
        result.wf(),
{
}

} // verus!

struct_marshaller_2! {
    format_name: ISuperblockBranchFormat,
    impl_type: ISuperblockBranchImage,
    spec_type: ASuperblockBranchImage,
    wf_proof: isuperblock_branch_wf_proof,
    postcondition_proof: isuperblock_branch_postcondition_proof,
    field1: {
        impl_field: roots,
        spec_field: roots,
        formatter_type: IBranchRootsFormat,
        formatter_spec_new: branch_roots_format_spec_new(),
        formatter_new: branch_roots_format_new(),
    },
    field2: {
        impl_field: seq_end,
        spec_field: seq_end,
        formatter_type: NatFormat<u64>,
        formatter_spec_new: NatFormat::spec_new(),
        formatter_new: NatFormat::new(),
    }
}

verus! {

proof fn isuperblock_wf_proof(
    journal: ISuperblockJournalImage,
    branch: ISuperblockBranchImage,
    sb: ISuperblock,
)
    requires
        journal.wf(),
        branch.wf(),
        sb.journal == journal,
        sb.branch == branch,
    ensures
        sb.wf(),
{
}

proof fn isuperblock_postcondition_proof(
    fmt: &ISuperblockFormat,
    slice: &Slice,
    data: &Vec<u8>,
    field1_slice: &Slice,
    field1_value: ISuperblockJournalImage,
    field2_slice: &Slice,
    field2_value: ISuperblockBranchImage,
    result: ISuperblock,
)
    requires
        fmt.valid(),
        slice@.valid(data@),
        result.journal == field1_value,
        result.branch == field2_value,
        field1_value.wf(),
        field2_value.wf(),
        fmt.parsable(slice@.i(data@)),
        Parsedview::<ASuperblockJournalImage>::parsedv(&field1_value)
            == fmt.field1_fmt.parse(field1_slice@.i(data@)),
        Parsedview::<ASuperblockBranchImage>::parsedv(&field2_value)
            == fmt.field2_fmt.parse(field2_slice@.i(data@)),
        field1_slice@.i(data@) == slice@.i(data@).subrange(0, fmt.field1_fmt.uniform_size() as int),
        field2_slice@.i(data@) == slice@.i(data@).subrange(
            fmt.field1_fmt.uniform_size() as int,
            fmt.field1_fmt.uniform_size() as int + fmt.field2_fmt.uniform_size() as int),
    ensures
        result.parsedv() == fmt.parse(slice@.i(data@)),
        result.wf(),
{
}

} // verus!

struct_marshaller_2! {
    format_name: ISuperblockFormat,
    impl_type: ISuperblock,
    spec_type: ASuperblock,
    wf_proof: isuperblock_wf_proof,
    postcondition_proof: isuperblock_postcondition_proof,
    field1: {
        impl_field: journal,
        spec_field: journal,
        formatter_type: ISuperblockJournalFormat,
        formatter_spec_new: ISuperblockJournalFormat::spec_new(),
        formatter_new: ISuperblockJournalFormat::new(),
    },
    field2: {
        impl_field: branch,
        spec_field: branch,
        formatter_type: ISuperblockBranchFormat,
        formatter_spec_new: ISuperblockBranchFormat::spec_new(),
        formatter_new: ISuperblockBranchFormat::new(),
    }
}
