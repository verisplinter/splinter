// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

//! ISuperblockFormat_v - marshaller for the concrete unified-cache superblock.

use vstd::prelude::*;

use crate::disk::GenericDisk_v::Address;
use crate::implementation::CachedJournal_v::JournalSnapshot;
use crate::implementation::JournalImpl_v::IJournalSnapshot;
use crate::implementation::SuperblockTypes_v::{
    ASuperblock, ASuperblockBranchImage, ASuperblockGeometry,
    ASuperblockJournalImage, ASuperblockPayload, ISuperblock,
    ISuperblockBranchImage, ISuperblockGeometry, ISuperblockJournalImage,
    ISuperblockPayload,
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
use crate::trusted::ClientAPI_t::BLOCK_SIZE;

verus! {

// The fixed-width geometry/journal/branch fields occupy 45 bytes, leaving 955 bytes
// for the length-prefixed sealed-root vector in a 1000-byte disk page.
pub const SUPERBLOCK_BRANCH_ROOTS_SIZE: usize = 955;

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

proof fn isuperblock_geometry_wf_proof(
    pages_per_au: u32,
    formatted_au_count: u32,
    geometry: ISuperblockGeometry,
)
    requires
        pages_per_au.wf(),
        formatted_au_count.wf(),
        geometry.pages_per_au == pages_per_au,
        geometry.formatted_au_count == formatted_au_count,
    ensures
        geometry.wf(),
{
}

proof fn isuperblock_geometry_postcondition_proof(
    fmt: &ISuperblockGeometryFormat,
    slice: &Slice,
    data: &Vec<u8>,
    field1_slice: &Slice,
    field1_value: u32,
    field2_slice: &Slice,
    field2_value: u32,
    result: ISuperblockGeometry,
)
    requires
        fmt.valid(),
        slice@.valid(data@),
        result.pages_per_au == field1_value,
        result.formatted_au_count == field2_value,
        field1_value.wf(),
        field2_value.wf(),
        fmt.parsable(slice@.i(data@)),
        Parsedview::<nat>::parsedv(&field1_value)
            == fmt.field1_fmt.parse(field1_slice@.i(data@)),
        Parsedview::<nat>::parsedv(&field2_value)
            == fmt.field2_fmt.parse(field2_slice@.i(data@)),
        field1_slice@.i(data@) == slice@.i(data@).subrange(
            0,
            fmt.field1_fmt.uniform_size() as int,
        ),
        field2_slice@.i(data@) == slice@.i(data@).subrange(
            fmt.field1_fmt.uniform_size() as int,
            fmt.field1_fmt.uniform_size() as int + fmt.field2_fmt.uniform_size() as int,
        ),
    ensures
        result.parsedv() == fmt.parse(slice@.i(data@)),
        result.wf(),
{
}

} // verus!

struct_marshaller_2! {
    format_name: ISuperblockGeometryFormat,
    impl_type: ISuperblockGeometry,
    spec_type: ASuperblockGeometry,
    wf_proof: isuperblock_geometry_wf_proof,
    postcondition_proof: isuperblock_geometry_postcondition_proof,
    field1: {
        impl_field: pages_per_au,
        spec_field: pages_per_au,
        formatter_type: NatFormat<u32>,
        formatter_spec_new: NatFormat::spec_new(),
        formatter_new: NatFormat::new(),
    },
    field2: {
        impl_field: formatted_au_count,
        spec_field: formatted_au_count,
        formatter_type: NatFormat<u32>,
        formatter_spec_new: NatFormat::spec_new(),
        formatter_new: NatFormat::new(),
    }
}

verus! {

proof fn isuperblock_payload_wf_proof(
    journal: ISuperblockJournalImage,
    branch: ISuperblockBranchImage,
    payload: ISuperblockPayload,
)
    requires
        journal.wf(),
        branch.wf(),
        payload.journal == journal,
        payload.branch == branch,
    ensures
        payload.wf(),
{
}

proof fn isuperblock_payload_postcondition_proof(
    fmt: &ISuperblockPayloadFormat,
    slice: &Slice,
    data: &Vec<u8>,
    field1_slice: &Slice,
    field1_value: ISuperblockJournalImage,
    field2_slice: &Slice,
    field2_value: ISuperblockBranchImage,
    result: ISuperblockPayload,
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
    format_name: ISuperblockPayloadFormat,
    impl_type: ISuperblockPayload,
    spec_type: ASuperblockPayload,
    wf_proof: isuperblock_payload_wf_proof,
    postcondition_proof: isuperblock_payload_postcondition_proof,
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

verus! {

proof fn isuperblock_wf_proof(
    geometry: ISuperblockGeometry,
    payload: ISuperblockPayload,
    sb: ISuperblock,
)
    requires
        geometry.wf(),
        payload.wf(),
        sb.geometry == geometry,
        sb.payload == payload,
    ensures
        sb.wf(),
{
}

proof fn isuperblock_postcondition_proof(
    fmt: &ISuperblockFormat,
    slice: &Slice,
    data: &Vec<u8>,
    field1_slice: &Slice,
    field1_value: ISuperblockGeometry,
    field2_slice: &Slice,
    field2_value: ISuperblockPayload,
    result: ISuperblock,
)
    requires
        fmt.valid(),
        slice@.valid(data@),
        result.geometry == field1_value,
        result.payload == field2_value,
        field1_value.wf(),
        field2_value.wf(),
        fmt.parsable(slice@.i(data@)),
        Parsedview::<ASuperblockGeometry>::parsedv(&field1_value)
            == fmt.field1_fmt.parse(field1_slice@.i(data@)),
        Parsedview::<ASuperblockPayload>::parsedv(&field2_value)
            == fmt.field2_fmt.parse(field2_slice@.i(data@)),
        field1_slice@.i(data@) == slice@.i(data@).subrange(
            0,
            fmt.field1_fmt.uniform_size() as int,
        ),
        field2_slice@.i(data@) == slice@.i(data@).subrange(
            fmt.field1_fmt.uniform_size() as int,
            fmt.field1_fmt.uniform_size() as int + fmt.field2_fmt.uniform_size() as int,
        ),
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
        impl_field: geometry,
        spec_field: geometry,
        formatter_type: ISuperblockGeometryFormat,
        formatter_spec_new: ISuperblockGeometryFormat::spec_new(),
        formatter_new: ISuperblockGeometryFormat::new(),
    },
    field2: {
        impl_field: payload,
        spec_field: payload,
        formatter_type: ISuperblockPayloadFormat,
        formatter_spec_new: ISuperblockPayloadFormat::spec_new(),
        formatter_new: ISuperblockPayloadFormat::new(),
    }
}

verus! {

pub proof fn isuperblock_format_uniform_size(fmt: &ISuperblockFormat)
    requires
        *fmt == ISuperblockFormat::spec_new(),
    ensures
        fmt.uniform_size() == BLOCK_SIZE,
{
    assert(BLOCK_SIZE == 1000);
    assert(fmt.field1_fmt.field1_fmt.uniform_size() == 4);
    assert(fmt.field1_fmt.field2_fmt.uniform_size() == 4);
    assert(fmt.field1_fmt.uniform_size() == 8);

    assert(fmt.field2_fmt.field2_fmt.field1_fmt.total_size
        == SUPERBLOCK_BRANCH_ROOTS_SIZE);
    assert(fmt.field2_fmt.field2_fmt.field1_fmt.uniform_size() == 955);
    assert(fmt.field2_fmt.field2_fmt.field2_fmt.uniform_size() == 8);
    assert(fmt.field2_fmt.field2_fmt.uniform_size() == 963);

    assert(fmt.field2_fmt.field1_fmt.field1_fmt.field1_fmt.uniform_size() == 8);
    assert(fmt.field2_fmt.field1_fmt.field1_fmt.field2_fmt.f.field1_fmt.uniform_size() == 4);
    assert(fmt.field2_fmt.field1_fmt.field1_fmt.field2_fmt.f.field2_fmt.uniform_size() == 4);
    assert(fmt.field2_fmt.field1_fmt.field1_fmt.field2_fmt.f.uniform_size() == 8);
    assert(fmt.field2_fmt.field1_fmt.field1_fmt.field2_fmt.uniform_size() == 9);
    assert(fmt.field2_fmt.field1_fmt.field1_fmt.field3_fmt.uniform_size() == 4);
    assert(fmt.field2_fmt.field1_fmt.field1_fmt.uniform_size() == 21);
    assert(fmt.field2_fmt.field1_fmt.field2_fmt.uniform_size() == 8);
    assert(fmt.field2_fmt.field1_fmt.uniform_size() == 29);
    assert(fmt.field2_fmt.uniform_size() == 992);
    assert(fmt.uniform_size() == 1000);
}

pub proof fn branch_roots_format_max_length_fits_u8(fmt: &ISuperblockFormat)
    requires
        *fmt == ISuperblockFormat::spec_new(),
    ensures
        fmt.field2_fmt.field2_fmt.field1_fmt.max_length <= u8::MAX as int,
{
    let roots_fmt = fmt.field2_fmt.field2_fmt.field1_fmt;
    assert(roots_fmt.total_size == SUPERBLOCK_BRANCH_ROOTS_SIZE);
    assert(roots_fmt.lenf.uniform_size() == 1);
    assert(roots_fmt.eltf.field1_fmt.uniform_size() == 4);
    assert(roots_fmt.eltf.field2_fmt.uniform_size() == 4);
    assert(roots_fmt.eltf.uniform_size() == 8);
    assert(roots_fmt.max_length
        == (SUPERBLOCK_BRANCH_ROOTS_SIZE - 1) as usize / 8);
}

} // verus!
