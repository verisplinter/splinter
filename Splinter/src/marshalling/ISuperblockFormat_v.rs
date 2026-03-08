// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

//! ISuperblockFormat_v - marshaller for ISuperblock using the struct_marshaller_2 macro

use crate::implementation::SuperblockTypes_v::{ASuperblock, ISuperblock};
use crate::implementation::JournalImpl_v::IJournalSnapshot;
use crate::marshalling::IJournalSnapshotFormat_v::IJournalSnapshotFormat;
use crate::marshalling::OptionFormat_v::OptionFormat;
use crate::marshalling::IAddressFormat_v::IAddressFormat;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;
use crate::disk::GenericDisk_v::Pointer;
use vstd::prelude::*;

verus! {

proof fn isuperblock_wf_proof(
    journal_snapshot: IJournalSnapshot,
    store_ptr: Option<crate::spec::ImplDisk_t::IAddress>,
    sb: ISuperblock
)
    requires
        journal_snapshot.wf(),
        store_ptr.wf(),
        sb.journal_snapshot == journal_snapshot,
        sb.store_ptr == store_ptr,
    ensures
        sb.wf(),
{
}

proof fn isuperblock_postcondition_proof(
    fmt: &ISuperblockFormat,
    slice: &Slice,
    data: &Vec<u8>,
    field1_slice: &Slice,
    field1_value: IJournalSnapshot,
    field2_slice: &Slice,
    field2_value: Option<crate::spec::ImplDisk_t::IAddress>,
    result: ISuperblock,
)
    requires
        fmt.valid(),
        slice@.valid(data@),
        result.journal_snapshot == field1_value,
        result.store_ptr == field2_value,
        field1_value.wf(),
        field2_value.wf(),
        fmt.parsable(slice@.i(data@)),
        Parsedview::<crate::implementation::CachedJournal_v::JournalSnapshot>::parsedv(&field1_value) == fmt.field1_fmt.parse(field1_slice@.i(data@)),
        Parsedview::<Pointer>::parsedv(&field2_value) == fmt.field2_fmt.parse(field2_slice@.i(data@)),
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
        impl_field: journal_snapshot,
        spec_field: journal,
        formatter_type: IJournalSnapshotFormat,
        formatter_spec_new: IJournalSnapshotFormat::spec_new(),
        formatter_new: IJournalSnapshotFormat::new(),
    },
    field2: {
        impl_field: store_ptr,
        spec_field: store_ptr,
        formatter_type: OptionFormat<IAddressFormat>,
        formatter_spec_new: OptionFormat::spec_new(IAddressFormat::spec_new()),
        formatter_new: OptionFormat::new(IAddressFormat::new()),
    }
}
