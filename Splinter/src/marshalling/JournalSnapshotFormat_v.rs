// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(macro_expanded_macro_exports_accessed_by_absolute_paths)]

//! JournalSnapshotFormat_v - marshaller for JournalSnapshot using the struct_marshaller_2 macro

use crate::implementation::JournalImpl_v::JournalSnapshot;
use crate::implementation::CachedJournal_v::JournalSnapShot;
use crate::disk::GenericDisk_v::IAddress;
use crate::marshalling::NatFormat_v::NatFormat;
use crate::marshalling::IAddressFormat_v::IAddressFormat;
use crate::marshalling::OptionFormat_v::OptionFormat;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;
use vstd::prelude::*;

verus! {

// Proof that JournalSnapshot is wf when constructed from wf fields
proof fn journal_snapshot_wf_proof(
    boundary_lsn: u64,
    freshest_rec: Option<IAddress>,
    js: JournalSnapshot
)
    requires
        boundary_lsn.wf(),
        freshest_rec.wf(),
        js.boundary_lsn == boundary_lsn,
        js.freshest_rec == freshest_rec,
    ensures
        js.wf(),
{
    assume(js.wf());
}

// Postcondition proof for JournalSnapshotFormat::try_parse
proof fn journal_snapshot_postcondition_proof(
    fmt: &JournalSnapshotFormat,
    slice: &Slice,
    data: &Vec<u8>,
    field1_slice: &Slice,
    field1_value: u64,
    field2_slice: &Slice,
    field2_value: Option<IAddress>,
    result: JournalSnapshot,
)
    requires
        fmt.valid(),
        slice@.valid(data@),
        result.boundary_lsn == field1_value,
        result.freshest_rec == field2_value,
        field1_value.wf(),
        field2_value.wf(),
        fmt.parsable(slice@.i(data@)),
    ensures
        result.parsedv() == fmt.parse(slice@.i(data@)),
        result.wf(),
{
    assume(result.parsedv() == fmt.parse(slice@.i(data@)));
    assume(result.wf());
}

} // verus!

struct_marshaller_2! {
    format_name: JournalSnapshotFormat,
    impl_type: JournalSnapshot,
    spec_type: JournalSnapShot,
    wf_proof: journal_snapshot_wf_proof,
    postcondition_proof: journal_snapshot_postcondition_proof,
    field1: {
        impl_field: boundary_lsn,
        spec_field: boundary_lsn,
        formatter_type: NatFormat<u64>,
        formatter_spec_new: NatFormat::spec_new(),
        formatter_new: NatFormat::new(),
    },
    field2: {
        impl_field: freshest_rec,
        spec_field: freshest_rec,
        formatter_type: OptionFormat<IAddressFormat>,
        formatter_spec_new: OptionFormat::spec_new(IAddressFormat::spec_new()),
        formatter_new: OptionFormat::new(IAddressFormat::new()),
    }
}
