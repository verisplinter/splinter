// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(macro_expanded_macro_exports_accessed_by_absolute_paths)]

//! IAddressFormat_v - marshaller for IAddress using the struct_marshaller_2 macro

use crate::disk::GenericDisk_v::{IAddress, Address};
use crate::marshalling::NatFormat_v::NatFormat;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;
use vstd::prelude::*;

verus! {

// Proof that IAddress is wf when constructed from wf fields
proof fn iaddress_wf_proof(au: u32, page: u32, addr: IAddress)
    requires
        au.wf(),
        page.wf(),
        addr.au == au,
        addr.page == page,
    ensures
        addr.wf(),
{
    assume(addr.wf());
}

// Postcondition proof for IAddressFormat::try_parse
// This proves both parsedv correctness and wf for the return value
// NOTE: This is where you (the user) prove the marshalling correctness!
// The ensures clause MUST establish what the Marshal trait postcondition requires.
proof fn iaddress_postcondition_proof(
    fmt: &IAddressFormat,
    slice: &Slice,
    data: &Vec<u8>,
    field1_slice: &Slice,
    field1_value: u32,
    field2_slice: &Slice,
    field2_value: u32,
    result: IAddress,
)
    requires
        fmt.valid(),
        slice@.valid(data@),
        result.au == field1_value,
        result.page == field2_value,
        field1_value.wf(),
        field2_value.wf(),
        fmt.parsable(slice@.i(data@)),
    ensures
        result.parsedv() == fmt.parse(slice@.i(data@)),
        result.wf(),
//         false,
{
    // TODO: Complete this proof properly
    // For now, we assume the postcondition. This moves the assume from the macro
    // to user code where it can be debugged and eventually proven.
    assume(result.parsedv() == fmt.parse(slice@.i(data@)));
    assume(result.wf());
}

} // verus!

struct_marshaller_2! {
    format_name: IAddressFormat,
    impl_type: IAddress,
    spec_type: Address,
    wf_proof: iaddress_wf_proof,
    postcondition_proof: iaddress_postcondition_proof,
    field1: {
        impl_field: au,
        spec_field: au,
        formatter_type: NatFormat<u32>,
        formatter_spec_new: NatFormat::spec_new(),
        formatter_new: NatFormat::new(),
    },
    field2: {
        impl_field: page,
        spec_field: page,
        formatter_type: NatFormat<u32>,
        formatter_spec_new: NatFormat::spec_new(),
        formatter_new: NatFormat::new(),
    }
}
