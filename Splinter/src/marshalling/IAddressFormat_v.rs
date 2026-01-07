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
    // IAddress::wf() returns true unconditionally (from impl WF for IAddress)
}

// Postcondition proof for IAddressFormat::try_parse
// This proves both parsedv correctness and wf for the return value
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
        // These facts come from the macro (try_parse postconditions of field formatters):
        Parsedview::<nat>::parsedv(&field1_value) == fmt.field1_fmt.parse(field1_slice@.i(data@)),
        Parsedview::<nat>::parsedv(&field2_value) == fmt.field2_fmt.parse(field2_slice@.i(data@)),
        // Slice relationships:
        field1_slice@.i(data@) == slice@.i(data@).subrange(0, fmt.field1_fmt.uniform_size() as int),
        field2_slice@.i(data@) == slice@.i(data@).subrange(
            fmt.field1_fmt.uniform_size() as int,
            fmt.field1_fmt.uniform_size() as int + fmt.field2_fmt.uniform_size() as int),
    ensures
        result.parsedv() == fmt.parse(slice@.i(data@)),
        result.wf(),
{
    // IAddress::wf() returns true unconditionally
    // result.parsedv() = Address { au: result.au as nat, page: result.page as nat }
    //                  = Address { au: field1_value as nat, page: field2_value as nat }
    // fmt.parse(...) = Address { au: fmt.field1_fmt.parse(...), page: fmt.field2_fmt.parse(...) }
    // From requires: field1_value as nat == fmt.field1_fmt.parse(...)
    // So result.parsedv() == fmt.parse(...)
    let idata = slice@.i(data@);
    let f1_end = fmt.field1_fmt.uniform_size() as int;
    let f2_end = f1_end + fmt.field2_fmt.uniform_size() as int;

    // Show the parse result matches field by field
    assert(result.parsedv().au == (field1_value as nat));
    assert(result.parsedv().page == (field2_value as nat));
    assert(fmt.parse(idata).au == fmt.field1_fmt.parse(idata.subrange(0, f1_end)));
    assert(fmt.parse(idata).page == fmt.field2_fmt.parse(idata.subrange(f1_end, f2_end)));

    // Connect via the requires
    assert(result.parsedv().au == fmt.parse(idata).au);
    assert(result.parsedv().page == fmt.parse(idata).page);
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
