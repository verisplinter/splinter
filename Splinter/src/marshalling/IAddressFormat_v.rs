// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(macro_expanded_macro_exports_accessed_by_absolute_paths)]

//! IAddressFormat_v - marshaller for IAddress using the struct_marshaller_2 macro

use crate::disk::GenericDisk_v::{IAddress, Address};
use crate::marshalling::NatFormat_v::NatFormat;
use crate::marshalling::Slice_v::Slice;
use crate::struct_marshaller_2;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use vstd::prelude::*;

verus! {

#[allow(macro_expanded_macro_exports_accessed_by_absolute_paths)]
struct_marshaller_2! {
    format_name: IAddressFormat,
    impl_type: IAddress,
    spec_type: Address,
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

} // verus!
