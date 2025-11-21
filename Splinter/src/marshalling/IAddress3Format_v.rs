// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

//! IAddress marshaller generated using the struct_marshaller_2! macro

use vstd::{prelude::*};
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::IntegerMarshalling_v::*;
use crate::marshalling::UniformSized_v::*;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;
use crate::disk::GenericDisk_v::{IAU, IPage, IAddress, Address, AU, Page};

verus! {

// Conversion functions for IAddress marshalling
pub open spec fn int_to_au(v: int) -> AU {
    v as AU
}

pub open spec fn au_to_int(v: AU) -> int {
    v as int
}

pub open spec fn int_to_page(v: int) -> Page {
    v as Page
}

pub open spec fn page_to_int(v: Page) -> int {
    v as int
}

} // verus!

struct_marshaller_2! {
    format_name: IAddress3Format,
    impl_type: IAddress,
    spec_type: Address,
    field1: {
        impl_field: au,
        spec_field: au,
        formatter_type: IntFormat<IAU>,
        formatter_spec_new: IntFormat::spec_new(),
        formatter_new: IntFormat::new(),
        parse_fn: int_to_au,
        marshallable_fn: au_to_int,
    },
    field2: {
        impl_field: page,
        spec_field: page,
        formatter_type: IntFormat<IPage>,
        formatter_spec_new: IntFormat::spec_new(),
        formatter_new: IntFormat::new(),
        parse_fn: int_to_page,
        marshallable_fn: page_to_int,
    }
}

