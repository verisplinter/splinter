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
        spec_cast: as AU,
    },
    field2: {
        impl_field: page,
        spec_field: page,
        formatter_type: IntFormat<IPage>,
        formatter_spec_new: IntFormat::spec_new(),
        formatter_new: IntFormat::new(),
        spec_cast: as Page,
    }
}

