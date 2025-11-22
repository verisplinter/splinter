// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

//! JournalSnapshot marshaller generated using the struct_marshaller_2! macro
//! This demonstrates how the macro handles Option fields elegantly!
//! Replaces the old hand-written implementation with 74% less code.

use vstd::{prelude::*};
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::IntegerMarshalling_v::*;
use crate::marshalling::UniformSized_v::*;
use crate::marshalling::WF_v::WF;
use crate::marshalling::StructMarshalMacro_v::identity;
use crate::marshalling::IAddressFormat_v::IAddressFormat;
use crate::marshalling::OptionFormat_v::OptionFormat;
use crate::implementation::JournalImpl_v::JournalSnapshot;
use crate::implementation::CachedJournal_v::JournalSnapShot;
use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::{IAddress, Address};
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;

verus! {

// Conversion functions for LSN field
pub open spec fn int_to_lsn(v: int) -> LSN {
    v as LSN
}

pub open spec fn lsn_to_int(v: LSN) -> int {
    v as int
}

} // verus!

struct_marshaller_2! {
    format_name: JournalSnapshotFormat,
    impl_type: JournalSnapshot,
    spec_type: JournalSnapShot,
    field1: {
        impl_field: boundary_lsn,
        spec_field: boundary_lsn,
        formatter_type: IntFormat<u64>,
        formatter_spec_new: IntFormat::spec_new(),
        formatter_new: IntFormat::new(),
        parse_fn: int_to_lsn,
        marshallable_fn: lsn_to_int,
    },
    field2: {
        impl_field: freshest_rec,
        spec_field: freshest_rec,
        formatter_type: OptionFormat<IAddressFormat>,
        formatter_spec_new: OptionFormat::spec_new(IAddressFormat::spec_new()),
        formatter_new: OptionFormat::new(IAddressFormat::new()),
        parse_fn: identity,
        marshallable_fn: identity,
    }
}

