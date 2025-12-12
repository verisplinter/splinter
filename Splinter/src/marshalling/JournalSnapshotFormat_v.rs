// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(macro_expanded_macro_exports_accessed_by_absolute_paths)]

//! JournalSnapshotFormat_v - marshaller for JournalSnapshot using the struct_marshaller_2 macro
//!
//! The macro requires that JournalSnapshot::parsedv() is "compositional".
//! JournalSnapshot::parsedv() = self@ which is defined field-by-field using each field's View.

use vstd::prelude::*;
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
use crate::marshalling::StructMarshalMacro_v::Compositional2;

struct_marshaller_2! {
    format_name: JournalSnapshotFormat,
    impl_type: JournalSnapshot,
    spec_type: JournalSnapShot,
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
