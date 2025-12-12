// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(macro_expanded_macro_exports_accessed_by_absolute_paths)]

//! ISuperblockFormat_v - marshaller for ISuperblock using the struct_marshaller_2 macro
//!
//! The macro requires that ISuperblock::parsedv() is "compositional".
//! ISuperblock::parsedv() = ASuperblock { journal: self.journal_snapshot@, store: self.store@ }
//! which matches the field-by-field Parsedview pattern.

use vstd::prelude::*;
use crate::implementation::SuperblockTypes_v::{ASuperblock, ISuperblock};
use crate::implementation::JournalImpl_v::JournalSnapshot as IJournalSnapshot;
use crate::marshalling::JournalSnapshotFormat_v::JournalSnapshotFormat;
use crate::marshalling::KeyValueFormat_v::KeyValueFormat;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;
use crate::marshalling::StructMarshalMacro_v::Compositional2;

struct_marshaller_2! {
    format_name: ISuperblockFormat,
    impl_type: ISuperblock,
    spec_type: ASuperblock,
    field1: {
        impl_field: journal_snapshot,
        spec_field: journal,
        formatter_type: JournalSnapshotFormat,
        formatter_spec_new: JournalSnapshotFormat::spec_new(),
        formatter_new: JournalSnapshotFormat::new(),
    },
    field2: {
        impl_field: store,
        spec_field: store,
        formatter_type: ResizableUniformSizedElementSeqFormat<KeyValueFormat, u8>,
        formatter_spec_new: ResizableUniformSizedElementSeqFormat::spec_new(KeyValueFormat::spec_new(), IntFormat::<u8>::spec_new(), 200),
        formatter_new: ResizableUniformSizedElementSeqFormat::new(KeyValueFormat::new(), IntFormat::<u8>::new(), 200),
    }
}
