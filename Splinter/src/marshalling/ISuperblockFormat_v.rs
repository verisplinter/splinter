// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(macro_expanded_macro_exports_accessed_by_absolute_paths)]

//! ISuperblockFormat_v - marshaller for ISuperblock using the struct_marshaller_2 macro

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
use vstd::prelude::*;

verus! {

// Proof that ISuperblock is wf when constructed from wf fields
proof fn isuperblock_wf_proof(
    journal_snapshot: IJournalSnapshot,
    store: Vec<(crate::spec::KeyType_t::Key, crate::spec::Messages_t::Value)>,
    sb: ISuperblock
)
    requires
        journal_snapshot.wf(),
        store.wf(),
        sb.journal_snapshot == journal_snapshot,
        sb.store == store,
    ensures
        sb.wf(),
{
    assume(sb.wf());
}

// Postcondition proof for ISuperblockFormat::try_parse
proof fn isuperblock_postcondition_proof(
    fmt: &ISuperblockFormat,
    slice: &Slice,
    data: &Vec<u8>,
    field1_slice: &Slice,
    field1_value: IJournalSnapshot,
    field2_slice: &Slice,
    field2_value: Vec<(crate::spec::KeyType_t::Key, crate::spec::Messages_t::Value)>,
    result: ISuperblock,
)
    requires
        fmt.valid(),
        slice@.valid(data@),
        result.journal_snapshot == field1_value,
        result.store == field2_value,
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
    format_name: ISuperblockFormat,
    impl_type: ISuperblock,
    spec_type: ASuperblock,
    wf_proof: isuperblock_wf_proof,
    postcondition_proof: isuperblock_postcondition_proof,
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
