// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

//! ISuperblockFormat_v - marshaller for ISuperblock using the struct_marshaller_2 macro

use crate::implementation::SuperblockTypes_v::{ASuperblock, ISuperblock};
use crate::implementation::JournalImpl_v::IJournalSnapshot;
use crate::marshalling::IJournalSnapshotFormat_v::IJournalSnapshotFormat;
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
    // ISuperblock::wf() returns true unconditionally
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
        // Facts from macro (try_parse postconditions):
        Parsedview::<crate::implementation::CachedJournal_v::JournalSnapshot>::parsedv(&field1_value) == fmt.field1_fmt.parse(field1_slice@.i(data@)),
        Parsedview::<Seq<(crate::spec::KeyType_t::Key, crate::spec::Messages_t::Value)>>::parsedv(&field2_value) == fmt.field2_fmt.parse(field2_slice@.i(data@)),
        // Slice relationships:
        field1_slice@.i(data@) == slice@.i(data@).subrange(0, fmt.field1_fmt.uniform_size() as int),
        field2_slice@.i(data@) == slice@.i(data@).subrange(
            fmt.field1_fmt.uniform_size() as int,
            fmt.field1_fmt.uniform_size() as int + fmt.field2_fmt.uniform_size() as int),
    ensures
        result.parsedv() == fmt.parse(slice@.i(data@)),
        result.wf(),
{
    // ISuperblock::wf() returns true unconditionally

    // result.parsedv() = ASuperblock { journal: result.journal_snapshot@, store: result.store@ }
    // fmt.parse(...) = ASuperblock { journal: fmt.field1_fmt.parse(...), store: fmt.field2_fmt.parse(...) }
    let idata = slice@.i(data@);
    let f1_end = fmt.field1_fmt.uniform_size() as int;
    let f2_end = f1_end + fmt.field2_fmt.uniform_size() as int;

    // For field1 (journal_snapshot):
    // JournalSnapshot::parsedv() = JournalSnapshot@
    // From requires: field1_value.parsedv() == fmt.field1_fmt.parse(...)
    assert(field1_value@ == Parsedview::<crate::implementation::CachedJournal_v::JournalSnapshot>::parsedv(&field1_value));
    assert(result.parsedv().journal == field1_value@);
    assert(result.parsedv().journal == fmt.field1_fmt.parse(idata.subrange(0, f1_end)));
    assert(fmt.parse(idata).journal == fmt.field1_fmt.parse(idata.subrange(0, f1_end)));

    // For field2 (store):
    // Vec<(K,V)>::@ and Vec<(K,V)>::parsedv() should be equal for identity-like Parsedview
    // Since (Key,Value)::parsedv() = identity, Vec::parsedv() = Vec::@
    assert(field2_value@ =~= Parsedview::<Seq<(crate::spec::KeyType_t::Key, crate::spec::Messages_t::Value)>>::parsedv(&field2_value));
    assert(result.parsedv().store == field2_value@);
    assert(result.parsedv().store =~= fmt.field2_fmt.parse(idata.subrange(f1_end, f2_end)));
    assert(fmt.parse(idata).store == fmt.field2_fmt.parse(idata.subrange(f1_end, f2_end)));
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
        formatter_type: IJournalSnapshotFormat,
        formatter_spec_new: IJournalSnapshotFormat::spec_new(),
        formatter_new: IJournalSnapshotFormat::new(),
    },
    field2: {
        impl_field: store,
        spec_field: store,
        formatter_type: ResizableUniformSizedElementSeqFormat<KeyValueFormat, u8>,
        formatter_spec_new: ResizableUniformSizedElementSeqFormat::spec_new(KeyValueFormat::spec_new(), IntFormat::<u8>::spec_new(), 200),
        formatter_new: ResizableUniformSizedElementSeqFormat::new(KeyValueFormat::new(), IntFormat::<u8>::new(), 200),
    }
}
