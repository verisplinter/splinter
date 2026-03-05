// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#[macro_use]
pub mod StructMarshalMacro_v;
pub mod IntegerMarshalling_v;
pub mod KeyFormat_v;
pub mod MessageFormat_v;
pub mod NatFormat_v;
pub mod Marshalling_v;
pub mod UniformSized_v;
pub mod StaticallySized_v;
pub mod ResizableUniformSizedSeq_v;
// pub mod ResizableIntegerSeq_v;
pub mod VariableSizedElementSeq_v;
pub mod SeqMarshalling_v;
pub mod Slice_v;
pub mod UniformSizedSeq_v;
pub mod math_v;
// pub mod LengthField_v;
pub mod UniformPairFormat_v;
pub mod WF_v;
pub mod KeyedMessageFormat_v;
pub mod KeyValueFormat_v;
pub mod IJournalRecordFormat_v;
pub mod IJournalSnapshotFormat_v;
pub mod ISuperblockFormat_v;
pub mod IStoreFormat_v;
pub mod VecMapFormat_v;
pub mod Wrappable_v;
pub mod PaddedFormat_v;
pub mod IAddressFormat_v;
pub mod OptionFormat_v;
pub mod UniformSizedMarshal_v;

// next steps:
//
// ResizableIntegerSeqMarshalling: perf improvement to marshall many ints in a batch
// VariableSizedElementSeqMarshalling: We'll eventually have variable-sized element lists: keys & values!
