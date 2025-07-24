// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
pub mod IntegerMarshalling_v;
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
pub mod LengthField_v;
pub mod KVPairFormat_v;
pub mod HashMapFormat_v;
pub mod UniformPairFormat_v;
pub mod KeyedMessageFormat_v;
pub mod KeyValueFormat_v;
pub mod JournalFormat_v;
// pub mod ISuperblockFormat_v;
pub mod Wrappable_v;

// next steps:
//
// ResizableIntegerSeqMarshalling: perf improvement to marshall many ints in a batch
// VariableSizedElementSeqMarshalling: We'll eventually have variable-sized element lists: keys & values!
