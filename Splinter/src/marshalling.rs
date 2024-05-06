// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
pub mod IntegerMarshalling_v;
pub mod Marshalling_v;
//pub mod ResizableUniformSizedSeq_v;
pub mod SeqMarshalling_v;
pub mod Slice_v;
pub mod UniformSizedSeq_v;
pub mod math_v;

// next steps:
//
// ResizableIntegerSeqMarshalling: perf improvement to marshall many ints in a batch
// VariableSizedElementSeqMarshalling: We'll eventually have variable-sized element lists: keys & values!
