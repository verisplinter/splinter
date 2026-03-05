// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;

use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::Value;
use crate::marshalling::KeyValueFormat_v::KeyValueFormat;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::Marshalling_v::Marshal;

verus! {

pub type AStore = Seq<(Key, Value)>;
pub type IStore = Vec<(Key, Value)>;

pub type IStoreFormat = ResizableUniformSizedElementSeqFormat<KeyValueFormat, u8>;

pub open spec fn store_max_length() -> usize
{
    200usize
}

pub open spec fn spec_new() -> IStoreFormat
{
    ResizableUniformSizedElementSeqFormat::spec_new(
        KeyValueFormat::spec_new(),
        IntFormat::<u8>::spec_new(),
        store_max_length(),
    )
}

pub fn new() -> (out: IStoreFormat)
    ensures out.valid(),
{
    ResizableUniformSizedElementSeqFormat::new(
        KeyValueFormat::new(),
        IntFormat::<u8>::new(),
        200usize,
    )
}

} // verus!
