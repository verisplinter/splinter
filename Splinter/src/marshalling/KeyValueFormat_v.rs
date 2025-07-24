// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::marshalling::Marshalling_v::Deepview;
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::Wrappable_v::*;

verus! {

pub struct KeyValueFormatWrappable {}
impl Wrappable for KeyValueFormatWrappable {
    type AF = IntFormat::<u64>;
    type BF = IntFormat::<u64>;
    type DV = (Key,Value);
    type U = (Key,Value);

    open spec fn value_marshallable(value: (Key, Value)) -> bool
    {
        true
    }

    open spec fn to_pair(value: (Key, Value)) -> (int, int)
    {
        (value.0.0 as int, value.1.0 as int)
    }

    open spec fn from_pair(pair: (int, int)) -> (value: (Key, Value))
    {
        (Key(pair.0 as u64), Value(pair.1 as u64))
    }

    proof fn to_from_bijective()
    {
    }

    exec fn exec_to_pair<'a>(value: &'a (Key, Value)) -> (pair: (&'a u64, &'a u64))
    {
        (&value.0.0, &value.1.0)
    }

    exec fn exec_from_pair(pair: (u64, u64)) -> (km: (Key, Value))
    {
        (Key(pair.0 as u64), Value(pair.1 as u64))
    }

    exec fn new_format_pair() -> (Self::AF, Self::BF)
    {
        (IntFormat::new(), IntFormat::new())
    }
}

pub type KeyValueFormat = WrappableFormat<KeyValueFormatWrappable>;

impl Deepview<(Key,Value)> for (Key,Value) {
    open spec fn deepv(&self) -> (Key,Value) { (self.0, self.1) }
}

} //verus!
