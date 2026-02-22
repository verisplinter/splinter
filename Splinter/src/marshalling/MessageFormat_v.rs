// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

//! MessageFormat - a wrapper around IntFormat<u64> that marshals Message (Define only)
//! This exists solely to match the Message type in structs

use vstd::{prelude::*};
use crate::spec::Messages_t::{Message, Value};
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;

verus! {

impl Parsedview<Message> for Message {
    open spec fn parsedv(&self) -> Message {
        *self
    }
}

impl WF for Message { }

pub struct MessageFormat {
    pub inner: IntFormat<u64>,
}

impl MessageFormat {
    pub open spec fn spec_new() -> Self {
        MessageFormat { inner: IntFormat::spec_new() }
    }

    pub fn new() -> (out: Self)
        ensures out == Self::spec_new()
    {
        MessageFormat { inner: IntFormat::new() }
    }
}

impl UniformSized for MessageFormat {
    open spec fn us_valid(&self) -> bool {
        self.inner.us_valid()
    }

    open spec fn uniform_size(&self) -> usize {
        self.inner.uniform_size()
    }

    proof fn uniform_size_ensures(&self) {
        self.inner.uniform_size_ensures();
    }

    exec fn exec_uniform_size(&self) -> (sz: usize) {
        self.inner.exec_uniform_size()
    }
}

impl Marshal for MessageFormat {
    type DV = Message;
    type U = Message;

    open spec fn valid(&self) -> bool {
        self.inner.valid()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool {
        self.inner.parsable(data)
    }

    open spec fn parse(&self, data: Seq<u8>) -> Self::DV {
        Message::Define { value: Value(self.inner.parse(data) as u64) }
    }

    open spec fn marshallable(&self, value: Self::DV) -> bool {
        &&& value is Define  // Only support Define messages
        &&& self.inner.marshallable(value->value.0 as int)
    }

    open spec fn impl_marshallable(&self, impl_value: Self::U) -> bool {
        &&& impl_value is Define
        &&& self.inner.impl_marshallable(impl_value->value.0)
    }

    open spec fn spec_size(&self, value: Self::DV) -> usize {
        self.inner.spec_size(value->value.0 as int)
    }

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize) {
        match value {
            Message::Define { value: Value(v) } => self.inner.exec_size(v),
            Message::Update { .. } => { assert(false); 0 }  // Not supported
        }
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize) {
        assert(self.valid());
        assert(value.wf());
        assert(self.marshallable(value.parsedv()));
        assert(self.impl_marshallable(*value));
        assert(start as int + self.spec_size(value.parsedv()) as int <= old(data).len());
        match value {
            Message::Define { value: Value(v) } => {
                let end = self.inner.exec_marshall(v, data, start);
                proof {
                    let subr = data@.subrange(start as int, end as int);
                    // inner postcondition: self.inner.parse(subr) == v.parsedv() (as int)
                    // we need: self.parse(subr) == value.parsedv()
                    // self.parse(subr) = Message::Define { value: Value(self.inner.parse(subr) as u64) }
                    // value.parsedv() = *value = Message::Define { value: Value(v) }
                    assert(Parsedview::<int>::parsedv(v) == (*v as int));
                    assert(self.inner.parse(subr) == (*v as int));
                    assert(self.parse(subr) == Message::Define { value: Value(self.inner.parse(subr) as u64) });
                    assert(self.parse(subr) == value.parsedv());
                }
                end
            }
            Message::Update { .. } => { assert(false); 0 }  // Not supported
        }
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>) {
        assert(self.valid());
        assert(slice@.valid(data@));
        match self.inner.try_parse(slice, data) {
            Some(v) => {
                proof {
                    // inner postcondition: v.parsedv() == self.inner.parse(...) (as int)
                    // we need: Message::Define{...}.parsedv() == self.parse(...)
                    let idata = slice@.i(data@);
                    assert(Parsedview::<int>::parsedv(&v) == (v as int));
                    assert(self.inner.parse(idata) == (v as int));
                    assert(self.parse(idata) == Message::Define { value: Value(self.inner.parse(idata) as u64) });
                    let result = Message::Define { value: Value(v) };
                    assert(result.parsedv() == result);
                    assert(result.wf());
                }
                Some(Message::Define { value: Value(v) })
            }
            None => None,
        }
    }
}

impl UniformSizedMarshal for MessageFormat {
    proof fn uniform_size_matches_spec_size(self: &Self) {
        // IntFormat<u64> is UniformSizedMarshal, so this is trivial
        assert forall |value: Message| #[trigger] self.spec_size(value) == self.uniform_size() by {
            // self.inner is UniformSizedMarshal
        }
    }
}

} // verus!
