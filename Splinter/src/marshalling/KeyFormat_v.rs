// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

//! KeyFormat - a simple wrapper around IntFormat<u64> that marshals Key directly
//! This exists solely to match the Key type in structs

use vstd::{prelude::*};
use crate::spec::KeyType_t::Key;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;

verus! {

impl Parsedview<Key> for Key {
    open spec fn parsedv(&self) -> Key {
        *self
    }
}

pub struct KeyFormat {
    pub inner: IntFormat<u64>,
}

impl KeyFormat {
    pub open spec fn spec_new() -> Self {
        KeyFormat { inner: IntFormat::spec_new() }
    }

    pub fn new() -> (out: Self)
        ensures out == Self::spec_new()
    {
        KeyFormat { inner: IntFormat::new() }
    }
}

impl UniformSized for KeyFormat {
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

impl Marshal for KeyFormat {
    type DV = Key;
    type U = Key;

    open spec fn valid(&self) -> bool {
        self.inner.valid()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool {
        self.inner.parsable(data)
    }

    open spec fn parse(&self, data: Seq<u8>) -> Self::DV {
        Key(self.inner.parse(data) as u64)
    }

    open spec fn marshallable(&self, value: Self::DV) -> bool {
        self.inner.marshallable(value.0 as int)
    }

    open spec fn impl_marshallable(&self, impl_value: Self::U) -> bool {
        self.inner.impl_marshallable(impl_value.0)
    }

    open spec fn spec_size(&self, value: Self::DV) -> usize {
        self.inner.spec_size(value.0 as int)
    }

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize) {
        self.inner.exec_size(&value.0)
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize) {
        assert(self.valid());
        assert(value.wf());
        assert(self.marshallable(value.parsedv()));
        assert(self.impl_marshallable(*value));
        assert(start as int + self.spec_size(value.parsedv()) as int <= old(data).len());
        let end = self.inner.exec_marshall(&value.0, data, start);
        proof {
            let subr = data@.subrange(start as int, end as int);
            // inner postcondition: self.inner.parse(subr) == value.0.parsedv() (as int)
            // we need: self.parse(subr) == value.parsedv()
            // self.parse(subr) = Key(self.inner.parse(subr) as u64)
            // value.parsedv() = *value = Key(value.0)
            // Since value.0.parsedv() = value.0 as int, and self.inner.parse(subr) = value.0 as int,
            // self.inner.parse(subr) as u64 = value.0
            assert(Parsedview::<int>::parsedv(&value.0) == (value.0 as int));
            assert(self.inner.parse(subr) == (value.0 as int));
            assert(self.parse(subr) == Key(self.inner.parse(subr) as u64));
            assert(self.parse(subr) == value.parsedv());
        }
        end
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>) {
        match self.inner.try_parse(slice, data) {
            Some(v) => {
                let result = Key(v);
                proof {
                    let idata = slice@.i(data@);

                    // Prove parsability (for postcondition self.parsable(idata) <==> ov is Some)
                    assert(self.inner.parsable(idata)); // inner was successfully parsed
                    assert(self.parsable(idata)); // therefore KeyFormat is parsable

                    // Prove wf (from inner postcondition)
                    assert(v.wf()); // inner postcondition guarantees v.wf()
                    assert(result.wf()); // Key wraps a wf u64

                    // inner postcondition: v.parsedv() == self.inner.parse(...) (as int)
                    // we need: result.parsedv() == self.parse(...)
                    // Key(v).parsedv() = Key(v) (identity)
                    // self.parse(...) = Key(self.inner.parse(...) as u64)
                    // Since v.parsedv() = v as int = self.inner.parse(...),
                    // self.inner.parse(...) as u64 = v
                    assert(Parsedview::<int>::parsedv(&v) == (v as int));
                    assert(self.inner.parse(idata) == (v as int));
                    assert(self.parse(idata) == Key(self.inner.parse(idata) as u64));
                    assert(result.parsedv() == result); // Key(v)
                    assert(result.parsedv() == self.parse(idata));
                }
                Some(result)
            }
            None => None,
        }
    }
}

impl UniformSizedMarshal for KeyFormat {
    proof fn uniform_size_matches_spec_size(self: &Self) {
        // IntFormat<u64> is UniformSizedMarshal, so this is trivial
        assert forall |value: Key| #[trigger] self.spec_size(value) == self.uniform_size() by {
            // self.inner is UniformSizedMarshal
        }
    }
}

} // verus!
