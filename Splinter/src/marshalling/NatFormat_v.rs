// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

//! NatFormat<T> - a wrapper around IntFormat<T> that marshals nat instead of int
//! This is the key adapter that allows IntFormat (which works with int in spec)
//! to be used for struct fields that are nat in spec.
//!
//! Usage: NatFormat::<u32> marshals u32 in exec, nat in spec (instead of int)
//!        NatFormat::<u64> marshals u64 in exec, nat in spec (instead of int)
//!
//! Note: This introduces Parsedview<nat> for u32/u64, which creates ambiguity with
//! the existing Parsedview<int> implementations. This may require type annotations
//! in some call sites, but eliminates the need for conversion functions in the macro.

use vstd::{prelude::*};
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::IntegerMarshalling_v::{IntFormat, IntFormattable};
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;

verus! {

// Implement Parsedview<nat> for integer types
// Note: This creates ambiguity with Parsedview<int>, but that's OK - the compiler
// can usually infer from context which one is needed.
impl Parsedview<nat> for u32 {
    open spec fn parsedv(&self) -> nat {
        *self as nat
    }
}

impl Parsedview<nat> for u64 {
    open spec fn parsedv(&self) -> nat {
        *self as nat
    }
}

pub struct NatFormat<T: IntFormattable> {
    pub inner: IntFormat<T>,
}

impl<T: IntFormattable + Parsedview<nat>> NatFormat<T> {
    pub open spec fn spec_new() -> Self {
        NatFormat { inner: IntFormat::spec_new() }
    }
    
    pub fn new() -> (out: Self)
        ensures out == Self::spec_new(), out.valid(),
    {
        NatFormat { inner: IntFormat::new() }
    }
}

impl<T: IntFormattable + Parsedview<nat>> UniformSized for NatFormat<T> {
    open spec fn us_valid(&self) -> bool {
        self.inner.us_valid()
    }
    
    open spec fn uniform_size(&self) -> usize {
        self.inner.uniform_size()
    }
    
    proof fn uniform_size_ensures(&self)
        ensures 0 < self.uniform_size()
    {
        self.inner.uniform_size_ensures();
    }
    
    exec fn exec_uniform_size(&self) -> (sz: usize)
        ensures sz == self.uniform_size()
    {
        self.inner.exec_uniform_size()
    }
}

impl<T: IntFormattable + Parsedview<nat>> Marshal for NatFormat<T> {
    type DV = nat;  // nat in spec (the key difference from IntFormat!)
    type U = T;     // T in exec (u32, u64, etc.)

    open spec fn valid(&self) -> bool {
        self.inner.valid()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool {
        self.inner.parsable(data)
    }

    open spec fn parse(&self, data: Seq<u8>) -> Self::DV {
        self.inner.parse(data) as nat  // Convert int to nat
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>) {
        self.inner.try_parse(slice, data)
    }

    open spec fn marshallable(&self, value: Self::DV) -> bool {
        self.inner.marshallable(value as int)  // Convert nat to int
    }

    open spec fn impl_marshallable(&self, impl_value: Self::U) -> bool {
        self.inner.impl_marshallable(impl_value)
    }

    open spec fn spec_size(&self, v: Self::DV) -> usize {
        self.inner.uniform_size()
    }

    exec fn exec_size(&self, val: &Self::U) -> (sz: usize) {
        self.inner.exec_size(val)
    }

    exec fn exec_marshall(&self, val: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        self.inner.exec_marshall(val, data, start)
    }
}

impl<T: IntFormattable + Parsedview<nat>> UniformSizedMarshal for NatFormat<T> {
    proof fn uniform_size_matches_spec_size(self: &Self) {
        assert forall |value: nat| #[trigger] self.spec_size(value) == self.uniform_size() by { }
    }
}

} // verus!

