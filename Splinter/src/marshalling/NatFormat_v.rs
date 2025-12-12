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

// Trait to capture the property that (T as int) as nat == T as nat
// This is true for unsigned integer types like u16, u32, u64
pub trait NatCastable: IntFormattable + Parsedview<nat> + Parsedview<int> {
    proof fn nat_cast_lemma(v: Self)
        ensures
            Parsedview::<int>::parsedv(&v) as nat == Parsedview::<nat>::parsedv(&v),
    ;
}

// Implement Parsedview<nat> for integer types
// Note: This creates ambiguity with Parsedview<int>, but that's OK - the compiler
// can usually infer from context which one is needed.
impl Parsedview<nat> for u16 {
    open spec fn parsedv(&self) -> nat {
        *self as nat
    }
}

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

// Implement NatCastable for unsigned integer types
impl NatCastable for u16 {
    proof fn nat_cast_lemma(v: Self) {
        // For u16: (*v as int) as nat == *v as nat
        // This is true because u16 values are non-negative
        // Verus should be able to prove this automatically
    }
}

impl NatCastable for u32 {
    proof fn nat_cast_lemma(v: Self) {
        // For u32: (v as int) as nat == v as nat
        // u32 values are always non-negative, so casting to int preserves the value,
        // and then casting that non-negative int to nat should equal casting u32 directly to nat

        // Try to prove it step by step
        let v_as_int: int = v as int;
        let v_as_nat_direct: nat = v as nat;
        let v_as_nat_via_int: nat = v_as_int as nat;

        // v is a u32, so v_as_int >= 0
        assert(v_as_int >= 0);

        // For non-negative ints, casting to nat should preserve the value
        // And both paths should yield the same result
        assert(v_as_nat_via_int == v_as_nat_direct);
    }
}

impl NatCastable for u64 {
    proof fn nat_cast_lemma(v: Self) {
        // For u64: (*v as int) as nat == *v as nat
        // This is true because u64 values are non-negative
        // Verus should be able to prove this automatically
    }
}

pub struct NatFormat<T: IntFormattable> {
    pub inner: IntFormat<T>,
}

impl<T: NatCastable> NatFormat<T> {
    pub open spec fn spec_new() -> Self {
        NatFormat { inner: IntFormat::spec_new() }
    }

    pub fn new() -> (out: Self)
        ensures out == Self::spec_new(), out.valid(),
    {
        NatFormat { inner: IntFormat::new() }
    }
}

impl<T: NatCastable> UniformSized for NatFormat<T> {
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

impl<T: NatCastable> Marshal for NatFormat<T> {
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
        let result = self.inner.try_parse(slice, data);
        proof {
            if result.is_some() {
                // IntFormat postcondition: result.unwrap().parsedv() == self.inner.parse(...) (as int)
                // We need: result.unwrap().parsedv() == self.parse(...) (as nat)
                let v = result.unwrap();
                let idata = slice@.i(data@);
                let v_int = Parsedview::<int>::parsedv(&v); // *v as int
                let v_nat = Parsedview::<nat>::parsedv(&v); // *v as nat

                assert(v_int == self.inner.parse(idata)); // From inner postcondition
                assert(self.parse(idata) == (self.inner.parse(idata) as nat)); // By definition

                // Prove: v_int as nat == v_nat using the NatCastable trait lemma
                T::nat_cast_lemma(v);
                assert(v_int as nat == v_nat);

                assert(v_nat == self.parse(idata));
            }
        }
        result
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
        let end = self.inner.exec_marshall(val, data, start);
        proof {
            // IntFormat postcondition: self.inner.parse(...) == val.parsedv() (as int)
            // We need: self.parse(...) == val.parsedv() (as nat)
            let subr = data@.subrange(start as int, end as int);
            let val_int = Parsedview::<int>::parsedv(val); // *val as int
            let val_nat = Parsedview::<nat>::parsedv(val); // *val as nat

            assert(self.inner.parse(subr) == val_int); // From inner postcondition
            assert(self.parse(subr) == (self.inner.parse(subr) as nat)); // By definition

            // Prove: For T, (*val as int) as nat == *val as nat
            T::nat_cast_lemma(*val);
            assert(val_int as nat == val_nat);

            assert(self.parse(subr) == val_nat);
        }
        end
    }
}

impl<T: NatCastable> UniformSizedMarshal for NatFormat<T> {
    proof fn uniform_size_matches_spec_size(self: &Self) {
        assert forall |value: nat| #[trigger] self.spec_size(value) == self.uniform_size() by { }
    }
}

} // verus!

