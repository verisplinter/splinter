// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use vstd::bytes::*;
use vstd::slice::*;
use core::hash::Hash;
use crate::marshalling::Slice_v::*;
use crate::marshalling::Marshalling_v::*;
use crate::marshalling::IntegerMarshalling_v::*;
use crate::marshalling::StaticallySized_v::*;
use crate::marshalling::UniformSized_v::*;
use crate::marshalling::UniformSizedSeq_v::*;
use crate::marshalling::SeqMarshalling_v::*;
use crate::marshalling::VariableSizedElementSeq_v::*;

verus! {

pub trait LengthField {
    // Looks a lot like UniformSized but no obligation to be nonzero
    spec fn field_size(&self) -> (sz: usize)
        ;

    exec fn exec_field_size(&self) -> (sz: usize)
    ensures sz == self.field_size()
    ;

    // IntegerMarshalling stuff, but specialized to usize. I want this to be its own
    // Format, not impressed onto the usize type itself.

    spec fn max() -> (m: usize)
    ;

    exec fn exec_max() -> (m: usize)
    ensures m == Self::max()
    ;

    //////////////////////////////////////////////////////////////////////
    // Parsing
    //////////////////////////////////////////////////////////////////////

    spec fn parsable(&self, data: Seq<u8>) -> bool
    ;

    spec fn parse(&self, data: Seq<u8>) -> int
    recommends
        self.parsable(data)
    ;

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<usize>)
    requires
        slice@.valid(data@),
    ensures
        self.parsable(slice@.i(data@)) <==> ov is Some,
        self.parsable(slice@.i(data@)) ==> ov.unwrap() as int == self.parse(slice@.i(data@))
    ;

    exec fn exec_parsable(&self, slice: &Slice, data: &Vec<u8>) -> (p: bool)
    requires
        slice@.valid(data@),
    ensures
        p == self.parsable(slice@.i(data@))
    {
        let ovalue = self.try_parse(slice, data);
        ovalue.is_some()
    }

    exec fn exec_parse(&self, slice: &Slice, data: &Vec<u8>) -> (value: usize)
    requires
        slice@.valid(data@),
        self.parsable(slice@.i(data@)),
    ensures
        value as int == self.parse(slice@.i(data@)),
    {
        self.try_parse(slice, data).unwrap()
    }

    //////////////////////////////////////////////////////////////////////
    // Marshalling
    //////////////////////////////////////////////////////////////////////

    exec fn exec_marshall(&self, value: usize, data: &mut Vec<u8>, start: usize) -> (end: usize)
    requires
        0 <= value <= Self::max(),
        start as int + self.field_size() as int <= old(data).len(),
    ensures
        end == start + self.field_size(),
        data.len() == old(data).len(),
        forall |i| 0 <= i < start ==> data[i] == old(data)[i],
        forall |i| end <= i < data.len() ==> data[i] == old(data)[i],
        self.parsable(data@.subrange(start as int, end as int)),
        self.parse(data@.subrange(start as int, end as int)) == value as int
    ;
}

// Dynamic length, recorded in an IntFormattable integer:
// use IntFormattable, which is UniformSize
// impl<T> LengthField for T where T: Marshal<DV = int> + UniformSized {
impl<T: IntFormattable> LengthField for IntFormat<T> {
    open spec fn field_size(&self) -> (sz: usize)
    {
        self.uniform_size()
    }

    exec fn exec_field_size(&self) -> (sz: usize)
    {
        self.exec_uniform_size()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        Marshal::parsable(self, data)
    }

    open spec fn parse(&self, data: Seq<u8>) -> int
    {
        Marshal::parse(self, data)
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<usize>)
    {
        match Marshal::try_parse(self, slice, data) {
            Some(t) => {
                let v = T::to_usize(t);
                let ov = Some(v);
                proof {
                    T::deepv_is_as_int(t);
                    assert( ov.unwrap() as int == LengthField::parse(self, slice@.i(data@)) );  // trigger
                }
                ov
            },
            None => None
        }
    }

    open spec fn max() -> (m: usize)
    {
        T::max()
    }

    exec fn exec_max() -> (m: usize)
    {
        T::exec_max()
    }

    //////////////////////////////////////////////////////////////////////
    // Marshalling
    //////////////////////////////////////////////////////////////////////

    exec fn exec_marshall(&self, value: usize, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let v = T::from_usize(value);
        let end = Marshal::exec_marshall(self, &v, data, start);

        proof { T::deepv_is_as_int(v); }
        end
    }
}

}
