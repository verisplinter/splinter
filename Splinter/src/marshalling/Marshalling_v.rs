// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
//use vstd::bytes::*;
//use vstd::slice::*;
use crate::marshalling::Slice_v::*;
use crate::marshalling::WF_v::WF;

verus! {

pub trait Deepview<DV> {
    //type DV = DV;

    spec fn deepv(&self) -> DV;
}

// VSE == ViewSeqElt
// If you have an Elt type that implements Deepview<DVE>,
// you may have a Vec<Elt> that implements Deepview<Seq<DVE>>.
impl<DVE, Elt: Deepview<DVE>> Deepview<Seq<DVE>> for Vec<Elt> {
    //type DV = Seq<<T as Deepview>::DV>;

    open spec fn deepv(&self) -> Seq<DVE> {
        Seq::new(self.len() as nat, |i: int| self[i].deepv())
    }
}

// Marshal is the most basic behavior: A format that implements Marshal
// knows how to parse and marshall the type all at once.
//
// Design note: Exec fns manipulate slices-of-seqs, so we can borrow a "big" seq
// and operate on some smaller part of it that stores a particular field.
//
// Spec fns manipulate standalone seqs, the slice.i(seq) of the slice,seq pair from
// the exec fn. This is deliberate: at the spec level, we want f.parse(a) == f.parse(a)
// even if f is some other opaque formatter. If we used slices, we'd have
// f.parse(s, x+a+y) == f.parse(s, x'+a+y'). Even though s is "selecting" out just the
// a part, we don't know from the outside that f only looks at that region of the data.
//
pub trait Marshal {
    type DV;                // The view (spec) type
    type U: WF + Deepview<Self::DV>;    // The runtime type

    spec fn valid(&self) -> bool;

    //////////////////////////////////////////////////////////////////////
    // Parsing
    //////////////////////////////////////////////////////////////////////

    spec fn parsable(&self, data: Seq<u8>) -> bool
    recommends self.valid()
    ;

    spec fn parse(&self, data: Seq<u8>) -> Self::DV
    recommends
        self.valid(),
        self.parsable(data)
    ;

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    requires
        self.valid(),
        slice@.valid(data@),
    ensures
        self.parsable(slice@.i(data@)) <==> ov is Some,
        self.parsable(slice@.i(data@)) ==> ov.unwrap().deepv() == self.parse(slice@.i(data@)) && ov.unwrap().wf()
    ;

    exec fn exec_parsable(&self, slice: &Slice, data: &Vec<u8>) -> (p: bool)
    requires
        self.valid(),
        slice@.valid(data@),
    ensures
        p == self.parsable(slice@.i(data@))
    {
        let ovalue = self.try_parse(slice, data);
        ovalue.is_some()
    }

    exec fn exec_parse(&self, slice: &Slice, data: &Vec<u8>) -> (value: Self::U)
    requires
        self.valid(),
        slice@.valid(data@),
        self.parsable(slice@.i(data@)),
    ensures
        value.wf(),
        value.deepv() == self.parse(slice@.i(data@)),
    {
        self.try_parse(slice, data).unwrap()
    }

    //////////////////////////////////////////////////////////////////////
    // Marshalling
    //////////////////////////////////////////////////////////////////////

    spec fn marshallable(&self, value: Self::DV) -> bool
    ;

    spec fn spec_size(&self, value: Self::DV) -> usize
    recommends
        self.valid(),
        self.marshallable(value)
    ;

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
    requires
        self.valid(),
        value.wf(),
        self.marshallable(value.deepv()),
    ensures
        sz == self.spec_size(value.deepv())
    ;

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    requires
        self.valid(),
        value.wf(),
        self.marshallable(value.deepv()),
        start as int + self.spec_size(value.deepv()) as int <= old(data).len(),
    ensures
        end == start + self.spec_size(value.deepv()),
        data.len() == old(data).len(),
        forall |i| 0 <= i < start ==> data[i] == old(data)[i],
        forall |i| end <= i < data.len() ==> data[i] == old(data)[i],
        self.parsable(data@.subrange(start as int, end as int)),
        self.parse(data@.subrange(start as int, end as int)) == value.deepv()
    ;
}

} // verus!
