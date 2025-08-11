// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Deepview};
use crate::marshalling::UniformPairFormat_v::*;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::WF_v::WF;

verus! {

impl<ADV,AU:Deepview<ADV>,BDV,BU:Deepview<BDV>> Deepview<(ADV,BDV)> for (AU,BU)
{
    open spec fn deepv(&self) -> (ADV,BDV) { (self.0.deepv(), self.1.deepv()) }
}

// A Wrappable struct explains how a type can be represented as a pair of other marshallable items.
// Presently the pair member formatters must be UniformSized, but this constraint could be relaxed
// by introducing an optional length field.
pub trait Wrappable {
    type AF: Marshal + UniformSized;
    type BF: Marshal + UniformSized;
    type DV;
    type U: WF + Deepview<Self::DV>;

    spec fn value_marshallable(value: Self::DV) -> bool
    ;

    spec fn to_pair(value: Self::DV) -> (<Self::AF as Marshal>::DV, <Self::BF as Marshal>::DV)
        recommends Self::value_marshallable(value),
    ;

    spec fn from_pair(pair: (<Self::AF as Marshal>::DV, <Self::BF as Marshal>::DV)) -> (value: Self::DV)
    ;

    proof fn to_from_bijective()
    ensures forall |value: Self::DV| #![auto] Self::value_marshallable(value) ==> Self::from_pair(Self::to_pair(value)) == value,
    ;

    exec fn exec_to_pair(value: &Self::U) -> (pair: (<Self::AF as Marshal>::U, <Self::BF as Marshal>::U))
    requires Self::value_marshallable((*value).deepv())
    ensures Self::to_pair((*value).deepv()) == pair.deepv(),
        pair.wf(),
    ;

    exec fn exec_from_pair(pair: (<Self::AF as Marshal>::U, <Self::BF as Marshal>::U)) -> (value: Self::U)
    requires pair.wf()
    ensures
        value.deepv() == Self::from_pair(pair.deepv()),
        Self::to_pair(value.deepv()) == pair.deepv(),
        value.wf(),
    ;

    spec fn spec_new_format_pair() -> (Self::AF, Self::BF)
    ;

    exec fn new_format_pair() -> (out: (Self::AF, Self::BF))
        ensures
            out.0.valid(),
            out.1.valid(),
            out.0.us_valid(),
            out.1.us_valid(),
            out.0.uniform_size() as int + out.1.uniform_size() as int <= usize::MAX,
            uniform_size_matches_spec_size(out.0),
            uniform_size_matches_spec_size(out.1),
    ;

}

// Marshalling formatter for any type that is a pretty wrapper for a pair of other Marshable things.
pub struct WrappableFormat<W: Wrappable> {
    pub pair_fmt: UniformPairFormat<W::AF, W::BF>,
}

// Need a valid predicate, since not every instance of WrappableFormat is UniformSized due to
// possible overflow.
impl<W: Wrappable> UniformSized for WrappableFormat<W> {
    open spec fn us_valid(&self) -> bool
    {
        &&& self.pair_fmt.valid()
//         &&& self.pair_fmt.a_fmt.us_valid()
//         &&& self.pair_fmt.b_fmt.us_valid()
//         &&& W::AF::uniform_size(&self.pair_fmt.a_fmt) as int + W::BF::uniform_size(&self.pair_fmt.b_fmt) as int <= usize::MAX
    }
    
    open spec fn uniform_size(&self) -> (sz: usize) {
        (W::AF::uniform_size(&self.pair_fmt.a_fmt) + W::BF::uniform_size(&self.pair_fmt.b_fmt)) as usize
    }

    proof fn uniform_size_ensures(&self)
    ensures 0 < self.uniform_size()
    {
        W::AF::uniform_size_ensures(&self.pair_fmt.a_fmt);
        W::BF::uniform_size_ensures(&self.pair_fmt.b_fmt);
    }

    exec fn exec_uniform_size(&self) -> (sz: usize)
    ensures sz == self.uniform_size()
    {
        W::AF::exec_uniform_size(&self.pair_fmt.a_fmt) + W::BF::exec_uniform_size(&self.pair_fmt.b_fmt)
    }
}

impl<W: Wrappable> WrappableFormat<W> {
    pub open spec fn spec_new() -> Self
    {
        let (a_fmt, b_fmt) = W::spec_new_format_pair();
        WrappableFormat{ pair_fmt: UniformPairFormat::spec_new(a_fmt, b_fmt), }
    }

    pub fn new() -> (out: Self)
    ensures out.valid()
    {
        let (a_fmt, b_fmt) = W::new_format_pair();
        assert( a_fmt.valid() );
        let pair_fmt = UniformPairFormat::new(a_fmt, b_fmt);
        assert( pair_fmt.valid() );
        WrappableFormat{ pair_fmt }
    }
}

impl<W: Wrappable> Marshal for WrappableFormat<W> {
    type DV = W::DV;
    type U = W::U;

    open spec fn valid(&self) -> bool {
        self.pair_fmt.valid()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        self.pair_fmt.parsable(data)
    }

    open spec fn parse(&self, data: Seq<u8>) -> Self::DV
    {
        W::from_pair(self.pair_fmt.parse(data))
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    {
        match self.pair_fmt.try_parse(slice, data) {
            None => None,
            Some(pair) => {
                let v = W::exec_from_pair(pair);
                assert( W::to_pair(v.deepv()) == pair.deepv() );
                assert( v.deepv() == self.parse(slice@.i(data@)) );
                Some(v)
            },
        }
    }

    open spec fn marshallable(&self, value: Self::DV) -> bool
    {
        &&& W::value_marshallable(value)
        &&& self.pair_fmt.marshallable(W::to_pair(value))
    }
        
    open spec fn spec_size(&self, value: Self::DV) -> usize
    {
        self.pair_fmt.spec_size(W::to_pair(value))
    }

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
    {
        self.pair_fmt.exec_size(&W::exec_to_pair(value))
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let end = self.pair_fmt.exec_marshall((&W::exec_to_pair(value)), data, start);
        proof {
            let dsr = data@.subrange(start as int, end as int);
            W::to_from_bijective();
        }
        end
    }
}


} //verus!
