// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Deepview};
use crate::marshalling::UniformSized_v::UniformSized;

verus! {

pub struct UniformPairMarshal<AF: Marshal + UniformSized, BF: Marshal + UniformSized> {
    pub a_fmt: AF,
    pub b_fmt: BF,
}

impl<AF: Marshal + UniformSized, BF: Marshal + UniformSized> UniformPairMarshal<AF, BF> {
    pub fn new(a_fmt: AF, b_fmt: BF) -> Self
    {
        UniformPairMarshal{ a_fmt, b_fmt }
    }
}

impl<AF: Marshal + UniformSized, BF: Marshal + UniformSized> Marshal for UniformPairMarshal<AF, BF>
    where (AF::U, BF::U): Deepview<(AF::DV, BF::DV)> 
{
    type DV = (AF::DV, BF::DV);
    type U = (AF::U, BF::U);

    open spec fn valid(&self) -> bool {
        &&& self.a_fmt.valid()
        &&& self.b_fmt.valid()
        &&& self.a_fmt.uniform_size() as int + self.b_fmt.uniform_size() as int <= usize::MAX

        // Uniform size matches spec_size
        &&& forall |a_val: AF::DV| self.a_fmt.spec_size(a_val) == self.a_fmt.uniform_size()
        &&& forall |b_val: BF::DV| self.b_fmt.spec_size(b_val) == self.b_fmt.uniform_size()

        // deepv of pair is pair of deepvs
        &&& forall |pair: (AF::U, BF::U)| #![auto] ( pair.0.deepv() == pair.deepv().0 && pair.1.deepv() == pair.deepv().1 )
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        &&& self.a_fmt.uniform_size() + self.b_fmt.uniform_size() <= data.len()
        &&& self.a_fmt.parsable(data.subrange(0, self.a_fmt.uniform_size() as int))
        &&& self.b_fmt.parsable(data.subrange(self.a_fmt.uniform_size() as int,
            (self.a_fmt.uniform_size() + self.b_fmt.uniform_size() as int)))
    }

    open spec fn parse(&self, data: Seq<u8>) -> Self::DV
    {
        let bdy0 = self.a_fmt.uniform_size() as int;
        let bdy1 = self.a_fmt.uniform_size() as int + self.b_fmt.uniform_size() as int;
        let a_value = self.a_fmt.parse(data.subrange(0, bdy0));
        let b_value = self.b_fmt.parse(data.subrange(bdy0, bdy1));
        ( a_value, b_value )
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    {
        if slice.len() < self.a_fmt.exec_uniform_size() + self.b_fmt.exec_uniform_size() {
            // Not enough slice for the format
            None
        } else if data.len() < slice.end {
            // Not enough data for the slice
            None
        } else {
            let ghost bdy0 = self.a_fmt.uniform_size() as int;
            let ghost bdy1 = self.a_fmt.uniform_size() as int + self.b_fmt.uniform_size() as int;

            let a_slice = slice.subslice(0, self.a_fmt.exec_uniform_size());
            assert( a_slice@.i(data@) == slice@.i(data@).subrange(0, bdy0) );

            let a_value = match self.a_fmt.try_parse(&a_slice, data) {
                None => { return None }
                Some(v) => v,
            };
            let b_slice = slice.subslice(self.a_fmt.exec_uniform_size(), self.a_fmt.exec_uniform_size() + self.b_fmt.exec_uniform_size());
            assert( b_slice@.i(data@) == slice@.i(data@).subrange(bdy0, bdy1) );
            let b_value = match self.b_fmt.try_parse(&b_slice, data) {
                None => { return None }
                Some(v) => v,
            };
            let pair_value = (a_value, b_value);
            proof {
                // extn: subrange transitivity
                let idata = slice@.i(data@);
//                 assert( pair_value.0.deepv() == self.a_fmt.parse(idata.subrange(0, bdy0)) );
                assert( pair_value.1.deepv() == self.b_fmt.parse(idata.subrange(bdy0, bdy1)) );
                assert( pair_value.deepv() == self.parse(idata) );   // extn
            }
            Some(pair_value)
        }
    }
    
    open spec fn marshallable(&self, value: Self::DV) -> bool
    {
        &&& self.a_fmt.marshallable(value.0)
        &&& self.b_fmt.marshallable(value.1)
    }
        
    open spec fn spec_size(&self, value: Self::DV) -> usize
    {
        (self.a_fmt.uniform_size() + self.b_fmt.uniform_size()) as usize
    }

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
    {
        self.a_fmt.exec_uniform_size() + self.b_fmt.exec_uniform_size()
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        assert( self.a_fmt.marshallable(value.0.deepv()) );
        let a_end = self.a_fmt.exec_marshall(&value.0, data, start);

        let ghost mid_data = data@;
        let end = self.b_fmt.exec_marshall(&value.1, data, a_end);
        proof {
            // extn: second exec_marshall didn't stomp first
            assert( mid_data.subrange(start as int, a_end as int) == data@.subrange(start as int, a_end as int) );

            // extn: subrange transitivity
            let bdy0 = self.a_fmt.uniform_size() as int;
            let bdy1 = self.a_fmt.uniform_size() as int + self.b_fmt.uniform_size() as int;
            assert( data@.subrange(start as int, end as int).subrange(0, bdy0)
                    == data@.subrange(start as int, a_end as int) ); // extn

            assert( data@.subrange(start as int, end as int).subrange(bdy0, bdy1)
                    == data@.subrange(a_end as int, end as int) );

            assert( end == start + self.spec_size(value.deepv()) );
            assert( self.parsable(data@.subrange(start as int, end as int)) );
        }
        end
    }
}

} //verus!
