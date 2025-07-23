// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
// use vstd::hash_map::*;
use crate::spec::MapSpec_t::*;
use crate::spec::AsyncDisk_t::*;
use crate::spec::ImplDisk_t::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::spec::TotalKMMap_t::*;
use crate::spec::FloatingSeq_t::*;
use crate::abstract_system::MsgHistory_v::{MsgHistory, KeyedMessage};
use crate::abstract_system::StampedMap_v::*;
use crate::implementation::VecMap_v::*;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Deepview};
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::StaticallySized_v::StaticallySized;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;

verus! {

pub struct UniformPairMarshal<AF: Marshal + UniformSized, BF: Marshal + UniformSized> {
    pub a_fmt: AF,
    pub b_fmt: BF,
}

impl<AF: Marshal + UniformSized, BF: Marshal + UniformSized> UniformPairMarshal<AF, BF> {
    fn new(a_fmt: AF, b_fmt: BF) -> Self
    {
        UniformPairMarshal{ a_fmt, b_fmt }
    }
}

impl<AF: Marshal + UniformSized, BF: Marshal + UniformSized> Marshal for UniformPairMarshal<AF, BF> {
    type DV = (AF::DV, BF::DV);
    type U = (AF::U, BF::U);

    open spec fn valid(&self) -> bool { true }

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        self.a_fmt.uniform_size() + self.b_fmt.uniform_size() <= data.len()
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
            let a_slice = slice.subslice(0, self.a_fmt.exec_uniform_size());
            let a_value = self.a_fmt.exec_parse(&a_slice, data);
            let b_slice = slice.subslice(self.a_fmt.exec_uniform_size(), self.a_fmt.exec_uniform_size() + self.b_fmt.exec_uniform_size());
            let b_value = self.b_fmt.exec_parse(&b_slice, data);
            let pair_value = (a_value, b_value);
            proof {
//                 assert( pair_value.deepv() == pair_value );   // trigger
                // extn: subrange transitivity
                let bdy0 = self.a_fmt.exec_uniform_size() as int;
                let bdy1 = self.a_fmt.exec_uniform_size() as int + self.b_fmt.exec_uniform_size() as int;
                let idata = slice@.i(data@);
                assert( idata.subrange(0, bdy0) == a_slice@.i(data@) );   // extn
                assert( idata.subrange(bdy0, bdy1) == b_slice@.i(data@) );    // extn
                assert( pair_value == self.parse(idata) );   // extn
            }
            Some(pair_value)
        }
    }
    
    open spec fn marshallable(&self, value: Self::DV) -> bool
    {
        true
    }
        
    open spec fn spec_size(&self, value: Self::DV) -> usize
    {
        (u64::uniform_size() + u64::uniform_size()) as usize
    }

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
    {
        u64::exec_uniform_size() + u64::exec_uniform_size()
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let a_end = self.a_fmt.exec_marshall(&value.0, data, start);

        assert( self.a_fmt.parse(data@.subrange(start as int, a_end as int)) == value.key.0 ); // TODO delete
        let ghost mid_data = data@;
        let end = self.b_fmt.exec_marshall(&value.1, data, a_end);
        proof {
            // extn: second exec_marshall didn't stomp first
            assert( mid_data.subrange(start as int, a_end as int) == data@.subrange(start as int, a_end as int) );

            // extn: subrange transitivity
            let bdy0 = self.a_fmt.exec_uniform_size() as int;
            let bdy1 = self.a_fmt.exec_uniform_size() as int + self.b_fmt.exec_uniform_size() as int;
            assert( data@.subrange(start as int, end as int).subrange(0, bdy0)
                    == data@.subrange(start as int, a_end as int) ); // extn

            assert( data@.subrange(start as int, end as int).subrange(bdy0, bdy1)
                    == data@.subrange(a_end as int, end as int) );
        }
        end
    }
}

} //verus!
