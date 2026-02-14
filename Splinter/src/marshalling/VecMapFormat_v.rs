// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::Value;
use crate::marshalling::Marshalling_v::Marshal;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::WF_v::WF;
// use crate::marshalling::SeqMarshalling_v::*;
use crate::marshalling::KeyValueFormat_v::KeyValueFormat;
// use crate::marshalling::UniformSized_v::*;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::implementation::VecMap_v::VecMap;

verus! {

impl Parsedview<Map<Key, Value>> for VecMap<Key,Value> {
    open spec fn parsedv(&self) -> Map<Key, Value> {
        self@
    }
}

struct VecMapFormat
{
    seq_fmt: ResizableUniformSizedElementSeqFormat<KeyValueFormat, u8>,
}

impl VecMapFormat {
    pub closed spec fn max_length(self) -> usize
    {
        self.seq_fmt.max_length
    }
}

impl Marshal for VecMapFormat {
    type DV = Map<Key,Value>;
    type U = VecMap<Key,Value>;

    closed spec fn valid(&self) -> bool
    {
        self.seq_fmt.valid()
    }

    //////////////////////////////////////////////////////////////////////
    // Parsing
    //////////////////////////////////////////////////////////////////////

    closed spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        &&& self.seq_fmt.parsable(data)
        &&& VecMap::unique_keys(self.seq_fmt.parse(data))   // can't parse it if contents aren't wf
    }

    closed spec fn parse(&self, data: Seq<u8>) -> Self::DV
    {
        VecMap::seq_to_map(self.seq_fmt.parse(data))
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    {
        match self.seq_fmt.try_parse(slice, data) {
            None => None,
            Some(v) => {
                let ghost idata = slice@.i(data@);
                assert( self.seq_fmt.parse(idata) == v@ );  // extn
                if !VecMap::exec_unique_keys(&v) { None }
                else {
                    let v = VecMap::from_vec(v);
                    assert( self.parse(slice@.i(data@)) == v.parsedv() ); // trigger trait ensures
                    assert(v.wf()); // trigger trait ensures
                    Some(v)
                } 
            }
        }
    }

    exec fn exec_parse(&self, slice: &Slice, data: &Vec<u8>) -> (value: Self::U)
    {
        let ghost idata = slice@.i(data@);
        let v = self.seq_fmt.exec_parse(slice, data);
//         assert( self.parsable(idata) );
        assert( v@ == self.seq_fmt.parse(idata) );  // trigger something?
//         assert( VecMap::unique_keys(v@) );
        let value = VecMap::from_vec(v);
//         assert( value.parsedv() == self.parse(idata) );
        value
    }

    //////////////////////////////////////////////////////////////////////
    // Marshalling
    //////////////////////////////////////////////////////////////////////

    closed spec fn marshallable(&self, value: Self::DV) -> bool
    {
        &&& self.seq_fmt.marshallable(VecMap::map_to_seq(value))
    }

    open spec fn impl_marshallable(&self, impl_value: Self::U) -> bool
    {
        &&& VecMap::unique_keys(impl_value.as_seq())
        &&& impl_value.as_seq().len() <= u8::MAX
        &&& impl_value.as_seq().len() <= self.max_length()
    }

    closed spec fn spec_size(&self, value: Self::DV) -> usize
    {
        self.seq_fmt.spec_size(VecMap::map_to_seq(value))
    }

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
    {
        let rv = value.borrow_vec();
        let ghost pv: Seq<(Key, Value)>  = rv.parsedv();
        // pv might not have unique_keys
        // except that's not the assertion complaint
        // and yeah we have marshallable of map_to_seq
        // Ah, but we have lost the fact that seq_to_map preserves the count and vice versa
        let ghost mv = VecMap::seq_to_map(pv);
        proof {
            assert( pv == value.as_seq() );
            assert( VecMap::unique_keys(value.as_seq()) );
            assert( VecMap::unique_keys(pv) );
            VecMap::seq_to_map_ensures(pv);
            assert( pv == rv@ );
            assert( pv.len() == rv@.len() );
            assert(pv.len() == VecMap::seq_to_map(rv@).len() );
            VecMap::map_to_seq_contents(mv);
            assert( VecMap::map_to_seq(mv).len() == mv.len() );
            assert( mv.len() == pv.len() );
        };
        let ghost qv = VecMap::map_to_seq(VecMap::seq_to_map(rv@));
        assert( qv == VecMap::map_to_seq(mv) );
        assert( qv.len() == pv.len() );
        assert( self.seq_fmt.marshallable(rv.parsedv()) );
        self.seq_fmt.exec_size(rv)
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let bv = value.borrow_vec();
        let end = self.seq_fmt.exec_marshall(bv, data, start);
        proof {
            assert( bv@ == bv.parsedv() );  // extn
            value.view_ensures();
        }
        end
    }
}

} //verus!

