// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::marshalling::Marshalling_v::Marshal;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::WF_v::WF;
use crate::marshalling::KeyValueFormat_v::*;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::implementation::VecMap_v::*;

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

    closed spec fn spec_size(&self, value: Self::DV) -> usize
    {
        self.seq_fmt.spec_size(VecMap::map_to_seq(value))
    }

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
    {
        let rv = value.borrow_vec();
        self.seq_fmt.exec_size(rv)
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let end = self.seq_fmt.exec_marshall(value.borrow_vec(), data, start);
        proof {
            let dsr = data@.subrange(start as int, end as int);
            assert( self.seq_fmt.parse(dsr) == VecMap::map_to_seq(value@) );    // extn
            value.view_ensures();
            VecMap::map_to_seq_contents(value@);
            VecMap::seq_to_map_inverse(value@);
        }
        end
    }
}

} //verus!

