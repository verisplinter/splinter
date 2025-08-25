// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::Marshalling_v::*;
use crate::marshalling::WF_v::*;
use crate::marshalling::UniformPairFormat_v::uniform_size_matches_spec_size;

verus! {

pub struct PaddedFormat<F: Marshal + UniformSized> {
    pub format: F,
    pub pad_size: usize,
}

impl<F: Marshal + UniformSized> PaddedFormat<F> {
    pub proof fn uniform_size_matches_spec_size(self)
    requires self.valid()
    ensures uniform_size_matches_spec_size(self)
    {
    }
}

impl<F: Marshal + UniformSized> Marshal for PaddedFormat<F> {
    type DV = F::DV;
    type U = F::U;

    open spec fn valid(&self) -> bool {
        &&& self.us_valid()
        &&& self.format.valid()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        &&& self.uniform_size() <= data.len()
        &&& self.format.parsable(data.subrange(0, self.format.uniform_size() as int))
    }

    open spec fn parse(&self, data: Seq<u8>) -> Self::DV
    {
        self.format.parse(data.subrange(0, self.format.uniform_size() as int))
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    {
        if slice.len() < self.exec_uniform_size() {
            // Can't even construct the subslice to exclude the padding.
            return None;
        }

        let subslice = slice.subslice(0, self.format.exec_uniform_size());
        let ov = self.format.try_parse(&subslice, data);

        assert( slice@.i(data@).subrange(0, self.format.uniform_size() as int) == subslice@.i(data@) ); // extn

        proof {
            let ghost ov = ov;
            match ov {
                Some(v) => {
                    assert( v.parsedv() == self.parse(slice@.i(data@)) ); // trigger
                },
                None => { },
            }
        }
        ov
    }

    open spec fn marshallable(&self, value: Self::DV) -> bool
    {
        self.format.marshallable(value)
    }
        
    open spec fn spec_size(&self, value: Self::DV) -> usize
    {
        self.pad_size
    }

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
    {
        self.pad_size
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let format_end = self.format.exec_marshall(value, data, start);
        let end = start + self.pad_size;
        assert( self.valid() );
        assert( data@.subrange(start as int, end as int).subrange(0, self.format.uniform_size() as int) == data@.subrange(start as int, format_end as int) );   // extn
        end
    }
}

impl<F: Marshal + UniformSized> UniformSized for PaddedFormat<F> {
    open spec fn us_valid(&self) -> bool
    {
        &&& self.format.us_valid()
        &&& uniform_size_matches_spec_size(self.format)
        &&& self.format.uniform_size() <= self.pad_size
    }

    open spec fn uniform_size(&self) -> (sz: usize)
    {
        self.pad_size
    }

    proof fn uniform_size_ensures(&self) {
        self.format.uniform_size_ensures();
    }

    exec fn exec_uniform_size(&self) -> (sz: usize)
    {
        self.pad_size
    }
}

}
