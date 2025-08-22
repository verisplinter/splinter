// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::Marshalling_v::Marshal;

verus! {

pub struct PaddedFormat<F: Marshal + UniformSized> {
    pub format: F,
    pub pad_size: usize,
}

impl<F: Marshal + UniformSized> Marshal for PaddedFormat<F> {
    type DV = F::DV;
    type U = F::U;

    open spec fn valid(&self) -> bool {
        &&& self.us_valid()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        self.format.parsable(data)
    }

    open spec fn parse(&self, data: Seq<u8>) -> Self::DV
    {
        self.format.parse(data)
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    {
        self.format.try_parse(slice, data)
    }

    open spec fn marshallable(&self, value: Self::DV) -> bool
    {
        self.format.marshallable(value)
    }
        
    open spec fn spec_size(&self, value: Self::DV) -> usize
    {
        self.format.spec_size(value)
    }

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
    {
        self.format.exec_size(value)
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        self.format.exec_marshall(value, data, start)
    }
}

impl<F: Marshal + UniformSized> UniformSized for PaddedFormat<F> {
    open spec fn us_valid(&self) -> bool
    {
        &&& self.format.us_valid()
        &&& self.format.uniform_size() <= self.pad_size
    }

    open spec fn uniform_size(&self) -> (sz: usize)
    {
        self.pad_size
    }

    proof fn uniform_size_ensures(&self) { }

    exec fn exec_uniform_size(&self) -> (sz: usize)
    {
        self.pad_size
    }
}

}
