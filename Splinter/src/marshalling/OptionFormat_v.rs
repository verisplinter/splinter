// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::UniformPairFormat_v::*;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::WF_v::WF;

verus! {

pub struct OptionFormat<F: Marshal> {
    pub f: F
}

impl<F: Marshal> OptionFormat<F> {
    pub open spec fn spec_new(f: F) -> Self
    {
        Self{f}
    }

    pub fn new(f: F) -> (out: Self)
    ensures out == Self::spec_new(f)
    {
        Self{f}
    }
}

impl<F: Marshal + UniformSized> UniformSized for OptionFormat<F>
{
    open spec fn us_valid(&self) -> bool
    {
        &&& self.f.us_valid()
        &&& self.f.uniform_size() + 1 <= usize::MAX
    }
    
    open spec fn uniform_size(&self) -> (sz: usize)
    {
        (1 + self.f.uniform_size()) as usize
    }
    
    proof fn uniform_size_ensures(&self)
    {
    }
    
    exec fn exec_uniform_size(&self) -> (sz: usize)
    {
        1 + self.f.exec_uniform_size()
    }
}

impl<U> WF for Option<U>
where U: WF
{
    open spec fn wf(&self) -> bool {
        match self {
            None => true,
            Some(f) => f.wf(),
        }
    }
}

impl<U, DV> Parsedview<Option<DV>> for Option<U>
where U: Parsedview<DV>
{
    open spec fn parsedv(&self) -> Option<DV> {
        match self {
            None => None,
            Some(f) => Some(f.parsedv()),
        }
    }
}

impl<F: Marshal + UniformSized> Marshal for OptionFormat<F>
// This constraint pushes the option-wrapper-Parsedview obligation
// off to the caller, which feels lame. But Rust won't let me write
// Parsedview for Option<F> in a generic way, frustratingly.
// where Option<F::U>: Parsedview<Option<F::DV>>
{
    type DV = Option<F::DV>;
    type U = Option<F::U>;
    
    open spec fn valid(&self) -> bool
    {
        self.f.valid()
    }
    
    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        false
    }
    
    open spec fn parse(&self, data: Seq<u8>) -> Self::DV
    {
        None
    }
    
    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    {
        None
    }

    open spec fn marshallable(&self, value: Self::DV) -> bool
    {
        match value {
            None => true,
            Some(v) => self.f.marshallable(v),
        }
    }

    // This marshaller is UniformSize, so we always waste the space
    // it would have taken to encode f, even when the option is None
    open spec fn spec_size(&self, value: Self::DV) -> usize
    {
        self.uniform_size()
    }
    
    exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
    {
        self.exec_uniform_size()
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        match value {
            None => { data[start] = 0; }
            Some(v) => {
                data[start] = 1;
                self.f.exec_marshall(v, data, start + 1);
            }
        }
        start + self.exec_uniform_size()
    }
}

} //verus!
