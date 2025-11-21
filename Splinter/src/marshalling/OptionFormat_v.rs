// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::UniformPairFormat_v::*;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;

verus! {

pub struct OptionFormat<F: UniformSizedMarshal> {
    pub f: F
}

impl<F: UniformSizedMarshal> OptionFormat<F> {
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

impl<F: UniformSizedMarshal> UniformSized for OptionFormat<F>
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

impl<F: UniformSizedMarshal> Marshal for OptionFormat<F>
// This constraint pushes the option-wrapper-Parsedview obligation
// off to the caller, which feels lame. But Rust won't let me write
// Parsedview for Option<F> in a generic way, frustratingly.
// where Option<F::U>: Parsedview<Option<F::DV>>
{
    type DV = Option<F::DV>;
    type U = Option<F::U>;
    
    open spec fn valid(&self) -> bool
    {
        &&& self.f.valid()
        &&& self.us_valid()
    }
    
    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        if data.len() < self.uniform_size() { false }
        else {
            match data[0] {
                0 => { true },
                1 => { self.f.parsable(data.subrange(1, 1 + self.f.uniform_size() as int)) },
                _ => { false },
            }
        }
    }
    
    open spec fn parse(&self, data: Seq<u8>) -> Self::DV
    {
        match data[0] {
            0 => { None },
            1 => { Some(self.f.parse(data.subrange(1, 1 + self.f.uniform_size() as int))) },
            _ => { arbitrary() },
        }
    }
    
    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    {
        if slice.len() < self.exec_uniform_size() {
            return None;
        }
        match data[slice.start] {
            0 => {
                let ov = Some(None);
                assert( ov.unwrap().parsedv() == self.parse(slice@.i(data@)) ); // trait ensures 🙄
                assert( ov.unwrap().wf() ); // what does this trigger!?
                ov
            }
            1 => {
                let ss = slice.subslice(1, 1 + self.f.exec_uniform_size());
                assert( ss@.i(data@) == slice@.i(data@).subrange(1, 1 + self.f.uniform_size() as int) );    // extn
                match self.f.try_parse(&ss, data)
                {
                    Some(v) => { Some(Some(v)) }
                    None => { None }
                }
            }
            _ => { None }
        }
    }

    open spec fn marshallable(&self, value: Self::DV) -> bool
    {
        match value {
            None => true,
            Some(v) => self.f.marshallable(v),
        }
    }

    open spec fn impl_marshallable(&self, impl_value: Self::U) -> bool
    {
        match impl_value {
            None => true,
            Some(v) => self.f.impl_marshallable(v),
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
        let end = start + self.exec_uniform_size();
        match value {
            None => { 
                data.set(start, 0);
                // We don't need to write anything to the rest of the space - parsable
                // only looks at the tag byte when it's 0
                proof {
                    let subr = data@.subrange(start as int, end as int);
                    assert(subr[0] == 0);
                    assert(self.parsable(subr));
                    assert(self.parse(subr) == value.parsedv());
                }
            }
            Some(v) => {
                data.set(start, 1);
                proof { self.f.uniform_size_matches_spec_size(); }
                let ghost mid_data = data@;
                let f_end = self.f.exec_marshall(v, data, start + 1);
                proof {
                    let subr = data@.subrange(start as int, end as int);
                    // Tag byte preserved
                    assert( mid_data.subrange(start as int, start + 1 as int) ==
                        data@.subrange(start as int, start + 1 as int) );
                    assert(subr[0] == 1);
                    // Inner value marshalled correctly
                    assert( data@.subrange(start + 1 as int, f_end as int ) ==
                        subr.subrange(1, 1 + self.f.uniform_size() as int) ); // extn
                    assert(self.f.parsable(subr.subrange(1, 1 + self.f.uniform_size() as int)));
                    assert(self.parsable(subr));
                    assert(self.parse(subr) == value.parsedv());
                }
            }
        }
        end
    }
}

} //verus!
