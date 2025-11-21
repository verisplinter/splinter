// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

//! Direct implementation of marshalling for IAddress without the Wrappable trait complexity.
//! This inlines all the machinery from WrappableFormat and UniformPairFormat to show what
//! a cleaner, more direct approach could look like.

use vstd::{prelude::*};
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::IntegerMarshalling_v::*;
use crate::marshalling::UniformSized_v::*;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;
use crate::disk::GenericDisk_v::IAU;
use crate::disk::GenericDisk_v::IPage;
use crate::disk::GenericDisk_v::IAddress;
use crate::disk::GenericDisk_v::Address;
use crate::disk::GenericDisk_v::AU;
use crate::disk::GenericDisk_v::Page;

verus! {

/// Direct marshaller for IAddress that marshalls it as two consecutive integers:
/// IAU followed by IPage.
pub struct IAddress2Format {
    pub au_fmt: IntFormat<IAU>,
    pub page_fmt: IntFormat<IPage>,
}

impl IAddress2Format {
    pub open spec fn spec_new() -> Self {
        IAddress2Format {
            au_fmt: IntFormat::spec_new(),
            page_fmt: IntFormat::spec_new(),
        }
    }

    pub fn new() -> (out: Self)
        ensures
            out == Self::spec_new(),
            out.valid(),
    {
        IAddress2Format {
            au_fmt: IntFormat::new(),
            page_fmt: IntFormat::new(),
        }
    }
}

// UniformSized implementation
impl UniformSized for IAddress2Format {
    open spec fn us_valid(&self) -> bool {
        &&& self.au_fmt.us_valid()
        &&& self.page_fmt.us_valid()
        &&& self.au_fmt.uniform_size() as int + self.page_fmt.uniform_size() as int <= usize::MAX
    }
    
    open spec fn uniform_size(&self) -> usize {
        (self.au_fmt.uniform_size() + self.page_fmt.uniform_size()) as usize
    }

    proof fn uniform_size_ensures(&self)
        ensures 0 < self.uniform_size()
    {
        self.au_fmt.uniform_size_ensures();
        self.page_fmt.uniform_size_ensures();
    }

    exec fn exec_uniform_size(&self) -> (sz: usize)
        ensures sz == self.uniform_size()
    {
        self.au_fmt.exec_uniform_size() + self.page_fmt.exec_uniform_size()
    }
}

// Marshal implementation
impl Marshal for IAddress2Format {
    type DV = Address;  // The spec view type
    type U = IAddress;  // The implementation type

    open spec fn valid(&self) -> bool {
        &&& self.au_fmt.valid()
        &&& self.page_fmt.valid()
        &&& self.us_valid()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool {
        &&& self.au_fmt.uniform_size() + self.page_fmt.uniform_size() <= data.len()
        &&& self.au_fmt.parsable(data.subrange(0, self.au_fmt.uniform_size() as int))
        &&& self.page_fmt.parsable(data.subrange(
                self.au_fmt.uniform_size() as int,
                (self.au_fmt.uniform_size() + self.page_fmt.uniform_size()) as int))
    }

    open spec fn parse(&self, data: Seq<u8>) -> Self::DV {
        let au_end = self.au_fmt.uniform_size() as int;
        let page_end = au_end + self.page_fmt.uniform_size() as int;
        
        let au_value = self.au_fmt.parse(data.subrange(0, au_end));
        let page_value = self.page_fmt.parse(data.subrange(au_end, page_end));
        
        Address {
            au: au_value as AU,
            page: page_value as Page,
        }
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>) {
        let total_size = self.au_fmt.exec_uniform_size() + self.page_fmt.exec_uniform_size();
        
        if slice.len() < total_size {
            return None;
        }
        if data.len() < slice.end {
            return None;
        }

        // Parse AU field
        let au_slice = slice.subslice(0, self.au_fmt.exec_uniform_size());
        let au_value = match self.au_fmt.try_parse(&au_slice, data) {
            None => { return None; }
            Some(v) => v,
        };

        // Parse Page field
        let page_slice = slice.subslice(
            self.au_fmt.exec_uniform_size(),
            self.au_fmt.exec_uniform_size() + self.page_fmt.exec_uniform_size()
        );
        let page_value = match self.page_fmt.try_parse(&page_slice, data) {
            None => { return None; }
            Some(v) => v,
        };

        let result = IAddress {
            au: au_value,
            page: page_value,
        };

        proof {
            let idata = slice@.i(data@);
            let au_end = self.au_fmt.uniform_size() as int;
            let page_end = au_end + self.page_fmt.uniform_size() as int;
            
            // Subrange transitivity: show that slicing slice@.i(data@) is the same as
            // slicing data@ first then taking i
            assert(au_slice@.i(data@) == idata.subrange(0, au_end));
            assert(page_slice@.i(data@) == idata.subrange(au_end, page_end));
            
            // The fields are well-formed (u32 is always WF)
            assert(au_value.wf());
            assert(page_value.wf());
            
            // Now the parsed values match
            // (extensionality needed for the struct construction)
            assert(result.parsedv() == self.parse(idata));
        }

        Some(result)
    }

    open spec fn marshallable(&self, value: Self::DV) -> bool {
        &&& self.au_fmt.marshallable(value.au as int)
        &&& self.page_fmt.marshallable(value.page as int)
    }

    open spec fn impl_marshallable(&self, impl_value: Self::U) -> bool {
        &&& self.au_fmt.impl_marshallable(impl_value.au)
        &&& self.page_fmt.impl_marshallable(impl_value.page)
    }

    open spec fn spec_size(&self, value: Self::DV) -> usize {
        (self.au_fmt.uniform_size() + self.page_fmt.uniform_size()) as usize
    }

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize) {
        self.au_fmt.exec_uniform_size() + self.page_fmt.exec_uniform_size()
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize) {
        // Marshall the AU field
        let au_end = self.au_fmt.exec_marshall(&value.au, data, start);
        
        proof {
            let ghost au_size = self.au_fmt.uniform_size() as int;
            assert(au_end == start + au_size);
        }

        // Marshall the Page field
        let ghost mid_data = data@;
        let page_end = self.page_fmt.exec_marshall(&value.page, data, au_end);

        proof {
            let au_size = self.au_fmt.uniform_size() as int;
            let page_size = self.page_fmt.uniform_size() as int;
            let total_size = au_size + page_size;
            
            // The second marshall didn't stomp the first
            assert(mid_data.subrange(start as int, au_end as int) 
                   == data@.subrange(start as int, au_end as int));
            
            // Show subrange properties
            assert(data@.subrange(start as int, page_end as int).subrange(0, au_size)
                   == data@.subrange(start as int, au_end as int));
            assert(data@.subrange(start as int, page_end as int).subrange(au_size, total_size)
                   == data@.subrange(au_end as int, page_end as int));
            
            // Final properties
            assert(page_end == start + self.spec_size(value.parsedv()));
            assert(self.parsable(data@.subrange(start as int, page_end as int)));
        }

        page_end
    }
}

// Prove that uniform size matches spec size for all values
impl UniformSizedMarshal for IAddress2Format {
    proof fn uniform_size_matches_spec_size(self: &Self) {
        // The spec_size is always uniform_size for this format
        assert forall |value: Address| #[trigger] self.spec_size(value) == self.uniform_size() by {
            // Both are just the sum of the two field sizes
        }
    }
}

} // verus!

