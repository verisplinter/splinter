// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

//! Direct implementation of marshalling for JournalSnapshot without the Wrappable trait complexity.

use vstd::{prelude::*};
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::IntegerMarshalling_v::*;
use crate::marshalling::UniformSized_v::*;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;
use crate::marshalling::IAddress2Format_v::IAddress2Format;
use crate::marshalling::OptionFormat_v::OptionFormat;
use crate::implementation::JournalImpl_v::JournalSnapshot;
use crate::implementation::CachedJournal_v::JournalSnapShot;
use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::{IAddress, Address};

verus! {

pub type ILsn = u64;
pub type Pointer = Option<Address>;

/// Direct marshaller for JournalSnapshot that marshalls it as:
/// - ILsn (u64, 8 bytes)
/// - Option<IAddress> using OptionFormat (1 byte tag + 8 bytes for IAddress)
pub struct JournalSnapshot2Format {
    pub lsn_fmt: IntFormat<ILsn>,
    pub addr_fmt: OptionFormat<IAddress2Format>,
}

impl JournalSnapshot2Format {
    pub open spec fn spec_new() -> Self {
        JournalSnapshot2Format {
            lsn_fmt: IntFormat::spec_new(),
            addr_fmt: OptionFormat::spec_new(IAddress2Format::spec_new()),
        }
    }

    pub fn new() -> (out: Self)
        ensures
            out == Self::spec_new(),
            out.valid(),
    {
        JournalSnapshot2Format {
            lsn_fmt: IntFormat::new(),
            addr_fmt: OptionFormat::new(IAddress2Format::new()),
        }
    }
}

// UniformSized implementation
impl UniformSized for JournalSnapshot2Format {
    open spec fn us_valid(&self) -> bool {
        &&& self.lsn_fmt.us_valid()
        &&& self.addr_fmt.us_valid()
        &&& self.lsn_fmt.uniform_size() as int + self.addr_fmt.uniform_size() as int <= usize::MAX
    }
    
    open spec fn uniform_size(&self) -> usize {
        (self.lsn_fmt.uniform_size() + self.addr_fmt.uniform_size()) as usize
    }

    proof fn uniform_size_ensures(&self)
        ensures 0 < self.uniform_size()
    {
        self.lsn_fmt.uniform_size_ensures();
        self.addr_fmt.uniform_size_ensures();
    }

    exec fn exec_uniform_size(&self) -> (sz: usize)
        ensures sz == self.uniform_size()
    {
        self.lsn_fmt.exec_uniform_size() + self.addr_fmt.exec_uniform_size()
    }
}

// Marshal implementation
impl Marshal for JournalSnapshot2Format {
    type DV = JournalSnapShot;  // The spec view type
    type U = JournalSnapshot;   // The implementation type

    open spec fn valid(&self) -> bool {
        &&& self.lsn_fmt.valid()
        &&& self.addr_fmt.valid()
        &&& self.us_valid()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool {
        let lsn_size = self.lsn_fmt.uniform_size() as int;
        let opt_start = lsn_size;
        let opt_end = lsn_size + self.addr_fmt.uniform_size() as int;
        
        &&& self.lsn_fmt.uniform_size() + self.addr_fmt.uniform_size() <= data.len()
        &&& self.lsn_fmt.parsable(data.subrange(0, lsn_size))
        &&& self.addr_fmt.parsable(data.subrange(opt_start, opt_end))
    }

    open spec fn parse(&self, data: Seq<u8>) -> Self::DV {
        let lsn_size = self.lsn_fmt.uniform_size() as int;
        let opt_start = lsn_size;
        let opt_end = lsn_size + self.addr_fmt.uniform_size() as int;
        
        let lsn_value = self.lsn_fmt.parse(data.subrange(0, lsn_size));
        let opt_value = self.addr_fmt.parse(data.subrange(opt_start, opt_end));
        
        JournalSnapShot {
            boundary_lsn: lsn_value as LSN,
            freshest_rec: opt_value,
        }
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>) {
        let total_size = self.exec_uniform_size();
        
        if slice.len() < total_size {
            return None;
        }
        if data.len() < slice.end {
            return None;
        }

        // Parse LSN field
        let lsn_size = self.lsn_fmt.exec_uniform_size();
        let lsn_slice = slice.subslice(0, lsn_size);
        let lsn_value = match self.lsn_fmt.try_parse(&lsn_slice, data) {
            None => { return None; }
            Some(v) => v,
        };

        // Parse Option<IAddress> field using OptionFormat
        let opt_start = lsn_size;
        let opt_end = lsn_size + self.addr_fmt.exec_uniform_size();
        let opt_slice = slice.subslice(opt_start, opt_end);
        let opt_value = match self.addr_fmt.try_parse(&opt_slice, data) {
            None => { return None; }
            Some(v) => v,
        };

        let result = JournalSnapshot {
            boundary_lsn: lsn_value,
            freshest_rec: opt_value,
        };

        proof {
            let idata = slice@.i(data@);
            let lsn_size_int = self.lsn_fmt.uniform_size() as int;
            let opt_size_int = self.addr_fmt.uniform_size() as int;
            let opt_start_int = lsn_size_int;
            let opt_end_int = lsn_size_int + opt_size_int;
            
            // Subrange transitivity
            assert(lsn_slice@.i(data@) == idata.subrange(0, lsn_size_int));
            assert(opt_slice@.i(data@) == idata.subrange(opt_start_int, opt_end_int));
            
            // Parsed values match
            assert(result.parsedv() == self.parse(idata));
        }

        Some(result)
    }

    open spec fn marshallable(&self, value: Self::DV) -> bool {
        &&& self.lsn_fmt.marshallable(value.boundary_lsn as int)
        &&& self.addr_fmt.marshallable(value.freshest_rec)
    }

    open spec fn impl_marshallable(&self, impl_value: Self::U) -> bool {
        &&& self.lsn_fmt.impl_marshallable(impl_value.boundary_lsn)
        &&& self.addr_fmt.impl_marshallable(impl_value.freshest_rec)
    }

    open spec fn spec_size(&self, value: Self::DV) -> usize {
        (self.lsn_fmt.uniform_size() + self.addr_fmt.uniform_size()) as usize
    }

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize) {
        self.lsn_fmt.exec_uniform_size() + self.addr_fmt.exec_uniform_size()
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize) {
        // Marshall the LSN field
        let lsn_end = self.lsn_fmt.exec_marshall(&value.boundary_lsn, data, start);
        
        proof {
            // Show we have enough space for the Option<IAddress> marshalling
            assert(lsn_end == start + self.lsn_fmt.uniform_size());
            assert(self.addr_fmt.marshallable(value.freshest_rec.parsedv()));
            assert(lsn_end as int + self.addr_fmt.spec_size(value.freshest_rec.parsedv()) as int <= data.len()) by {
                assert(start as int + self.spec_size(value.parsedv()) as int <= data.len());
            }
        }
        
        // Marshall the Option<IAddress> field using OptionFormat
        let ghost mid_data = data@;
        let opt_end = self.addr_fmt.exec_marshall(&value.freshest_rec, data, lsn_end);

        proof {
            let lsn_size = self.lsn_fmt.uniform_size() as int;
            let opt_size = self.addr_fmt.uniform_size() as int;
            
            // The first marshall didn't get stomped
            assert(mid_data.subrange(start as int, lsn_end as int) 
                   == data@.subrange(start as int, lsn_end as int));
            
            // Subrange properties
            assert(data@.subrange(start as int, opt_end as int).subrange(0, lsn_size)
                   == data@.subrange(start as int, lsn_end as int));
            assert(data@.subrange(start as int, opt_end as int).subrange(lsn_size, lsn_size + opt_size)
                   == data@.subrange(lsn_end as int, opt_end as int));
            
            assert(opt_end == start + self.spec_size(value.parsedv()));
            assert(self.parsable(data@.subrange(start as int, opt_end as int)));
        }

        opt_end
    }
}

// Prove that uniform size matches spec size for all values
impl UniformSizedMarshal for JournalSnapshot2Format {
    proof fn uniform_size_matches_spec_size(self: &Self) {
        // The spec_size is always uniform_size for this format
        assert forall |value: JournalSnapShot| #[trigger] self.spec_size(value) == self.uniform_size() by {
            // Both are always lsn_size + 1 + addr_size
        }
    }
}

} // verus!

