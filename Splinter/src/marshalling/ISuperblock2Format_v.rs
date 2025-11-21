// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

//! Direct implementation of marshalling for ISuperblock without the Wrappable trait complexity.

use vstd::{prelude::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::IntegerMarshalling_v::*;
use crate::marshalling::UniformSized_v::*;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;
use crate::marshalling::JournalSnapshot2Format_v::JournalSnapshot2Format;
use crate::marshalling::KeyValueFormat_v::KeyValueFormat;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::marshalling::PaddedFormat_v::*;
use crate::trusted::ClientAPI_t::BLOCK_SIZE;
use crate::implementation::JournalTypes_v::*;
use crate::implementation::SuperblockTypes_v::*;
use crate::implementation::CachedJournal_v;
use crate::implementation::JournalImpl_v::JournalSnapshot;
use crate::disk::GenericDisk_v::Address;
use crate::disk::GenericDisk_v::IAddress;

verus! {

/// Direct marshaller for ISuperblock that marshalls it as:
/// - JournalSnapshot (using JournalSnapshot2Format)
/// - Vec<(Key, Value)> (using ResizableUniformSizedElementSeqFormat<KeyValueFormat>)
pub struct ISuperblock2Format {
    pub journal_fmt: JournalSnapshot2Format,
    pub store_fmt: ResizableUniformSizedElementSeqFormat<KeyValueFormat, u8>,
}

impl ISuperblock2Format {
    pub open spec fn spec_new() -> Self {
        ISuperblock2Format {
            journal_fmt: JournalSnapshot2Format::spec_new(),
            store_fmt: ResizableUniformSizedElementSeqFormat::spec_new(
                KeyValueFormat::spec_new(),
                IntFormat::<u8>::spec_new(),
                200
            ),
        }
    }

    pub fn new() -> (out: Self)
        ensures
            out == Self::spec_new(),
            out.valid(),
    {
        ISuperblock2Format {
            journal_fmt: JournalSnapshot2Format::new(),
            store_fmt: ResizableUniformSizedElementSeqFormat::new(
                KeyValueFormat::new(),
                IntFormat::<u8>::new(),
                200
            ),
        }
    }
}

// UniformSized implementation
impl UniformSized for ISuperblock2Format {
    open spec fn us_valid(&self) -> bool {
        &&& self.journal_fmt.us_valid()
        &&& self.store_fmt.us_valid()
        &&& self.journal_fmt.uniform_size() as int + self.store_fmt.uniform_size() as int <= usize::MAX
    }
    
    open spec fn uniform_size(&self) -> usize {
        (self.journal_fmt.uniform_size() + self.store_fmt.uniform_size()) as usize
    }

    proof fn uniform_size_ensures(&self)
        ensures 0 < self.uniform_size()
    {
        self.journal_fmt.uniform_size_ensures();
        self.store_fmt.uniform_size_ensures();
    }

    exec fn exec_uniform_size(&self) -> (sz: usize)
        ensures sz == self.uniform_size()
    {
        self.journal_fmt.exec_uniform_size() + self.store_fmt.exec_uniform_size()
    }
}

// Marshal implementation
impl Marshal for ISuperblock2Format {
    type DV = ASuperblock;  // The spec view type
    type U = ISuperblock;   // The implementation type

    open spec fn valid(&self) -> bool {
        &&& self.journal_fmt.valid()
        &&& self.store_fmt.valid()
        &&& self.us_valid()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool {
        let journal_size = self.journal_fmt.uniform_size() as int;
        let store_start = journal_size;
        let store_end = journal_size + self.store_fmt.uniform_size() as int;
        
        &&& self.journal_fmt.uniform_size() + self.store_fmt.uniform_size() <= data.len()
        &&& self.journal_fmt.parsable(data.subrange(0, journal_size))
        &&& self.store_fmt.parsable(data.subrange(store_start, store_end))
    }

    open spec fn parse(&self, data: Seq<u8>) -> Self::DV {
        let journal_size = self.journal_fmt.uniform_size() as int;
        let store_start = journal_size;
        let store_end = journal_size + self.store_fmt.uniform_size() as int;
        
        let journal_value = self.journal_fmt.parse(data.subrange(0, journal_size));
        let store_value = self.store_fmt.parse(data.subrange(store_start, store_end));
        
        ASuperblock {
            journal: journal_value,
            store: store_value,
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

        // Parse JournalSnapshot field
        let journal_size = self.journal_fmt.exec_uniform_size();
        let journal_slice = slice.subslice(0, journal_size);
        let journal_value = match self.journal_fmt.try_parse(&journal_slice, data) {
            None => { 
                proof {
                    // If journal doesn't parse, the whole thing doesn't parse
                    assert(!self.journal_fmt.parsable(journal_slice@.i(data@)));
                    assert(!self.parsable(slice@.i(data@)));
                }
                return None;
            }
            Some(v) => v,
        };

        // Parse RawStore field
        let store_start = journal_size;
        let store_end = journal_size + self.store_fmt.exec_uniform_size();
        let store_slice = slice.subslice(store_start, store_end);
        let store_value = match self.store_fmt.try_parse(&store_slice, data) {
            None => { 
                proof {
                    let idata = slice@.i(data@);
                    let journal_size_int = self.journal_fmt.uniform_size() as int;
                    let store_size_int = self.store_fmt.uniform_size() as int;
                    let store_start_int = journal_size_int;
                    let store_end_int = journal_size_int + store_size_int;
                    
                    // If store doesn't parse, the whole thing doesn't parse
                    assert(store_slice@.i(data@) == idata.subrange(store_start_int, store_end_int));
                    assert(!self.store_fmt.parsable(idata.subrange(store_start_int, store_end_int)));
                    assert(!self.parsable(idata));
                }
                return None;
            }
            Some(v) => v,
        };

        let result = ISuperblock {
            journal_snapshot: journal_value,
            store: store_value,
        };

        proof {
            let idata = slice@.i(data@);
            let journal_size_int = self.journal_fmt.uniform_size() as int;
            let store_size_int = self.store_fmt.uniform_size() as int;
            let store_start_int = journal_size_int;
            let store_end_int = journal_size_int + store_size_int;
            
            // Subrange transitivity
            assert(journal_slice@.i(data@) == idata.subrange(0, journal_size_int));
            assert(store_slice@.i(data@) == idata.subrange(store_start_int, store_end_int));
            
            // Show the fields parse correctly
            assert(journal_value.parsedv() == self.journal_fmt.parse(idata.subrange(0, journal_size_int)));
            assert(store_value.parsedv() == self.store_fmt.parse(idata.subrange(store_start_int, store_end_int)));
            
            // Parsed values match (requires extensionality for the struct)
            assert(result.parsedv().journal == self.parse(idata).journal);
            assert(result.parsedv().store == self.parse(idata).store);
        }

        Some(result)
    }

    open spec fn marshallable(&self, value: Self::DV) -> bool {
        &&& self.journal_fmt.marshallable(value.journal)
        &&& self.store_fmt.marshallable(value.store)
    }

    open spec fn impl_marshallable(&self, impl_value: Self::U) -> bool {
        &&& self.journal_fmt.impl_marshallable(impl_value.journal_snapshot)
        &&& self.store_fmt.impl_marshallable(impl_value.store)
    }

    open spec fn spec_size(&self, value: Self::DV) -> usize {
        (self.journal_fmt.uniform_size() + self.store_fmt.uniform_size()) as usize
    }

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize) {
        self.journal_fmt.exec_uniform_size() + self.store_fmt.exec_uniform_size()
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize) {
        // Marshall the JournalSnapshot field
        let journal_end = self.journal_fmt.exec_marshall(&value.journal_snapshot, data, start);
        
        // Marshall the RawStore field
        let ghost mid_data = data@;
        let store_end = self.store_fmt.exec_marshall(&value.store, data, journal_end);

        proof {
            let journal_size = self.journal_fmt.uniform_size() as int;
            let store_size = self.store_fmt.uniform_size() as int;
            let subr = data@.subrange(start as int, store_end as int);
            
            // The first marshall didn't get stomped
            assert(mid_data.subrange(start as int, journal_end as int) 
                   == data@.subrange(start as int, journal_end as int));
            
            // Subrange properties
            assert(subr.subrange(0, journal_size)
                   == data@.subrange(start as int, journal_end as int));
            assert(subr.subrange(journal_size, journal_size + store_size)
                   == data@.subrange(journal_end as int, store_end as int));
            
            // Show parsable
            assert(self.journal_fmt.parsable(subr.subrange(0, journal_size)));
            assert(self.store_fmt.parsable(subr.subrange(journal_size, journal_size + store_size)));
            assert(self.parsable(subr));
            
            // Show parse matches
            assert(self.journal_fmt.parse(subr.subrange(0, journal_size)) == value.journal_snapshot.parsedv());
            assert(self.store_fmt.parse(subr.subrange(journal_size, journal_size + store_size)) == value.store.parsedv());
            assert(self.parse(subr).journal == value.parsedv().journal);
            assert(self.parse(subr).store == value.parsedv().store);
            
            assert(store_end == start + self.spec_size(value.parsedv()));
        }

        store_end
    }
}

// Prove that uniform size matches spec size for all values
impl UniformSizedMarshal for ISuperblock2Format {
    proof fn uniform_size_matches_spec_size(self: &Self) {
        // The spec_size is always uniform_size for this format
        assert forall |value: ASuperblock| #[trigger] self.spec_size(value) == self.uniform_size() by {
            // Both are always journal_size + store_size
        }
    }
}

// The padded version for BLOCK_SIZE alignment
pub type ISuperblock2FormatPadded = PaddedFormat<ISuperblock2Format>;

impl ISuperblock2FormatPadded {
    pub open spec fn spec_new() -> (out: Self)
    {
        PaddedFormat{
            format: ISuperblock2Format::spec_new(),
            pad_size: BLOCK_SIZE
        }
    }

    pub fn new() -> (out: Self)
        ensures out == Self::spec_new()
    {
        PaddedFormat{
            format: ISuperblock2Format::new(),
            pad_size: BLOCK_SIZE
        }
    }
}

} // verus!

