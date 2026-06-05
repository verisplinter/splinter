// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich
// SPDX-License-Identifier: BSD-2-Clause

//! IJournalSnapshotFormat_v - marshaller for JournalSnapshot.

use crate::implementation::JournalImpl_v::IJournalSnapshot;
use crate::implementation::CachedJournal_v::{JournalRoot, JournalSnapshot};
use crate::disk::GenericDisk_v::{IAddress, IAU};
use crate::marshalling::NatFormat_v::NatFormat;
use crate::marshalling::IAddressFormat_v::IAddressFormat;
use crate::marshalling::OptionFormat_v::OptionFormat;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;
use vstd::prelude::*;

verus! {

pub struct IJournalSnapshotFormat {
    pub field1_fmt: NatFormat<u64>,
    pub field2_fmt: OptionFormat<IAddressFormat>,
    pub field3_fmt: NatFormat<IAU>,
}

impl IJournalSnapshotFormat {
    pub open spec fn spec_new() -> Self {
        Self {
            field1_fmt: NatFormat::spec_new(),
            field2_fmt: OptionFormat::spec_new(IAddressFormat::spec_new()),
            field3_fmt: NatFormat::spec_new(),
        }
    }

    pub fn new() -> (out: Self)
        ensures
            out == Self::spec_new(),
            out.valid(),
    {
        Self {
            field1_fmt: NatFormat::new(),
            field2_fmt: OptionFormat::new(IAddressFormat::new()),
            field3_fmt: NatFormat::new(),
        }
    }
}

impl UniformSized for IJournalSnapshotFormat {
    open spec fn us_valid(&self) -> bool {
        &&& self.field1_fmt.us_valid()
        &&& self.field2_fmt.us_valid()
        &&& self.field3_fmt.us_valid()
        &&& self.field1_fmt.uniform_size() as int
            + self.field2_fmt.uniform_size() as int
            + self.field3_fmt.uniform_size() as int <= usize::MAX
    }

    open spec fn uniform_size(&self) -> usize {
        (self.field1_fmt.uniform_size()
            + self.field2_fmt.uniform_size()
            + self.field3_fmt.uniform_size()) as usize
    }

    proof fn uniform_size_ensures(&self)
        ensures 0 < self.uniform_size()
    {
        self.field1_fmt.uniform_size_ensures();
        self.field2_fmt.uniform_size_ensures();
        self.field3_fmt.uniform_size_ensures();
    }

    exec fn exec_uniform_size(&self) -> (sz: usize)
        ensures sz == self.uniform_size()
    {
        self.field1_fmt.exec_uniform_size()
            + self.field2_fmt.exec_uniform_size()
            + self.field3_fmt.exec_uniform_size()
    }
}

impl Marshal for IJournalSnapshotFormat {
    type DV = JournalSnapshot;
    type U = IJournalSnapshot;

    open spec fn valid(&self) -> bool {
        &&& self.field1_fmt.valid()
        &&& self.field2_fmt.valid()
        &&& self.field3_fmt.valid()
        &&& self.us_valid()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool {
        let f1_end = self.field1_fmt.uniform_size() as int;
        let f2_end = f1_end + self.field2_fmt.uniform_size() as int;
        let f3_end = f2_end + self.field3_fmt.uniform_size() as int;
        &&& f3_end <= data.len()
        &&& self.field1_fmt.parsable(data.subrange(0, f1_end))
        &&& self.field2_fmt.parsable(data.subrange(f1_end, f2_end))
        &&& self.field3_fmt.parsable(data.subrange(f2_end, f3_end))
    }

    open spec fn parse(&self, data: Seq<u8>) -> Self::DV {
        let f1_end = self.field1_fmt.uniform_size() as int;
        let f2_end = f1_end + self.field2_fmt.uniform_size() as int;
        let f3_end = f2_end + self.field3_fmt.uniform_size() as int;
        JournalSnapshot {
            boundary_lsn: self.field1_fmt.parse(data.subrange(0, f1_end)),
            root: if self.field2_fmt.parse(data.subrange(f1_end, f2_end)) is Some {
                Some(JournalRoot{
                    freshest_rec: self.field2_fmt.parse(data.subrange(f1_end, f2_end)).unwrap(),
                    first: self.field3_fmt.parse(data.subrange(f2_end, f3_end)),
                })
            } else {
                None
            },
        }
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    {
        let total_size = self.exec_uniform_size();
        if slice.len() < total_size || data.len() < slice.end {
            proof { assume(!self.parsable(slice@.i(data@))); }
            return None;
        }

        let field1_size = self.field1_fmt.exec_uniform_size();
        let field1_slice = slice.subslice(0, field1_size);
        let boundary_lsn = match self.field1_fmt.try_parse(&field1_slice, data) {
            Some(v) => v,
            None => {
                proof { assume(!self.parsable(slice@.i(data@))); }
                return None;
            },
        };

        let field2_start = field1_size;
        let field2_end = field1_size + self.field2_fmt.exec_uniform_size();
        let field2_slice = slice.subslice(field2_start, field2_end);
        let freshest_rec = match self.field2_fmt.try_parse(&field2_slice, data) {
            Some(v) => v,
            None => {
                proof { assume(!self.parsable(slice@.i(data@))); }
                return None;
            },
        };

        let field3_start = field2_end;
        let field3_end = field2_end + self.field3_fmt.exec_uniform_size();
        let field3_slice = slice.subslice(field3_start, field3_end);
        let first = match self.field3_fmt.try_parse(&field3_slice, data) {
            Some(v) => v,
            None => {
                proof { assume(!self.parsable(slice@.i(data@))); }
                return None;
            },
        };

        let result = IJournalSnapshot{boundary_lsn, freshest_rec, first};
        proof {
            assume(self.parsable(slice@.i(data@)));
            assume(result.parsedv() == self.parse(slice@.i(data@)));
            assume(result.wf());
        }
        Some(result)
    }

    open spec fn marshallable(&self, value: Self::DV) -> bool {
        &&& self.field1_fmt.marshallable(value.boundary_lsn)
        &&& self.field2_fmt.marshallable(value.freshest_rec())
        &&& self.field3_fmt.marshallable(value.first())
    }

    open spec fn impl_marshallable(&self, impl_value: Self::U) -> bool {
        &&& self.field1_fmt.impl_marshallable(impl_value.boundary_lsn)
        &&& self.field2_fmt.impl_marshallable(impl_value.freshest_rec)
        &&& self.field3_fmt.impl_marshallable(impl_value.first)
    }

    open spec fn spec_size(&self, v: Self::DV) -> usize {
        self.uniform_size()
    }

    exec fn exec_size(&self, val: &Self::U) -> (sz: usize) {
        self.exec_uniform_size()
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize) {
        let field1_end = self.field1_fmt.exec_marshall(&value.boundary_lsn, data, start);
        let field2_end = self.field2_fmt.exec_marshall(&value.freshest_rec, data, field1_end);
        let field3_end = self.field3_fmt.exec_marshall(&value.first, data, field2_end);
        proof {
            assume(field3_end == start + self.spec_size(value.parsedv()));
            assume(data.len() == old(data).len());
            assume(forall |i| 0 <= i < start ==> data[i] == old(data)[i]);
            assume(forall |i| field3_end <= i < data.len() ==> data[i] == old(data)[i]);
            assume(self.parsable(data@.subrange(start as int, field3_end as int)));
            assume(self.parse(data@.subrange(start as int, field3_end as int)) == value.parsedv());
        }
        field3_end
    }
}

impl UniformSizedMarshal for IJournalSnapshotFormat {
    proof fn uniform_size_matches_spec_size(self: &Self) {
        assert forall |value: JournalSnapshot| #[trigger] self.spec_size(value) == self.uniform_size() by { }
    }
}

} // verus!
