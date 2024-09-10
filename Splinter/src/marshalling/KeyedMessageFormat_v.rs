// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use vstd::bytes::*;
use vstd::slice::*;
use crate::marshalling::Slice_v::*;
use crate::marshalling::Marshalling_v::*;
use crate::marshalling::IntegerMarshalling_v::*;
use crate::marshalling::StaticallySized_v::*;
use crate::marshalling::UniformSized_v::*;
use crate::marshalling::UniformSizedSeq_v::*;
use crate::marshalling::SeqMarshalling_v::*;
use crate::marshalling::VariableSizedElementSeq_v::*;

verus! {

pub struct SpecKVPair {
    key: Seq<u8>,
    value: Seq<u8>,
}

pub struct KVPair {
    key: Vec<u8>,
    value: Vec<u8>,
}

impl Deepview<SpecKVPair> for KVPair {
    open spec fn deepv(&self) -> SpecKVPair
    {
        SpecKVPair{key: self.key@, value: self.value@}
    }
}

pub struct KVPairSeqFormat {
    vfmt: VariableSizedElementSeqFormat<UniformSizedElementSeqFormat<IntFormat<u8>>, u32, u32>,
}

impl SeqMarshal<SpecKVPair, KVPair>
    for KVPairSeqFormat
{
    spec fn seq_valid(&self) -> bool
    {
        self.vfmt.seq_valid()
    }

    spec fn lengthable(&self, data: Seq<u8>) -> bool
    {
        &&& self.vfmt.lengthable(data)
    }

    spec fn length(&self, data: Seq<u8>) -> int
    {
        self.vfmt.length(data) / 2
    }

    exec fn try_length(&self, dslice: &Slice, data: &Vec<u8>) -> (out: Option<usize>)
    {
        match self.vfmt.length(dslice, data) {
            case Some(len) => len / 2,
            case None => None,
        }
    }

    spec fn gettable(&self, data: Seq<u8>, idx: int) -> bool
    {
        &&& self.vfmt.gettable(data, idx*2)
        &&& self.vfmt.gettable(data, idx*2 + 1)
    }

    spec fn get(&self, dslice: SpecSlice, data: Seq<u8>, idx: int) -> (eslice: SpecSlice)
    {
        // I don't really want to return a slice! hrmm.
        TODO
    }

    proof fn get_ensures(&self, dslice: SpecSlice, data: Seq<u8>, idx: int)
    requires
        self.seq_valid(),
        dslice.valid(data),
        self.gettable(dslice.i(data), idx),
    ensures
        self.get(dslice, data, idx).valid(data)
    {
        // TODO
    }

    // I can't make these two implementations (elt_parsable, get_elt) default without having a way
    // to "dispatch" to the element marshaller, which would require knowing the element marshaller
    // type here in this trait. That's more than I want to encode, so I'll settle for a little
    // duplication in the implementations for now.
    spec fn elt_parsable(&self, data: Seq<u8>, idx: int) -> bool
    {
        &&& self.vfmt.elt_parsable(data, idx*2)
        &&& self.vfmt.elt_parsable(data, idx*2 + 1)
    }

    spec fn get_elt(&self, data: Seq<u8>, idx: int) -> (elt: DVElt)
    recommends
        self.seq_valid(),
        self.gettable(data, idx),
        self.elt_parsable(data, idx)
    {
        let key = self.vfmt.get_elt(data, idx*2);
        let value = self.vfmt.get_elt(data, idx*2 + 1);
        KVPair{key, value}
    }

    exec fn try_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oeslice: Option<Slice>)
    {
        TODO
    }

    exec fn exec_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (eslice: Slice)
    {
        let key = self.vfmt.get_elt(data, idx*2);
        let value = self.vfmt.get_elt(data, idx*2 + 1);
        KVPair{key, value}
    }

    exec fn try_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oelt: Option<Elt>)
    requires
        self.seq_valid(),
        dslice@.valid(data@),
    ensures
        oelt is Some <==> {
                &&& self.gettable(dslice@.i(data@), idx as int)
                &&& self.elt_parsable(dslice@.i(data@), idx as int)
        },
        oelt is Some ==> oelt.unwrap().deepv() == self.get_elt(dslice@.i(data@), idx as int)
    // TODO the implementations of this method could be factored out into a default method here
    // if we had a way of talking about eltm and its type in this trait.
    ;

    exec fn exec_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (elt: Elt)
    requires
        self.seq_valid(),
        self.gettable(dslice@.i(data@), idx as int),
        self.elt_parsable(dslice@.i(data@), idx as int),
        dslice@.valid(data@),
    ensures
        elt.deepv() == self.get_elt(dslice@.i(data@), idx as int)
    // TODO the implementations of this method could be factored out into a default method here
    // if we had a way of talking about eltm and its type in this trait.
    ;

    /////////////////////////////////////////////////////////////////////////
    // setting individual elements
    /////////////////////////////////////////////////////////////////////////
    // TODO: make this a separate trait, since not all seq formatters support it.
    spec fn elt_marshallable(&self, elt: DVElt) -> bool
        ;

    spec fn settable(&self, data: Seq<u8>, idx: int, value: DVElt) -> bool
    recommends
        self.seq_valid(),
        self.elt_marshallable(value)
    ;

    open spec fn preserves_entry(&self, data: Seq<u8>, idx: int, new_data: Seq<u8>) -> bool
    recommends
        self.seq_valid()
    {
        &&& (self.gettable(data, idx) ==> self.gettable(new_data, idx))
        &&& (self.gettable(data, idx) && self.elt_parsable(data, idx)) ==> {
            &&& self.elt_parsable(new_data, idx)
            &&& self.get_elt(new_data, idx) == self.get_elt(data, idx)
            }
    }

    // proof fn preserves_entry_transitive

    open spec fn sets(&self, data: Seq<u8>, idx: int, value: DVElt, new_data: Seq<u8>) -> bool
    recommends
        self.seq_valid(),
        self.elt_marshallable(value),
        self.settable(data, idx, value)
    {
        &&& new_data.len() == data.len()
        &&& self.lengthable(data) ==> {
            &&& self.lengthable(new_data)
            &&& self.length(new_data) == self.length(data)
            }
        &&& forall |i| i!=idx ==> self.preserves_entry(data, i, new_data)
        &&& self.gettable(new_data, idx)
        &&& self.elt_parsable(new_data, idx)
        &&& self.get_elt(new_data, idx) == value
    }

    exec fn exec_settable(&self, dslice: &Slice, data: &Vec<u8>, idx: usize, value: &Elt) -> (s: bool)
    requires
        self.seq_valid(),
        dslice@.valid(data@),
        self.elt_marshallable(value.deepv()),
    ensures
        s == self.settable(dslice@.i(data@), idx as int, value.deepv())
    ;

    exec fn exec_set(&self, dslice: &Slice, data: &mut Vec<u8>, idx: usize, value: &Elt)
    requires
        self.seq_valid(),
        dslice@.valid(old(data)@),
        self.elt_marshallable(value.deepv()),
        self.settable(dslice@.i(old(data)@), idx as int, value.deepv()),
    ensures
        dslice@.agree_beyond_slice(old(data)@, data@),
        self.sets(dslice@.i(old(data)@), idx as int, value.deepv(), dslice@.i(data@)),
    ;


    /////////////////////////////////////////////////////////////////////////
    // resizing
    /////////////////////////////////////////////////////////////////////////

    spec fn resizable(&self, data: Seq<u8>, newlen: int) -> bool
        recommends self.seq_valid()
        ;

    open spec fn resizes(&self, data: Seq<u8>, newlen: int, new_data: Seq<u8>) -> bool
        recommends self.seq_valid(), self.resizable(data, newlen)
    {
        &&& new_data.len() == data.len()
        &&& self.lengthable(new_data)
        &&& self.length(new_data) == newlen
        &&& forall |i| self.preserves_entry(data, i, new_data)
    }

    exec fn exec_resizable(&self, dslice: &Slice, data: &Vec<u8>, newlen: usize) -> (r: bool)
        requires self.seq_valid(), dslice@.valid(data@),
        ensures r == self.resizable(dslice@.i(data@), newlen as int)
        ;

    exec fn resize(&self, dslice: &Slice, data: &mut Vec<u8>, newlen: usize)
        requires self.seq_valid(), dslice@.valid(old(data)@), self.resizable(dslice@.i(old(data)@), newlen as int)
        ensures data@.len() == old(data)@.len(),
            dslice@.agree_beyond_slice(old(data)@, data@),
            self.resizes(dslice@.i(old(data)@), newlen as int, dslice@.i(data@)),
    ;

    /////////////////////////////////////////////////////////////////////////
    // append
    /////////////////////////////////////////////////////////////////////////
    spec fn well_formed(&self, data: Seq<u8>) -> bool
        recommends self.seq_valid()
        ;

    proof fn well_formed_ensures(&self, data: Seq<u8>)
        requires self.seq_valid()
        ensures self.well_formed(data) ==> self.lengthable(data)
        ;

    spec fn appendable(&self, data: Seq<u8>, value: DVElt) -> bool
        recommends self.seq_valid(), self.well_formed(data), self.elt_marshallable(value)
        ;

    open spec fn appends(&self, data: Seq<u8>, value: DVElt, newdata: Seq<u8>) -> bool
    recommends
        self.seq_valid(),
        self.well_formed(data),
        self.elt_marshallable(value),
        self.appendable(data, value)
    {
        let oldlen = self.length(data);
        &&& newdata.len() == data.len()
        &&& self.length(newdata) == oldlen + 1

        // TODO: Dafny original didn't particularly bound i because preserves_entry's body has
        // *able(i) on the LHS of all implications. Kinda mysteriously magical, tho. Not a fan.
        &&& forall |i| i != oldlen ==> self.preserves_entry(data, i, newdata)

        &&& self.gettable(newdata, oldlen)
        &&& self.elt_parsable(newdata, oldlen)
        &&& self.get_elt(newdata, oldlen) == value
        &&& self.well_formed(newdata)
    }

    exec fn exec_well_formed(&self, dslice: &Slice, data: &Vec<u8>) -> (w: bool)
    requires
        self.seq_valid(),
        dslice@.valid(data@),
    ensures
            w == self.well_formed(dslice@.i(data@))
        ;

    exec fn exec_appendable(&self, dslice: &Slice, data: &Vec<u8>, value: &Elt) -> (r: bool)
    requires
        self.seq_valid(),
        dslice@.valid(data@),
        self.well_formed(dslice@.i(data@)),
        self.elt_marshallable(value.deepv()),
    ensures
        r == self.appendable(dslice@.i(data@), value.deepv())
    ;

    exec fn exec_append(&self, dslice: &Slice, data: &mut Vec<u8>, value: &Elt)
    requires
        self.seq_valid(),
        dslice@.valid(old(data)@),
        self.well_formed(dslice@.i(old(data)@)),
        self.elt_marshallable(value.deepv()),
        self.appendable(dslice@.i(old(data)@), value.deepv()),
    ensures
        data@.len() == old(data)@.len(),
        dslice@.agree_beyond_slice(old(data)@, data@),
        self.appends(dslice@.i(old(data)@), value.deepv(), dslice@.i(data@))
    ;

    /////////////////////////////////////////////////////////////////////////
    // parse (entire sequence)
    /////////////////////////////////////////////////////////////////////////
    open spec fn gettable_to_len(&self, data: Seq<u8>, len: int) -> bool
    recommends self.seq_valid()
    {
        forall |i: int| 0<=i && i<len ==> self.gettable(data, i)
    }

    open spec fn elt_parsable_to_len(&self, data: Seq<u8>, len: int) -> bool
    recommends self.seq_valid(), self.gettable_to_len(data, len)
    {
        forall |i: int| 0<=i && i<len ==> self.elt_parsable(data, i)
    }

    // TODO(robj): why switch to usize in spec land here?
    open spec fn parsable_to_len(&self, data: Seq<u8>, len: usize) -> bool
    recommends self.seq_valid()
    {
        &&& self.gettable_to_len(data, len as int)
        &&& self.elt_parsable_to_len(data, len as int)
    }

    open spec fn parse_to_len(&self, data: Seq<u8>, len: usize) -> Seq<DVElt>
    recommends self.seq_valid(), self.parsable_to_len(data, len)
    {
        Seq::new(len as nat, |i: int| self.get_elt(data, i))
    }
}

impl Marshal
    for KVPairSeqFormat
{   
    type DV = Seq<SpecKVPair>;
    type U = Vec<KVPair>;
}


}
