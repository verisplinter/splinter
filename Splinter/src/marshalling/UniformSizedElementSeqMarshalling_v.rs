// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
// use vstd::bytes::*;
// use vstd::slice::*;
use crate::marshalling::Slice_v::*;
use crate::marshalling::Marshalling_v::*;
use crate::marshalling::IntegerMarshalling_v::*;
use crate::marshalling::math_v::*;
use crate::marshalling::SeqMarshalling_v::*;

verus! {

pub trait UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt: Deepview<DVElt>> {
    spec fn valid(&self) -> bool
        ;

    spec fn uniform_size(&self) -> (sz: usize)
        ;

    proof fn uniform_size_ensures(&self)
    requires self.valid(),
    ensures 0 < self.uniform_size()
    ;

    exec fn exec_uniform_size(&self) -> (sz: usize)
    requires self.valid(),
    ensures sz == self.uniform_size()
    ;

    type EltMarshalling : Marshalling<DVElt, Elt>;

    spec fn spec_elt_marshalling(&self) -> Self::EltMarshalling
        ;

    // PLEASE PLEASE CAN I HAVE SPEC ENSURES
    proof fn spec_elt_marshalling_ensures(&self)
    requires self.valid()
    ensures self.spec_elt_marshalling().valid()
    ;

    exec fn exec_elt_marshalling(&self) -> (eltm: &Self::EltMarshalling)
    requires self.valid()
    ensures eltm.valid(),
        eltm == self.spec_elt_marshalling()
        ;
}

pub struct IntegerSeqMarshallingOblinfo<Elt: Deepview<int> + builtin::Integer, IO: IntObligations<Elt>> {
    pub int_marshalling: IO,
    _p: std::marker::PhantomData<(Elt,)>,
}

impl<Elt: Deepview<int> + builtin::Integer + Copy, IO: IntObligations<Elt>>
    UniformSizedElementSeqMarshallingOblinfo<int, Elt>
    for IntegerSeqMarshallingOblinfo<Elt, IO>
{
    open spec fn valid(&self) -> bool
    {
        self.int_marshalling.valid()
    }

    open spec fn uniform_size(&self) -> (sz: usize)
    {
        IO::o_spec_size()
    }

    proof fn uniform_size_ensures(&self) {
        IO::o_spec_size_ensures()
    }

    exec fn exec_uniform_size(&self) -> (sz: usize)
    {
        IO::o_exec_size()
    }

    type EltMarshalling = IO;

    open spec fn spec_elt_marshalling(&self) -> Self::EltMarshalling
    {
        self.int_marshalling
    }

    // PLEASE PLEASE CAN I HAVE SPEC ENSURES
    proof fn spec_elt_marshalling_ensures(&self)
    {
    }

    exec fn exec_elt_marshalling(&self) -> (eltm: &Self::EltMarshalling)
    {
        &self.int_marshalling
    }
}

pub struct UniformSizedElementSeqMarshalling<DVElt, Elt: Deepview<DVElt>, O: UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>> {
    pub oblinfo: O,
    _p: std::marker::PhantomData<(DVElt,Elt,)>,
}

impl <DVElt, Elt: Deepview<DVElt>, O: UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>> UniformSizedElementSeqMarshalling<DVElt, Elt, O> {
    spec fn slice_length(&self, dslice: Slice) -> int
    recommends self.valid(), dslice.wf(),
    {
        dslice.spec_len() / (self.oblinfo.uniform_size() as int)
    }

    proof fn length_ensures(&self, data: Seq<u8>)
    requires
        self.valid(),
        data.len() < usize::MAX,
    ensures (
        self.slice_length(Slice::all(data))
        == self.length(data)
        <= self.length(data) * (self.oblinfo.uniform_size() as int)
        <= data.len()
        )
    {
        self.oblinfo.uniform_size_ensures();
        div_mul_order(data.len() as int, self.oblinfo.uniform_size() as int);
        mul_le(self.length(data), self.oblinfo.uniform_size() as int);
    }

    proof fn index_bounds_facts(&self, slice: Slice, idx: int)
    requires self.valid(), slice.wf(), 0 <= idx, idx < slice.spec_len() / (self.oblinfo.uniform_size() as int)
    ensures
        0
            <= idx * (self.oblinfo.uniform_size() as int)
            < idx * (self.oblinfo.uniform_size() as int) + (self.oblinfo.uniform_size() as int)
            == (idx+1) * (self.oblinfo.uniform_size() as int)
            <= slice.spec_len()
    {
        self.oblinfo.uniform_size_ensures();   // TODO(verus): lament of the spec ensures
        nat_mul_nat_is_nat(idx, self.oblinfo.uniform_size() as int);
        pos_mul_preserves_order(idx, idx+1, self.oblinfo.uniform_size() as int);
        distribute_left(idx, 1, self.oblinfo.uniform_size() as int);
        div_mul_order(slice.spec_len(), self.oblinfo.uniform_size() as int);
        if idx + 1 < self.slice_length(slice) {
            pos_mul_preserves_order(idx + 1, self.slice_length(slice), self.oblinfo.uniform_size() as int);
        }
    }
}

impl<DVElt, Elt: Deepview<DVElt>, O: UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>>
    SeqMarshalling<DVElt, Elt>
    for UniformSizedElementSeqMarshalling<DVElt, Elt, O>
{
    open spec fn seq_valid(&self) -> bool { self.oblinfo.valid() }

    open spec fn lengthable(&self, data: Seq<u8>) -> bool { true }

    open spec fn length(&self, data: Seq<u8>) -> int
    {
        (data.len() as int) / (self.oblinfo.uniform_size() as int)
    }

    exec fn try_length(&self, dslice: &Slice, data: &Vec<u8>) -> (out: Option<usize>)
    {
        proof { self.oblinfo.uniform_size_ensures() }
        Some(dslice.exec_len() / self.oblinfo.exec_uniform_size())
    }

    exec fn exec_lengthable(&self, dslice: &Slice, data: &Vec<u8>) -> (l: bool) { true }

    exec fn exec_length(&self, dslice: &Slice, data: &Vec<u8>) -> (len: usize)
    {
        proof { self.oblinfo.uniform_size_ensures() }   // 0 < denom
        dslice.exec_len() / self.oblinfo.exec_uniform_size()
    }

    /////////////////////////////////////////////////////////////////////////
    // getting individual elements
    /////////////////////////////////////////////////////////////////////////

    open spec fn gettable(&self, data: Seq<u8>, idx: int) -> bool
    {
        0 <= idx < self.length(data)
    }

    open spec fn get(&self, dslice: Slice, data: Seq<u8>, idx: int) -> (eslice: Slice)
    {
        dslice.spec_sub(
            ((idx as usize) * self.oblinfo.uniform_size()) as usize,
            ((idx as usize) * self.oblinfo.uniform_size() + self.oblinfo.uniform_size()) as usize
        )
    }

    proof fn get_ensures(&self, dslice: Slice, data: Seq<u8>, idx: int)
    {
        self.index_bounds_facts(dslice, idx as int);
        assert( self.get(dslice, data, idx).valid(data) );
    }

    open spec fn get_data(&self, data: Seq<u8>, idx: int) -> (edata: Seq<u8>)
    // TODO factor out this common impl
    {
        self.get(Slice::all(data), data, idx).i(data)
    }

    open spec fn elt_parsable(&self, data: Seq<u8>, idx: int) -> bool
    // TODO factor out this common impl
    {
        self.oblinfo.spec_elt_marshalling().parsable(self.get_data(data, idx))
    }

    open spec fn get_elt(&self, data: Seq<u8>, idx: int) -> (elt: DVElt)
    // TODO factor out this common impl
    {
        self.oblinfo.spec_elt_marshalling().parse(self.get_data(data, idx))
    }

    exec fn try_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oeslice: Option<Slice>)
    {
        let len = self.exec_length(dslice, data);
        if idx < len {
            proof { self.index_bounds_facts(*dslice, idx as int); }
            Some( dslice.exec_sub(
                    (idx as usize) * self.oblinfo.exec_uniform_size(),
                    (idx as usize) * self.oblinfo.exec_uniform_size() + self.oblinfo.exec_uniform_size()) )
        } else {
            None
        }
    }

    exec fn exec_gettable(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (g: bool)
    {
        let len = self.exec_length(dslice, data);
        idx < len
    }

    exec fn exec_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (eslice: Slice)
    {
        proof { self.index_bounds_facts(*dslice, idx as int); }
        dslice.exec_sub(
            (idx as usize) * self.oblinfo.exec_uniform_size(),
            (idx as usize) * self.oblinfo.exec_uniform_size() + self.oblinfo.exec_uniform_size())
    }

    exec fn try_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oelt: Option<Elt>)
    // TODO factor out this common impl
    {
        proof { self.oblinfo.spec_elt_marshalling_ensures() };  // :v(

        let oeslice = self.try_get(dslice, data, idx);
        match oeslice {
            None => None,
            Some(eslice) => {
                proof {
                    self.get_ensures(*dslice, data@, idx as int);   // TODO(verus): lament of spec ensures
                    self.index_bounds_facts(*dslice, idx as int);
                    let edslice = self.get(Slice::all(dslice.i(data@)), dslice.i(data@), idx as int);
                    assert( edslice.i(dslice.i(data@)) == eslice.i(data@));   // trigger
                }
                let oelt = self.oblinfo.exec_elt_marshalling().try_parse(&eslice, data);
                oelt
            }
        }
    }

    exec fn exec_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (elt: Elt)
    // TODO factor out this common impl
    {
        let eslice = self.exec_get(dslice, data, idx);
        proof { // duplicated from try_get_elt
            self.get_ensures(*dslice, data@, idx as int);   // TODO(verus): lament of spec ensures
            self.index_bounds_facts(*dslice, idx as int);
            let edslice = self.get(Slice::all(dslice.i(data@)), dslice.i(data@), idx as int);
            assert( edslice.i(dslice.i(data@)) == eslice.i(data@));   // trigger
        }
        self.oblinfo.exec_elt_marshalling().exec_parse(&eslice, data)
    }

    /////////////////////////////////////////////////////////////////////////
    // setting individual elements
    /////////////////////////////////////////////////////////////////////////

    open spec fn elt_marshallable(&self, elt: DVElt) -> bool
    {
        self.oblinfo.spec_elt_marshalling().marshallable(elt)
    }

    open spec fn settable(&self, data: Seq<u8>, idx: int, value: DVElt) -> bool
    {
        &&& 0 <= idx < self.length(data)
        &&& self.elt_marshallable(value)
        &&& self.oblinfo.spec_elt_marshalling().spec_size(value) == self.oblinfo.uniform_size()
    }

    open spec fn preserves_entry(&self, data: Seq<u8>, idx: int, new_data: Seq<u8>) -> bool
    {
        &&& self.gettable(data, idx) ==> self.gettable(new_data, idx)
        &&& (self.gettable(data, idx) && self.elt_parsable(new_data, idx)) ==> {
            &&& self.elt_parsable(new_data, idx)
            &&& self.get_elt(new_data, idx) == self.get_elt(new_data, idx)
            }
    }

    open spec fn sets(&self, data: Seq<u8>, idx: int, value: DVElt, new_data: Seq<u8>) -> bool
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
    {
        let len = self.exec_length(dslice, data);
        let sz = self.oblinfo.exec_elt_marshalling().exec_size(value);
        idx < len && sz == self.oblinfo.exec_uniform_size()
    }

    exec fn exec_set(&self, dslice: &Slice, data: &mut Vec<u8>, idx: usize, value: &Elt)
    {
        proof {
            self.index_bounds_facts(*dslice, idx as int);
            self.oblinfo.uniform_size_ensures();
        }
        let newend = self.oblinfo.exec_elt_marshalling().exec_marshall(value, data, dslice.start + idx * self.oblinfo.exec_uniform_size());
        assert forall |i: int| i != idx as int && self.gettable(dslice.i(old(data)@), i)
            implies self.get_data(dslice.i(data@), i) == self.get_data(dslice.i(old(data)@), i) by
        {
            self.index_bounds_facts(*dslice, i);

            lemma_seq_slice_slice(data@,
                dslice.start as int,
                dslice.end as int,
                i * self.oblinfo.uniform_size() as int,
                i * self.oblinfo.uniform_size() as int + self.oblinfo.uniform_size() as int);
            lemma_seq_slice_slice(old(data)@,
                dslice.start as int,
                dslice.end as int,
                i * self.oblinfo.uniform_size() as int,
                i * self.oblinfo.uniform_size() as int + self.oblinfo.uniform_size() as int);

            if i < idx as int {
                mul_preserves_le(i + 1, idx as int, self.oblinfo.uniform_size() as int);
            } else {
                mul_preserves_le(idx as int + 1, i, self.oblinfo.uniform_size() as int);
            }

            // TODO(verus): shouldn't assert-by conclusion give us this trigger for free?
            assert( self.get_data(dslice.i(data@), i) == self.get_data(dslice.i(old(data)@), i) );
        }

        proof {
            lemma_seq_slice_slice(
                data@,
                dslice.start as int,
                dslice.end as int,
                idx as int * self.oblinfo.uniform_size() as int,
                idx as int * self.oblinfo.uniform_size() as int + self.oblinfo.uniform_size() as int);
        }
    }

    /////////////////////////////////////////////////////////////////////////
    // resizing
    /////////////////////////////////////////////////////////////////////////

    open spec fn resizable(&self, data: Seq<u8>, newlen: int) -> bool { false }

    open spec fn resizes(&self, data: Seq<u8>, newlen: int, newdata: Seq<u8>) -> bool { false }

    exec fn exec_resizable(&self, dslice: &Slice, data: &Vec<u8>, newlen: usize) -> (r: bool) { false }

    exec fn resize(&self, dslice: &Slice, data: &mut Vec<u8>, newlen: usize) { }

    /////////////////////////////////////////////////////////////////////////
    // append
    /////////////////////////////////////////////////////////////////////////

    open spec fn well_formed(&self, data: Seq<u8>) -> bool { false }

    proof fn well_formed_ensures(&self, data: Seq<u8>) {}

    open spec fn appendable(&self, data: Seq<u8>, value: DVElt) -> bool { false }

    open spec fn appends(&self, data: Seq<u8>, value: DVElt, newdata: Seq<u8>) -> bool { false }


    exec fn exec_well_formed(&self, dslice: &Slice, data: &Vec<u8>) -> (w: bool) { false }

    exec fn exec_appendable(&self, dslice: &Slice, data: &Vec<u8>, value: Elt) -> (r: bool) { false }

    exec fn exec_append(&self, dslice: &Slice, data: &mut Vec<u8>, value: Elt) {}

//     /////////////////////////////////////////////////////////////////////////
//     // marshall
//     /////////////////////////////////////////////////////////////////////////
// 
//     open spec fn marshallable(&self, value: Seq<DVElt>) -> bool { false }
// 
//     open spec fn spec_size(&self, value: Seq<DVElt>) -> usize { 0 }
// 
//     exec fn exec_size(&self, value: &Vec<Elt>) -> (sz: usize) { 0 }
// 
//     exec fn exec_marshall(&self, value: &Vec<Elt>, data: &mut Vec<u8>, start: usize) -> (end: usize)
//     {
//         0
//     }
// 
//         // TODO(jonh) [performance]: In Dafny this is a cast operation. We should do this with an
//         // untrusted cast axiom in Rust, I guess.
//         // For now, rely on Marshalling default trait method impl
//     exec fn seq_exec_parse(&self, dslice: &Slice, data: &Vec<u8>) -> (value: Vec<Elt>)
}

impl<DVElt, Elt: Deepview<DVElt>, O: UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>>
    UniformSizedElementSeqMarshalling<DVElt, Elt, O>
{
    pub open spec fn seq_parsable(&self, data: Seq<u8>) -> bool
    {
        &&& self.seq_valid()
        &&& self.lengthable(data)
        &&& self.length(data) <= usize::MAX
        &&& self.parsable_to_len(data, self.length(data) as usize)
    }

    pub open spec fn seq_parse(&self, data: Seq<u8>) -> Seq<DVElt>
    {
        self.parse_to_len(data, self.length(data) as usize)
    }
}

impl<DVElt, Elt: Deepview<DVElt>, O: UniformSizedElementSeqMarshallingOblinfo<DVElt, Elt>>
    Marshalling<Seq<DVElt>, Vec<Elt>>
    for UniformSizedElementSeqMarshalling<DVElt, Elt, O>
{
    open spec fn valid(&self) -> bool { self.seq_valid() }

    exec fn exec_parsable(&self, dslice: &Slice, data: &Vec<u8>) -> (p: bool)
    {
        // TODO factor this into Marshalling trait default method
        let ovalue = self.try_parse(dslice, data);
        ovalue.is_some()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        self.seq_parsable(data)
    }

    open spec fn parse(&self, data: Seq<u8>) -> Seq<DVElt>
    {
        self.seq_parse(data)
    }

    exec fn try_parse(&self, dslice: &Slice, data: &Vec<u8>) -> (ovalue: Option<Vec<Elt>>)
    {
        match self.try_length(dslice, data) {
            None => {
                proof {
                    let ghost idata = dslice.i(data@);
                    assert( !self.lengthable(idata) );
                }
                assert( !self.seq_parsable(dslice.i(data@)) );
                assert( !self.parsable(dslice.i(data@)) );
                return None;
            },
            Some(len) => {
                assert( len as int == self.length(dslice.i(data@)) );
                assert( len <= usize::MAX );
                let mut i: usize = 0;
                let mut result:Vec<Elt> = Vec::with_capacity(len);
                while i < len
                    invariant i <= len,
                    self.valid(),   // TODO(verus #984): waste of my debugging time
                    dslice.valid(data@),   // TODO(verus #984): waste of my debugging time
                    len as int == self.length(dslice.i(data@)), // TODO(verus #984): waste of my debugging time
                        result.len() == i,
                        forall |j| 0<=j<i as nat ==> self.gettable(dslice.i(data@), j),
                        forall |j| 0<=j<i as nat ==> self.elt_parsable(dslice.i(data@), j),
                        forall |j| #![auto] 0<=j<i as nat ==> result[j].deepv() == self.get_elt(dslice.i(data@), j),
                {
                    let ghost idata = dslice.i(data@);
                    let oelt = self.try_get_elt(dslice, data, i);

                    assert(
                        oelt is Some <==> {
                                &&& self.gettable(dslice.i(data@), i as int)
                                &&& self.elt_parsable(dslice.i(data@), i as int)
                        } );
 
                    if oelt.is_none() {
                        proof {
                            assert(!{
                                &&& self.gettable(dslice.i(data@), i as int)
                                &&& self.elt_parsable(dslice.i(data@), i as int)
                            });
    //                         if ({
    //                             &&& self.gettable_to_len(dslice.i(data@), i as int)
    //                             &&& self.elt_parsable_to_len(dslice.i(data@), i as int)
    //                         }) {
    //                             assert( oelt is Some );
    //                         }
    //                         if ({
    //                             &&& self.gettable_to_len(idata, i as int)
    //                             &&& self.elt_parsable_to_len(idata, i as int)
    //                         }) {
    //                             assert( oelt is Some );
    //                         }

                            assert( self.seq_valid() );
                            assert( self.lengthable(idata) );
    //                         assert( len == self.length(dslice.i(data@)) as usize );
    //                         assert( len == self.length(dslice.i(data@)) );
    //                         //assert( self.length(idata) == len );
    //                         assert( idata == dslice.i(data@) );
                            assert( self.length(idata) <= usize::MAX );

                            assert( idata == dslice.i(data@) );

                            if !self.gettable(idata, i as int) {
                                assert( !self.gettable_to_len(idata, i as int) );
                                assert( !self.parsable_to_len(idata, self.length(idata) as usize) );
                            } else {
                                assert( !self.elt_parsable(idata, i as int) );
                                assert( 0 <= (i as int) < (len as int) );
                                assert( self.elt_parsable_to_len(idata, len as int) ==
                                        (forall |i: int| 0<=i<len as int ==> self.elt_parsable(idata, i)) );
                                assert( !self.elt_parsable_to_len(idata, len as int) );
                                assert( !self.parsable_to_len(idata, len) );
                                assert( !self.parsable_to_len(idata, self.length(idata) as usize) );
                            }
                            assert(!{
                                &&& self.gettable_to_len(idata, i as int)
                                &&& self.elt_parsable_to_len(idata, i as int)
                            });
                            assert( !self.parsable_to_len(idata, self.length(idata) as usize) );
                        }

                        assert( !self.seq_parsable(dslice.i(data@)) );
                        assert( !self.parsable(dslice.i(data@)) );
                        return None;
                    }
                    result.push(oelt.unwrap());
                    i += 1;
                }
                // Looks like this wants extensionality, but no ~! Not sure why it's needed.
                // Oh maybe it's the trait-ensures-don't-trigger bug?
                assert( result.deepv() == self.parse(dslice.i(data@)) );    // trigger.
                return Some(result);
            }
        }
    }

    // dummy placeholders; I guess we need to implement this yet
    open spec fn marshallable(&self, value: Seq<DVElt>) -> bool
    {
        false
    }

    open spec fn spec_size(&self, value: Seq<DVElt>) -> usize
    {
        0
    }

    exec fn exec_size(&self, value: &Vec<Elt>) -> (sz: usize)
    {
        0
    }

    exec fn exec_marshall(&self, value: &Vec<Elt>, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        start
    }
}

// Convince myself that IntegerSeqMarshalling is indeed SeqMarshalling<T, int>
fn test_is_seq_marshalling<SM: SeqMarshalling<int, u64>>(sm: &SM) { }
fn test_is_marshalling<M: Marshalling<Seq<int>, Vec<u64>>>(m: &M) { }

type IntegerSeqMarshalling<IT> = UniformSizedElementSeqMarshalling<int, IT, IntegerSeqMarshallingOblinfo<IT, IntMarshalling<IT>>>;

fn test(t: IntegerSeqMarshalling<u64>, data: &Vec<u8>) {
    let dslice = Slice::exec_all(data);
    test_is_seq_marshalling(&t);
    test_is_marshalling(&t);
    let oelt = t.try_get_elt(&dslice, data, 0);
}

}
