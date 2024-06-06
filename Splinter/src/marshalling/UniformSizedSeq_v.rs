// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
// use vstd::bytes::*;
// use vstd::slice::*;
use crate::marshalling::Slice_v::*;
use crate::marshalling::Marshalling_v::*;
use crate::marshalling::SeqMarshalling_v::*;
use crate::marshalling::UniformSized_v::*;
use crate::marshalling::math_v::*;

verus! {

pub struct UniformSizedElementSeqFormat<EltFormat: Marshal + UniformSized> {
    pub eltf: EltFormat,
}

impl<EltFormat: Marshal + UniformSized> UniformSizedElementSeqFormat<EltFormat>
{
    // TODO(verus): modify Verus to allow constructing default phantomdata fields
    #[verifier(external_body)]
    pub fn new(eltf: EltFormat) -> (s: Self)
    requires eltf.valid()
    ensures s.seq_valid()
    {
        Self{ eltf }
    }

    spec fn slice_length(&self, dslice: SpecSlice) -> int
    recommends self.valid(), dslice.wf(),
    {
        dslice.len() / (self.eltf.uniform_size() as int)
    }

    proof fn index_bounds_facts(&self, slice: SpecSlice, idx: int)
    requires self.valid(), slice.wf(), 0 <= idx, idx < slice.len() / (self.eltf.uniform_size() as int)
    ensures
        0
            <= idx * (self.eltf.uniform_size() as int)
            < idx * (self.eltf.uniform_size() as int) + (self.eltf.uniform_size() as int)
            == (idx+1) * (self.eltf.uniform_size() as int)
            <= slice.len()
    {
        self.eltf.uniform_size_ensures();   // TODO(verus): lament of the spec ensures
        nat_mul_nat_is_nat(idx, self.eltf.uniform_size() as int);
        pos_mul_preserves_order(idx, idx+1, self.eltf.uniform_size() as int);
        distribute_left(idx, 1, self.eltf.uniform_size() as int);
        div_mul_order(slice.len(), self.eltf.uniform_size() as int);
        if idx + 1 < self.slice_length(slice) {
            pos_mul_preserves_order(idx + 1, self.slice_length(slice), self.eltf.uniform_size() as int);
        }
    }
}

impl<EltFormat: Marshal + UniformSized>
    SeqMarshal< EltFormat::DV, EltFormat::U >
    for UniformSizedElementSeqFormat<EltFormat>
{
    open spec fn seq_valid(&self) -> bool {
        &&& self.eltf.valid()
    }

    open spec fn lengthable(&self, dslice: SpecSlice, data: Seq<u8>) -> bool { true }

    open spec fn length(&self, dslice: SpecSlice, data: Seq<u8>) -> int
    {
        (dslice.len() as int) / (self.eltf.uniform_size() as int)
    }

    exec fn try_length(&self, dslice: &Slice, data: &Vec<u8>) -> (out: Option<usize>)
    {
        proof { self.eltf.uniform_size_ensures() }
        Some(dslice.len() / self.eltf.exec_uniform_size())
    }

    exec fn exec_lengthable(&self, dslice: &Slice, data: &Vec<u8>) -> (l: bool) { true }

    exec fn exec_length(&self, dslice: &Slice, data: &Vec<u8>) -> (len: usize)
    {
        proof { self.eltf.uniform_size_ensures() }   // 0 < denom
        dslice.len() / self.eltf.exec_uniform_size()
    }

    /////////////////////////////////////////////////////////////////////////
    // getting individual elements
    /////////////////////////////////////////////////////////////////////////

    open spec fn gettable(&self, dslice: SpecSlice, data: Seq<u8>, idx: int) -> bool
    {
        0 <= idx < self.length(dslice, data)
    }

    open spec fn get(&self, dslice: SpecSlice, data: Seq<u8>, idx: int) -> (eslice: SpecSlice)
    {
        dslice.subslice(
            idx * self.eltf.uniform_size(),
            idx * self.eltf.uniform_size() + self.eltf.uniform_size())
    }

    proof fn get_ensures(&self, dslice: SpecSlice, data: Seq<u8>, idx: int)
    {
        self.index_bounds_facts(dslice, idx as int);
        assert( self.get(dslice, data, idx).valid(data) );
    }

    open spec fn elt_parsable(&self, dslice: SpecSlice, data: Seq<u8>, idx: int) -> bool
    {
        self.eltf.parsable(self.get(dslice, data, idx), data)
    }

    open spec fn get_elt(&self, dslice: SpecSlice, data: Seq<u8>, idx: int) -> (elt: EltFormat::DV)
    {
        self.eltf.parse(self.get(dslice, data, idx), data)
    }

    exec fn try_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oeslice: Option<Slice>)
    {
        let len = self.exec_length(dslice, data);
        if idx < len {
            proof {
                self.index_bounds_facts(dslice@, idx as int);
            }
            Some( dslice.subslice(
                    (idx as usize) * self.eltf.exec_uniform_size(),
                    (idx as usize) * self.eltf.exec_uniform_size() + self.eltf.exec_uniform_size()) )
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
        proof { self.index_bounds_facts(dslice@, idx as int); }
        dslice.subslice(
            (idx as usize) * self.eltf.exec_uniform_size(),
            (idx as usize) * self.eltf.exec_uniform_size() + self.eltf.exec_uniform_size())
    }

    exec fn try_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oelt: Option<EltFormat::U>)
    // TODO factor out this common impl
    {
        //proof { self.eltf.spec_elt_marshalling_ensures() };  // :v(

        let oeslice = self.try_get(dslice, data, idx);
        match oeslice {
            None => {
                let oelt = None;
        assert(
        oelt is Some <==> {
                &&& self.gettable(dslice@, data@, idx as int)
                &&& self.elt_parsable(dslice@, data@, idx as int)
        } );
                oelt
            },
            Some(eslice) => {
                proof {
                    assert( eslice@ == self.get(dslice@, data@, idx as int) );
                    let didx = idx as int;
                    assert( eslice@ == self.get(dslice@, data@, didx) );

                    self.get_ensures(dslice@, data@, idx as int);   // TODO(verus): lament of spec ensures
                    self.index_bounds_facts(dslice@, idx as int);
                    let edslice = self.get(SpecSlice::all(dslice@.i(data@)), dslice@.i(data@), idx as int);
                    assert( edslice.i(dslice@.i(data@)) == eslice@.i(data@));   // trigger
                }
                let oelt = self.eltf.try_parse(&eslice, data);

                proof {
                    let goelt = oelt;
                    if goelt is Some {
                        assert( self.gettable(dslice@, data@, idx as int) );
                        assert( self.eltf.parsable(eslice@, data@) );
//                         assert( eslice@.i(data@) == self.get_data(dslice@, data@, idx as int) );
                        assert( self.elt_parsable(dslice@, data@, idx as int) );
                        assert( oelt.unwrap().deepv() == self.get_elt(dslice@, data@, idx as int) );
                    } else {
                    }
                }
                oelt
            }
        }
    }

    exec fn exec_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (elt: EltFormat::U)
    // TODO factor out this common impl
    {
        let eslice = self.exec_get(dslice, data, idx);
        proof { // duplicated from try_get_elt
            self.get_ensures(dslice@, data@, idx as int);   // TODO(verus): lament of spec ensures
            self.index_bounds_facts(dslice@, idx as int);
            let edslice = self.get(SpecSlice::all(dslice@.i(data@)), dslice@.i(data@), idx as int);
            assert( edslice.i(dslice@.i(data@)) == eslice@.i(data@));   // trigger
        }
        self.eltf.exec_parse(&eslice, data)
    }

    /////////////////////////////////////////////////////////////////////////
    // setting individual elements
    /////////////////////////////////////////////////////////////////////////

    open spec fn elt_marshallable(&self, elt: EltFormat::DV) -> bool
    {
        self.eltf.marshallable(elt)
    }

    open spec fn settable(&self, dslice: SpecSlice, data: Seq<u8>, idx: int, value: EltFormat::DV) -> bool
    {
        &&& 0 <= idx < self.length(dslice, data)
        &&& self.elt_marshallable(value)
        &&& self.eltf.spec_size(value) == self.eltf.uniform_size()
    }

    exec fn exec_settable(&self, dslice: &Slice, data: &Vec<u8>, idx: usize, value: &EltFormat::U) -> (s: bool)
    {
        let len = self.exec_length(dslice, data);
        let sz = self.eltf.exec_size(value);
        idx < len && sz == self.eltf.exec_uniform_size()
    }

    exec fn exec_set(&self, dslice: &Slice, data: &mut Vec<u8>, idx: usize, value: &EltFormat::U)
    {
        proof {
            self.index_bounds_facts(dslice@, idx as int);
            self.eltf.uniform_size_ensures();
        }
        let newend = self.eltf.exec_marshall(value, data, dslice.start + idx * self.eltf.exec_uniform_size());
        assert( old(data)@.len() == data@.len() );
        // assert( self.seq_valid() ); // BS bogus recommendation
        assert( dslice@.valid(old(data)@) );
        assert forall |i: int| i != idx as int && self.gettable(dslice@, old(data)@, i)
            implies self.get(dslice@, data@, i).i(data@) == self.get(dslice@, old(data)@, i).i(old(data)@) by
        {
            self.index_bounds_facts(dslice@, i);

            lemma_seq_slice_slice(data@,
                dslice.start as int,
                dslice.end as int,
                i * self.eltf.uniform_size() as int,
                i * self.eltf.uniform_size() as int + self.eltf.uniform_size() as int);
            lemma_seq_slice_slice(old(data)@,
                dslice.start as int,
                dslice.end as int,
                i * self.eltf.uniform_size() as int,
                i * self.eltf.uniform_size() as int + self.eltf.uniform_size() as int);

            if i < idx as int {
                mul_preserves_le(i + 1, idx as int, self.eltf.uniform_size() as int);
            } else {
                mul_preserves_le(idx as int + 1, i, self.eltf.uniform_size() as int);
            }

            // TODO(verus): shouldn't assert-by conclusion give us this trigger for free?
            assert( self.get(dslice@, data@, i).i(data@) == self.get(dslice@, old(data)@, i).i(old(data)@) );
        }

        proof {
            lemma_seq_slice_slice(
                data@,
                dslice.start as int,
                dslice.end as int,
                idx as int * self.eltf.uniform_size() as int,
                idx as int * self.eltf.uniform_size() as int + self.eltf.uniform_size() as int);
        }
        assert forall |i: int| i != idx as int implies self.preserves_entry(dslice@, old(data)@, i, data@) by {
            if self.gettable(dslice@, old(data)@, i) && self.elt_parsable(dslice@, old(data)@, i) {
                assert( self.elt_parsable(dslice@, data@, i) );
                assume( self.get_elt(dslice@, data@, i) == self.get_elt(dslice@, old(data)@, i) );
            }
        }
        assert( dslice@.valid(old(data)@) );
        assert( dslice@.valid(data@) );
        assert( data@.len() == old(data)@.len() );
        assert(
            self.sets(dslice@, old(data)@, idx as int, value.deepv(), data@)
        );
    }

    /////////////////////////////////////////////////////////////////////////
    // resizing
    /////////////////////////////////////////////////////////////////////////

    open spec fn resizable(&self, dslice: SpecSlice, data: Seq<u8>, newlen: int) -> bool { false }

    open spec fn resizes(&self, dslice: SpecSlice, data: Seq<u8>, newlen: int, newdata: Seq<u8>) -> bool { false }

    exec fn exec_resizable(&self, dslice: &Slice, data: &Vec<u8>, newlen: usize) -> (r: bool) { false }

    exec fn resize(&self, dslice: &Slice, data: &mut Vec<u8>, newlen: usize) { }

    /////////////////////////////////////////////////////////////////////////
    // append
    /////////////////////////////////////////////////////////////////////////

    open spec fn well_formed(&self, dslice: SpecSlice, data: Seq<u8>) -> bool { false }

    proof fn well_formed_ensures(&self, dslice: SpecSlice, data: Seq<u8>) {}

    open spec fn appendable(&self, dslice: SpecSlice, data: Seq<u8>, value: EltFormat::DV) -> bool { false }

    open spec fn appends(&self, dslice: SpecSlice, data: Seq<u8>, value: EltFormat::DV, newdata: Seq<u8>) -> bool { false }


    exec fn exec_well_formed(&self, dslice: &Slice, data: &Vec<u8>) -> (w: bool) { false }

    exec fn exec_appendable(&self, dslice: &Slice, data: &Vec<u8>, value: EltFormat::U) -> (r: bool) { false }

    exec fn exec_append(&self, dslice: &Slice, data: &mut Vec<u8>, value: EltFormat::U) {}

    // TODO: delete; testing why definition in trait default isn't visible here
    open spec fn elt_parsable_to_len(&self, dslice:SpecSlice, data: Seq<u8>, len: int) -> bool
    {
        forall |i: int| 0<=i && i<len ==> self.elt_parsable(dslice, data, i)
    }

    // TODO: delete; testing why definition in trait default isn't visible here
    open spec fn parsable_to_len(&self, dslice: SpecSlice, data: Seq<u8>, len: usize) -> bool
    {
        &&& self.gettable_to_len(dslice, data, len as int)
        &&& self.elt_parsable_to_len(dslice, data, len as int)
    }

    // TODO: delete; testing why definition in trait default isn't visible here
    open spec fn gettable_to_len(&self, dslice: SpecSlice, data: Seq<u8>, len: int) -> bool
    {
        forall |i: int| 0<=i && i<len ==> self.gettable(dslice, data, i)
    }

    // TODO: delete; testing why definition in trait default isn't visible here
    open spec fn parse_to_len(&self, dslice: SpecSlice, data: Seq<u8>, len: usize) -> Seq<EltFormat::DV>
    {
        Seq::new(len as nat, |i: int| self.get_elt(dslice, data, i))
    }

    // TODO: delete; testing why definition in trait default isn't visible here
    open spec fn sets(&self, dslice: SpecSlice, data: Seq<u8>, idx: int, value: EltFormat::DV, new_data: Seq<u8>) -> bool
    {
        &&& new_data.len() == data.len()
        &&& self.lengthable(dslice, data) ==> {
            &&& self.lengthable(dslice, new_data)
            &&& self.length(dslice, new_data) == self.length(dslice, data)
            }
        &&& forall |i| i!=idx ==> self.preserves_entry(dslice, data, i, new_data)
        &&& self.gettable(dslice, new_data, idx)
        &&& self.elt_parsable(dslice, new_data, idx)
        &&& self.get_elt(dslice, new_data, idx) == value
    }

    // TODO: delete; testing why definition in trait default isn't visible here
    open spec fn preserves_entry(&self, dslice: SpecSlice, data: Seq<u8>, idx: int, new_data: Seq<u8>) -> bool
    {
        &&& (self.gettable(dslice, data, idx) ==> self.gettable(dslice, new_data, idx))
        &&& (self.gettable(dslice, data, idx) && self.elt_parsable(dslice, data, idx)) ==> {
            &&& self.elt_parsable(dslice, new_data, idx)
            &&& self.get_elt(dslice, new_data, idx) == self.get_elt(dslice, data, idx)
            }
    }
}

impl<EltFormat: Marshal + UniformSized>
    UniformSizedElementSeqFormat<EltFormat>
{
    pub open spec fn seq_parsable(&self, dslice: SpecSlice, data: Seq<u8>) -> bool
    {
        &&& self.seq_valid()
        &&& dslice.valid(data)
        &&& self.lengthable(dslice, data)
        &&& self.length(dslice, data) <= usize::MAX
        &&& self.parsable_to_len(dslice, data, self.length(dslice, data) as usize)
    }

    pub open spec fn seq_parse(&self, dslice: SpecSlice, data: Seq<u8>) -> Seq<EltFormat::DV>
    {
        self.parse_to_len(dslice, data, self.length(dslice, data) as usize)
    }

    pub open spec fn marshallable_at(&self, value: Seq<EltFormat::DV>, i: int) -> bool
    recommends 0 <= i < value.len()
    {
        &&& self.eltf.marshallable(value[i])
        &&& self.eltf.spec_size(value[i]) == self.eltf.uniform_size()
    }

// I don't remember what this was for, but it doesn't have a prototype in the dafny version.
//     proof fn marshallable_subrange(&self, value: Seq<DVElt>, l: int)
//     requires self.marshallable(value), 0<=l<=value.len()
//     ensures self.marshallable(value.subrange(0, l))
//     {
//         mul_preserves_le(l, value.len() as int, self.eltf.uniform_size() as int);
//         assert forall |i| 0 <= i < value.subrange(0, l).len() implies self.marshallable_at(value.subrange(0, l), i) by {
//             assert( self.marshallable_at(value, i) );
//         }
//     }
}

impl<EltFormat: Marshal + UniformSized>
    Marshal
    for UniformSizedElementSeqFormat<EltFormat>
{
    type DV = Seq<EltFormat::DV>;
    type U = Vec<EltFormat::U>;

    open spec fn valid(&self) -> bool { self.seq_valid() }

    exec fn exec_parsable(&self, dslice: &Slice, data: &Vec<u8>) -> (p: bool)
    {
        // TODO factor this into Marshal trait default method
        let ovalue = self.try_parse(dslice, data);
        ovalue.is_some()
    }

    open spec fn parsable(&self, dslice: SpecSlice, data: Seq<u8>) -> bool
    {
        self.seq_parsable(dslice, data)
    }

    open spec fn parse(&self, dslice: SpecSlice, data: Seq<u8>) -> Self::DV
    {
        self.seq_parse(dslice, data)
    }

    exec fn try_parse(&self, dslice: &Slice, data: &Vec<u8>) -> (ovalue: Option<Self::U>)
    {
        match self.try_length(dslice, data) {
            None => {
                proof {
                    assert( !self.lengthable(dslice@, data@) );
                }
                assert( !self.seq_parsable(dslice@, data@) );
                assert( !self.parsable(dslice@, data@) );
                return None;
            },
            Some(len) => {
                assert( len as int == self.length(dslice@, data@) );
                assert( len <= usize::MAX );
                let mut i: usize = 0;
                let mut result:Self::U = Vec::with_capacity(len);
                while i < len
                    invariant i <= len,
                    self.valid(),   // TODO(verus #984): waste of my debugging time
                    dslice@.valid(data@),   // TODO(verus #984): waste of my debugging time
                    len as int == self.length(dslice@, data@), // TODO(verus #984): waste of my debugging time
                    result.len() == i,
                    forall |j| 0<=j<i as nat ==> self.gettable(dslice@, data@, j),
                    forall |j| 0<=j<i as nat ==> self.elt_parsable(dslice@, data@, j),
                    forall |j| #![auto] 0<=j<i as nat ==> result[j].deepv() == self.get_elt(dslice@, data@, j),
                {
                    let oelt = self.try_get_elt(dslice, data, i);
                    if oelt.is_none() {
                        assert( !self.elt_parsable(dslice@, data@, i as int) );
                        assert( 0 <= i );
                        assert( i < self.length(dslice@, data@) );
                        let ghost glen = self.length(dslice@, data@);
                        let ghost gi = i as int;
                        assert( 0<=gi && gi<glen && !self.elt_parsable(dslice@, data@, gi) );
                        assert( !self.elt_parsable_to_len(dslice@, data@, glen) );
                        assert( !self.elt_parsable_to_len(dslice@, data@, self.length(dslice@, data@)) );
                        assert( !self.parsable_to_len(dslice@, data@, self.length(dslice@, data@) as usize) );
                        assert( !self.seq_parsable(dslice@, data@) );
                        assert( !self.parsable(dslice@, data@) );
                        return None;
                    }
                    result.push(oelt.unwrap());
                    i += 1;
                }
                // Looks like this wants extensionality, but no ~! Not sure why it's needed.
                // Oh maybe it's the trait-ensures-don't-trigger bug?
                assert( self.gettable_to_len(dslice@, data@, self.length(dslice@, data@)) );
                assert( self.seq_parsable(dslice@, data@) );
                let ghost glen = self.length(dslice@, data@);
                assert( result.len() == i );
                assume(
                    result.deepv() == Seq::new(result.len() as nat, |i: int| result[i].deepv()) );
                assert( result.deepv().len() == result.len() );
                assert( result.deepv().len() == i );
                assert( result.deepv().len() == glen );
                assert( self.parse_to_len(dslice@, data@, glen as usize).len() == glen );
                assert( result.deepv().len() == self.parse_to_len(dslice@, data@, glen as usize).len() );
                assert( result.deepv() =~= self.parse_to_len(dslice@, data@, glen as usize) );
                assert( result.deepv() == self.seq_parse(dslice@, data@) );
                assert( result.deepv() == self.parse(dslice@, data@) );
                assert( self.parsable(dslice@, data@) );
                return Some(result);
            }
        }
    }

    open spec fn marshallable(&self, value: Self::DV) -> bool
    {
        &&& forall |i| 0 <= i < value.len() ==> self.marshallable_at(value, i)
        &&& value.len() * self.eltf.uniform_size() <= usize::MAX
    }

    open spec fn spec_size(&self, value: Self::DV) -> usize
    {
        (value.len() * self.eltf.uniform_size()) as usize
    }

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
    {
        value.len() * self.eltf.exec_uniform_size()
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let mut i: usize = 0;
        let mut end = start;

        proof {
            self.eltf.uniform_size_ensures();

            // trigger extn equality
            assert( self.parse(SpecSlice{ start: start as int, end: end as int}, data@) == value.deepv().subrange(0, i as int) );
        }

        while i < value.len()
        invariant
            0 <= i <= value.len(),
            data@.len() == old(data)@.len(),
            end as int == start as int + self.spec_size(value.deepv().subrange(0, i as int)) as int,
            end as int == start as int + i * self.eltf.uniform_size(),
            forall |j| 0 <= j < start ==> data@[j] == old(data)@[j],
            forall |j| end as int <= j < old(data)@.len() ==> data@[j] == old(data)@[j],

            // TODO(verus): another decoy recommends failure that proves if you just ask for it
//             end as int <= data@.len(),
            self.parsable(SpecSlice{ start: start as int, end: end as int}, data@),
            self.parse(SpecSlice{ start: start as int, end: end as int}, data@) == value.deepv().subrange(0, i as int),

            // These should have been pulled through the loop via spinoff_loop(false); not sure why that didn't work.
            self.marshallable(value.deepv()),
            start as int + self.spec_size(value.deepv()) as int <= old(data).len(),
        {
            let ghost oldend = end;
            assert( oldend as int == start as int + self.spec_size(value.deepv().subrange(0, i as int)) as int );
            let ghost olddata = data@.subrange(start as int, end as int);
            let ghost oldi = i;

            proof {
                // TODO(verus): lament of the spec ensures
                // Also lament that this fact didn't get carried around the while invariants automatically. :v(
                self.eltf.uniform_size_ensures();

                if i as int + 1 < value.len() {
                    pos_mul_preserves_order(i as int + 1, value.len() as int, self.eltf.uniform_size() as int);
                }
                distribute_left(i as int, 1, self.eltf.uniform_size() as int);

                let esz = self.eltf.spec_size(value.deepv()[i as int]) as int;
                assert( esz == self.eltf.uniform_size() ) by {
                    assert( self.marshallable_at(value.deepv(), i as int) );
                }

                assert( self.eltf.marshallable(value[i as int].deepv()) ) by {
                    assert( self.marshallable_at(value.deepv(), i as int) );
                }
            }

            end = self.eltf.exec_marshall(&value[i], data, end);
            i += 1;

            proof {
                let u = self.eltf.uniform_size() as int;

                assert( data@.subrange(start as int, oldend as int) == olddata );   // trigger extn equality

                let oslice = SpecSlice{start: start as int, end: oldend as int};
                let nslice = SpecSlice{start: start as int, end: end as int};
//                 let odata = data@.subrange(start as int, oldend as int);
//                 let sdata = data@.subrange(start as int, end as int);
                let osubv = value.deepv().subrange(0, oldi as int);
                let subv = value.deepv().subrange(0, i as int);

                assert( i == self.length(nslice, data@) ) by { div_plus_one(oldi as int, oldend-start, u); }

                // Prove two inductive steps together because they share most proof text.
                assert( self.parsable(nslice, data@) && self.parse(nslice, data@) =~= subv ) by {
                    assert forall |j: int|
                        // Mention both triggers to be able to use both conjuncts of the forall
                        // when we're done.
//                         #![trigger self.elt_parsable(sdata, j)]
//                         #![trigger self.get_elt(sdata, j)]
                        0<=j<self.length(nslice, data@)
                        implies
                        self.elt_parsable(nslice, data@, j) && self.get_elt(nslice, data@, j) == subv[j]
                    by {
                        if j < oldi {
                            // j was from an earlier iteration; appeal to invariants
                            mul_preserves_le(j + 1, oldi as int, u as int);
                            assert( (j+1)*u == j*u +u ) by(nonlinear_arith);
//                             assert( self.get_data(oslice, data@, j) == self.get_data(nslice, data@, j) );   // trigger extn equality

                            assert( self.elt_parsable(oslice, data@, j) ); // trigger old parsable
//                             assert( self.eltf.parse(self.get_data(olddata, j)) == osubv[j] );    // trigger old parse_to_len
                        } else {
                            // we just marshalled j
//                             assert( data@.subrange(oldend as int, end as int) =~= self.get_data(sdata, j) );    // trigger extn equality
                        }
                    }
                }
            }
        }
//         assert( self.parse(data@.subrange(start as int, end as int)) == value.deepv() );    // trigger extn equality
        end
    }
}

} //verus!
