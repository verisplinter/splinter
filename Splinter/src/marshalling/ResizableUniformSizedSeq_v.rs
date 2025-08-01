// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
// use vstd::bytes::*;
// use vstd::slice::*;
use crate::marshalling::Slice_v::*;
use crate::marshalling::Marshalling_v::*;
use crate::marshalling::IntegerMarshalling_v::*;
use crate::marshalling::SeqMarshalling_v::*;
use crate::marshalling::UniformSized_v::*;
use crate::marshalling::math_v::*;

verus! {

// In a ResizableUniformSizedElementSeqFormat, the length (set of readable elements) is
// conveyed by a dynamically-stored length field. The marshaller knows how to read that field and
// dissuade the caller from reading off the end of the valid data.

pub struct ResizableUniformSizedElementSeqFormat
    <EltFormat: Marshal + UniformSized, LenType: IntFormattable>
{
    pub eltf: EltFormat,
    pub lenf: IntFormat<LenType>,

    // `total_size` is like a "capacity" -- the allocated space.  It's measured in bytes.
    // This field ports totalSize from the dfy original
    pub total_size: usize, 

    pub max_length: usize,
}

impl<EltFormat: Marshal + UniformSized, LenType: IntFormattable>
    ResizableUniformSizedElementSeqFormat<EltFormat, LenType>
{
    pub fn new(eltf: EltFormat, lenf: IntFormat<LenType>, total_size: usize) -> (s: Self)
    requires
        eltf.us_valid(),
        eltf.valid(),
        lenf.us_valid(),
        lenf.valid(),
        LenType::uniform_size() <= total_size,
    ensures
        s.seq_valid(),
        s.total_size == total_size,
    {
        proof { eltf.uniform_size_ensures(); };
        let max_length = (total_size - lenf.exec_uniform_size()) as usize / eltf.exec_uniform_size();
        Self{ eltf, lenf, total_size, max_length }
    }

    pub open spec fn spec_max_length(&self) -> usize
    {
        // Why does subtraction of usizes produce an int?
        (self.total_size - self.size_of_length_field()) as usize / self.eltf.uniform_size()
    }

    // TODO(jonh): inline this defn away
    pub open spec fn size_of_length_field(&self) -> usize
    {
        self.lenf.uniform_size()
    }

    exec fn exec_size_of_length_field(&self) -> (out: usize)
    requires self.seq_valid(),
    ensures out == self.size_of_length_field()
    {
        self.lenf.exec_uniform_size()
    }

    pub proof fn index_bounds_facts(&self, idx: int)
    requires self.valid(), 0 <= idx, idx < self.spec_max_length()
    ensures
        self.size_of_length_field() as int
            <= self.size_of_length_field() as int + idx * (self.eltf.uniform_size() as int)
            <  self.size_of_length_field() as int + idx * (self.eltf.uniform_size() as int) + (self.eltf.uniform_size() as int)
            == self.size_of_length_field() as int + (idx+1) * (self.eltf.uniform_size() as int)
            <= self.size_of_length_field() + (self.spec_max_length() as int) * (self.eltf.uniform_size() as int)
            <= self.total_size
    {
        self.eltf.uniform_size_ensures();   // TODO(verus): lament of the spec ensures
        nat_mul_nat_is_nat(idx, self.eltf.uniform_size() as int);
        pos_mul_preserves_order(idx, idx+1, self.eltf.uniform_size() as int);
        distribute_left(idx, 1, self.eltf.uniform_size() as int);
        div_mul_order(self.total_size as int, self.eltf.uniform_size() as int);
        if idx + 1 < self.spec_max_length() {
            pos_mul_preserves_order(idx + 1, self.spec_max_length() as int, self.eltf.uniform_size() as int);
            // (idx+1)*us < m * us
        }
        euclidean_div_truncates(
            (self.total_size - self.size_of_length_field()) as usize as int,
            self.eltf.uniform_size() as int);
    }

    pub proof fn length_ensures(&self, data: Seq<u8>)
    ensures 0 <= self.length(data) <= LenType::max()
    {
        self.lenf.parse_nat(data.subrange(0, self.size_of_length_field() as int));
    }

    // How you get an uninitialized Vec<u8> into a condition where you can begin append()ing
    pub exec fn initialize(&self, dslice: &Slice, data: &mut Vec<u8>)
    requires
        self.valid(),
        dslice@.valid(old(data)@),
        self.total_size <= dslice@.len(),
    ensures
        data.len() == old(data).len(),
        self.well_formed(dslice@.i(data@)),
        self.lengthable(dslice@.i(data@)),
        self.length(dslice@.i(data@)) == 0,
        dslice@.agree_beyond_slice(old(data)@, data@),
    {
        proof { self.length_ensures(dslice@.i(old(data)@)); };
        self.resize(dslice, data, 0);
    }

    // exec_append promises not to touch any bytes beyond the spot it places the appended value.
    // This is a bit of a layering violation used in VariableSizedElementSeq to share space between
    // the boundary seq and the value storage.
    pub open spec fn first_unused_byte(&self, dslice: SpecSlice, data: Seq<u8>) -> int
    {
        dslice.start + self.size_of_length_field() + self.length(dslice.i(data)) * self.eltf.uniform_size()
    }

    pub open spec fn untampered_bytes(&self, dslice: SpecSlice, olddata: Seq<u8>, newdata: Seq<u8>) -> bool
    {
        forall |i| self.first_unused_byte(dslice, newdata) <= i < newdata.len() ==> olddata[i] == newdata[i]
    }
}

impl<EltFormat: Marshal + UniformSized, LenType: IntFormattable>
    SeqMarshal for ResizableUniformSizedElementSeqFormat<EltFormat, LenType>
{
    type DVElt = EltFormat::DV;
    type Elt = EltFormat::U;

    open spec fn seq_valid(&self) -> bool {
        &&& self.eltf.us_valid()
        &&& self.eltf.valid()
        &&& self.lenf.us_valid()
        &&& self.lenf.valid()
        &&& self.size_of_length_field() <= self.total_size
        &&& self.max_length == self.spec_max_length()
    }

    open spec fn lengthable(&self, data: Seq<u8>) -> bool {
        &&& self.total_size <= data.len()
    }

    open spec fn length(&self, data: Seq<u8>) -> int
    {
        self.lenf.parse(data.subrange(0, self.size_of_length_field() as int)) as int
    }

    exec fn try_length(&self, dslice: &Slice, data: &Vec<u8>) -> (out: Option<usize>)
    {
        assume(false);  // TODO proof rot
        if (dslice.len() as usize) < self.total_size {
            assert( !self.lengthable(dslice@.i(data@)) );
            return None;    // lengthable first conjunct is false
        }

        let sslice = dslice.subslice(0, self.lenf.exec_uniform_size());

        // TODO(verus): trait instability: this expression appears in exec_parse requires, but
        // mentioning it completes the proof.
//         assert( self.lenf.parsable(sslice@.i(data@)) );

        assume( self.lenf.parsable(sslice@.i(data@)) ); // TODO proof rotted
        let parsed_len = self.lenf.exec_parse(&sslice, data);

        proof {
            // Took way too long to track down this lemma call. Decent automation would have been nice.
            assert( dslice@.subslice(0, self.lenf.uniform_size() as int).i(data@)
                    == dslice@.i(data@).subrange(0, self.size_of_length_field() as int) );   // subrange trigger
            LenType::deepv_is_as_int(parsed_len);

            self.length_ensures(dslice@.i(data@));  // trigger for lengthable LenType::max() conjunct
            // goal
//             assert( self.lengthable(dslice@.i(data@)) );
        }

        Some(LenType::to_usize(parsed_len))
    }

    /////////////////////////////////////////////////////////////////////////
    // getting individual elements
    /////////////////////////////////////////////////////////////////////////

    // NB: gettable doesn't care about the stored length field! You can store
    // a too-long value; doesn't matter, if there's not enough data we won't let
    // you index it. Or you can access a field past the stored length field;
    // it's a sign, not a cop.
    // TODO it's a bit weird that we need lengthable; that forces a try_length in try_get.
    open spec fn gettable(&self, data: Seq<u8>, idx: int) -> bool
    {
        // This conjunct forces data (and hence the slice arg to get) to be at least total_size
        &&& self.lengthable(data)
        &&& 0 <= idx < self.spec_max_length()
    }

    open spec fn get(&self, dslice: SpecSlice, data: Seq<u8>, idx: int) -> (eslice: SpecSlice)
    {
        dslice.subslice(
            self.size_of_length_field() + idx * self.eltf.uniform_size(),
            self.size_of_length_field() + idx * self.eltf.uniform_size() + self.eltf.uniform_size())
    }

    proof fn get_ensures(&self, dslice: SpecSlice, data: Seq<u8>, idx: int)
    {
        assume(false);  // TODO proof rot
        self.index_bounds_facts(idx as int);
    }

    open spec fn elt_parsable(&self, data: Seq<u8>, idx: int) -> bool
    {
        self.eltf.parsable(self.get_data(data, idx))
    }

    open spec fn get_elt(&self, data: Seq<u8>, idx: int) -> (elt: EltFormat::DV)
    {
        self.eltf.parse(self.get_data(data, idx))
    }

    exec fn try_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oeslice: Option<Slice>)
    {
        assume(false);  // TODO proof rot
        // gettable requires lengthable, so I guess we better go check
        let olen = self.try_length(dslice, data);
        if olen.is_none() { return None; }

        if idx < self.max_length {
            proof { self.index_bounds_facts(idx as int); }
            Some( self.exec_get(dslice, data, idx) )
        } else {
            None
        }
    }

    exec fn exec_gettable(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (g: bool)
    {
        self.try_length(dslice, data).is_some() && idx < self.max_length
    }

    exec fn exec_get(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (eslice: Slice)
    {
        assume(false);  // TODO proof rot
        proof { self.index_bounds_facts(idx as int); }
        let eslice = dslice.subslice(
            self.exec_size_of_length_field() + (idx as usize) * self.eltf.exec_uniform_size(),
            self.exec_size_of_length_field() + (idx as usize) * self.eltf.exec_uniform_size() + self.eltf.exec_uniform_size());
        eslice
    }

    exec fn try_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (oelt: Option<EltFormat::U>)
    {
        assume(false);  // TODO proof rot
        let oeslice = self.try_get(dslice, data, idx);
        match oeslice {
            None => None,
            Some(eslice) => {
                proof {
                    self.get_ensures(dslice@, data@, idx as int);   // TODO(verus): lament of spec ensures
                    self.index_bounds_facts(idx as int);
                    let edslice = self.get(SpecSlice::all(dslice@.i(data@)), dslice@.i(data@), idx as int);
                    assert( edslice.i(dslice@.i(data@)) == eslice@.i(data@));   // trigger
                }
                self.eltf.try_parse(&eslice, data)
            }
        }
    }

    exec fn exec_get_elt(&self, dslice: &Slice, data: &Vec<u8>, idx: usize) -> (elt: EltFormat::U)
    {
        let eslice = self.exec_get(dslice, data, idx);
        proof { // duplicated from try_get_elt
            self.get_ensures(dslice@, data@, idx as int);   // TODO(verus): lament of spec ensures
            self.index_bounds_facts(idx as int);
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

    open spec fn settable(&self, data: Seq<u8>, idx: int, value: EltFormat::DV) -> bool
    {
        &&& self.lengthable(data)
        &&& 0 <= idx < self.spec_max_length() as int
        &&& self.eltf.spec_size(value) == self.eltf.uniform_size()
    }

    exec fn exec_settable(&self, dslice: &Slice, data: &Vec<u8>, idx: usize, value: &EltFormat::U) -> (s: bool)
    {
        let olen = self.try_length(dslice, data);
        let sz = self.eltf.exec_size(value);

        let s = {
            &&& olen.is_some()
            &&& idx < self.max_length
            &&& sz == self.eltf.exec_uniform_size()
        };
        assert( s == self.settable(dslice@.i(data@), idx as int, value.deepv()) );
        s
    }

    exec fn exec_set(&self, dslice: &Slice, data: &mut Vec<u8>, idx: usize, value: &EltFormat::U)
    ensures idx < self.length(dslice@.i(data@)) ==> self.untampered_bytes(dslice@, old(data)@, data@)
    {
        proof { self.index_bounds_facts(idx as int); }
        let elt_start = dslice.start + self.exec_size_of_length_field() + idx * self.eltf.exec_uniform_size();
        let Ghost(elt_end) = self.eltf.exec_marshall(value, data, elt_start);

        // Extensionality trigger.
        assert( dslice@.i(data@).subrange(0, self.size_of_length_field() as int)
                =~= dslice@.i(old(data)@).subrange(0, self.size_of_length_field() as int) );

        // Extensionality trigger.
        assert( data@.subrange(elt_start as int, elt_end as int) =~= self.get_data(dslice@.i(data@), idx as int) );

        assert forall |i: int| i != idx as int && self.gettable(dslice@.i(old(data)@), i)
            implies self.get_data(dslice@.i(data@), i) == self.get_data(dslice@.i(old(data)@), i) by
        {
            self.index_bounds_facts(i);

            if i < idx as int {
                mul_preserves_le(i + 1, idx as int, self.eltf.uniform_size() as int);
            } else {
                mul_preserves_le(idx as int + 1, i, self.eltf.uniform_size() as int);
            }

            // TODO(verus): #1257
            assert( self.get_data(dslice@.i(data@), i) == self.get_data(dslice@.i(old(data)@), i) );
        }
            
        // postcondition goal
        // assert( self.sets(dslice@.i(old(data)@), idx as int, value.deepv(), dslice@.i(data@)) );

        assume(false);  // TODO proof rot
        proof {
            let len = self.length(dslice@.i(data@));
            if idx < len {
                mul_preserves_le(idx + 1, len, self.eltf.uniform_size() as int);
                // postcondition goal
                // assert( self.untampered_bytes(dslice@, old(data)@, data@) );
            }
        }
    }

    /////////////////////////////////////////////////////////////////////////
    // resizing
    /////////////////////////////////////////////////////////////////////////

    open spec fn resizable(&self, data: Seq<u8>, newlen: int) -> bool {
        &&& self.lengthable(data)
        &&& newlen <= self.spec_max_length() as nat
        &&& newlen <= LenType::max()
    }

    exec fn exec_resizable(&self, dslice: &Slice, data: &Vec<u8>, newlen: usize) -> (r: bool) {
        &&& self.exec_lengthable(dslice, data)
        &&& newlen <= self.max_length
        // Have to be able to write the length down in the alotted space
        &&& newlen <= LenType::exec_max()
    }

    exec fn resize(&self, dslice: &Slice, data: &mut Vec<u8>, newlen: usize)
    ensures self.untampered_bytes(dslice@, old(data)@, data@)
    {
        let length_val = LenType::from_usize(newlen);
        proof { length_val.always_wf(); }
        let length_end = self.lenf.exec_marshall(&length_val, data, dslice.start);

        proof {
            LenType::deepv_is_as_int(length_val);

            let sdata_old = dslice@.i(old(data)@);
            let sdata_new = dslice@.i(data@);

            // We updated the length correctly
            // extensional equality to connect seq as given by exec_marshall to seq as expected by
            // self.length
            assert( data@.subrange(dslice.start as int, length_end as int)
                    == sdata_new.subrange(0, self.size_of_length_field() as int) );
            
            // We didn't touch any of the actual indexed data
            assert forall |i| self.gettable(sdata_old, i) && self.elt_parsable(sdata_old, i)
                implies {
                    &&& self.elt_parsable(sdata_new, i)
                    &&& self.get_elt(sdata_new, i) == self.get_elt(sdata_old, i)
            } by {
                self.index_bounds_facts(i);
                // TODO(verus): #1257
                assert( self.get_data(sdata_new, i) == self.get_data(sdata_old, i) );
            }

            // goal
//             assert( self.resizes(dslice@.i(old(data)@), newlen as int, dslice@.i(data@)) );
            assume(false);  // TODO proof rot
        }
    }

    /////////////////////////////////////////////////////////////////////////
    // append
    /////////////////////////////////////////////////////////////////////////

    open spec fn well_formed(&self, data: Seq<u8>) -> bool {
        self.lengthable(data)
    }

    proof fn well_formed_ensures(&self, data: Seq<u8>) {}

    open spec fn appendable(&self, data: Seq<u8>, value: EltFormat::DV) -> bool {
        &&& self.length(data) < self.spec_max_length() as nat
        &&& self.eltf.spec_size(value) == self.eltf.uniform_size()

        // dafny does this computation in a u64; why is it okay with overflow!?
        &&& self.length(data) + 1 <= LenType::max()
    }

    exec fn exec_well_formed(&self, dslice: &Slice, data: &Vec<u8>) -> (w: bool) {
        self.exec_lengthable(dslice, data)
    }

    exec fn exec_appendable(&self, dslice: &Slice, data: &Vec<u8>, value: &EltFormat::U) -> (r: bool) {
        let len = self.exec_length(dslice, data);
        let sz = self.eltf.exec_size(value);
        let r = {
            &&& len < self.max_length
            &&& sz == self.eltf.exec_uniform_size()
            &&& len + 1 <= LenType::exec_max()
        };
        r
    }

    exec fn exec_append(&self, dslice: &Slice, data: &mut Vec<u8>, value: &EltFormat::U)
    ensures self.untampered_bytes(dslice@, old(data)@, data@)
    {
        let ghost sliced_begin = dslice@.i(data@);
        let len = self.exec_length(dslice, data);
        self.resize(dslice, data, len + 1);

        let ghost sliced_middle = dslice@.i(data@);
        self.exec_set(dslice, data, len, value);

        assume(false);  // TODO proof rot
        assert( self.preserves_entry(sliced_begin, len as int, sliced_middle) );   // trigger
        assert forall |i| i != len implies self.preserves_entry(dslice@.i(old(data)@), i, dslice@.i(data@)) by {
            assert( self.preserves_entry(dslice@.i(old(data)@), i, sliced_middle) );   // trigger
            assert( self.preserves_entry(sliced_middle, i, dslice@.i(data@)) );        // trigger
        }
    }
}

// TODO(jonh): A great deal of this type duplicates what's in UniformSizedSeq. I'm reasonably
// confident we could shoehorn them together somehow, so that UniformSizedSeq is just a variant
// of ResizableUniformSizedSeq with a 0-byte length field that knows to get its "dynamic"
// length from the static length ("total_size") in the Marshal object.

impl<EltFormat: Marshal + UniformSized, LenType: IntFormattable>
    ResizableUniformSizedElementSeqFormat<EltFormat, LenType>
{
    pub open spec fn seq_parsable(&self, data: Seq<u8>) -> bool
    {
        &&& self.seq_valid()
        &&& self.lengthable(data)
        &&& self.length(data) <= usize::MAX
        &&& self.parsable_to_len(data, self.length(data) as usize)
    }

    pub open spec fn seq_parse(&self, data: Seq<u8>) -> Seq<EltFormat::DV>
    {
        self.parse_to_len(data, self.length(data) as usize)
    }

    pub open spec fn marshallable_at(&self, value: Seq<EltFormat::DV>, i: int) -> bool
    recommends 0 <= i < value.len()
    {
        &&& self.eltf.marshallable(value[i])
        &&& self.eltf.spec_size(value[i]) == self.eltf.uniform_size()
    }

    pub proof fn parsable_length_bounds(&self, data: Seq<u8>)
    requires self.seq_valid(), self.parsable(data),
    ensures
        self.length(data) <= self.spec_max_length() as int,
        self.length(data) * self.eltf.uniform_size() as int
            <= self.total_size as int - self.size_of_length_field() as int,
    {
        self.length_ensures(data);
        let len = self.length(data);
        if 0 < len {
            assert( self.gettable(data, len-1) );
            self.index_bounds_facts(len - 1);
        } else {
            // trigger nonnegative ... but I have no idea how! length mentions
            // IntegerMarshalling::parse, which has no ensures and never mentions
            // type T. Weird.
            assert( len == 0 );
        }
    }
}

impl<EltFormat: Marshal + UniformSized, LenType: IntFormattable>
    Marshal
    for ResizableUniformSizedElementSeqFormat<EltFormat, LenType>
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

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        self.seq_parsable(data)
    }

    open spec fn parse(&self, data: Seq<u8>) -> Seq<EltFormat::DV>
    {
        self.seq_parse(data)
    }

    exec fn try_parse(&self, dslice: &Slice, data: &Vec<u8>) -> (ovalue: Option<Vec<EltFormat::U>>)
    {
        assume(false);  // TODO proof rot
        match self.try_length(dslice, data) {
            None => { None },
            Some(len) => {
                let mut i: usize = 0;
                let mut result:Vec<EltFormat::U> = Vec::with_capacity(len);
                while i < len
                invariant
                    i <= len,
                    result.len() == i,
                    forall |j| 0<=j<i as nat ==> self.gettable(dslice@.i(data@), j),
                    forall |j| 0<=j<i as nat ==> self.elt_parsable(dslice@.i(data@), j),
                    forall |j| #![auto] 0<=j<i as nat ==> result[j].deepv() == self.get_elt(dslice@.i(data@), j),
                decreases len-i,
                {
                    assume(false); // proof rotted
                    let oelt = self.try_get_elt(dslice, data, i);
                    if oelt.is_none() {
                        return None;
                    }
                    result.push(oelt.unwrap());
                    i += 1;
                }
                // Looks like this wants extensionality, but no ~! Not sure why it's needed.
                // TODO(verus): Oh maybe it's the trait-ensures-don't-trigger bug?
                assert( result.deepv() == self.parse(dslice@.i(data@)) );    // trigger.
                Some(result)
            }
        }
    }

    open spec fn marshallable(&self, value: Seq<EltFormat::DV>) -> bool
    {
        &&& forall |i| 0 <= i < value.len() ==> self.marshallable_at(value, i)
        &&& value.len() as int <= LenType::max()

        &&& self.size_of_length_field() + value.len() * self.eltf.uniform_size() <= self.total_size
    }

    open spec fn spec_size(&self, value: Seq<EltFormat::DV>) -> usize
    {
        self.total_size
    }

    exec fn exec_size(&self, value: &Vec<EltFormat::U>) -> (sz: usize)
    {
        self.total_size
    }

    exec fn exec_marshall(&self, value: &Vec<EltFormat::U>, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let end = start + self.total_size;
        let slice = Slice{start, end};

        // Just call resize instead? no, that requires the data already be well-formatted
        // (such as lengthable)
        let length_val = LenType::from_usize(value.len());
        proof { length_val.always_wf(); }
        let length_end = self.lenf.exec_marshall(&length_val, data, start);
        proof {
            LenType::deepv_is_as_int(length_val);
            // trigger: Extensional equality between the thing we know holds length_val and the self.length defn
            assert( slice@.i(data@).subrange(0, self.size_of_length_field() as int)
                    == SpecSlice{start: start as int, end: length_end as int}.i(data@) );
        }

        let mut i: usize = 0;

        assert( value.len() <= self.spec_max_length() as int ) by {
            self.eltf.uniform_size_ensures();
            inequality_move_divisor(
                value.len() as int,
                self.total_size as int - self.size_of_length_field() as int,
                self.eltf.uniform_size() as int);
        }
        
        assert forall |j| #![auto] 0 <= j < value.len() implies self.settable(slice@.i(data@), j, value[j].deepv()) by {
            assert( self.marshallable_at(value.deepv(), j) );   // trigger
        }

        while i < value.len()
        invariant
            data@.len() == old(data)@.len(),
            forall |j| 0 <= j < start ==> data@[j] == old(data)@[j],
            forall |j| end as int <= j < old(data)@.len() ==> data@[j] == old(data)@[j],
            self.length(slice@.i(data@)) == value.len(),
            forall |j| 0 <= j < i ==> self.elt_parsable(slice@.i(data@), j),
            forall |j| #![auto] 0 <= j < i ==> self.get_elt(slice@.i(data@), j) == value[j].deepv(),
        decreases value.len() - i,
        {
            assume( false );    // proof rotted
            let ghost prev_data = data@;
            let ghost old_i = i;
            proof {
                self.eltf.uniform_size_ensures();
                assert( self.marshallable_at(value.deepv(), i as int) );
            }
            self.exec_set(&slice, data, i, &value[i]);
            i += 1;

            proof {
                assert forall |j| 0 <= j < i implies self.elt_parsable(slice@.i(data@), j) by {
                    if j < old_i {
                        assert( self.preserves_entry( slice@.i(prev_data), j, slice@.i(data@)) );    // trigger
                    }
                }
                assert forall |j| #![auto] 0 <= j < i implies self.get_elt(slice@.i(data@), j) == value[j].deepv() by {
                    if j < old_i {
                        assert( self.preserves_entry( slice@.i(prev_data), j, slice@.i(data@)) );    // trigger
                    }
                }
            }
        }
        // TODO(verus): This is just a postcondition; why wasn't it automatically triggered?
        assert( self.parse(data@.subrange(start as int, end as int)) == value.deepv() );
        end
    }
}

} //verus!
