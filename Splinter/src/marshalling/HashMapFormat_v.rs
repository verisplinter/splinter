// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use vstd::bytes::*;
use vstd::slice::*;
use vstd::hash_map::*;
use vstd::std_specs::hash::*;
use core::hash::Hash;
use crate::marshalling::Slice_v::*;
use crate::marshalling::Marshalling_v::*;
use crate::marshalling::IntegerMarshalling_v::*;
use crate::marshalling::StaticallySized_v::*;
use crate::marshalling::UniformSized_v::*;
use crate::marshalling::UniformSizedSeq_v::*;
use crate::marshalling::SeqMarshalling_v::*;
use crate::marshalling::VariableSizedElementSeq_v::*;
use crate::marshalling::KVPairFormat_v::*;
use crate::marshalling::ResizableUniformSizedSeq_v::*;

verus! {

struct HashablePair<KMarshal: Marshal + UniformSized, VMarshal: Marshal + UniformSized>
where KMarshal::U : Eq + Hash
{
    key_fmt: KMarshal,
    value_fmt: VMarshal,
}

impl<KMarshal: Marshal + UniformSized, VMarshal: Marshal + UniformSized>
KVTrait for HashablePair<KMarshal, VMarshal>
where KMarshal::U : Eq + Hash
{
    type KeyLenType = IntFormat<u8>;    // TODO make zero length
    type KeyFormat = KMarshal;
    type ValueFormat = VMarshal;

    exec fn key_format(&self) -> &Self::KeyFormat
    {
        &self.key_fmt
    }

    exec fn value_format(&self) -> &Self::ValueFormat
    {
        &self.value_fmt
    }
}

struct HashMapFormat<KMarshal: Marshal + UniformSized, VMarshal: Marshal + UniformSized>
where KMarshal::U : Eq + Hash
{
    // underlying formatter is a seq of k,v pairs
    kvpair_format: ResizableUniformSizedElementSeqFormat<KVPairFormat<HashablePair<KMarshal, VMarshal>>, u16>,
}

// impl<KMarshal: Marshal + Eq + Hash, VMarshal: Marshal>
// Deepview<Map<KMarshal::DV, VMarshal::DV>> for HashMapWithView<KMarshal::U, VMarshal::U> {
impl<KDV,KU,VDV,VU>
Deepview<Map<KDV,VDV>> for HashMapWithView<KU,VU>
where
    KU : View<V = KDV> + Deepview<KDV> + Eq + Hash,
    VU : View<V = VDV> + Deepview<VDV>,
//     KDV = <KU as View>::V,
//     VDV = <VU as View>::V,
{
    // TODO Our "deep" view of the keys & values is only a View. Hrrm.
    open spec fn deepv(&self) -> Map<KDV, VDV>
    {
        Map::new(|k| self@.dom().contains(k), |k| self@[k]@)
    }
}

spec fn map_to_pair_seq<K,V>(m: Map<K,V>) -> (out: Seq<SpecKVPair<K, V>>)
decreases m.dom().len()
    when m.dom().finite()
//     via map_to_pair_seq_via::<K,V>
{
    let key = m.dom().choose();
    if !m.dom().contains(key) {
        Seq::empty()
    } else {
        map_to_pair_seq(m.remove(key)).push(SpecKVPair{key, value: m[key]})
    }
}

spec fn pair_seq_to_map<K,V>(pair_seq: Seq<SpecKVPair<K, V>>) -> Map<K,V>
decreases pair_seq.len()
{
    if pair_seq.len()==0 {
        Map::empty()
    } else {
        let last = pair_seq.last();
        pair_seq_to_map(pair_seq.drop_last()).insert(last.key, last.value)
    }
}

proof fn pair_seq_map_equiv<K,V>(m: Map<K,V>)
requires m.dom().finite()
ensures pair_seq_to_map(map_to_pair_seq(m)) == m
decreases m.dom().len()
{
    if m.dom().len() != 0 {
        let key = m.dom().choose();
        let rm = m.remove(key);
        // recurse
        pair_seq_map_equiv(rm);
        // seq extn
        assert( map_to_pair_seq(rm).push(SpecKVPair{key, value: m[key]}).drop_last()
            == map_to_pair_seq(rm) );
    }
    // map extn
    assert( pair_seq_to_map(map_to_pair_seq(m)) == m ); // map extn
}

impl<KMarshal: Marshal + UniformSized, VMarshal: Marshal + UniformSized>
HashMapFormat<KMarshal, VMarshal>
where
    <KMarshal as Marshal>::U : View<V = <KMarshal as Marshal>::DV> + Eq + Hash,
    <VMarshal as Marshal>::U : View<V = <VMarshal as Marshal>::DV>,
{
    exec fn pair_vec_to_hash_map(mut pair_vec: Vec<KVPair<<KMarshal as Marshal>::U, <VMarshal as Marshal>::U>>)
        -> (out: HashMapWithView<<KMarshal as Marshal>::U, <VMarshal as Marshal>::U>)
    ensures out.deepv() == pair_seq_to_map(pair_vec.deepv())
    {
        let ghost orig_pair_vec = pair_vec.deepv();
        assume( obeys_key_model::<<KMarshal as Marshal>::U>() );
        // not sure where to push this obligation upstream. Trait?
        assume( forall |k1: <KMarshal as Marshal>::U, k2: <KMarshal as Marshal>::U| k1@==k2@ ==> k1==k2 );
        assume( forall |k1: <KMarshal as Marshal>::U| #![auto] k1@ == k1.deepv() );
        assume( forall |v1: <VMarshal as Marshal>::U| #![auto] v1@ == v1.deepv() );
//         new_map_assumption::<<kMarshal as Marshal>::U>();

        let mut hm = HashMapWithView::new();
        let ghost count = 0;

        // TODO(verus): this extn equality didn't trigger itself in the invariant context;
        // had to utter it out loud to get it to go.
        assert( hm.deepv() == pair_seq_to_map(orig_pair_vec.take(count)) );
        assert( orig_pair_vec == orig_pair_vec.subrange(count, orig_pair_vec.len() as int) ); // extn

        while 0 < pair_vec.len()
        invariant
            count == orig_pair_vec.len() - pair_vec.len(),
            0 <= count <= orig_pair_vec.len(),
            hm.deepv() == pair_seq_to_map(orig_pair_vec.take(count)),
            pair_vec.deepv() == orig_pair_vec.subrange(count, orig_pair_vec.len() as int),
        {
            let ghost prev_count = count;
            let ghost prev_pair_vec = pair_vec.deepv();

            assert( 0 < pair_vec.len() );

            let pair = pair_vec.remove(0);

            // trigger via deepv/@ equivalence
            assert( pair_vec.deepv() == prev_pair_vec.remove(0 as int) );

            hm.insert(pair.key, pair.value);
            proof {
                count = count + 1;

                let oc = orig_pair_vec.take(count);
                let last = oc.last();
                // extn
                assert( orig_pair_vec[prev_count] == prev_pair_vec[0] );
                // extn
                assert( orig_pair_vec.take(prev_count) == oc.drop_last() );
                // extn
                assert( hm.deepv() == pair_seq_to_map(oc.drop_last()).insert(last.key, last.value) );

                // loop invariant extn trigger failure
                assert( pair_vec.deepv() == orig_pair_vec.subrange(count, orig_pair_vec.len() as int) );
            }
        }
        hm
    }

//     spec fn map_to_pair_seq(m: Map<<KMarshal as Marshal>::DV, <VMarshal as Marshal>::DV>)
//         -> (out: Seq<SpecKVPair<<KMarshal as Marshal>::DV, <VMarshal as Marshal>::DV>>)
//     decreases m.dom().len()
//     {
//         if !exists |key| m.dom().contains(key) {
//             Seq::empty()
//         } else {
// //             assert( m.dom() != Set::<<KMarshal as Marshal>::DV>::empty() );
//             let key = choose |key| m.dom().contains(key);
//             let submap = m.remove(key);
//             Self::map_to_pair_seq(m.remove(key)).push(SpecKVPair{key, value: m[key]})
//         }
//     }

    exec fn hash_map_to_pair_vec(m: &HashMapWithView<<KMarshal as Marshal>::U, <VMarshal as Marshal>::U>)
        -> (out: Vec<KVPair<<KMarshal as Marshal>::U, <VMarshal as Marshal>::U>>)
    ensures out.deepv() == map_to_pair_seq(m.deepv())
    {
        let out = vec!(); // TODO
        assume( out.deepv() == map_to_pair_seq(m.deepv()) );    // LEFT OFF
        out
    }
}

impl<KMarshal: Marshal + UniformSized, VMarshal: Marshal + UniformSized>
Marshal for HashMapFormat<KMarshal, VMarshal>
where
    <KMarshal as Marshal>::U : View<V = <KMarshal as Marshal>::DV> + Eq + Hash,
    <VMarshal as Marshal>::U : View<V = <VMarshal as Marshal>::DV>,
{
    type DV = Map<KMarshal::DV, VMarshal::DV>;
    type U = HashMapWithView<KMarshal::U, VMarshal::U>;

    closed spec fn valid(&self) -> bool
    {
        self.kvpair_format.valid()
    }

    //////////////////////////////////////////////////////////////////////
    // Parsing
    //////////////////////////////////////////////////////////////////////

    closed spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        self.kvpair_format.parsable(data)
    }

    closed spec fn parse(&self, data: Seq<u8>) -> Self::DV
    {
        pair_seq_to_map(self.kvpair_format.parse(data))
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    {
        match self.kvpair_format.try_parse(slice, data) {
            Some(v) => {
                Some(Self::pair_vec_to_hash_map(v))
            },
            None => None,
        }
    }

    exec fn exec_parsable(&self, slice: &Slice, data: &Vec<u8>) -> (p: bool)
    {
        match self.kvpair_format.try_parse(slice, data) {
            Some(v) => true,
            None => false,
        }
    }

    exec fn exec_parse(&self, slice: &Slice, data: &Vec<u8>) -> (value: Self::U)
    {
        Self::pair_vec_to_hash_map(self.kvpair_format.exec_parse(slice, data))
    }

    //////////////////////////////////////////////////////////////////////
    // Marshalling
    //////////////////////////////////////////////////////////////////////

    closed spec fn marshallable(&self, value: Self::DV) -> bool
    {
        &&& value.dom().finite()
        &&& self.kvpair_format.marshallable(map_to_pair_seq(value))
    }

    closed spec fn spec_size(&self, value: Self::DV) -> usize
    {
        self.kvpair_format.spec_size(map_to_pair_seq(value))
    }

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
    {
        self.kvpair_format.exec_size(&Self::hash_map_to_pair_vec(value))
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let pair_vec = &Self::hash_map_to_pair_vec(value);
        assert( pair_vec.deepv() == map_to_pair_seq(value.deepv()) );
        let end = self.kvpair_format.exec_marshall(pair_vec, data, start);
        let ghost bytes = data@.subrange(start as int, end as int);
        proof { pair_seq_map_equiv(value.deepv()) };
        assert( self.kvpair_format.parse(bytes) == pair_vec.deepv() );
        assert( self.parse(bytes) == pair_seq_to_map(self.kvpair_format.parse(bytes)) );
        assert( pair_seq_to_map(map_to_pair_seq(value.deepv())) == value.deepv() );
        assert( value.deepv() == pair_seq_to_map(pair_vec.deepv()) );
        assert( self.parse(bytes) == value.deepv() );
        end
    }
}

}
