// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;
use vstd::bytes::*;
use vstd::slice::*;
use vstd::hash_map::*;
use vstd::set_lib::*;
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

pub struct HashMapFormat<KMarshal: Marshal + UniformSized, VMarshal: Marshal + UniformSized>
where KMarshal::U : Eq + Hash
{
    // underlying formatter is a seq of k,v pairs
    kvpair_format: ResizableUniformSizedElementSeqFormat<KVPairFormat<HashablePair<KMarshal, VMarshal>>, u16>,
}

impl<KMarshal: Marshal + UniformSized, VMarshal: Marshal + UniformSized> HashMapFormat<KMarshal, VMarshal>
where KMarshal::U : Eq + Hash
{
    pub fn new(kformat: KMarshal, vformat: VMarshal) -> Self
    {
        let total_size = 7;
        let kvpair_format = KVPairFormat::new(IntFormat::new(), kformat, vformat);
        assume( kvpair_format.valid() );    // left off wip
        Self{ kvpair_format: ResizableUniformSizedElementSeqFormat::new(kvpair_format, IntFormat::new(), total_size) }
    }
}

// impl<KMarshal: Marshal + Eq + Hash, VMarshal: Marshal>
// Deepview<Map<KMarshal::DV, VMarshal::DV>> for HashMapWithView<KMarshal::U, VMarshal::U> {
// impl<KDV,KU,VDV,VU>
// Deepview<Map<KDV,VDV>> for HashMapWithView<KU,VU>
// where
//     KU : View<V = KDV> + Deepview<KDV> + Eq + Hash,
//     VU : View<V = VDV> + Deepview<VDV>,
// //     KDV = <KU as View>::V,
// //     VDV = <VU as View>::V,
// {
//     // TODO Our "deep" view of the keys & values is only a View. Hrrm.
//     open spec fn deepv(&self) -> Map<KDV, VDV>
//     {
//         Map::new(|k| self@.dom().contains(k), |k| self@[k]@)
//     }
// }

spec fn map_to_pair_seq<K,V>(m: Map<K,V>) -> (out: Seq<SpecKVPair<K, V>>)
{
    choose |ord| pair_seq_to_map(ord) == m
}

proof fn map_to_pair_seq_ensures<K,V>(m: Map<K,V>)
ensures unique_keys(map_to_pair_seq(m))
{
    assume(false);
}

spec fn unique_keys<K,V>(pairs: Seq<SpecKVPair<K,V>>) -> bool
{
    forall |i1, i2| #![auto] 0<=i1<pairs.len() && 0<=i2<pairs.len() && pairs[i1].key == pairs[i2].key
        ==> i1 == i2
}

spec fn unique_elts<T>(seq: Seq<T>) -> bool
{
    forall |i1, i2| #![auto] 0<=i1<seq.len() && 0<=i2<seq.len() && seq[i1] == seq[i2] ==> i1 == i2
}

spec fn seq_to_set<T>(seq: Seq<T>) -> Set<T>
{
    Set::new(|t| exists |idx| 0<=idx<seq.len() && seq[idx] == t)
}

proof fn seq_to_set_size<T>(seq: Seq<T>)
requires unique_elts(seq)
ensures
    seq_to_set(seq).finite(),
    seq_to_set(seq).len() == seq.len(),
decreases seq.len()
{
    if seq.len() == 0 {
        assert( seq_to_set(seq) == Set::<T>::empty() );    // extn to trigger length axiom
        return;
    }

    let rseq = seq.drop_last();
    seq_to_set_size(rseq);

    // Establish set equivalence, from which both postconditions follow
    let set1 = seq_to_set(seq);
    let set2 = seq_to_set(rseq).insert(seq.last());

    assert forall |t| set1.contains(t) implies set2.contains(t) by {
        if seq.last()!=t {
            let idx = choose |idx| 0<=idx<seq.len() && seq[idx]==t;
            assert(rseq[idx] == t); // witness
        }
    }
    assert( set1 == set2 );
}

// proof fn unique_keys_implies_uniq_elts<K,V>(pairs: Seq<SpecKVPair<K,V>>)
// requires unique_keys(pairs)
// ensures unique_elts(pairs)
// {
// }

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

proof fn idx_for_key<K,V>(a: Seq<SpecKVPair<K,V>>, k: K) -> (ai: int)
requires
    unique_keys(a),
    pair_seq_to_map(a).contains_key(k),
ensures
    0<=ai<a.len() && a[ai].key == k
decreases a.len()
{
    if a.last().key == k {
        a.len() - 1
    } else {
        idx_for_key(a.drop_last(), k)
    }
}

proof fn idx_implies_map<K,V>(a: Seq<SpecKVPair<K,V>>, ai: int)
requires
    unique_keys(a),
    0<=ai<a.len(),
ensures
    pair_seq_to_map(a).contains_key(a[ai].key),
    pair_seq_to_map(a)[a[ai].key] == a[ai].value,
decreases a.len()
{
    if ai == a.len() - 1 {
        // trigger something
        assert( pair_seq_to_map(a) == pair_seq_to_map(a.drop_last()).insert(a[ai].key, a[ai].value) );
    } else {
        idx_implies_map(a.drop_last(), ai); // recurse
    }
}

spec fn pairs_agree_on_values<K,V>(a: Seq<SpecKVPair<K,V>>, b: Seq<SpecKVPair<K,V>>) -> bool
{
    forall |ai, bi| #![auto] 0<=ai<a.len() && 0<=bi<b.len() && a[ai].key == b[bi].key
        ==> a[ai].value == b[bi].value
}

spec fn pair_seqs_comport<K,V>(a: Seq<SpecKVPair<K,V>>, b: Seq<SpecKVPair<K,V>>) -> bool
{
    &&& unique_keys(a)
    &&& unique_keys(b)
    &&& seq_to_set(a) == seq_to_set(b)
    &&& pairs_agree_on_values(a, b)
}

proof fn pair_seq_order_equiv<K,V>(a: Seq<SpecKVPair<K,V>>, b: Seq<SpecKVPair<K,V>>)
requires
    pair_seqs_comport(a, b),
ensures
    pair_seq_to_map(a) == pair_seq_to_map(b),
decreases a.len()
{
    let am = pair_seq_to_map(a);
    let bm = pair_seq_to_map(b);

    assert forall |k| am.contains_key(k) implies bm.contains_key(k) by {
        let ai = idx_for_key(a, k);
        assert( seq_to_set(a).contains(a[ai]) );    // trigger
        let bi = choose |bi| #![auto] 0<=bi<b.len() && b[bi].key == k;
        idx_implies_map(b, bi);
    }
    // wolog swap a & b...
    assert forall |k| bm.contains_key(k) implies am.contains_key(k) by {
        let bi = idx_for_key(b, k);
        assert( seq_to_set(b).contains(b[bi]) );    // trigger
        let ai = choose |ai| #![auto] 0<=ai<a.len() && a[ai].key == k;
        idx_implies_map(a, ai);
    }
    assert forall |k| #![auto] am.contains_key(k) implies am[k] == bm[k] by {
        let ai = idx_for_key(a, k);
        let bi = idx_for_key(b, k);
        idx_implies_map(a, ai);
        idx_implies_map(b, bi);
    }
    assert( pair_seq_to_map(a) == pair_seq_to_map(b) ); // extn not triggered by postcond
}

proof fn pair_seq_map_equiv<K,V>(m: Map<K,V>)
requires m.dom().finite()
ensures pair_seq_to_map(map_to_pair_seq(m)) == m
decreases m.dom().len()
{
    assume(false);  // LEFT OFF silly puzzle
    if m.dom().len() != 0 {
        let key = m.dom().choose();
        let rm = m.remove(key);
        // seq extn
        assert( map_to_pair_seq(rm).push(SpecKVPair{key, value: m[key]}).drop_last()
            == map_to_pair_seq(rm) );

        let last = SpecKVPair{key, value: m[key]};

        assert( map_to_pair_seq(m).len() != 0 ) by { assume(false); } // left off
        let mseq = map_to_pair_seq(m);
        assert( pair_seq_to_map(mseq) ==
            pair_seq_to_map(mseq.drop_last()).insert(mseq.last().key, mseq.last().value) );

        // recurse
        pair_seq_map_equiv(rm);
        assert( pair_seq_to_map(map_to_pair_seq(rm)) == rm );

        let reordered_seq = map_to_pair_seq(rm).push(last);
        map_to_pair_seq_ensures(rm);
        map_to_pair_seq_ensures(m);
        assert forall |i1, i2| #![auto] 0<=i1<reordered_seq.len() && 0<=i2<reordered_seq.len() && reordered_seq[i1].key == reordered_seq[i2].key
            implies i1 == i2 by {
            if i1 < reordered_seq.len()-1 {
                idx_implies_map(map_to_pair_seq(rm), i1);
            }
            if i2 < reordered_seq.len()-1 {
                idx_implies_map(map_to_pair_seq(rm), i2);
            }
        }
//         assert( unique_keys(reordered_seq) ) by {
//         }
//         assert( unique_keys(mseq) );
        assert forall |k| seq_to_set(reordered_seq).contains(k)
            implies seq_to_set(mseq).contains(k) by {
            
            if k == last {
                assert( seq_to_set(mseq).contains(k) );
            } else {
                assert( seq_to_set(mseq).contains(k) );
            }
        }
        assert forall |k| seq_to_set(mseq).contains(k)
            implies seq_to_set(reordered_seq).contains(k) by {
        }
        assert( seq_to_set(reordered_seq) == seq_to_set(mseq) );
        assert( pairs_agree_on_values(reordered_seq, mseq) );
        
        assert( pair_seqs_comport(reordered_seq, mseq) );
        pair_seq_order_equiv(map_to_pair_seq(rm).push(last), mseq);

//         assert( m == rm.insert(key, m[key]) );
//         assert( rm == pair_seq_to_map(map_to_pair_seq(rm)) );
// 
//         assert( map_to_pair_seq(m).last() == last );
//         assert( map_to_pair_seq(m)
//             == map_to_pair_seq(m).drop_last().push(last) );
// 
//         pair_seq_order_equiv(
//             map_to_pair_seq(rm).push(SpecKVPair{key, value: m[key]}).drop_last(),
//             map_to_pair_seq(rm) );
// 
// 
//         assert( map_to_pair_seq(m).drop_last().push(last) == map_to_pair_seq(m) );

        assert( pair_seq_to_map(map_to_pair_seq(m)) == m ); // map extn
    } else {
        if map_to_pair_seq(m).len() > 0 {
            assert( m.dom().contains(map_to_pair_seq(m)[0].key) );
            assert(false);
        }
        assert( map_to_pair_seq(m).len() == 0 );
        assert( pair_seq_to_map(map_to_pair_seq(m)) == Map::<K,V>::empty() );
        assert( pair_seq_to_map(map_to_pair_seq(m)) == m ); // map extn
    }
    // map extn
}

spec fn view_injective<T: View>() -> bool
{
    forall |e1: T, e2: T| e1@==e2@ ==> e1==e2
}

// spec fn view_is_deepview<T: View + Deepview<<T as View>::V>>() -> bool
// {
//     forall |e: T| #![auto] e@ == e.deepv()
// }

impl<KMarshal: Marshal + UniformSized, VMarshal: Marshal + UniformSized>
HashMapFormat<KMarshal, VMarshal>
where
    <KMarshal as Marshal>::U : View + Eq + Hash,
    HashMapWithView<KMarshal::U, VMarshal::U>: Deepview<Map<KMarshal::DV, VMarshal::DV>>
// where
//     <KMarshal as Marshal>::U : View<V = <KMarshal as Marshal>::DV> + Eq + Hash,
//     <VMarshal as Marshal>::U : View<V = <VMarshal as Marshal>::DV>,
{
    exec fn pair_vec_to_hash_map(mut pair_vec: Vec<KVPair<<KMarshal as Marshal>::U, <VMarshal as Marshal>::U>>)
        -> (out: HashMapWithView<<KMarshal as Marshal>::U, <VMarshal as Marshal>::U>)
    requires
        obeys_key_model::<<KMarshal as Marshal>::U>(),
        view_injective::<<KMarshal as Marshal>::U>(),
//         view_is_deepview::<<KMarshal as Marshal>::U>(),
//         view_is_deepview::<<VMarshal as Marshal>::U>(),
    ensures out.deepv() == pair_seq_to_map(pair_vec.deepv())
    {
        let ghost orig_pair_vec = pair_vec.deepv();

        let mut hm = HashMapWithView::new();
        let ghost count = 0;

        // TODO(verus): this extn equality didn't trigger itself in the invariant context;
        // had to utter it out loud to get it to go.
        // TODO assume wip due to removal of view_is_deepview
        assume( hm.deepv() == pair_seq_to_map(orig_pair_vec.take(count)) ); // extn
        assert( orig_pair_vec == orig_pair_vec.subrange(count, orig_pair_vec.len() as int) ); // extn

        while 0 < pair_vec.len()
        invariant
            count == orig_pair_vec.len() - pair_vec.len(),
            0 <= count <= orig_pair_vec.len(),
            hm.deepv() == pair_seq_to_map(orig_pair_vec.take(count)),
            pair_vec.deepv() == orig_pair_vec.subrange(count, orig_pair_vec.len() as int),
        decreases pair_vec.len(),
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
                // TODO assume wip due to removal of view_is_deepview
                assume( hm.deepv() == pair_seq_to_map(oc.drop_last()).insert(last.key, last.value) );

                // loop invariant extn trigger failure
                assert( pair_vec.deepv() == orig_pair_vec.subrange(count, orig_pair_vec.len() as int) );
            }
        }
        hm
    }

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
    <KMarshal as Marshal>::U : View + Eq + Hash,
    HashMapWithView<KMarshal::U, VMarshal::U>: Deepview<Map<KMarshal::DV, VMarshal::DV>>
// This type-equality constraint is here because we're trying to relate the View
// of HashMapWithView to the result of the Marshaling library taking the deepv()
// of the same thing. Maybe it would be easier to simply demand a deepv on
// HashMapWithView and make any further relation the caller's problem?
// where
//     <KMarshal as Marshal>::U : View<V = <KMarshal as Marshal>::DV> + Eq + Hash,
//     <VMarshal as Marshal>::U : View<V = <VMarshal as Marshal>::DV>,
{
    type DV = Map<KMarshal::DV, VMarshal::DV>;
    type U = HashMapWithView<KMarshal::U, VMarshal::U>;

    closed spec fn valid(&self) -> bool
    {
        &&& obeys_key_model::<<KMarshal as Marshal>::U>()
        &&& view_injective::<<KMarshal as Marshal>::U>()
//         &&& view_is_deepview::<<KMarshal as Marshal>::U>()   // TODO remove view_is_deepview
//         &&& view_is_deepview::<<VMarshal as Marshal>::U>()
        &&& self.kvpair_format.valid()
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
