// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use builtin::*;
use builtin_macros::*;
// use vstd::pervasive::*;
use vstd::prelude::*;
// use vstd::modes::*;
// use vstd::tokens::InstanceId;
// use vstd::hash_map::*;
// use vstd::std_specs::hash::*;
// 
// use crate::trusted::ClientAPI_t::*;
// use crate::trusted::ReqReply_t::*;
// use crate::trusted::KVStoreTrait_t::*;
// use crate::trusted::KVStoreTokenized_t::*;
// use crate::trusted::ProgramModelTrait_t::*;
// 
// use crate::spec::MapSpec_t::{ID, MapSpec, PersistentState};
// use crate::spec::TotalKMMap_t::*;
// use crate::spec::KeyType_t::*;
// use crate::spec::Messages_t::*;
// use crate::implementation::ModelRefinement_v::*;
// use crate::implementation::ConcreteProgramModel_v::*;
// use crate::implementation::AtomicState_v::*;
// use crate::implementation::MultisetMapRelation_v::*;
// 
// #[allow(unused_imports)]
// use vstd::multiset::*;
// #[allow(unused_imports)]
// use vstd::tokens::*;
// #[allow(unused_imports)]
// use crate::spec::AsyncDisk_t::*;
// use crate::spec::ImplDisk_t::*;
// #[allow(unused_imports)]
// use crate::implementation::DiskLayout_v::*;
use crate::spec::injective_t::*;

verus!{

#[verifier::external_body]
#[inline]
fn structural_equal<T: PartialEq + Structural>(x: &T, y: &T) -> (b: bool)
ensures
    b <==> x == y,
{
    x == y
}

// Structural required for Rust eq to connect to SMT ==
pub struct VecMap<Key,Value>
where Key: View + Injective + Eq + Structural
{
    v: Vec<(Key,Value)>
}

// TODO(jonh): move into verus std lib
// map.rs takes 'Fn's and only gets away with it because it passes them to
// an axiom in set.rs
//     pub open spec fn new(fk: impl Fn(K) -> bool, fv: impl Fn(K) -> V) -> Map<K, V> {

// Build a map from some arbitrary index
// spec fn map_from_index<I,K,V>(fi: impl SpecFn(I) -> bool, fk: impl Fn(I) -> K, fv: impl Fn(I) -> V)
//     -> Map<K,V>
// {
//     Map::new(|k| exists |i| fi(i) && fk(i) == k, |k| fv(choose |i| fi(i) && fk(i)==k) )
// }

impl<Key,Value> VecMap<Key,Value>
where Key: View + Injective + Eq + Structural
{
    pub closed spec fn wf(self) -> bool
    {
        // unique key views
        forall |i,j| #![auto] 0<=i<self.v.len() && 0<=j<self.v.len() && self.v[i].0@ == self.v[j].0@ ==> i == j
    }

    pub fn new() -> (out: Self)
    ensures
        out.wf(),
        out@ == Map::<<Key as View>::V, Value>::empty(),
    {
        let out = Self{v: vec![]};
        assert( out@ == Map::<<Key as View>::V, Value>::empty() );  // trigger extn in ensures
        out
    }
    
    pub fn insert(&mut self, k: Key, v: Value)
    requires
        old(self).wf(),
    ensures
        self.wf(),
        self@ == old(self)@.insert(k@, v),
    {
        assume( false );
    }

    pub fn get<'a>(&'a self, k: &Key) -> (result: Option<&'a Value>)
    requires
        self.wf(),
    ensures
        match result {
            Some(v) => self@.contains_key(k@) && *v == self@[k@],
            None => !self@.contains_key(k@),
        },
    {
        let mut i: usize = 0;
        while i < self.v.len()
        invariant
            0 <= i <= self.v.len(),
            forall |j| #![auto] 0<=j<i ==> self.v[j].0 != *k,
            self.wf(),  // gaaah irritating loop isolation default
        decreases self.v.len() - i,
        {
//             if self.v[i].0.eq(k) {
            if structural_equal(&self.v[i].0, k) {
                let out = &self.v[i].1;
                proof {
                    let ii = choose |ii| #![auto] 0<=ii<self.v.len() && self.v[ii].0@ == k@;
                    let iasint = i as int;
                    assert( 0<=ii<self.v.len() && self.v[ii].0@ == k@ );
                    assert( 0<=iasint<self.v.len() && 0<=ii<self.v.len() && self.v[iasint].0@ == self.v[ii].0@ );
                    assert( iasint == ii );
                    assert( ii == i );
                    assert( self.index_for_key(*k) == Some(i as int) );
                    assert( self@[k@] == self.v[ii].1 );
                    assert( self@[k@] == out );
                }
                return Some(out)
            }
            i += 1;
        }
        // Loop proves that impl k doesn't appear in impl vec, but we also need
        // to know that no other k could have supplied the same view k@:
        proof { Key::lemma_injective(); }
        assert( !self@.contains_key(k@) );
        None
    }

    spec fn index_for_key(&self, k: Key) -> (oi: Option<int>)
    {
        let i = choose |i| #![auto] 0<=i<self.v.len() && self.v[i].0 == k;
        if 0<=i<self.v.len() && self.v[i].0 == k {
            Some(i)
        } else {
            None
        }
    }

    proof fn index_for_key_ensures(&self, k: Key)
    ensures
        match self.index_for_key(k) {
            Some(i) => 0<=i<self.v.len() && self.v[i].0 == k,
            None => forall |i| #![auto] 0<=i<self.v.len() ==> self.v[i].0 != k,
        }
    {
    }
}

impl<Key, Value> View for VecMap<Key, Value>
where Key: View + Injective + Eq + Structural
{
    type V = Map<<Key as View>::V, Value>;

    closed spec fn view(&self) -> Self::V
    {
        Map::new(
            |k| exists |i| #![auto] 0<=i<self.v.len() && self.v[i].0@ == k,
            |k| self.v[choose |i| #![auto] 0<=i<self.v.len() && self.v[i].0@ == k].1)
    }
}

// We didn't want to clone this anyway. Huff.
// impl<Key,Value> Clone for (Key,Value) {
//     fn clone(&self) -> Self {
//         return (self.0.clone(), self.1.clone())
//     }
// }
// 
// impl<Key, Value> Clone for VecMap<Key, Value>
// where Key: View + Eq + Structural
// {
//     fn clone(&self) -> Self {
//         VecMap{v: self.v.clone()}
//     }
// }


}
