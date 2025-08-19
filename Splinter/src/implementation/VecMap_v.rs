// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::spec::injective_t::*;
use crate::marshalling::WF_v::WF;

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

impl<Key,Value> WF for VecMap<Key,Value>
where Key: View + Injective + Eq + Structural
{
    closed spec fn wf(&self) -> bool
    {
        Self::unique_keys(self.v@)
    }
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
    pub open spec fn unique_keys(s: Seq<(Key, Value)>) -> bool
    {
        forall |i,j| #![auto] 0<=i<s.len() && 0<=j<s.len() && s[i].0@ == s[j].0@ ==> i == j
    }

    pub fn exec_unique_keys(v: &Vec<(Key, Value)>) -> (out: bool)
    ensures out == Self::unique_keys(v@)
    {
        assume(false);  // TODO(jonh): write some code. Only relevant on the try_parse path.
        true
    }

    pub closed spec fn seq_to_map_r(s: Seq<(Key, Value)>) -> Map<Key, Value>
    decreases s.len()
    {
        if s.len() == 0 {
            Map::empty()
        } else {
            let (k,v) = s.last();
            Self::seq_to_map_r(s.drop_last()).insert(k, v)
        }
    }

    pub closed spec fn seq_to_map(s: Seq<(Key, Value)>) -> Map<Key, Value>
    recommends Self::unique_keys(s)
    {
        Map::new(
            |k| exists |i| #![auto] 0<=i<s.len() && s[i].0 == k,
            |k| s[choose |i| #![auto] 0<=i<s.len() && s[i].0 == k].1)
    }

    pub proof fn seq_to_map_ensures(s: Seq<(Key, Value)>)
    requires Self::unique_keys(s),
    ensures
        Self::seq_to_map(s).dom().finite(),
        Self::seq_to_map(s) == Self::seq_to_map_r(s)
    decreases s.len()
    {
        // TODO(jonh): ensmallify proof
        if s.len() == 0 {
            assert( Self::seq_to_map(s) == Map::<Key, Value>::empty() );
            assert( Self::seq_to_map(s).dom().finite() );
            assert( Self::seq_to_map(s) == Self::seq_to_map_r(s) );
        } else {
            let rs = s.drop_last();
            Self::seq_to_map_ensures(rs);
            let (kl,vl) = s.last();
            let ms = Self::seq_to_map(s);
            let rm = Self::seq_to_map(rs);
            assert( rm == Self::seq_to_map(s.drop_last()) );    // from rec call
            let rmi = rm.insert(kl,vl);
            assert forall |k| ms.contains_key(k) implies rmi.contains_key(k) by {
                if k == kl {
                    assert(rmi.contains_key(kl));
                } else {
                    let i = choose |i| #![auto] 0<=i<s.len() && s[i].0 == k;
                    assert(s[i].0 == k);
                    assert(rs[i].0 == k);
                    assert(rm.contains_key(k));
                }
            }
//             assert forall |k| rmi.contains_key(k) implies ms.contains_key(k) by {
//             }
            assert forall |k| #![auto] rmi.contains_key(k) implies rmi[k] == ms[k] by {
                let i = choose |i| #![auto] 0<=i<s.len() && s[i].0 == k;
                assert(ms[k] == s[i].1);
                assert(rmi[k] == s[i].1);
                if k == kl {
                    assert(s[s.len()-1].0 == k);
                    assert(Self::unique_keys(s));
                    assert(i == s.len()-1);
                } else {
                    assert(rs[i].0 == k);
                    assert(rmi[k] == rs[i].1);
                }
            }
            assert( ms == rmi );
            assert( Self::seq_to_map(s).dom().finite() );
            assert( Self::seq_to_map(s) == Self::seq_to_map_r(s) );
        }
    }

    pub closed spec fn map_to_seq(m: Map<Key, Value>) -> (s: Seq<(Key, Value)>)
    decreases m.dom().len() when m.dom().finite()
    {
        if m.dom().is_empty() {
            seq![]
        } else {
            let k = m.dom().choose();
            Self::map_to_seq(m.remove(k)).push((k, m[k]))
        }
    }

    pub proof fn map_to_seq_contents(m: Map<Key, Value>)
    requires m.dom().finite()
    ensures ({
        let s = Self::map_to_seq(m);
            &&& Self::unique_keys(s)
            &&& forall |i| #![auto] 0<=i<s.len() ==> m.contains_key(s[i].0)
            &&& forall |k| m.contains_key(k) ==> exists |i| 0 <= i < s.len() && s[i]==(k, m[k])
        }),
    decreases m.dom().len()
    {
        let s = Self::map_to_seq(m);

        if m.dom().is_empty() {
            assert( forall |i| #![auto] 0<=i<s.len() ==> m.contains_key(s[i].0) );
            assert( forall |k| m.contains_key(k) ==> exists |i| 0 <= i < s.len() && s[i]==(k, m[k]) );
        } else {
            let ck = m.dom().choose();
            let rm = m.remove(ck);
            Self::map_to_seq_contents(rm);
            let rs = Self::map_to_seq(rm);
            Key::lemma_injective(); // needed to prove unique_keys, since it's over key views
                                    //
            assert forall |i| #![auto] 0<=i<s.len() implies m.contains_key(s[i].0) by {
                if i < s.len()-1 {
                    let rs = Self::map_to_seq(m.remove(ck)); // trigger
                }
            }
            assert forall |k| m.contains_key(k) implies exists |i| 0 <= i < s.len() && s[i]==(k, m[k])  by {
                let i = if k == ck {
                    s.len() - 1
                } else {
                    choose |i| 0 <= i < rs.len() && rs[i]==(k, rm[k])
                };
                assert( 0 <= i < s.len() && s[i]==(k, m[k]) );  // provide the witness
            }
        }
    }

    // Yeah you can't have this one, since map_to_seq is nondeterministic!
//     pub proof fn map_to_seq_inverse(v: Seq<(Key, Value)>)
//     requires Self::unique_keys(v)
//     ensures Self::map_to_seq(Self::seq_to_map(v)) == v
//     {
//         Self::map_to_seq_contents(Self::seq_to_map(v));
//     }

    pub proof fn seq_to_map_inverse(m: Map<Key, Value>)
    requires m.dom().finite()
    ensures Self::seq_to_map(Self::map_to_seq(m)) == m
    {
        Self::map_to_seq_contents(m);
        assert( Self::seq_to_map(Self::map_to_seq(m)) == m ); // verus #1534
    }

    pub fn new() -> (out: Self)
    ensures
        out.wf(),
        out@ == Map::<Key, Value>::empty(),
    {
        let out = Self{v: vec![]};
        assert( out@ == Map::<Key, Value>::empty() );  // trigger extn in ensures
        out
    }

    pub fn from_vec(v: Vec<(Key, Value)>) -> (out: Self)
        requires Self::unique_keys(v@)
        ensures out@ == Self::seq_to_map(v@), out.wf()
    {
        Self{v}
    }

    pub fn borrow_vec<'a>(&'a self) -> (out: &'a Vec<(Key, Value)>)
        ensures
            Self::map_to_seq(self@) == (*out)@,
//             (*out)@ == Self::map_to_seq(self@),
    {
        assume(false);  // left off here
//         proof { Self::seq_to_map_inverse(self.v@); }
        &self.v
    }
    
    pub fn insert(&mut self, k: Key, v: Value)
    requires
        old(self).wf(),
    ensures
        self.wf(),
        self@ == old(self)@.insert(k, v),
    {
        // TODO: this is trash, should remove duplicate, not sure if needed for actual ds
        self.v.insert(0, (k, v));
        // need to look for an existing element
        assume( false );
    }

    pub fn get<'a>(&'a self, k: &Key) -> (result: Option<&'a Value>)
    requires
        self.wf(),
    ensures
        match result {
            Some(v) => self@.contains_key(*k) && *v == self@[*k],
            None => !self@.contains_key(*k),
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
                    assert( self@[*k] == self.v[ii].1 );
                    assert( self@[*k] == out );
                }
                return Some(out)
            }
            i += 1;
        }
        // Loop proves that impl k doesn't appear in impl vec, but we also need
        // to know that no other k could have supplied the same view k@:
        proof { Key::lemma_injective(); }
        assert( !self@.contains_key(*k) );
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

    pub proof fn view_ensures(self)
    requires self.wf()
    ensures self@.dom().finite()
    {
        Self::seq_to_map_ensures(self.v@);
    }
}

impl<Key, Value> View for VecMap<Key, Value>
where Key: View + Injective + Eq + Structural
{
    type V = Map<Key, Value>;

    closed spec fn view(&self) -> Self::V
    {
        VecMap::seq_to_map(self.v@)
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
