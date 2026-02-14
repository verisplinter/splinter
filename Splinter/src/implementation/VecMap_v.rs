// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
//use vstd::prelude_macros::*;
use vstd::prelude::*;
use crate::spec::injective_t::Injective;
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
    pub v: Vec<(Key,Value)>
}

impl<Key,Value> WF for VecMap<Key,Value>
where Key: View + Injective + Eq + Structural + Clone
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
where Key: View + Injective + Eq + Structural + Clone
{
    pub open spec fn unique_keys(s: Seq<(Key, Value)>) -> bool
    {
        forall |i,j| #![auto] 0<=i<s.len() && 0<=j<s.len() && s[i].0@ == s[j].0@ ==> i == j
    }

    pub fn exec_unique_keys(v: &Vec<(Key, Value)>) -> (out: bool)
    ensures out == Self::unique_keys(v@)
    {
        // The code for this would need to put keys in a HashSet, requiring the keys to be Hash.
        // Maybe there should be a way to declare we aren't implementing try_parse?
        // Dumb quadratic algorithm.
        let len = v.len();
        let mut x_idx = 0usize;
        while x_idx < len
        invariant
            len == v.len(), // bah
            0 <= x_idx <= len,
            // every key before x_idx is unique
            forall |xl, xo| #![auto] 0 <= xl < x_idx && 0 <= xo < len && v[xl].0 == v[xo].0 ==> xl == xo,
        decreases len-x_idx
        {
            let kx = v[x_idx].0.clone();
            assume( kx == v[x_idx as int].0 );  // clone trouble
            let mut y_idx = x_idx + 1;
            while y_idx < len
            invariant
                // bah, outer invariants
                len == v.len(), // bah
                0 <= x_idx <= len,
                forall |xl, xo| #![auto] 0 <= xl < x_idx && 0 <= xo < len && v[xl].0 == v[xo].0 ==> xl == xo,
                kx == v[x_idx as int].0,

                x_idx < y_idx <= len,
                // x_idx is unique wrt every index before y
                forall |yy| #![auto] 0 <= yy < y_idx && v[x_idx as int].0 == v[yy].0 ==> x_idx == yy,
            decreases len-y_idx
            {
                let ky = v[y_idx].0.clone();
                assume( ky == v[y_idx as int].0 );  // clone trouble
                if Self::compare_keys(&kx, &ky) {
                    proof {
                        let s = v@;
                        let i = x_idx as int;
                        let j = y_idx as int;
                        assert( 0<=i<s.len() && 0<=j<s.len() && s[i].0@ == s[j].0@ && i != j );
                    }
                    return false;
                }
                let ghost old_y_idx = y_idx;
                y_idx += 1;
                assert forall |yy| #![auto] 0 <= yy < y_idx && v[x_idx as int].0 == v[yy].0 implies x_idx == yy by {
                    if yy < old_y_idx { assert( x_idx == yy ); }
                    else {
                        assert( yy == old_y_idx );
                        assert( v[yy].0 == ky );
                        assert( v[yy].0 != kx );
                        assert( x_idx == yy );
                    }
                }
            }
            x_idx += 1;
        }
        proof {
            assert( forall |xl, xo| #![auto] 0 <= xl < x_idx && 0 <= xo < len && v[xl].0 == v[xo].0 ==> xl == xo );
            let s = v@;
            assert forall |i,j| #![auto] 0<=i<s.len() && 0<=j<s.len() && s[i].0@ == s[j].0@ implies i == j by {
                let (xl,xo) = if i < j { (i,j) } else { (j,i) };
                assert( s[xl].0@ == s[xo].0@ );
                Key::lemma_injective(); // needed to prove unique_keys, since it's over key views
//                 assert( s[xl].0@ == v[xl].0 ); // need to apply injectiveness
                assert( 0 <= xl < x_idx && 0 <= xo < len && v[xl].0 == v[xo].0 );
                assert( xl == xo );
            }
        }
        return true;
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
        Self::seq_to_map(s) == Self::seq_to_map_r(s),
        Self::seq_to_map(s).len() == s.len(),
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

    // pretty accessor to seq_to_map ctor.
    pub proof fn index_in_seq(s: Seq<(Key, Value)>, k: Key) -> (idx: int)
    requires
        Self::seq_to_map(s).contains_key(k),
    ensures
        0<=idx<s.len(),
        s[idx].0 == k,
    {
        choose |i| #![auto] 0<=i<s.len() && s[i].0 == k
    }

    // unneeded
    pub proof fn seq_to_map_index(s: Seq<(Key, Value)>, i: int)
    requires
        Self::unique_keys(s),
        0<=i<s.len(),
    ensures Self::seq_to_map(s)[s[i].0] == s[i].1
    {
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
            &&& m.len() == s.len()
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

    pub closed spec fn as_seq(&self) -> (out: Seq<(Key, Value)>)
    {
        self.v@
    }

    pub fn borrow_vec<'a>(&'a self) -> (out: &'a Vec<(Key, Value)>)
        ensures
            Self::seq_to_map((*out)@) == self@,
            out@ == self.as_seq(),
    {
        &self.v
    }

    #[verifier::external_body]
    pub fn compare_keys(k1: &Key, k2: &Key) -> (out: bool)
    ensures (*k1 == *k2) <==> out
    {
        *k1 == *k2
    }
    
    pub fn insert(&mut self, k: Key, v: Value)
    requires
        old(self).wf(),
    ensures
        self.wf(),
        self@ == old(self)@.insert(k, v),
    {
        proof { Key::lemma_injective(); }

        let mut idx:usize = 0;
        let test_k = k.clone();
        assume( test_k == k );  // clone!
        let write_k = k;
        let len = self.v.len();
        // look for an existing element to replace. Yay linear search.
        while idx < len
        invariant
            self.wf(),
            len == self.v.len(),
            idx <= len,
            test_k == k,
            write_k == k,
            forall |i| #![auto] 0 <= i < idx ==> self.v[i].0 != k,
            *old(self) == *self,
        decreases len - idx
        {
            if Self::compare_keys(&self.v[idx].0, &test_k) {
                // replace existing key case
                let ghost os = self.v@;
                let ghost iidx = idx as int;
                self.v[idx] = (write_k,v);

                assert( self@ == old(self)@.insert(k, v) ) by {
                    assert forall |kk| #![auto] old(self)@.insert(k,v).contains_key(kk)
                        implies self@.contains_key(kk) by {
                        if k == kk {
                            Self::seq_to_map_index(self.v@, iidx);
                        } else {
                            let kki = Self::index_in_seq(os, kk);
                            Self::seq_to_map_index(self.v@, kki);
                        }
                    }
                    assert( self@ == old(self)@.insert(k, v) ); // verus failure to trigger extn on assert-by
                }
                return;
            }
            idx += 1;
        }

        // push case
        let ghost os = self.v@;
        self.v.push((write_k, v));
        let ghost s = self.v@;
        assert( self@ == old(self)@.insert(k, v) ) by {
            let ghost iidx = idx as int;
            assert forall |kk| #![auto] old(self)@.insert(k,v).contains_key(kk)
                implies self@.contains_key(kk) by {
                if k == kk {
                    Self::seq_to_map_index(self.v@, iidx);
                } else {
                    let kki = Self::index_in_seq(os, kk);
                    Self::seq_to_map_index(self.v@, kki);
                }
            }
            assert( self@ == old(self)@.insert(k, v) ); // verus failure to trigger extn on assert-by
        }
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
where Key: View + Injective + Eq + Structural + Clone
{
    type V = Map<Key, Value>;

    open spec fn view(&self) -> Self::V
    {
        VecMap::seq_to_map(self.v@)
    }
}

impl<Key: Clone, Value: Clone> VecMap<Key,Value>
where Key: View + Injective + Eq + Structural
{
    #[verifier::external_body]
    pub fn clone(&self) -> (out: Self)
        ensures out == self
    {
        // Argh, Tuple () isn't Clone!
        let mut out = vec![];
        for (key,value) in &self.v {
            out.push((key.clone(), value.clone()));
        }
        VecMap{v: out}
    }
}

}
