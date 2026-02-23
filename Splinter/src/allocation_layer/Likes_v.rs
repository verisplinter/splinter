// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::prelude::*;
use vstd::{map::*,multiset::*};
use crate::disk::GenericDisk_v::{AU, Address, to_aus, to_aus_additive, to_aus_singleton};

verus!{
    pub type Likes = Multiset<Address>;

    pub type AULikes = Multiset<AU>;

    pub open spec(checked) fn no_likes() -> Likes
    {
        Multiset::empty()
    }

    pub open spec(checked) fn all_elems_single<V>(m: Multiset<V>) -> bool
    {
        forall |e| #[trigger] m.contains(e) ==> m.count(e) == 1
    }

    pub closed spec(checked) fn to_au_likes(likes: Likes) -> AULikes
        decreases likes.len()
    {
        if likes.is_empty() {
            Multiset::empty()
        } else {
            let e = likes.choose();
            to_au_likes(likes.remove(e)).insert(e.au)
        }
    }

    pub proof fn to_au_likes_domain(likes: Likes)
        ensures 
            forall |addr| #[trigger] likes.contains(addr) ==> 
                to_au_likes(likes).contains(addr.au),
            to_au_likes(likes).dom() == to_aus(likes.dom()),
        decreases likes.len()
    {
        if likes.len() > 0 {
            let e = likes.choose();
            to_au_likes_domain(likes.remove(e));

            assert forall |addr| #[trigger] likes.contains(addr)
            implies to_au_likes(likes).contains(addr.au)
            by {
                if addr != e {
                    assert(likes.remove(e).contains(addr)); // trigger
                }
            }

            to_aus_singleton(e);
            to_au_likes_singleton(e);

            to_aus_additive(likes.remove(e).dom(), set!{e});
            assert(likes.dom() == likes.remove(e).dom() + set!{e}); // trigger
            to_au_likes_commutative_over_add(likes.remove(e), Multiset::singleton(e));
            assert(to_au_likes(likes).dom() == to_au_likes(likes.remove(e)).dom() + to_au_likes(Multiset::singleton(e)).dom()); // trigger
        } else {
        }
    }

    pub proof fn to_au_likes_singleton(addr: Address) 
        ensures to_au_likes(Multiset::singleton(addr)) == Multiset::singleton(addr.au)
    {
        assert(Multiset::singleton(addr).remove(addr) =~= Multiset::empty()); // trigger
        assert(to_au_likes(Multiset::empty()) == Multiset::<AU>::empty()); // trigger
        // TODO: seems like we need to assert this rather than relying on the ensures?
    }

    // NOTE: same proof as buffer_likes_additive, would be better if we can 
    // generalize this
    #[verifier::spinoff_prover]
    pub proof fn to_au_likes_commutative_over_add(likes: Likes, delta: Likes)
        ensures to_au_likes(likes.add(delta)) =~= to_au_likes(likes).add(to_au_likes(delta))
        decreases likes.len() + delta.len()
    {
        let total = likes.add(delta);

        if likes.len() == 0 {
            assert(total =~= delta); // trigger
        } else if delta.len() == 0 {
            assert(total =~= likes); // trigger
        } else {
            let e = total.choose();
            let sub_au_likes = to_au_likes(total.remove(e));

            to_au_likes_singleton(e);
            if likes.contains(e) {
                to_au_likes_commutative_over_add(likes.remove(e), delta);
                assert(total.remove(e) == likes.remove(e).add(delta)); // trigger
                to_au_likes_commutative_over_add(likes.remove(e), Multiset::singleton(e));
                assert(likes.remove(e).add(Multiset::singleton(e)) == likes); // trigger
            } else {
                to_au_likes_commutative_over_add(likes, delta.remove(e));
                assert(total.remove(e) == likes.add(delta.remove(e))); // trigger
                to_au_likes_commutative_over_add(delta.remove(e), Multiset::singleton(e));
                assert(delta.remove(e).add(Multiset::singleton(e)) == delta); // trigger
            }
        }
    }

    pub proof fn to_au_likes_commutative_over_sub(likes: Likes, delta: Likes)
    requires delta <= likes
    ensures to_au_likes(likes.sub(delta)) == to_au_likes(likes).sub(to_au_likes(delta))
    {
        to_au_likes_commutative_over_add(likes.sub(delta), delta);
        assert(likes.sub(delta).add(delta) == likes); // trigger
    }

    pub open spec fn restrict_domain_au<V>(m: Map<Address, V>, aus: Set<AU>) -> Set<Address>
    {
        m.dom().filter(|addr: Address| aus.contains(addr.au))
    }

    pub proof fn restrict_domain_au_ensures<V>(likes: Likes, m: Map<Address, V>)
        requires likes.dom() <= m.dom()
        ensures likes.dom() <= restrict_domain_au(m, to_au_likes(likes).dom()) 
    {
        let aus = to_au_likes(likes);
        let kept_addrs = restrict_domain_au(m, aus.dom());
    
        to_au_likes_domain(likes);
    
        assert forall |addr| #[trigger] likes.dom().contains(addr)
        implies kept_addrs.contains(addr) 
        by {
            assert(likes.contains(addr)); // trigger
        }
    }

    // pub proof fn single_elems_add<V>(a: Multiset<V>, b: Multiset<V>)
    // requires 
    //     all_elems_single(a),
    //     all_elems_single(b),
    //     a.is_disjoint_from(b),
    // ensures
    //     all_elems_single(a.add(b)),
    //     a.add(b).dom() == a.dom() + b.dom()
    // {
    //     let r = a.add(b);
    //     assert forall |e| #[trigger] r.contains(e)
    //     implies r.count(e) == 1 by
    //     {
    //         assert(a.contains(e) || b.contains(e)); // trigger
    //     }
    // }

    // pub proof fn single_elems_sub<V>(a: Multiset<V>, b: Multiset<V>)
    // requires 
    //     all_elems_single(a),
    //     b <= a,
    // ensures
    //     all_elems_single(a.sub(b)),
    //     a.sub(b).dom() =~= a.dom() - b.dom()
    // {
    //     let r = a.sub(b);
    //     let r_dom = a.dom() - b.dom();
    //     assert forall |e| r.contains(e)
    //     implies r.count(e) == 1 && r_dom.contains(e) 
    //     by {
    //         assert(a.contains(e)); // trigger
    //     }
    // }

    // pub proof fn single_elems_eq<V>(a: Multiset<V>, b: Multiset<V>)
    // requires 
    //     all_elems_single(a),
    //     all_elems_single(b),
    //     a.dom() =~= b.dom(),
    // ensures
    //     a == b
    // {
    //     assert forall |v: V| a.count(v) == b.count(v)
    //     by {
    //         if a.contains(v) {
    //             assert(b.dom().contains(v)); 
    //             assert(b.contains(v)); // trigger
    //         } else if b.contains(v) {
    //             assert(a.dom().contains(v)); 
    //             assert(false);
    //         } 
    //     }
    //     assert(a =~= b);
    // }

    // pub proof fn single_elems_insert_ensures<V>(m: Multiset<V>, new: V)
    // requires all_elems_single(m), !m.contains(new)
    // ensures all_elems_single(m.insert(new))
    // {
    //     let post_m = m.insert(new);
    //     assert forall |e| #[trigger] post_m.contains(e)
    //     implies post_m.count(e) == 1
    //     by {
    //         if e != new {
    //             assert(m.contains(e)); // trigger
    //         }
    //     }
    // }

    // pub proof fn single_elems_subset<V>(a: Multiset<V>, b: Multiset<V>)
    // requires all_elems_single(a), all_elems_single(b), a.dom() <= b.dom()
    // ensures a <= b 
    // {
    //     assert forall |e| true
    //     implies a.count(e) <= b.count(e)
    //     by {
    //         if a.contains(e) {
    //             assert(a.dom().contains(e));
    //             assert(b.contains(e));
    //             assert(b.count(e) == a.count(e));
    //         }
    //     }
    // }

    // pub proof fn single_elems_disjoint<V>(a: Multiset<V>, b: Multiset<V>)
    // requires all_elems_single(a), all_elems_single(b), a.dom().disjoint(b.dom())
    // ensures a.is_disjoint_from(b), all_elems_single(a.add(b)),
    // {
    //     assert forall |e| true
    //     implies a.count(e) == 0 || b.count(e) == 0
    //     by {
    //         if a.count(e) > 0 {
    //             assert(a.dom().contains(e));
    //             assert(!b.dom().contains(e));
    //         }
    //     }
    //     assert(a.is_disjoint_from(b));

    //     assert forall |e| #[trigger] a.add(b).contains(e)
    //     implies a.add(b).count(e) == 1
    //     by {
    //         if a.contains(e) {
    //             assert(!b.contains(e));
    //         } else {
    //             assert(b.contains(e));
    //         }
    //     }
    // }
}

