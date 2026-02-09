// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::prelude::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::IAddress;
use crate::implementation::JournalTypes_v::ILsn;
use crate::allocation_layer::LikesJournal_v::{LsnAddrIndex, lsn_addr_index_append_record, singleton_index};

verus!{

// external_body workaround for: complex arguments to &mut parameters
#[verifier::external_body]
exec fn vec_push_front<T>(v: &mut Vec<T>, value: T)
    ensures v@ == old(v)@.insert(0, value)
{
    v.insert(0, value)
}

pub struct ILsnAddrIndex {
    bounds: Vec<ILsn>,
    addrs: Vec<IAddress>,
}

impl ILsnAddrIndex {
    closed spec fn sorted_entry(&self, idx: int) -> bool
        recommends 0 <= idx < self.bounds.len() - 1
    {
        &&& self.bounds[idx] < self.bounds[idx+1]
    }

    pub closed spec fn wf(&self) -> bool
    {
        &&& self.bounds.len() == self.addrs.len() + 1
        &&& forall |i| 0 <= i < self.bounds.len() - 1 ==> self.sorted_entry(i)
    }

    // TODO maybe delete; does any caller care?
    pub closed spec fn is_empty(&self) -> bool
    {
        &&& self.bounds.len() == 1
        &&& self.addrs.len() == 0
    }

    pub closed spec fn seq_start(self) -> ILsn
    {
        self.bounds[0]
    }

    pub exec fn exec_seq_start(&self) -> (out: ILsn)
        requires self.wf()
        ensures out == self.seq_start()
    {
        self.bounds[0]
    }

    pub closed spec fn seq_end(self) -> ILsn
    {
        self.bounds[self.bounds.len()-1]
    }

    pub exec fn exec_seq_end(&self) -> (out: ILsn)
        requires self.wf()
        ensures out == self.seq_end()
    {
        self.bounds[self.bounds.len()-1]
    }

    closed spec fn i(&self, idx: int) -> LsnAddrIndex
        recommends self.wf(), 0 <= idx < self.bounds.len()
        decreases idx when 0 <= idx < self.bounds.len()
    {
        if idx == 0 {
            map!{}
        } else {
            let curr = self.bounds[idx] as nat;
            let prev = self.bounds[idx-1] as nat;
            lsn_addr_index_append_record(self.i(idx-1), prev, curr, self.addrs[idx-1]@)
        }
    }

    proof fn ascending_bounds_monotone(&self, idx: int)
        requires self.wf(), 0 <= idx < self.bounds.len()
        ensures self.bounds[0] <= self.bounds[idx]
        decreases idx
    {
        if idx > 0 {
            self.ascending_bounds_monotone(idx-1);
            assert(self.sorted_entry(idx-1)); // trigger
        }
    }

    proof fn i_domain(&self, idx: int)
        requires self.wf(), 0 <= idx < self.bounds.len()
        ensures
            self.i(idx).dom() =~= Set::new(|lsn: LSN| self.bounds[0] <= lsn < self.bounds[idx])
        decreases idx
    {
        if idx > 0 {
            let prev = self.bounds[idx-1] as nat;
            let curr = self.bounds[idx] as nat;
            let lb = self.bounds[0] as nat;

            assert(self.sorted_entry(idx-1)); // trigger
            self.i_domain(idx-1);

            let update = singleton_index(prev, curr, self.addrs[idx-1]@);

            assert forall |lsn: LSN| #[trigger] self.i(idx).contains_key(lsn) <==> lb <= lsn < curr
            by {
                let out = self.i(idx);
                let prev_index = self.i(idx-1);
                reveal(lsn_addr_index_append_record);
                assert(out == prev_index.union_prefer_right(update));

                // -> direction
                if out.contains_key(lsn) {
                    self.ascending_bounds_monotone(idx-1);
                }

                // <- direction
                if lb <= lsn < curr {
                    self.ascending_bounds_monotone(idx-1);
                    if lsn < prev {
                        assert(prev_index.contains_key(lsn));
                    } else {
                        assert(update.contains_key(lsn));
                    }
                }
            }
        }
    }

    pub exec fn new(lsn: ILsn) -> (out: Self)
        ensures
            out.wf(),
            out@.is_empty(),
            out.seq_end() == lsn,
            out.seq_start() == lsn,
    {
        ILsnAddrIndex{
            bounds: vec![lsn],
            addrs: vec![],
        }
    }

    exec fn insert_bound_at_front(&mut self, val: ILsn)
    ensures
        self.bounds.len() == old(self).bounds.len() + 1,
        self.bounds[0] == val,
        forall |k: int| 0 <= k < old(self).bounds.len() ==> self.bounds[k + 1] == old(self).bounds[k],
        self.addrs == old(self).addrs,
    {
        vec_push_front(&mut self.bounds, val);
    }

    exec fn insert_addr_at_front(&mut self, val: IAddress)
    ensures
        self.addrs.len() == old(self).addrs.len() + 1,
        self.addrs[0] == val,
        forall |k: int| 0 <= k < old(self).addrs.len() ==> self.addrs[k + 1] == old(self).addrs[k],
        self.bounds == old(self).bounds,
    {
        vec_push_front(&mut self.addrs, val);
    }

    // After inserting a new entry at the front, the spec interpretation at index k
    // equals the old interpretation unioned with the new front range.
    proof fn prepend_i_shift(new_self: Self, old_self: Self, k: int)
        requires
            new_self.wf(),
            old_self.wf(),
            1 <= k < new_self.bounds.len(),
            new_self.bounds.len() == old_self.bounds.len() + 1,
            new_self.addrs.len() == old_self.addrs.len() + 1,
            forall |j: int| 0 <= j < old_self.bounds.len() ==> new_self.bounds[j + 1] == old_self.bounds[j],
            forall |j: int| 0 <= j < old_self.addrs.len() ==> new_self.addrs[j + 1] == old_self.addrs[j],
        ensures
            new_self.i(k) =~= lsn_addr_index_append_record(
                old_self.i(k - 1),
                new_self.bounds[0] as nat,
                new_self.bounds[1] as nat,
                new_self.addrs[0]@,
            )
        decreases k
    {
        reveal(lsn_addr_index_append_record);
        assert(new_self.sorted_entry(0)); // trigger: bounds[0] < bounds[1]
        if k == 1 {
            // Base: new_self.i(1) = lar(new_self.i(0), ...) = lar({}, ...)
            //       old_self.i(0) = {}
            // So both sides are lar({}, new_lb, old_lb, addr).
            assert(old_self.i(0) =~= map!{});
            assert(new_self.i(0) =~= map!{});
        } else {
            Self::prepend_i_shift(new_self, old_self, k - 1);

            let front = singleton_index(new_self.bounds[0] as nat, new_self.bounds[1] as nat, new_self.addrs[0]@);
            let step = singleton_index(old_self.bounds[k-2] as nat, old_self.bounds[k-1] as nat, old_self.addrs[k-2]@);

            old_self.ascending_bounds_monotone(k - 2);

            let A = old_self.i(k - 2);

            // Align bounds/addrs between new_self and old_self
            assert(new_self.bounds[k-1] == old_self.bounds[k-2]);
            assert(new_self.bounds[k] == old_self.bounds[k-1]);
            assert(new_self.addrs[k-1] == old_self.addrs[k-2]);

            // Chain: new_self.i(k) =~= (A ∪_r front) ∪_r step
            assert(new_self.i(k - 1) =~= A.union_prefer_right(front));  // IH
            assert(new_self.i(k) =~= new_self.i(k-1).union_prefer_right(step));
            let lhs = A.union_prefer_right(front).union_prefer_right(step);
            assert(new_self.i(k) =~= lhs);

            // Chain: target =~= (A ∪_r step) ∪_r front
            assert(old_self.i(k - 1) =~= A.union_prefer_right(step));
            let rhs = A.union_prefer_right(step).union_prefer_right(front);

            // Commutativity: front ∩ step = ∅ (front < old_lb <= step)
            assert forall |lsn: LSN| #![auto]
                lhs.contains_key(lsn) == rhs.contains_key(lsn) &&
                (lhs.contains_key(lsn) ==> lhs[lsn] == rhs[lsn])
            by {}

            assert(new_self.i(k) =~= rhs);
            assert(new_self.i(k) =~= lsn_addr_index_append_record(
                old_self.i(k - 1),
                new_self.bounds[0] as nat,
                new_self.bounds[1] as nat,
                new_self.addrs[0]@,
            ));
        }
    }

    // Record the fact that every lsn in [new_lower_bound, old_lower_bound) maps to addr
    pub exec fn index_prepend_record(&mut self, old_lower_bound: ILsn, new_lower_bound: ILsn, addr: IAddress)
        requires
            old(self).wf(),
            old(self).seq_start() == old_lower_bound,
            new_lower_bound < old_lower_bound,
        ensures
            self.wf(),
            self.seq_start() == new_lower_bound,
            self.seq_end() == old(self).seq_end(),
            self@ == lsn_addr_index_append_record(old(self)@, new_lower_bound as nat, old_lower_bound as nat, addr@),
    {
        let ghost old_snap = *self;
        self.insert_bound_at_front(new_lower_bound);
        self.insert_addr_at_front(addr);

        proof {
            // wf: sorted
            assert forall |i: int| 0 <= i < self.bounds.len() - 1 implies self.sorted_entry(i) by {
                if i == 0 {
                    // self.bounds[0] = new_lower_bound < old_lower_bound = old_snap.bounds[0] = self.bounds[1]
                } else {
                    assert(old_snap.sorted_entry(i - 1)); // trigger
                }
            }

            // view equality via the shift lemma
            Self::prepend_i_shift(*self, old_snap, (self.bounds.len() - 1) as int);
        }
    }

    pub proof fn view_domain(&self) 
        requires self.wf()
        ensures self@.dom() =~= Set::new(|lsn: LSN| self.seq_start() <= lsn < self.seq_end())
    {
        self.i_domain(self.bounds.len()-1);
    }
}

impl View for ILsnAddrIndex {
    type V = LsnAddrIndex;

    closed spec fn view(&self) -> Self::V
    {
        self.i(self.bounds.len()-1)
    }
}


}
