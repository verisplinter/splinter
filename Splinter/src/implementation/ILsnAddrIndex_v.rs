// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::prelude::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::IAddress;
use crate::implementation::JournalTypes_v::ILsn;
use crate::allocation_layer::LikesJournal_v::{LsnAddrIndex, lsn_addr_index_append_record, singleton_index};

verus!{

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
//         if idx > 0 {
//             let prev = self.bounds[idx-1] as nat;
//             let curr = self.bounds[idx] as nat;
// 
//             let (curr_lb, curr_ub) = (prev, curr);
//             assert(self.sorted_entry(idx-1)); // trigger
//             assert(curr_lb < curr_ub);
// 
//             let update = singleton_index(curr_lb, curr_ub, self.addrs[idx-1]@);
//             let (lb, ub) = (self.bounds[0], self.bounds[idx]);
//             self.i_domain(idx-1);
// 
//             assert forall |lsn| #[trigger] self.i(idx).contains_key(lsn) <==> lb <= lsn < ub
//             by {
//                 let out = self.i(idx);
//                 let prev_index = self.i(idx-1);
//                 reveal(ILsnAddrIndex::i);
//                 reveal(lsn_addr_index_append_record);
//                 assert(out == prev_index.union_prefer_right(update));
// 
//                 let (lb_prev, ub_prev) = if self.ascending { (self.bounds[0], self.bounds[idx-1]) }
//                     else { (self.bounds[idx-1], self.bounds[0]) };
//                 assert(prev_index.dom() =~= Set::new(|lsn: LSN| lb_prev <= lsn < ub_prev));
//                 assert(update.contains_key(lsn) <==> (curr_lb <= lsn < curr_ub));
// 
//                 // -> direction
//                 if out.contains_key(lsn) {
//                     if prev_index.contains_key(lsn) {
//                         assert(lb_prev <= lsn < ub_prev);
//                         if self.ascending {
//                             assert(lb_prev == lb);
//                             assert(ub_prev == prev);
//                             self.ascending_bounds_monotone(idx-1);
//                             assert(lb <= lsn < prev);
//                         } else {
//                             assert(lb_prev == prev);
//                             assert(ub_prev == ub);
//                             self.descending_bounds_monotone(idx-1);
//                             assert(prev <= lsn < ub);
//                         }
//                     } else {
//                         assert(update.contains_key(lsn));
//                         assert(curr_lb <= lsn < curr_ub);
//                         if self.ascending {
//                             assert(curr_lb == prev);
//                             assert(curr_ub == curr);
//                             self.ascending_bounds_monotone(idx-1);
//                             assert(prev <= lsn < curr);
//                         } else {
//                             assert(curr_lb == curr);
//                             assert(curr_ub == prev);
//                             assert(curr <= lsn < prev);
//                             self.descending_bounds_monotone(idx-1);
//                         }
//                     }
//                     assert(lb <= lsn < ub);
//                 }
// 
//                 // <- direction
//                 if lb <= lsn < ub {
//                     if self.ascending {
//                         self.ascending_bounds_monotone(idx-1);
//                         if lsn < prev {
//                             assert(prev_index.contains_key(lsn));
//                         } else {
//                             assert(prev <= lsn);
//                             assert(lsn < curr);
//                             assert(update.contains_key(lsn));
//                         }
//                     } else {
//                         self.descending_bounds_monotone(idx-1);
//                         if lsn < prev {
//                             assert(curr <= lsn);
//                             assert(update.contains_key(lsn));
//                         } else {
//                             assert(prev_index.contains_key(lsn));
//                         }
//                     }
//                     assert(out.contains_key(lsn));
//                 }
//             }
//         }
        assume( false );
    }

    proof fn prefix_same_i(self, other: Self, idx: int) 
        requires self.wf(),
            0 <= idx < self.bounds.len(),
            self.bounds@.is_prefix_of(other.bounds@),
            self.addrs@.is_prefix_of(other.addrs@),
        ensures self.i(idx) == other.i(idx)
        decreases idx
    {
        if idx > 0 {
            self.prefix_same_i(other, idx-1);
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

    // Record the fact that every lsn from old_bound .. new_bound maps to addr
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
        assume( false );
        self.bounds.push(new_lower_bound);
        self.addrs.push(addr);

        proof {
            assert(self.bounds@ == old(self).bounds@.push(new_lower_bound));
            assert(self.addrs@ == old(self).addrs@.push(addr));
            assert(self.seq_end() == new_lower_bound);
            if !old(self).is_empty() {
                assert forall |i| 0 <= i < self.bounds.len() - 1
                implies self.sorted_entry(i) by {
                    if i < old(self).bounds.len() - 1 {
                        assert(old(self).sorted_entry(i)); // trigger
                    }
                }
            }
            old(self).prefix_same_i(*self, old(self).bounds.len()-1);
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
