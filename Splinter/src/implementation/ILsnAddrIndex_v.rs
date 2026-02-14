// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::prelude::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::{Address, IAddress};
use crate::implementation::JournalTypes_v::ILsn;
use crate::allocation_layer::LikesJournal_v::{LsnAddrIndex, lsn_addr_index_append_record, singleton_index};
use crate::implementation::CachedJournal_v::{
    addr_to_lsns,
    complete_lsn_range_for_addr,
    lsn_index_domain_exact,
    all_addrs_have_complete_lsn_ranges,
    all_addrs_have_finite_lsn_sets,
};
 
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
        &&& forall |i: int, j: int| 0 <= i < j < self.addrs.len() ==> self.addrs[i]@ != self.addrs[j]@
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

    proof fn bounds_monotone(&self, i: int, j: int)
        requires
            self.wf(),
            0 <= i <= j < self.bounds.len(),
        ensures
            self.bounds[i] <= self.bounds[j],
        decreases j - i
    {
        if i < j {
            self.bounds_monotone(i, j - 1);
            assert(self.sorted_entry(j - 1));
            assert(self.bounds[j - 1] < self.bounds[j]);
        }
    }

    proof fn i_segment_maps_to_addr(&self, j: int, idx: int, lsn: LSN)
        requires
            self.wf(),
            0 <= idx < j < self.bounds.len(),
            self.bounds[idx] <= lsn < self.bounds[idx + 1],
        ensures
            self.i(j).contains_key(lsn),
            self.i(j)[lsn] == self.addrs[idx]@,
        decreases j - idx
    {
        if j == idx + 1 {
            let update = singleton_index(self.bounds[idx] as nat, self.bounds[idx + 1] as nat, self.addrs[idx]@);
            reveal(lsn_addr_index_append_record);
            assert(self.i(j) == self.i(j - 1).union_prefer_right(update));
            assert(update.contains_key(lsn));
            assert(self.i(j).contains_key(lsn));
            assert(self.i(j)[lsn] == update[lsn]);
        } else {
            self.i_segment_maps_to_addr(j - 1, idx, lsn);
            let update = singleton_index(self.bounds[j - 1] as nat, self.bounds[j] as nat, self.addrs[j - 1]@);
            self.bounds_monotone(idx + 1, j - 1);
            assert(self.bounds[idx + 1] <= self.bounds[j - 1]);
            assert(lsn < self.bounds[j - 1]);
            assert(!update.contains_key(lsn));
            reveal(lsn_addr_index_append_record);
            assert(self.i(j) == self.i(j - 1).union_prefer_right(update));
            assert(self.i(j).contains_key(lsn));
            assert(self.i(j)[lsn] == self.i(j - 1)[lsn]);
        }
    }

    proof fn lsn_maps_to_addr(&self, idx: int, lsn: LSN)
        requires
            self.wf(),
            0 <= idx < self.addrs.len(),
            self.bounds[idx] <= lsn < self.bounds[idx + 1],
        ensures
            self@.contains_key(lsn),
            self@[lsn] == self.addrs[idx]@,
    {
        let j = (self.bounds.len() - 1) as int;
        assert(idx < j);
        self.i_segment_maps_to_addr(j, idx, lsn);
    }

    proof fn addr_at_idx_in_values(&self, idx: int)
        requires
            self.wf(),
            0 <= idx < self.addrs.len(),
        ensures
            self@.values().contains(self.addrs[idx]@),
    {
        assert(self.sorted_entry(idx));
        let lsn = self.bounds[idx] as nat;
        self.lsn_maps_to_addr(idx, lsn);
        assert(self@[lsn] == self.addrs[idx]@);
        assert(self@.contains_key(lsn));
        assert(self@.values().contains(self.addrs[idx]@));
    }

    proof fn find_segment_up_to(&self, lsn: LSN, j: int) -> (idx: int)
        requires
            self.wf(),
            self.bounds[0] <= lsn < self.bounds[j],
            1 <= j < self.bounds.len(),
        ensures
            0 <= idx < j,
            self.bounds[idx] <= lsn < self.bounds[idx + 1],
        decreases j
    {
        if j == 1 {
            0
        } else if lsn < self.bounds[j - 1] {
            self.find_segment_up_to(lsn, j - 1)
        } else {
            (j - 1) as int
        }
    }

    proof fn find_segment(&self, lsn: LSN) -> (idx: int)
        requires
            self.wf(),
            self.seq_start() <= lsn < self.seq_end(),
        ensures
            0 <= idx < self.addrs.len(),
            self.bounds[idx] <= lsn < self.bounds[idx + 1],
    {
        let j = (self.bounds.len() - 1) as int;
        assert(j == self.addrs.len());
        let idx = self.find_segment_up_to(lsn, j);
        idx
    }

    proof fn segment_complete_range(&self, idx: int)
        requires
            self.wf(),
            0 <= idx < self.addrs.len(),
        ensures
            complete_lsn_range_for_addr(
                self@,
                self.seq_start() as nat,
                self.addrs[idx]@,
                self.bounds[idx] as nat,
                self.bounds[idx + 1] as nat,
            ),
    {
        let start_lsn = self.bounds[idx] as nat;
        let end_lsn = self.bounds[idx + 1] as nat;
        self.view_domain();
        self.bounds_monotone(0, idx);
        assert(self.seq_start() as nat <= start_lsn);
        assert(start_lsn < end_lsn) by {
            assert(self.sorted_entry(idx));
        }
        assert(complete_lsn_range_for_addr(
            self@,
            self.seq_start() as nat,
            self.addrs[idx]@,
            start_lsn,
            end_lsn,
        )) by {
            assert forall |lsn: LSN|
                #![trigger self@.contains_key(lsn)]
                #![trigger self@[lsn]]
                self.seq_start() as nat <= lsn ==> {
                    &&& (self@.contains_key(lsn) && self@[lsn] == self.addrs[idx]@)
                        <==> (start_lsn <= lsn < end_lsn)
                } by {
                if start_lsn <= lsn < end_lsn {
                    self.lsn_maps_to_addr(idx, lsn);
                    assert(self@[lsn] == self.addrs[idx]@);
                } else if self@.contains_key(lsn) && self@[lsn] == self.addrs[idx]@ {
                    assert(self.seq_start() <= lsn < self.seq_end());
                    let idx2 = self.find_segment(lsn);
                    self.lsn_maps_to_addr(idx2, lsn);
                    self.lsn_maps_to_addr(idx, start_lsn);
                    assert(self@[lsn] == self.addrs[idx2]@);
                    assert(self@[start_lsn] == self.addrs[idx]@);
                    assert(self@[start_lsn] == self.addrs[idx]@);
                    assert(self@[lsn] == self@[start_lsn]);
                    assert(self.addrs[idx2]@ == self.addrs[idx]@);
                    if idx2 < idx {
                        assert(self.addrs[idx2]@ != self.addrs[idx]@);
                        assert(false);
                    }
                    if idx < idx2 {
                        assert(self.addrs[idx]@ != self.addrs[idx2]@);
                        assert(false);
                    }
                    assert(idx2 == idx);
                    assert(self.bounds[idx2] <= lsn < self.bounds[idx2 + 1]);
                    assert(start_lsn <= lsn < end_lsn);
                }
            };
        };
    }

    pub proof fn derive_complete_ranges(&self)
        requires
            self.wf(),
        ensures
            all_addrs_have_complete_lsn_ranges(self@, self.seq_start() as nat),
    {
        self.view_domain();
        assert forall |addr: Address| #[trigger] self@.values().contains(addr)
            implies exists |start_lsn: LSN, end_lsn: LSN|
                complete_lsn_range_for_addr(self@, self.seq_start() as nat, addr, start_lsn, end_lsn)
        by {
            let lsn0 = choose |lsn: LSN| self@.contains_key(lsn) && self@[lsn] == addr;
            assert(self.seq_start() <= lsn0 < self.seq_end());
            let idx = self.find_segment(lsn0);
            let start_lsn = self.bounds[idx] as nat;
            let end_lsn = self.bounds[idx + 1] as nat;

            self.bounds_monotone(0, idx);
            assert(self.seq_start() as nat <= start_lsn);
            assert(start_lsn < end_lsn);
            assert(complete_lsn_range_for_addr(self@, self.seq_start() as nat, addr, start_lsn, end_lsn)) by {
                assert forall |lsn: LSN|
                    #![trigger self@.contains_key(lsn)]
                    #![trigger self@[lsn]]
                    self.seq_start() as nat <= lsn ==> {
                        &&& (self@.contains_key(lsn) && self@[lsn] == addr)
                            <==> (start_lsn <= lsn < end_lsn)
                    } by {
                    if start_lsn <= lsn < end_lsn {
                        self.lsn_maps_to_addr(idx, lsn);
                        self.lsn_maps_to_addr(idx, lsn0);
                        assert(self@[lsn] == self.addrs[idx]@);
                        assert(self@[lsn0] == self.addrs[idx]@);
                        assert(self@[lsn0] == addr);
                        assert(self@[lsn] == addr);
                    } else if self@.contains_key(lsn) && self@[lsn] == addr {
                        assert(self.seq_start() <= lsn < self.seq_end());
                        let idx2 = self.find_segment(lsn);
                        self.lsn_maps_to_addr(idx2, lsn);
                        self.lsn_maps_to_addr(idx, lsn0);
                        assert(self@[lsn] == self.addrs[idx2]@);
                        assert(self@[lsn0] == self.addrs[idx]@);
                        assert(self@[lsn] == addr);
                        assert(self@[lsn0] == addr);
                        assert(self.addrs[idx2]@ == self.addrs[idx]@);
                        if idx2 < idx {
                            assert(self.addrs[idx2]@ != self.addrs[idx]@);
                            assert(false);
                        }
                        if idx < idx2 {
                            assert(self.addrs[idx]@ != self.addrs[idx2]@);
                            assert(false);
                        }
                        assert(idx2 == idx);
                        assert(start_lsn <= lsn < end_lsn);
                    }
                };
            };
        };

        assert(all_addrs_have_complete_lsn_ranges(self@, self.seq_start() as nat));
    }

    pub proof fn derive_lsn_index_domain_exact(&self)
        requires
            self.wf(),
        ensures
            lsn_index_domain_exact(self@, self.seq_start() as nat, self.seq_end() as nat),
    {
        self.view_domain();
        assert forall |lsn: LSN| #[trigger] self@.contains_key(lsn)
            <==> (self.seq_start() as nat <= lsn < self.seq_end() as nat) by {
            assert(self@.dom().contains(lsn) <==> (self.seq_start() as nat <= lsn < self.seq_end() as nat));
            if self@.contains_key(lsn) {
                assert(self@.dom().contains(lsn));
            } else if self@.dom().contains(lsn) {
                assert(false);
            }
        };
    }

    proof fn nat_lsn_range_finite(start_lsn: LSN, end_lsn: LSN)
        requires
            start_lsn <= end_lsn,
        ensures
            Set::<LSN>::new(|lsn: LSN| start_lsn <= lsn < end_lsn).finite(),
    {
        let int_range = vstd::set_lib::set_int_range(start_lsn as int, end_lsn as int);
        let nat_range = Set::<LSN>::new(|lsn: LSN| start_lsn <= lsn < end_lsn);
        let mapped = int_range.map(|i: int| i as nat);

        vstd::set_lib::lemma_int_range(start_lsn as int, end_lsn as int);
        int_range.lemma_map_finite(|i: int| i as nat);

        assert(nat_range =~= mapped) by {
            assert forall |lsn: LSN| #[trigger] nat_range.contains(lsn)
                implies mapped.contains(lsn) by {
                let i = lsn as int;
                assert(start_lsn as int <= i < end_lsn as int);
                assert(int_range.contains(i));
                assert((i as nat) == lsn);
                assert(mapped.contains(lsn));
            };

            assert forall |lsn: LSN| #[trigger] mapped.contains(lsn)
                implies nat_range.contains(lsn) by {
                let i = choose |i: int| int_range.contains(i) && (i as nat) == lsn;
                assert(start_lsn as int <= i < end_lsn as int);
                assert(0 <= i);
                assert((i as nat) as int == i);
                assert(lsn as int == i) by {
                    assert(i as nat == lsn);
                };
                assert(start_lsn <= lsn);
                assert(lsn < end_lsn);
            };
        };
    }

    pub proof fn derive_all_addrs_have_finite_lsn_sets(&self)
        requires
            self.wf(),
        ensures
            all_addrs_have_finite_lsn_sets(self@, self.seq_start() as nat),
    {
        let bdy = self.seq_start() as nat;
        self.derive_complete_ranges();

        assert forall |addr: Address| #[trigger] self@.values().contains(addr)
            implies addr_to_lsns(self@, addr, bdy).finite() by {
            assert(exists |start_lsn: LSN, end_lsn: LSN|
                complete_lsn_range_for_addr(self@, bdy, addr, start_lsn, end_lsn)) by {
                assert(all_addrs_have_complete_lsn_ranges(self@, bdy));
                assert(self@.values().contains(addr));
            }
            let (start_lsn, end_lsn) = choose |start_lsn: LSN, end_lsn: LSN|
                complete_lsn_range_for_addr(self@, bdy, addr, start_lsn, end_lsn);
            assert(complete_lsn_range_for_addr(self@, bdy, addr, start_lsn, end_lsn));

            let lsns = addr_to_lsns(self@, addr, bdy);
            let interval = Set::<LSN>::new(|lsn: LSN| start_lsn <= lsn < end_lsn);
            assert(lsns =~= interval) by {
                assert forall |lsn: LSN| #[trigger] lsns.contains(lsn)
                    implies interval.contains(lsn) by {
                    assert(bdy <= lsn);
                    assert(self@.contains_key(lsn));
                    assert(self@[lsn] == addr);
                    assert(start_lsn <= lsn < end_lsn) by {
                        assert(complete_lsn_range_for_addr(self@, bdy, addr, start_lsn, end_lsn));
                    }
                };
                assert forall |lsn: LSN| #[trigger] interval.contains(lsn)
                    implies lsns.contains(lsn) by {
                    assert(start_lsn <= lsn < end_lsn);
                    assert(bdy <= start_lsn);
                    assert(bdy <= lsn);
                    assert(self@.contains_key(lsn) && self@[lsn] == addr) by {
                        assert(complete_lsn_range_for_addr(self@, bdy, addr, start_lsn, end_lsn));
                    }
                    assert(lsns.contains(lsn));
                };
            };

            Self::nat_lsn_range_finite(start_lsn, end_lsn);
            assert(interval.finite());
            assert(lsns.finite());
        };

        assert(all_addrs_have_finite_lsn_sets(self@, bdy));
    }

    pub proof fn derive_recovery_index_properties(&self)
        requires
            self.wf(),
        ensures
            lsn_index_domain_exact(self@, self.seq_start() as nat, self.seq_end() as nat),
            all_addrs_have_complete_lsn_ranges(self@, self.seq_start() as nat),
            all_addrs_have_finite_lsn_sets(self@, self.seq_start() as nat),
    {
        self.derive_lsn_index_domain_exact();
        self.derive_complete_ranges();
        self.derive_all_addrs_have_finite_lsn_sets();
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

    pub exec fn lookup_lsn(&self, lsn: ILsn) -> (out: IAddress)
        requires
            self.wf(),
            self.seq_start() <= lsn < self.seq_end(),
        ensures
            self@.contains_key(lsn as nat),
            out@ == self@[lsn as nat],
    {
        let mut i: usize = 0;
        while i < self.addrs.len()
            invariant
                self.wf(),
                i <= self.addrs.len(),
                forall |j: int|
                    #![trigger self.bounds[j]]
                    #![trigger self.bounds[j + 1]]
                    0 <= j < i as int ==> !(self.bounds[j] <= lsn < self.bounds[j + 1]),
            decreases self.addrs.len() - i
        {
            if self.bounds[i] <= lsn && lsn < self.bounds[i + 1] {
                proof {
                    assert(self.bounds.len() == self.addrs.len() + 1);
                    assert(i + 1 < self.bounds.len());
                    assert(i < self.addrs.len());
                    self.lsn_maps_to_addr(i as int, lsn as nat);
                }
                return self.addrs[i];
            }
            proof {
                assert(!(self.bounds[i as int] <= lsn < self.bounds[i as int + 1]));
            }
            i = i + 1;
        }

        proof {
            let idx = self.find_segment(lsn as nat);
            assert(0 <= idx < self.addrs.len());
            assert(i == self.addrs.len());
            assert(0 <= idx < i as int);
            assert(!(self.bounds[idx] <= lsn < self.bounds[idx + 1]));
            assert(self.bounds[idx] <= lsn < self.bounds[idx + 1]);
            assert(false);
        }
        unreached()
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
            !old(self)@.values().contains(addr@),
        ensures
            self.wf(),
            self.seq_start() == new_lower_bound,
            self.seq_end() == old(self).seq_end(),
            self@ == lsn_addr_index_append_record(old(self)@, new_lower_bound as nat, old_lower_bound as nat, addr@),
    {
        let ghost old_snap = *self;

        self.bounds.insert(0, new_lower_bound);
        self.addrs.insert(0, addr);

        proof {
            // wf: sorted
            assert forall |i: int| 0 <= i < self.bounds.len() - 1 implies self.sorted_entry(i) by {
                if i == 0 {
                    // self.bounds[0] = new_lower_bound < old_lower_bound = old_snap.bounds[0] = self.bounds[1]
                } else {
                    assert(old_snap.sorted_entry(i - 1)); // trigger
                }
            }
            assert forall |i: int, j: int| 0 <= i < j < self.addrs.len()
                implies self.addrs[i]@ != self.addrs[j]@ by {
                if i == 0 {
                    assert(self.addrs[i]@ == addr@);
                    assert(self.addrs[j]@ == old_snap.addrs[j - 1]@);
                    old_snap.addr_at_idx_in_values(j - 1);
                    if self.addrs[i]@ == self.addrs[j]@ {
                        assert(old_snap@.values().contains(addr@));
                        assert(!old_snap@.values().contains(addr@));
                        assert(false);
                    }
                } else {
                    assert(self.addrs[i]@ == old_snap.addrs[i - 1]@);
                    assert(self.addrs[j]@ == old_snap.addrs[j - 1]@);
                    assert(old_snap.addrs[i - 1]@ != old_snap.addrs[j - 1]@);
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
