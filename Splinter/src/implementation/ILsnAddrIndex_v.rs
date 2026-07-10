// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::prelude::*;
use vstd::assert_maps_equal;
use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::{Address, AU, IAddress, to_aus, to_aus_domain};
use crate::implementation::AuPoolImpl_v::iau_vec_set;
use crate::implementation::JournalTypes_v::ILsn;
use crate::spec::ImplDisk_t::IAU;
use crate::allocation_layer::LikesJournal_v::{LsnAddrIndex, largest_lsn_plus_one, maxmax, lsn_addr_index_append_record, lsn_addr_index_discard_up_to, singleton_index};
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
        &&& forall |i: int, j: int| #![auto] 0 <= i < j < self.addrs.len() ==> self.addrs[i]@ != self.addrs[j]@
    }

    closed spec fn addrs_values(&self) -> Set<Address>
    {
        Set::new(|addr: Address| exists |i: int| 0 <= i < self.addrs.len() && self.addrs[i]@ == addr)
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

    pub exec fn au_vec(&self) -> (out: Vec<IAU>)
        requires
            self.wf(),
        ensures
            iau_vec_set(out@) =~= to_aus(self@.values()),
    {
        let mut out = Vec::<IAU>::new();
        let mut idx: usize = 0;
        while idx < self.addrs.len()
            invariant
                self.wf(),
                idx <= self.addrs.len(),
                out@.len() == idx,
                forall |i: int| 0 <= i < idx ==> out@[i] as nat == self.addrs[i]@.au,
            decreases self.addrs.len() - idx,
        {
            out.push(self.addrs[idx].au);
            idx = idx + 1;
        }
        proof {
            self.values_match_addrs();
            assert(iau_vec_set(out@) =~= to_aus(self@.values())) by {
                assert forall |au: AU| #[trigger] iau_vec_set(out@).contains(au)
                    implies to_aus(self@.values()).contains(au) by {
                    let i = choose |i: int| 0 <= i < out@.len() && (out@[i] as nat) == au;
                    assert(self@.values().contains(self.addrs[i]@));
                    to_aus_domain(self@.values());
                };
                assert forall |au: AU| #[trigger] to_aus(self@.values()).contains(au)
                    implies iau_vec_set(out@).contains(au) by {
                    let addr = choose |addr: Address| self@.values().contains(addr) && addr.au == au;
                    assert(exists |i: int| 0 <= i < self.addrs.len() && self.addrs[i]@ == addr);
                    let i = choose |i: int| 0 <= i < self.addrs.len() && self.addrs[i]@ == addr;
                    assert(out@[i] as nat == self.addrs[i]@.au);
                };
            };
        }
        out
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

    proof fn i_prefix_unchanged_after_append(old: Self, new: Self, idx: int)
        requires
            old.wf(),
            new.wf(),
            new.bounds.len() == old.bounds.len() + 1,
            new.addrs.len() == old.addrs.len() + 1,
            forall |i: int| 0 <= i < old.bounds.len() ==> new.bounds[i] == old.bounds[i],
            forall |i: int| 0 <= i < old.addrs.len() ==> new.addrs[i] == old.addrs[i],
            0 <= idx < old.bounds.len(),
        ensures
            new.i(idx) == old.i(idx),
        decreases idx
    {
        if idx > 0 {
            Self::i_prefix_unchanged_after_append(old, new, idx - 1);
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

                // -> direction
                if out.contains_key(lsn) {
                    self.ascending_bounds_monotone(idx-1);
                }

                // <- direction
                if lb <= lsn < curr {
                    self.ascending_bounds_monotone(idx-1);
                    if lsn < prev {
                    } else {
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
            assert(self.sorted_entry(j - 1)); // trigger
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
        } else {
            self.i_segment_maps_to_addr(j - 1, idx, lsn);
            let update = singleton_index(self.bounds[j - 1] as nat, self.bounds[j] as nat, self.addrs[j - 1]@);
            self.bounds_monotone(idx + 1, j - 1);
            reveal(lsn_addr_index_append_record);
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
        self.i_segment_maps_to_addr(j, idx, lsn);
    }

    proof fn addr_at_idx_in_values(&self, idx: int)
        requires
            self.wf(),
            0 <= idx < self.addrs.len(),
        ensures
            self@.values().contains(self.addrs[idx]@),
    {
        assert(self.sorted_entry(idx)); // trigger
        let lsn = self.bounds[idx] as nat;
        self.lsn_maps_to_addr(idx, lsn);
    }

    proof fn values_match_addrs(&self)
        requires
            self.wf(),
        ensures
            self@.values() =~= self.addrs_values(),
    {
        assert forall |addr: Address| #[trigger] self@.values().contains(addr)
            implies exists |i: int| 0 <= i < self.addrs.len() && self.addrs[i]@ == addr by {
            let lsn = choose |lsn: LSN| #[trigger] self@.contains_key(lsn) && self@[lsn] == addr;
            self.view_domain();
            let idx = self.find_segment(lsn);
            self.lsn_maps_to_addr(idx, lsn);
            assert(self.addrs[idx]@ == addr);
        };
        assert forall |addr: Address| #[trigger] self.addrs_values().contains(addr)
            implies self@.values().contains(addr) by {
            let i = choose |i: int| 0 <= i < self.addrs.len() && self.addrs[i]@ == addr;
            self.addr_at_idx_in_values(i);
        };
    }

    pub exec fn contains_addr(&self, addr: &IAddress) -> (out: bool)
        requires
            self.wf(),
        ensures
            out == self@.values().contains(addr@),
    {
        let mut idx: usize = 0;
        while idx < self.addrs.len()
            invariant
                self.wf(),
                idx <= self.addrs.len(),
                forall |i: int| 0 <= i < idx ==> self.addrs[i]@ != addr@,
            decreases self.addrs.len() - idx,
        {
            if self.addrs[idx].au == addr.au && self.addrs[idx].page == addr.page {
                proof {
                    assert(self.addrs[idx as int]@.au == addr@.au);
                    assert(self.addrs[idx as int]@.page == addr@.page);
                    assert(self.addrs[idx as int]@ == addr@);
                    self.addr_at_idx_in_values(idx as int);
                }
                return true;
            }
            proof {
                if self.addrs[idx as int]@ == addr@ {
                    assert(self.addrs[idx as int]@.au == addr@.au);
                    assert(self.addrs[idx as int]@.page == addr@.page);
                    assert(self.addrs[idx as int].au == addr.au);
                    assert(self.addrs[idx as int].page == addr.page);
                    assert(false);
                }
                assert(self.addrs[idx as int]@ != addr@);
            }
            idx = idx + 1;
        }
        proof {
            self.values_match_addrs();
            assert(!self.addrs_values().contains(addr@)) by {
                if self.addrs_values().contains(addr@) {
                    let i = choose |i: int| 0 <= i < self.addrs.len() && self.addrs[i]@ == addr@;
                    assert(i < idx);
                    assert(self.addrs[i]@ != addr@);
                    assert(false);
                }
            }
        }
        false
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
        assert(start_lsn < end_lsn) by {
            assert(self.sorted_entry(idx)); // trigger
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
                } else if self@.contains_key(lsn) && self@[lsn] == self.addrs[idx]@ {
                    let idx2 = self.find_segment(lsn);
                    self.lsn_maps_to_addr(idx2, lsn);
                    self.lsn_maps_to_addr(idx, start_lsn);
                    if idx2 < idx {
                    }
                    if idx < idx2 {
                    }
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
            let lsn0 = choose |lsn: LSN| #![auto] self@.contains_key(lsn) && self@[lsn] == addr;
            let idx = self.find_segment(lsn0);
            let start_lsn = self.bounds[idx] as nat;
            let end_lsn = self.bounds[idx + 1] as nat;

            self.bounds_monotone(0, idx);
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
                    } else if self@.contains_key(lsn) && self@[lsn] == addr {
                        let idx2 = self.find_segment(lsn);
                        self.lsn_maps_to_addr(idx2, lsn);
                        self.lsn_maps_to_addr(idx, lsn0);
                        if idx2 < idx {
                        }
                        if idx < idx2 {
                        }
                    }
                };
            };
        };

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
            if self@.contains_key(lsn) {
            } else if self@.dom().contains(lsn) {
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
                assert(int_range.contains(i)); // trigger
            };

            assert forall |lsn: LSN| #[trigger] mapped.contains(lsn)
                implies nat_range.contains(lsn) by {
                let i = choose |i: int| int_range.contains(i) && (i as nat) == lsn;
                assert(lsn as int == i);
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
                complete_lsn_range_for_addr(self@, bdy, addr, start_lsn, end_lsn));
            let (start_lsn, end_lsn) = choose |start_lsn: LSN, end_lsn: LSN|
                complete_lsn_range_for_addr(self@, bdy, addr, start_lsn, end_lsn);

            let lsns = addr_to_lsns(self@, addr, bdy);
            let interval = Set::<LSN>::new(|lsn: LSN| start_lsn <= lsn < end_lsn);
            assert(lsns =~= interval) by {
                assert forall |lsn: LSN| #[trigger] lsns.contains(lsn)
                    implies interval.contains(lsn) by {
                    assert(start_lsn <= lsn < end_lsn);
                };
                assert forall |lsn: LSN| #[trigger] interval.contains(lsn)
                    implies lsns.contains(lsn) by {
                    assert(self@.contains_key(lsn) && self@[lsn] == addr);
                };
            };

            Self::nat_lsn_range_finite(start_lsn, end_lsn);
        };

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

    pub exec fn lookup_lsn_with_segment_end(&self, lsn: ILsn) -> (out: (IAddress, ILsn))
        requires
            self.wf(),
            self.seq_start() <= lsn < self.seq_end(),
        ensures
            self@.contains_key(lsn as nat),
            out.0@ == self@[lsn as nat],
            lsn < out.1,
            out.1 <= self.seq_end(),
            self@.restrict(Set::new(|k: LSN| lsn <= k < out.1)).values() == set![out.0@],
            forall |other_lsn: LSN| #![auto]
                self@.contains_key(other_lsn) && self@[other_lsn] == out.0@
                    ==> other_lsn < out.1,
            largest_lsn_plus_one(self@, Some(out.0@)) == out.1 as nat,
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
                let out_addr = self.addrs[i];
                let out_end = self.bounds[i + 1];
                proof {
                    let ii = i as int;
                    self.lsn_maps_to_addr(i as int, lsn as nat);
                    self.bounds_monotone((i + 1) as int, (self.bounds.len() - 1) as int);
                    let seg_index = self@.restrict(Set::new(|k: LSN| lsn <= k < out_end));
                    let seg_values = self@.restrict(Set::new(|k: LSN| lsn <= k < out_end)).values();
                    assert(seg_values =~= set![out_addr@]) by {
                        assert forall |a: Address| #[trigger] seg_values.contains(a) implies set![out_addr@].contains(a) by {
                            let k = choose |k: LSN| #![auto] seg_index.contains_key(k) && seg_index[k] == a;
                            assert(self@.contains_key(k));
                            assert(lsn <= k < out_end);
                            assert(self.bounds[ii] <= k < self.bounds[ii + 1]) by {
                                assert(self.bounds[ii] <= lsn);
                                assert(out_end == self.bounds[ii + 1]);
                            }
                            self.lsn_maps_to_addr(ii, k);
                            assert(a == out_addr@);
                        };
                        assert(seg_values.contains(out_addr@)) by {
                            assert(self@.contains_key(lsn as nat));
                            assert(self@[lsn as nat] == out_addr@) by {
                                self.lsn_maps_to_addr(ii, lsn as nat);
                            }
                            assert(seg_index.contains_key(lsn as nat));
                        }
                    };

                    assert(self@[(out_end - 1) as nat] == out_addr@) by {
                        assert(self.bounds[ii] <= (out_end - 1) as nat);
                        assert(((out_end - 1) as nat) < (self.bounds[ii + 1] as nat)) by {
                            assert(self.bounds[ii + 1] == out_end);
                            assert(self.bounds[ii] <= lsn < out_end);
                            assert(lsn < out_end);
                        }
                        self.lsn_maps_to_addr(ii, (out_end - 1) as nat);
                    }

                    assert forall |other_lsn: LSN| #![auto]
                        self@.contains_key(other_lsn) && self@[other_lsn] == out_addr@
                        implies other_lsn < out_end by {
                        self.view_domain();
                        assert(self.seq_start() <= other_lsn < self.seq_end());
                        let idx2 = self.find_segment(other_lsn);
                        self.lsn_maps_to_addr(idx2, other_lsn);
                        self.lsn_maps_to_addr(ii, lsn as nat);
                        if idx2 < ii {
                            assert(self.addrs[idx2]@ != self.addrs[ii]@);
                            assert(false);
                        }
                        if ii < idx2 {
                            assert(self.addrs[ii]@ != self.addrs[idx2]@);
                            assert(false);
                        }
                        assert(idx2 == ii);
                        assert(self.bounds[ii] <= other_lsn < self.bounds[ii + 1]);
                    };

                    let end_minus_one = (out_end - 1) as nat;
                    assert(maxmax(self@, out_addr@, end_minus_one)) by {
                        assert(self.bounds[ii] <= end_minus_one < self.bounds[ii + 1]) by {
                            assert(self.bounds[ii + 1] == out_end);
                            assert(self.bounds[ii] <= lsn < out_end);
                            assert(lsn < out_end);
                        }
                        self.lsn_maps_to_addr(ii, end_minus_one);
                        assert forall |other_lsn: LSN| #![auto]
                            self@.contains_key(other_lsn) && self@[other_lsn] == out_addr@
                            implies other_lsn <= end_minus_one by {
                            assert(other_lsn < out_end);
                            if other_lsn > end_minus_one {
                                assert(other_lsn >= out_end);
                                assert(false);
                            }
                        };
                    }
                    let max_lsn = choose |m: LSN| maxmax(self@, out_addr@, m);
                    assert(max_lsn <= end_minus_one);
                    assert(end_minus_one <= max_lsn);
                }
                return (out_addr, out_end);
            }
            i = i + 1;
        }

        proof {
            let idx = self.find_segment(lsn as nat);
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
            assert(new_self.i(0) =~= map!{}); // trigger
        } else {
            Self::prepend_i_shift(new_self, old_self, k - 1);

            let front = singleton_index(new_self.bounds[0] as nat, new_self.bounds[1] as nat, new_self.addrs[0]@);
            let step = singleton_index(old_self.bounds[k-2] as nat, old_self.bounds[k-1] as nat, old_self.addrs[k-2]@);

            old_self.ascending_bounds_monotone(k - 2);

            let A = old_self.i(k - 2);

            // Align bounds/addrs between new_self and old_self

            // Chain: new_self.i(k) =~= (A ∪_r front) ∪_r step
            let lhs = A.union_prefer_right(front).union_prefer_right(step);

            // Chain: target =~= (A ∪_r step) ∪_r front
            let rhs = A.union_prefer_right(step).union_prefer_right(front);

            // Commutativity: front ∩ step = ∅ (front < old_lb <= step)
            assert forall |lsn: LSN| #![auto]
                lhs.contains_key(lsn) == rhs.contains_key(lsn) &&
                (lhs.contains_key(lsn) ==> lhs[lsn] == rhs[lsn])
            by {
                assert(lhs.contains_key(lsn) == rhs.contains_key(lsn));
                if lhs.contains_key(lsn) {
                    assert(lhs[lsn] == rhs[lsn]);
                }
            }

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
            assert forall |i: int, j: int| #![auto] 0 <= i < j < self.addrs.len()
                implies self.addrs[i]@ != self.addrs[j]@ by {
                if i == 0 {
                    old_snap.addr_at_idx_in_values(j - 1);
                    if self.addrs[i]@ == self.addrs[j]@ {
                    }
                } else {
                }
            }

            // view equality via the shift lemma
            Self::prepend_i_shift(*self, old_snap, (self.bounds.len() - 1) as int);
        }
    }

    pub exec fn discard_up_to(&mut self, new_lower_bound: ILsn)
        requires
            old(self).wf(),
            old(self).seq_start() <= new_lower_bound <= old(self).seq_end(),
        ensures
            self.wf(),
            self.seq_start() == new_lower_bound,
            self.seq_end() == old(self).seq_end(),
            self@ == lsn_addr_index_discard_up_to(old(self)@, new_lower_bound as nat),
    {
        if new_lower_bound == self.bounds[0] {
            proof {
                let discarded = lsn_addr_index_discard_up_to(self@, new_lower_bound as nat);
                self.view_domain();
                crate::allocation_layer::LikesJournal_v::lsn_addr_index_discard_up_to_ensures(
                    self@,
                    new_lower_bound as nat,
                );
                assert_maps_equal!(self@, discarded, lsn => {
                    if self@.contains_key(lsn) {
                        assert(self.seq_start() as nat <= lsn);
                        assert(new_lower_bound as nat <= lsn);
                        assert(discarded.contains_key(lsn));
                        assert(discarded[lsn] == self@[lsn]);
                    }
                });
            }
            return;
        }

        if new_lower_bound == self.bounds[self.bounds.len() - 1] {
            let ghost old_view = self@;
            self.bounds = vec![new_lower_bound];
            self.addrs = vec![];
            proof {
                assert(old_view == old(self)@);
                assert(self.wf());
                assert(self.bounds.len() == 1);
                assert(self.addrs.len() == 0);
                let ghost discarded = lsn_addr_index_discard_up_to(old_view, new_lower_bound as nat);
                self.i_domain(0);
                old(self).i_domain(old(self).bounds.len() - 1);
                assert_maps_equal!(self@, discarded, lsn => {
                    if self@.contains_key(lsn) {
                        assert(self@.dom().contains(lsn));
                        assert(self.bounds[0] <= lsn < self.bounds[0]);
                        assert(false);
                    }
                    if discarded.contains_key(lsn) {
                        assert(old_view.contains_key(lsn));
                        assert(old_view.dom().contains(lsn));
                        assert(old(self).seq_start() <= lsn < old(self).seq_end());
                        assert(new_lower_bound == old(self).seq_end());
                        assert(false);
                    }
                });
                assert(self@ == discarded);
                assert(lsn_addr_index_discard_up_to(old_view, new_lower_bound as nat)
                    == lsn_addr_index_discard_up_to(old(self)@, new_lower_bound as nat));
                assert(self@ == lsn_addr_index_discard_up_to(old(self)@, new_lower_bound as nat));
            }
            assert(self@ == lsn_addr_index_discard_up_to(old(self)@, new_lower_bound as nat));
            return;
        }

        let ghost old_self = *self;
        let mut idx: usize = 0;
        while idx < self.addrs.len()
            invariant
                old_self.wf(),
                old_self.seq_start() < new_lower_bound < old_self.seq_end(),
                idx <= old_self.addrs.len(),
                idx == 0 || old_self.bounds[idx as int] <= new_lower_bound,
                *self == old_self,
            decreases old_self.addrs.len() - idx
        {
            if self.bounds[idx] <= new_lower_bound && new_lower_bound < self.bounds[idx + 1] {
                break;
            }
            proof {
                if idx == 0 {
                    assert(old_self.bounds[0] == old_self.seq_start());
                    assert(old_self.bounds[0] < new_lower_bound);
                } else {
                    assert(old_self.bounds[idx as int] <= new_lower_bound);
                }
                assert(self.bounds[idx as int] <= new_lower_bound);
                assert(!(self.bounds[idx as int] <= new_lower_bound && new_lower_bound < self.bounds[(idx + 1) as int]));
                assert(self.bounds[(idx + 1) as int] <= new_lower_bound);
            }
            idx += 1;
        }

        let ghost suffix_bounds = old_self.bounds@.subrange(
            (idx + 1) as int,
            old_self.bounds@.len() as int,
        );
        let ghost suffix_addrs = old_self.addrs@.subrange(
            idx as int,
            old_self.addrs@.len() as int,
        );
        let mut new_bounds = self.bounds.split_off(idx + 1);
        let new_addrs = self.addrs.split_off(idx);
        proof {
            assert(new_bounds@ == suffix_bounds);
            assert(new_addrs@ == suffix_addrs);
        }
        new_bounds.insert(0, new_lower_bound);
        self.bounds = new_bounds;
        self.addrs = new_addrs;

        proof {
            assert(idx < old_self.addrs.len()) by {
                if !(idx < old_self.addrs.len()) {
                    assert(idx == old_self.addrs.len());
                    assert(old_self.bounds[old_self.addrs.len() as int + 0] == old_self.seq_end());
                    assert(old_self.bounds[idx as int] == old_self.seq_end());
                    assert(old_self.seq_end() <= new_lower_bound);
                    assert(false);
                }
            }
            assert(old_self.bounds[idx as int] <= new_lower_bound < old_self.bounds[(idx + 1) as int]);

            assert(self.bounds.len() == self.addrs.len() + 1);
            assert forall |i: int| 0 <= i < self.bounds.len() - 1 implies self.sorted_entry(i) by {
                if i == 0 {
                    assert(self.bounds[0] == new_lower_bound);
                    assert(self.bounds[1] == old_self.bounds[(idx + 1) as int]);
                    assert(new_lower_bound < old_self.bounds[(idx + 1) as int]);
                } else {
                    assert(self.bounds[i] == old_self.bounds[(idx as int) + i]);
                    assert(self.bounds[i + 1] == old_self.bounds[(idx as int) + i + 1]);
                    assert(old_self.sorted_entry((idx as int) + i));
                }
            }
            assert forall |i: int, j: int| #![auto] 0 <= i < j < self.addrs.len() implies self.addrs[i]@ != self.addrs[j]@ by {
                assert(self.addrs[i] == old_self.addrs[(idx as int) + i]);
                assert(self.addrs[j] == old_self.addrs[(idx as int) + j]);
                assert(old_self.addrs[(idx as int) + i]@ != old_self.addrs[(idx as int) + j]@);
            }
            assert(self.bounds@ == suffix_bounds.insert(0, new_lower_bound));
            assert(self.addrs@ == suffix_addrs);
            assert(self.bounds[0] == new_lower_bound);
            assert forall |j: int| 0 <= j < self.addrs.len()
                implies #[trigger] self.addrs[j] == old_self.addrs[(idx as int) + j] by {
                assert(self.addrs@ == suffix_addrs);
            }
            assert forall |j: int| 1 <= j < self.bounds.len()
                implies #[trigger] self.bounds[j] == old_self.bounds[(idx as int) + j] by {
                assert(self.bounds@ == suffix_bounds.insert(0, new_lower_bound));
            }

            let discarded = lsn_addr_index_discard_up_to(old_self@, new_lower_bound as nat);
            old_self.view_domain();
            self.view_domain();
            crate::allocation_layer::LikesJournal_v::lsn_addr_index_discard_up_to_ensures(
                old_self@,
                new_lower_bound as nat,
            );
            assert_maps_equal!(self@, discarded, lsn => {
                if self@.contains_key(lsn) {
                    assert(self.seq_start() as nat <= lsn < self.seq_end() as nat);
                    assert(self.seq_start() == new_lower_bound);
                    let new_segment = self.find_segment(lsn);
                    let old_segment = (idx as int) + new_segment;
                    assert(0 <= old_segment < old_self.addrs.len());
                    assert(self.addrs[new_segment] == old_self.addrs[old_segment]);
                    if new_segment == 0 {
                        assert(old_self.bounds[idx as int] <= new_lower_bound);
                        assert(old_self.bounds[idx as int] <= lsn);
                        assert(self.bounds[1] == old_self.bounds[(idx + 1) as int]);
                        assert(lsn < old_self.bounds[(idx + 1) as int]);
                    } else {
                        assert(self.bounds[new_segment]
                            == old_self.bounds[old_segment]);
                        assert(self.bounds[new_segment + 1]
                            == old_self.bounds[old_segment + 1]);
                    }
                    old_self.lsn_maps_to_addr(old_segment, lsn);
                    self.lsn_maps_to_addr(new_segment, lsn);
                    assert(old_self@[lsn] == self@[lsn]);
                    assert(discarded.contains_key(lsn));
                    assert(discarded[lsn] == old_self@[lsn]);
                }

                if discarded.contains_key(lsn) {
                    assert(old_self@.contains_key(lsn));
                    assert(new_lower_bound as nat <= lsn);
                    let old_segment = old_self.find_segment(lsn);
                    assert((idx as int) <= old_segment) by {
                        if old_segment < idx {
                            old_self.bounds_monotone(old_segment + 1, idx as int);
                            assert(lsn < old_self.bounds[old_segment + 1]);
                            assert(old_self.bounds[old_segment + 1]
                                <= old_self.bounds[idx as int]);
                            assert(old_self.bounds[idx as int] <= new_lower_bound);
                            assert(false);
                        }
                    }
                    let new_segment = old_segment - (idx as int);
                    assert(0 <= new_segment < self.addrs.len());
                    assert(self.addrs[new_segment] == old_self.addrs[old_segment]);
                    if new_segment == 0 {
                        assert(self.bounds[0] == new_lower_bound);
                        assert(self.bounds[1] == old_self.bounds[old_segment + 1]);
                    } else {
                        assert(self.bounds[new_segment] == old_self.bounds[old_segment]);
                        assert(self.bounds[new_segment + 1]
                            == old_self.bounds[old_segment + 1]);
                    }
                    self.lsn_maps_to_addr(new_segment, lsn);
                    old_self.lsn_maps_to_addr(old_segment, lsn);
                    assert(self@[lsn] == old_self@[lsn]);
                    assert(discarded[lsn] == old_self@[lsn]);
                }
            });
        }
    }

    // Record the fact that every lsn in [old_upper_bound, new_upper_bound) maps to addr
    pub exec fn index_append_record(&mut self, old_upper_bound: ILsn, new_upper_bound: ILsn, addr: IAddress)
        requires
            old(self).wf(),
            old(self).seq_end() == old_upper_bound,
            old(self).seq_start() <= old_upper_bound,
            old_upper_bound < new_upper_bound,
            !old(self)@.values().contains(addr@),
        ensures
            self.wf(),
            self.seq_start() == old(self).seq_start(),
            self.seq_end() == new_upper_bound,
            self@ == lsn_addr_index_append_record(old(self)@, old_upper_bound as nat, new_upper_bound as nat, addr@),
    {
        self.bounds.push(new_upper_bound);
        self.addrs.push(addr);

        proof {
            // sortedness at the new boundary edge
            assert forall |i: int| 0 <= i < self.bounds.len() - 1 implies self.sorted_entry(i) by {
                if i < old(self).bounds.len() - 1 {
                    assert(old(self).sorted_entry(i));
                } else {
                    assert(i == old(self).bounds.len() - 1);
                    assert(self.bounds[i] == old_upper_bound);
                    assert(self.bounds[i + 1] == new_upper_bound);
                }
            }
            // addrs remain distinct, using caller-provided freshness
            assert forall |i: int, j: int| #![auto] 0 <= i < j < self.addrs.len()
                implies self.addrs[i]@ != self.addrs[j]@ by {
                if j < old(self).addrs.len() {
                } else {
                    assert(j == old(self).addrs.len());
                    if i < old(self).addrs.len() {
                        old(self).addr_at_idx_in_values(i);
                        if self.addrs[i]@ == self.addrs[j]@ {
                        }
                    }
                }
            }

            assert(forall |i: int| 0 <= i < old(self).bounds.len()
                ==> self.bounds[i] == old(self).bounds[i]);
            assert(forall |i: int| 0 <= i < old(self).addrs.len()
                ==> self.addrs[i] == old(self).addrs[i]);

            // New top-level view is one append step over the old top-level view.
            let new_last = (self.bounds.len() - 1) as int;
            assert(new_last == old(self).bounds.len());
            assert(self.i(new_last) =~= lsn_addr_index_append_record(
                self.i(new_last - 1),
                self.bounds[new_last - 1] as nat,
                self.bounds[new_last] as nat,
                self.addrs[new_last - 1]@,
            ));
            Self::i_prefix_unchanged_after_append(*old(self), *self, new_last - 1);
            assert(self.i(new_last - 1) == old(self).i(new_last - 1));
            assert(old(self).i(new_last - 1) == old(self)@);
            assert(self.bounds[new_last - 1] == old_upper_bound);
            assert(self.bounds[new_last] == new_upper_bound);
            assert(self.addrs[new_last - 1] == addr);
        }
    }

    pub proof fn view_domain(&self) 
        requires self.wf()
        ensures self@.dom() =~= Set::new(|lsn: LSN| self.seq_start() <= lsn < self.seq_end())
    {
        self.i_domain(self.bounds.len()-1);
    }

    pub proof fn seq_start_le_seq_end(&self)
        requires self.wf()
        ensures self.seq_start() <= self.seq_end()
    {
        self.ascending_bounds_monotone(self.bounds.len() - 1);
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
