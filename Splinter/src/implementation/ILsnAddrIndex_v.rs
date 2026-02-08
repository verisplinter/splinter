// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
// use vstd::hash_map::HashMapWithView;
use crate::abstract_system::MsgHistory_v::{MsgHistory, KeyedMessage};
use crate::abstract_system::StampedMap_v::*;
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::marshalling::KeyedMessageFormat_v::KeyedMessageFormat;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::spec::AsyncDisk_t::RawPage;
use crate::implementation::AtomicState_v::{to_journal_reads, raw_page_to_record};
use crate::implementation::OverflowFiction_v::*;
use crate::implementation::CachedJournal_v::*;
use crate::disk::GenericDisk_v::{Address, IAddress, Pointer};
use crate::implementation::JournalTypes_v::AJournal;
use crate::implementation::JournalTypes_v::ILsn;
use crate::allocation_layer::LikesJournal_v::{LsnAddrIndex, lsn_addr_index_append_record, singleton_index, lsn_disjoint};
use crate::implementation::Cache_v::Cache;
use crate::implementation::FracCacheImpl_v::*;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::IJournalRecordFormat_v::{IJournalRecord, IJournalRecordFormat, IJournalRecordWrappable};
use crate::marshalling::Marshalling_v::Marshal;
use crate::marshalling::Wrappable_v::Wrappable;
use crate::journal::LinkedJournal_v;

verus!{

pub struct ILsnAddrIndex {
    pub bounds: Vec<ILsn>,
    pub addrs: Vec<IAddress>,
    pub ascending: bool,
}

impl ILsnAddrIndex {
    pub closed spec fn seq_start(self) -> ILsn
    {
        if self.ascending {
            self.bounds[0]
        } else {
            self.bounds[self.bounds.len()-1]
        }
    }

    pub exec fn exec_seq_start(&self) -> (out: ILsn)
        requires self.wf(), !self.ascending
        ensures out == self.seq_start()
    {
        self.bounds[self.bounds.len()-1]
    }

    pub closed spec fn seq_end(self) -> ILsn
    {
        if self.ascending {
            self.bounds[self.bounds.len()-1]
        } else {
            self.bounds[0]
        }
    }

    pub exec fn exec_seq_end(&self) -> (out: ILsn)
        requires self.wf(), self.ascending
        ensures out == self.seq_end()
    {
        self.bounds[self.bounds.len()-1]
    }

    pub closed spec fn sorted_entry(&self, idx: int) -> bool
        recommends 0 <= idx < self.bounds.len() - 1
    {
        &&& self.ascending ==> self.bounds[idx] < self.bounds[idx+1]
        &&& !(self.ascending) ==> self.bounds[idx] > self.bounds[idx+1]
    }

    pub closed spec fn is_empty(&self) -> bool
    {
        &&& self.bounds.len() == 1
        &&& self.addrs.len() == 0
    }

    pub closed spec fn wf(&self) -> bool
    {
        ||| self.is_empty()
        ||| {
            &&& self.bounds.len() == self.addrs.len() + 1
            &&& forall |i| 0 <= i < self.bounds.len() - 1 ==> self.sorted_entry(i)
        }
    }

    pub closed spec fn i(&self, idx: int) -> LsnAddrIndex
        recommends self.wf(), 0 <= idx < self.bounds.len()
        decreases idx when idx < self.bounds.len()
    {
        if idx > 0 {
            let curr = self.bounds[idx] as nat;
            let prev = self.bounds[idx-1] as nat;

            if self.ascending {
                lsn_addr_index_append_record(self.i(idx-1), prev, curr, self.addrs[idx-1]@)
            } else {
                lsn_addr_index_append_record(self.i(idx-1), curr, prev, self.addrs[idx-1]@)
            }
        } else {
            map!{}
        }
    }

    proof fn ascending_bounds_monotone(&self, idx: int)
        requires self.wf(), self.ascending, 0 <= idx < self.bounds.len()
        ensures self.bounds[0] <= self.bounds[idx]
        decreases idx
    {
        if idx > 0 {
            self.ascending_bounds_monotone(idx-1);
            assert(self.sorted_entry(idx-1)); // trigger
        }
    }

    proof fn descending_bounds_monotone(&self, idx: int)
        requires self.wf(), !self.ascending, 0 <= idx < self.bounds.len()
        ensures self.bounds[idx] <= self.bounds[0]
        decreases idx
    {
        if idx > 0 {
            self.descending_bounds_monotone(idx-1);
            assert(self.sorted_entry(idx-1)); // trigger
        }
    }

    proof fn i_domain(&self, idx: int) 
        requires self.wf(), 0 <= idx < self.bounds.len()
        ensures ({
            let (lb, ub) = if self.ascending { 
                (self.bounds[0], self.bounds[idx])
            } else {
                (self.bounds[idx], self.bounds[0])
            };
            &&& self.i(idx).dom() =~= Set::new(|lsn: LSN| lb <= lsn < ub)
        })
        decreases idx
    {
        if idx > 0 {
            let prev = self.bounds[idx-1] as nat;
            let curr = self.bounds[idx] as nat;

            let (curr_lb, curr_ub) = if self.ascending { (prev, curr) } else { (curr, prev) };
            assert(self.sorted_entry(idx-1)); // trigger
            assert(curr_lb < curr_ub);

            let update = singleton_index(curr_lb, curr_ub, self.addrs[idx-1]@);
            let (lb, ub) = if self.ascending { (self.bounds[0], self.bounds[idx])
                } else { (self.bounds[idx], self.bounds[0])};
            self.i_domain(idx-1);

            assert forall |lsn| #[trigger] self.i(idx).contains_key(lsn) <==> lb <= lsn < ub
            by {
                let out = self.i(idx);
                let prev_index = self.i(idx-1);
                reveal(ILsnAddrIndex::i);
                reveal(lsn_addr_index_append_record);
                assert(out == prev_index.union_prefer_right(update));

                let (lb_prev, ub_prev) = if self.ascending { (self.bounds[0], self.bounds[idx-1]) }
                    else { (self.bounds[idx-1], self.bounds[0]) };
                assert(prev_index.dom() =~= Set::new(|lsn: LSN| lb_prev <= lsn < ub_prev));
                assert(update.contains_key(lsn) <==> (curr_lb <= lsn < curr_ub));

                // -> direction
                if out.contains_key(lsn) {
                    if prev_index.contains_key(lsn) {
                        assert(lb_prev <= lsn < ub_prev);
                        if self.ascending {
                            assert(lb_prev == lb);
                            assert(ub_prev == prev);
                            self.ascending_bounds_monotone(idx-1);
                            assert(lb <= lsn < prev);
                        } else {
                            assert(lb_prev == prev);
                            assert(ub_prev == ub);
                            self.descending_bounds_monotone(idx-1);
                            assert(prev <= lsn < ub);
                        }
                    } else {
                        assert(update.contains_key(lsn));
                        assert(curr_lb <= lsn < curr_ub);
                        if self.ascending {
                            assert(curr_lb == prev);
                            assert(curr_ub == curr);
                            self.ascending_bounds_monotone(idx-1);
                            assert(prev <= lsn < curr);
                        } else {
                            assert(curr_lb == curr);
                            assert(curr_ub == prev);
                            assert(curr <= lsn < prev);
                            self.descending_bounds_monotone(idx-1);
                        }
                    }
                    assert(lb <= lsn < ub);
                }

                // <- direction
                if lb <= lsn < ub {
                    if self.ascending {
                        self.ascending_bounds_monotone(idx-1);
                        if lsn < prev {
                            assert(prev_index.contains_key(lsn));
                        } else {
                            assert(prev <= lsn);
                            assert(lsn < curr);
                            assert(update.contains_key(lsn));
                        }
                    } else {
                        self.descending_bounds_monotone(idx-1);
                        if lsn < prev {
                            assert(curr <= lsn);
                            assert(update.contains_key(lsn));
                        } else {
                            assert(prev_index.contains_key(lsn));
                        }
                    }
                    assert(out.contains_key(lsn));
                }
            }
        }
    }

    proof fn prefix_same_i(self, other: Self, idx: int) 
        requires self.wf(),
            0 <= idx < self.bounds.len(),
            self.bounds@.is_prefix_of(other.bounds@),
            self.addrs@.is_prefix_of(other.addrs@),
            self.ascending == other.ascending,
        ensures self.i(idx) == other.i(idx)
        decreases idx
    {
        if idx > 0 {
            self.prefix_same_i(other, idx-1);
        }
    }

    pub exec fn new(lsn: ILsn, ascending: bool) -> (out: Self)
        ensures out.wf(), out.ascending == ascending, out@.is_empty(), out.seq_end() == lsn, out.seq_start() == lsn,
    {
        ILsnAddrIndex{
            bounds: vec![lsn],
            addrs: vec![],
            ascending,
        }
    }

    #[verifier::external_body]
    pub exec fn reverse(&mut self)
        requires old(self).wf()
        ensures self.wf(), old(self)@ == self@, self.ascending == !old(self).ascending, 
            old(self).seq_end() == self.seq_end(), old(self).seq_start() == self.seq_start(),
    {
        self.bounds.reverse();
        self.addrs.reverse();
        self.ascending = !(self.ascending);
    }

    pub exec fn index_extend_bound(&mut self, old_bound: ILsn, new_bound: ILsn, addr: IAddress)
        requires 
            old(self).wf(),
            old(self).ascending ==> old(self).seq_end() == old_bound,
            !old(self).ascending ==> old(self).seq_start() == old_bound,
            old(self).ascending ==> old_bound < new_bound,
            !old(self).ascending ==> old_bound > new_bound,
        ensures 
            self.wf(),
            self.ascending == old(self).ascending,
            self.bounds@ == old(self).bounds@.push(new_bound),
            self.addrs@ == old(self).addrs@.push(addr),
            self.ascending ==> self.seq_end() == new_bound,
            !self.ascending ==> self.seq_end() == old(self).seq_end(),
            self.ascending ==> self@ == lsn_addr_index_append_record(old(self)@, old_bound as nat, new_bound as nat, addr@),
            !self.ascending ==> self@ == lsn_addr_index_append_record(old(self)@, new_bound as nat, old_bound as nat, addr@),
    {
        self.bounds.push(new_bound);
        self.addrs.push(addr);

        proof {
            assert(self.bounds@ == old(self).bounds@.push(new_bound));
            assert(self.addrs@ == old(self).addrs@.push(addr));
            if old(self).ascending {
                assert(self.seq_end() == new_bound);
            } else {
                assert(self.seq_end() == old(self).seq_end());
            }
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
