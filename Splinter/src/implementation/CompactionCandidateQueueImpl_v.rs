// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::assert_seqs_equal;

use crate::spec::ImplDisk_t::IAddress;
use crate::spec::KeyType_t::Key;

verus! {

#[derive(Debug, Copy, Clone)]
pub struct CompactionCandidate {
    pub route_key: Key,
    pub target_addr: IAddress,
    pub target_depth: usize,
    pub fuel: usize,
    pub start: usize,
    pub end: usize,
}

impl CompactionCandidate {
    pub open spec fn wf(&self) -> bool {
        &&& self.target_depth < self.fuel
        &&& self.start < self.end
    }

    pub open spec fn same_job(&self, other: &Self) -> bool {
        &&& self.target_addr@ == other.target_addr@
        &&& self.target_depth == other.target_depth
        &&& self.start == other.start
        &&& self.end == other.end
    }

    fn exec_wf(&self) -> (out: bool)
        ensures out == self.wf(),
    {
        self.target_depth < self.fuel && self.start < self.end
    }

    fn exec_same_job(&self, other: &Self) -> (out: bool)
        ensures out == self.same_job(other),
    {
        self.target_addr.au == other.target_addr.au
            && self.target_addr.page == other.target_addr.page
            && self.target_depth == other.target_depth
            && self.start == other.start
            && self.end == other.end
    }
}

#[derive(Debug, Copy, Clone)]
pub enum CompactionEnqueueResult {
    Enqueued,
    Noop,
}

pub struct CompactionCandidateQueue {
    pub entries: Vec<CompactionCandidate>,
    pub capacity: usize,
}

impl CompactionCandidateQueue {
    pub open spec fn entries_wf(&self) -> bool {
        forall |i: int| 0 <= i < self.entries@.len()
            ==> (#[trigger] self.entries@[i]).wf()
    }

    pub open spec fn entries_unique(&self) -> bool {
        forall |i: int, j: int| 0 <= i < j < self.entries@.len()
            ==> !(#[trigger] self.entries@[i].same_job(&self.entries@[j]))
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.capacity > 0
        &&& self.entries@.len() <= self.capacity
        &&& self.entries_wf()
        &&& self.entries_unique()
    }

    pub fn new(capacity: usize) -> (out: Self)
        requires capacity > 0,
        ensures
            out.wf(),
            out.entries@.len() == 0,
            out.capacity == capacity,
    {
        Self {
            entries: Vec::new(),
            capacity,
        }
    }

    pub fn len(&self) -> (out: usize)
        ensures out as nat == self.entries@.len(),
    {
        self.entries.len()
    }

    pub fn is_empty(&self) -> (out: bool)
        ensures out == (self.entries@ == Seq::<CompactionCandidate>::empty()),
    {
        let out = self.entries.len() == 0;
        proof {
            if out {
                assert(self.entries@
                    == Seq::<CompactionCandidate>::empty()) by {
                    assert_seqs_equal!(
                        self.entries@,
                        Seq::<CompactionCandidate>::empty(),
                        i => {}
                    );
                }
            } else if self.entries@
                == Seq::<CompactionCandidate>::empty()
            {
                assert(self.entries@.len() == 0);
            }
        }
        out
    }

    pub fn is_full(&self) -> (out: bool)
        requires self.wf(),
        ensures out == (self.entries@.len() == self.capacity),
    {
        self.entries.len() == self.capacity
    }

    pub fn contains(&self, candidate: &CompactionCandidate) -> (out: bool)
        ensures
            out <==> exists |i: int| 0 <= i < self.entries@.len()
                && (#[trigger] self.entries@[i]).same_job(candidate),
    {
        let mut index = 0usize;
        while index < self.entries.len()
            invariant
                index <= self.entries.len(),
                forall |i: int| 0 <= i < index
                    ==> !(#[trigger] self.entries@[i]).same_job(candidate),
            decreases self.entries.len() - index,
        {
            if self.entries[index].exec_same_job(candidate) {
                return true;
            }
            index += 1;
        }
        false
    }

    pub fn push(
        &mut self,
        candidate: CompactionCandidate,
    ) -> (out: CompactionEnqueueResult)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.capacity == old(self).capacity,
            match out {
                CompactionEnqueueResult::Enqueued => {
                    &&& self.entries@
                        == old(self).entries@.push(candidate)
                    &&& candidate.wf()
                    &&& old(self).entries@.len() < old(self).capacity
                    &&& forall |i: int|
                        0 <= i < old(self).entries@.len()
                            ==> !(#[trigger] old(self).entries@[i])
                                .same_job(&candidate)
                },
                CompactionEnqueueResult::Noop => {
                    &&& self.entries@ == old(self).entries@
                    &&& (!candidate.wf()
                        || old(self).entries@.len() == old(self).capacity
                        || exists |i: int|
                            0 <= i < old(self).entries@.len()
                                && (#[trigger] old(self).entries@[i])
                                    .same_job(&candidate))
                },
            },
    {
        if !candidate.exec_wf()
            || self.entries.len() == self.capacity
            || self.contains(&candidate)
        {
            return CompactionEnqueueResult::Noop;
        }

        let ghost old_entries = self.entries@;
        self.entries.push(candidate);
        proof {
            assert(self.entries_wf()) by {
                assert forall |i: int| 0 <= i < self.entries@.len()
                    implies (#[trigger] self.entries@[i]).wf() by {
                    if i == old_entries.len() {
                        assert(self.entries@[i] == candidate);
                    } else {
                        assert(self.entries@[i] == old_entries[i]);
                    }
                }
            }
            assert(self.entries_unique()) by {
                assert forall |i: int, j: int|
                    0 <= i < j < self.entries@.len()
                    implies !(#[trigger] self.entries@[i]
                        .same_job(&self.entries@[j])) by {
                    if j == old_entries.len() {
                        assert(self.entries@[j] == candidate);
                        assert(self.entries@[i] == old_entries[i]);
                    } else {
                        assert(self.entries@[i] == old_entries[i]);
                        assert(self.entries@[j] == old_entries[j]);
                    }
                }
            }
        }
        CompactionEnqueueResult::Enqueued
    }

    pub fn pop(&mut self) -> (out: Option<CompactionCandidate>)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.capacity == old(self).capacity,
            match out {
                Some(candidate) => {
                    &&& old(self).entries@.len() > 0
                    &&& candidate == old(self).entries@[0]
                    &&& self.entries@ == old(self).entries@.drop_first()
                },
                None => {
                    &&& old(self).entries@.len() == 0
                    &&& self.entries@ == old(self).entries@
                },
            },
    {
        if self.entries.len() == 0 {
            return None;
        }
        let candidate = self.entries.remove(0);
        proof {
            assert(self.entries@ == old(self).entries@.drop_first());
            assert(self.entries_wf()) by {
                assert forall |i: int| 0 <= i < self.entries@.len()
                    implies (#[trigger] self.entries@[i]).wf() by {
                    assert(self.entries@[i] == old(self).entries@[i + 1]);
                }
            }
            assert(self.entries_unique()) by {
                assert forall |i: int, j: int|
                    0 <= i < j < self.entries@.len()
                    implies !(#[trigger] self.entries@[i]
                        .same_job(&self.entries@[j])) by {
                    assert(self.entries@[i] == old(self).entries@[i + 1]);
                    assert(self.entries@[j] == old(self).entries@[j + 1]);
                }
            }
        }
        Some(candidate)
    }

    pub fn clear(&mut self)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.capacity == old(self).capacity,
            self.entries@.len() == 0,
    {
        self.entries.clear();
    }
}

} // verus!
