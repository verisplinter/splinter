// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_seqs_equal};
use vstd::arithmetic::div_mod::{group_div_basics, lemma_fundamental_div_mod};

use crate::allocation_layer::BranchTypes_v::{BranchNode, Summary};
use crate::betree::LinkedBranch_v::LinkedBranch;
use crate::disk::GenericDisk_v::{Address, addrs_closed};
use crate::implementation::BranchBulkBuilderImpl_v::{
    BranchChildDescriptor, BranchSubtreeReceipt,
    descriptor_forest_contents, descriptor_forest_nodes,
    descriptor_forest_wf, descriptor_pivots,
    descriptor_sequence_wf, finalize_index_seal, finalize_leaf_seal,
    index_from_descriptors, leaf_entries_contents, leaf_from_entries,
    make_index_receipt, make_leaf_receipt,
};
use crate::implementation::CachedBranch_v::LoadedBranch;
use crate::implementation::IBranchNode_v::{IBranchNode, iopt_addr};
use crate::implementation::MemtableImpl_v::{MemtableBucket, MemtableEntry};
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::WF_v::WF;
use crate::spec::ImplDisk_t::IAddress;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::Message;

verus! {

pub open spec fn entry_sequences_ordered(
    left: Seq<MemtableEntry>,
    right: Seq<MemtableEntry>,
) -> bool {
    forall |i: int, j: int|
        0 <= i < left.len() && 0 <= j < right.len()
        ==> (#[trigger] left[i]).key.0 < (#[trigger] right[j]).key.0
}

proof fn sorted_concat(
    left: Seq<MemtableEntry>,
    right: Seq<MemtableEntry>,
)
    requires
        MemtableBucket::strictly_sorted(left),
        MemtableBucket::strictly_sorted(right),
        entry_sequences_ordered(left, right),
    ensures MemtableBucket::strictly_sorted(left + right),
{
    assert forall |i: int, j: int| 0 <= i < j < (left + right).len()
        implies (left + right)[i].key.0 < (left + right)[j].key.0 by {
        if j < left.len() {
            assert((left + right)[i] == left[i]);
            assert((left + right)[j] == left[j]);
        } else if i < left.len() {
            assert((left + right)[i] == left[i]);
            assert((left + right)[j] == right[j - left.len()]);
        } else {
            assert((left + right)[i] == right[i - left.len()]);
            assert((left + right)[j] == right[j - left.len()]);
        }
    }
}

proof fn sorted_push(entries: Seq<MemtableEntry>, entry: MemtableEntry)
    requires
        MemtableBucket::strictly_sorted(entries),
        forall |i: int| 0 <= i < entries.len()
            ==> (#[trigger] entries[i]).key.0 < entry.key.0,
    ensures MemtableBucket::strictly_sorted(entries.push(entry)),
{
    assert forall |i: int, j: int|
        0 <= i < j < entries.push(entry).len()
        implies entries.push(entry)[i].key.0
            < entries.push(entry)[j].key.0 by {
        if j == entries.len() {
            assert(entries.push(entry)[j] == entry);
            assert(entries.push(entry)[i] == entries[i]);
        } else {
            assert(entries.push(entry)[i] == entries[i]);
            assert(entries.push(entry)[j] == entries[j]);
        }
    }
}

proof fn sorted_entries_unique(entries: Seq<MemtableEntry>)
    requires MemtableBucket::strictly_sorted(entries),
    ensures MemtableBucket::unique_keys(entries),
{
    assert forall |i: int, j: int|
        #![trigger entries[i].key, entries[j].key]
        0 <= i < entries.len()
        && 0 <= j < entries.len()
        && entries[i].key == entries[j].key
        implies i == j by {
        if i < j {
            assert(entries[i].key.0 < entries[j].key.0);
        } else if j < i {
            assert(entries[j].key.0 < entries[i].key.0);
        }
    }
}

proof fn entries_map_concat(
    left: Seq<MemtableEntry>,
    right: Seq<MemtableEntry>,
)
    requires
        MemtableBucket::strictly_sorted(left),
        MemtableBucket::strictly_sorted(right),
        entry_sequences_ordered(left, right),
    ensures
        MemtableBucket::entries_map(left + right)
            == MemtableBucket::entries_map(left).union_prefer_right(
                MemtableBucket::entries_map(right),
            ),
{
    sorted_entries_unique(left);
    sorted_entries_unique(right);
    sorted_concat(left, right);
    sorted_entries_unique(left + right);
    assert_maps_equal!(
        MemtableBucket::entries_map(left + right),
        MemtableBucket::entries_map(left).union_prefer_right(
            MemtableBucket::entries_map(right),
        ),
        key => {
            if MemtableBucket::entries_map(left + right).contains_key(key) {
                let i = MemtableBucket::entries_map_index_for_key(
                    left + right,
                    key,
                );
                if i < left.len() {
                    assert((left + right)[i] == left[i]);
                    MemtableBucket::entries_map_index(left, i);
                    assert(!MemtableBucket::entries_map(right)
                        .contains_key(key)) by {
                        if MemtableBucket::entries_map(right)
                            .contains_key(key)
                        {
                            let j = MemtableBucket::entries_map_index_for_key(
                                right,
                                key,
                            );
                            assert(left[i].key.0 < right[j].key.0);
                        }
                    }
                } else {
                    let j = i - left.len();
                    assert((left + right)[i] == right[j]);
                    MemtableBucket::entries_map_index(right, j);
                }
            }
            if MemtableBucket::entries_map(left)
                .union_prefer_right(
                    MemtableBucket::entries_map(right),
                ).contains_key(key)
            {
                if MemtableBucket::entries_map(right).contains_key(key) {
                    let j = MemtableBucket::entries_map_index_for_key(
                        right,
                        key,
                    );
                    assert((left + right)[left.len() as int + j]
                        == right[j]);
                    MemtableBucket::entries_map_index(
                        left + right,
                        left.len() as int + j,
                    );
                } else {
                    let i = MemtableBucket::entries_map_index_for_key(
                        left,
                        key,
                    );
                    assert((left + right)[i] == left[i]);
                    MemtableBucket::entries_map_index(left + right, i);
                }
            }
        }
    );
}

pub struct StreamingLeafTail {
    pub capacity: usize,
    pub previous: Vec<MemtableEntry>,
    pub current: Vec<MemtableEntry>,
}

pub enum StreamingLeafPushResult {
    Accepted,
    PageReady { entries: Vec<MemtableEntry> },
}

pub enum StreamingLeafFinishResult {
    Empty,
    One { entries: Vec<MemtableEntry> },
    Two {
        left: Vec<MemtableEntry>,
        right: Vec<MemtableEntry>,
    },
}

impl StreamingLeafTail {
    pub open spec fn entries(&self) -> Seq<MemtableEntry> {
        self.previous@ + self.current@
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.capacity > 1
        &&& self.capacity <= u8::MAX as usize
        &&& (self.previous.len() == 0
            || self.previous.len() == self.capacity)
        &&& self.current.len() < self.capacity
        &&& MemtableBucket::strictly_sorted(self.previous@)
        &&& MemtableBucket::strictly_sorted(self.current@)
        &&& entry_sequences_ordered(self.previous@, self.current@)
        &&& MemtableBucket::strictly_sorted(self.entries())
    }

    pub fn new(capacity: usize) -> (out: Option<Self>)
        ensures
            match out {
                Some(tail) => {
                    &&& capacity > 1
                    &&& tail.wf()
                    &&& tail.capacity == capacity
                    &&& tail.entries().len() == 0
                },
                None => capacity <= 1 || capacity > u8::MAX as usize,
            },
    {
        if capacity <= 1 || capacity > u8::MAX as usize {
            return None;
        }
        let out = Self {
            capacity,
            previous: Vec::new(),
            current: Vec::new(),
        };
        proof {
            assert(MemtableBucket::strictly_sorted(out.entries()));
            assert(out.wf());
        }
        Some(out)
    }

    pub fn push(
        &mut self,
        entry: MemtableEntry,
    ) -> (out: StreamingLeafPushResult)
        requires
            old(self).wf(),
            forall |i: int| 0 <= i < old(self).entries().len()
                ==> (#[trigger] old(self).entries()[i]).key.0
                    < entry.key.0,
        ensures
            self.wf(),
            self.capacity == old(self).capacity,
            match out {
                StreamingLeafPushResult::Accepted => {
                    self.entries() == old(self).entries().push(entry)
                },
                StreamingLeafPushResult::PageReady { entries } => {
                    &&& entries.len() == old(self).capacity
                    &&& MemtableBucket::strictly_sorted(entries@)
                    &&& old(self).entries().push(entry)
                        =~= entries@ + self.entries()
                    &&& entry_sequences_ordered(entries@, self.entries())
                },
            },
    {
        let ghost old_entries = self.entries();
        let ghost old_previous = self.previous@;
        let ghost old_current = self.current@;
        self.current.push(entry);
        proof {
            assert(self.current@
                == old_current.push(entry));
            assert forall |i: int| 0 <= i < old_current.len()
                implies old_current[i].key.0 < entry.key.0 by {
                assert(old_entries[old_previous.len() as int + i]
                    == old_current[i]);
            }
            sorted_push(old_current, entry);
            assert(entry_sequences_ordered(
                old_previous,
                self.current@,
            )) by {
                assert forall |i: int, j: int|
                    0 <= i < old_previous.len()
                    && 0 <= j < self.current@.len()
                    implies old_previous[i].key.0
                        < self.current@[j].key.0 by {
                    if j == old_current.len() {
                        assert(self.current@[j] == entry);
                        assert(old_entries[i] == old_previous[i]);
                    } else {
                        assert(self.current@[j] == old_current[j]);
                    }
                }
            }
        }
        if self.current.len() < self.capacity {
            proof {
                sorted_concat(self.previous@, self.current@);
                assert(self.entries() == old_entries.push(entry)) by {
                    assert_seqs_equal!(
                        self.entries(),
                        old_entries.push(entry),
                        i => {}
                    );
                }
                assert(self.wf());
            }
            return StreamingLeafPushResult::Accepted;
        }

        if self.previous.len() == 0 {
            self.previous = self.current.clone();
            self.current.clear();
            proof {
                assert(self.previous@ == old_current.push(entry));
                assert(self.entries() == old_entries.push(entry));
                assert(self.wf());
            }
            StreamingLeafPushResult::Accepted
        } else {
            let page = self.previous.clone();
            self.previous = self.current.clone();
            self.current.clear();
            proof {
                assert(page@ == old_previous);
                assert(self.previous@ == old_current.push(entry));
                assert(old_entries.push(entry)
                    =~= page@ + self.entries()) by {
                    assert_seqs_equal!(
                        old_entries.push(entry),
                        page@ + self.entries(),
                        i => {}
                    );
                }
                assert(entry_sequences_ordered(page@, self.entries()));
                assert(self.wf());
            }
            StreamingLeafPushResult::PageReady { entries: page }
        }
    }

    fn copy_entries(
        previous: &Vec<MemtableEntry>,
        current: &Vec<MemtableEntry>,
        start: usize,
        end: usize,
    ) -> (out: Vec<MemtableEntry>)
        requires
            start <= end <= previous.len() + current.len(),
        ensures
            out@ == (previous@ + current@).subrange(
                start as int,
                end as int,
            ),
    {
        let mut out = Vec::new();
        let mut index = start;
        while index < end
            invariant
                start <= index <= end,
                end <= previous.len() + current.len(),
                out@ == (previous@ + current@).subrange(
                    start as int,
                    index as int,
                ),
            decreases end - index,
        {
            let entry = if index < previous.len() {
                previous[index]
            } else {
                current[index - previous.len()]
            };
            out.push(entry);
            proof {
                assert(out@ == (previous@ + current@).subrange(
                    start as int,
                    index as int + 1,
                ));
            }
            index += 1;
        }
        out
    }

    pub fn finish(&mut self) -> (out: StreamingLeafFinishResult)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.capacity == old(self).capacity,
            self.entries().len() == 0,
            match out {
                StreamingLeafFinishResult::Empty => {
                    old(self).entries().len() == 0
                },
                StreamingLeafFinishResult::One { entries } => {
                    &&& entries@ == old(self).entries()
                    &&& 0 < entries.len() <= old(self).capacity
                    &&& MemtableBucket::strictly_sorted(entries@)
                },
                StreamingLeafFinishResult::Two { left, right } => {
                    &&& old(self).entries() =~= left@ + right@
                    &&& 0 < left.len() <= old(self).capacity
                    &&& 0 < right.len() <= old(self).capacity
                    &&& old(self).capacity <= 2 * left.len()
                    &&& old(self).capacity <= 2 * right.len()
                    &&& MemtableBucket::strictly_sorted(left@)
                    &&& MemtableBucket::strictly_sorted(right@)
                    &&& entry_sequences_ordered(left@, right@)
                },
            },
    {
        let ghost self0 = *self;
        proof {
            assert(self.previous.len() <= self.capacity);
            assert(self.current.len() < self.capacity);
            assert(self.previous.len() + self.current.len()
                <= 2 * self.capacity);
            assert(2 * self.capacity <= 2 * (u8::MAX as usize));
            assert(2 * (u8::MAX as usize) < usize::MAX);
        }
        let total = self.previous.len() + self.current.len();
        if total == 0 {
            return StreamingLeafFinishResult::Empty;
        }
        if self.previous.len() == 0 || self.current.len() == 0 {
            let entries = Self::copy_entries(
                &self.previous,
                &self.current,
                0,
                total,
            );
            self.previous.clear();
            self.current.clear();
            proof {
                assert(entries@ == self0.entries());
                assert(entries.len() <= self0.capacity);
                assert(self.wf());
            }
            return StreamingLeafFinishResult::One { entries };
        }

        let left_size = total / 2 + total % 2;
        let left = Self::copy_entries(
            &self.previous,
            &self.current,
            0,
            left_size,
        );
        let right = Self::copy_entries(
            &self.previous,
            &self.current,
            left_size,
            total,
        );
        self.previous.clear();
        self.current.clear();
        proof {
            broadcast use group_div_basics;
            lemma_fundamental_div_mod(total as int, 2);
            assert(total as int
                == 2 * (total / 2) as int + (total % 2) as int);
            assert((total % 2) < 2);
            assert(total % 2 == 0 || total % 2 == 1);
            assert(left_size as int
                == (total / 2) as int + (total % 2) as int);
            assert((total - left_size) as int
                == (total / 2) as int);
            assert(total <= 2 * self0.capacity);
            assert(self0.capacity < total);
            assert(left_size > 0);
            assert(left_size <= self0.capacity);
            assert(total - left_size > 0);
            assert(total - left_size <= self0.capacity);
            assert(self0.capacity <= 2 * (total - left_size)) by {
                if self0.capacity > 2 * (total - left_size) {
                    assert(self0.capacity
                        >= 2 * (total - left_size) + 1);
                    if total % 2 == 0 {
                        assert(total == 2 * (total - left_size));
                    } else {
                        assert(total == 2 * (total - left_size) + 1);
                    }
                    assert(false);
                }
            }
            assert(total - left_size <= left_size);
            assert(self0.capacity <= 2 * left_size);
            assert(self0.entries() =~= left@ + right@) by {
                assert_seqs_equal!(
                    self0.entries(),
                    left@ + right@,
                    i => {}
                );
            }
            assert(MemtableBucket::strictly_sorted(left@));
            assert(MemtableBucket::strictly_sorted(right@));
            assert(entry_sequences_ordered(left@, right@));
            assert(self.wf());
        }
        StreamingLeafFinishResult::Two { left, right }
    }
}

proof fn descriptor_subrange_wf(
    entries: Seq<BranchChildDescriptor>,
    start: int,
    end: int,
)
    requires
        descriptor_sequence_wf(entries),
        0 <= start <= end <= entries.len(),
    ensures descriptor_sequence_wf(entries.subrange(start, end)),
{
    let slice = entries.subrange(start, end);
    assert forall |i: int| 0 <= i < slice.len()
        implies (#[trigger] slice[i]).wf() by {
        vstd::seq::axiom_seq_subrange_index(entries, start, end, i);
    }
    assert forall |i: int, j: int|
        #![trigger slice[i], slice[j]]
        0 <= i < j < slice.len()
        implies slice[i].receipt@.nodes.dom().disjoint(
            slice[j].receipt@.nodes.dom(),
        ) by {
        vstd::seq::axiom_seq_subrange_index(entries, start, end, i);
        vstd::seq::axiom_seq_subrange_index(entries, start, end, j);
    }
    assert forall |i: int, j: int|
        #![trigger slice[i], slice[j]]
        0 <= i < j < slice.len()
        implies slice[i].receipt@.last_key.0
            < slice[j].first_key.0 by {
        vstd::seq::axiom_seq_subrange_index(entries, start, end, i);
        vstd::seq::axiom_seq_subrange_index(entries, start, end, j);
    }
    assert forall |i: int, j: int|
        #![trigger slice[i], slice[j]]
        0 <= i < j < slice.len()
        implies slice[i].receipt@.height
            == slice[j].receipt@.height by {
        vstd::seq::axiom_seq_subrange_index(entries, start, end, i);
        vstd::seq::axiom_seq_subrange_index(entries, start, end, j);
    }
}

pub struct StreamingIndexTail {
    pub capacity: usize,
    pub previous: Vec<BranchChildDescriptor>,
    pub current: Vec<BranchChildDescriptor>,
}

pub enum StreamingIndexPushResult {
    Accepted,
    PageReady { children: Vec<BranchChildDescriptor> },
}

pub enum StreamingIndexFinishResult {
    Empty,
    One { children: Vec<BranchChildDescriptor> },
    Two {
        left: Vec<BranchChildDescriptor>,
        right: Vec<BranchChildDescriptor>,
    },
}

impl StreamingIndexTail {
    pub open spec fn entries(&self) -> Seq<BranchChildDescriptor> {
        self.previous@ + self.current@
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.capacity > 1
        &&& self.capacity <= u8::MAX as usize + 1
        &&& (self.previous.len() == 0
            || self.previous.len() == self.capacity)
        &&& self.current.len() < self.capacity
        &&& descriptor_sequence_wf(self.entries())
    }

    pub fn new(capacity: usize) -> (out: Option<Self>)
        ensures
            match out {
                Some(tail) => {
                    &&& tail.wf()
                    &&& tail.capacity == capacity
                    &&& tail.entries().len() == 0
                },
                None => capacity <= 1
                    || capacity > u8::MAX as usize + 1,
            },
    {
        if capacity <= 1 || capacity > u8::MAX as usize + 1 {
            return None;
        }
        let out = Self {
            capacity,
            previous: Vec::new(),
            current: Vec::new(),
        };
        proof {
            assert(descriptor_sequence_wf(out.entries()));
            assert(out.wf());
        }
        Some(out)
    }

    pub fn push(
        &mut self,
        descriptor: BranchChildDescriptor,
    ) -> (out: StreamingIndexPushResult)
        requires
            old(self).wf(),
            descriptor_sequence_wf(
                old(self).entries().push(descriptor),
            ),
        ensures
            self.wf(),
            self.capacity == old(self).capacity,
            match out {
                StreamingIndexPushResult::Accepted => {
                    self.entries() == old(self).entries().push(descriptor)
                },
                StreamingIndexPushResult::PageReady { children } => {
                    &&& children.len() == old(self).capacity
                    &&& descriptor_sequence_wf(children@)
                    &&& old(self).entries().push(descriptor)
                        =~= children@ + self.entries()
                },
            },
    {
        let ghost old_entries = self.entries();
        let ghost old_previous = self.previous@;
        let ghost old_current = self.current@;
        self.current.push(descriptor);
        if self.current.len() < self.capacity {
            proof {
                assert(self.entries() == old_entries.push(descriptor)) by {
                    assert_seqs_equal!(
                        self.entries(),
                        old_entries.push(descriptor),
                        i => {}
                    );
                }
                assert(self.wf());
            }
            return StreamingIndexPushResult::Accepted;
        }
        if self.previous.len() == 0 {
            self.previous = self.current.clone();
            self.current.clear();
            proof {
                assert(self.entries() == old_entries.push(descriptor));
                assert(self.wf());
            }
            StreamingIndexPushResult::Accepted
        } else {
            let page = self.previous.clone();
            self.previous = self.current.clone();
            self.current.clear();
            proof {
                assert(page@ == old_previous);
                assert(self.previous@ == old_current.push(descriptor));
                assert(old_entries.push(descriptor)
                    =~= page@ + self.entries()) by {
                    assert_seqs_equal!(
                        old_entries.push(descriptor),
                        page@ + self.entries(),
                        i => {}
                    );
                }
                let ghost combined = old_entries.push(descriptor);
                assert(page@ == combined.subrange(
                    0,
                    page.len() as int,
                )) by {
                    assert_seqs_equal!(
                        page@,
                        combined.subrange(0, page.len() as int),
                        i => {
                            vstd::seq::axiom_seq_subrange_index(
                                combined,
                                0,
                                page.len() as int,
                                i,
                            );
                        }
                    );
                }
                assert(self.entries() == combined.subrange(
                    page.len() as int,
                    combined.len() as int,
                )) by {
                    assert_seqs_equal!(
                        self.entries(),
                        combined.subrange(
                            page.len() as int,
                            combined.len() as int,
                        ),
                        i => {
                            vstd::seq::axiom_seq_subrange_index(
                                combined,
                                page.len() as int,
                                combined.len() as int,
                                i,
                            );
                        }
                    );
                }
                descriptor_subrange_wf(
                    combined,
                    0,
                    page.len() as int,
                );
                descriptor_subrange_wf(
                    combined,
                    page.len() as int,
                    old_entries.len() as int + 1,
                );
                assert(self.wf());
            }
            StreamingIndexPushResult::PageReady { children: page }
        }
    }

    fn copy_descriptors(
        previous: &Vec<BranchChildDescriptor>,
        current: &Vec<BranchChildDescriptor>,
        start: usize,
        end: usize,
    ) -> (out: Vec<BranchChildDescriptor>)
        requires
            start <= end <= previous.len() + current.len(),
        ensures
            out@ == (previous@ + current@).subrange(
                start as int,
                end as int,
            ),
    {
        let mut out = Vec::new();
        let mut index = start;
        while index < end
            invariant
                start <= index <= end,
                end <= previous.len() + current.len(),
                out@ == (previous@ + current@).subrange(
                    start as int,
                    index as int,
                ),
            decreases end - index,
        {
            let descriptor = if index < previous.len() {
                previous[index]
            } else {
                current[index - previous.len()]
            };
            out.push(descriptor);
            proof {
                assert(out@ == (previous@ + current@).subrange(
                    start as int,
                    index as int + 1,
                ));
            }
            index += 1;
        }
        out
    }

    pub fn finish(&mut self) -> (out: StreamingIndexFinishResult)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.capacity == old(self).capacity,
            self.entries().len() == 0,
            match out {
                StreamingIndexFinishResult::Empty => {
                    &&& old(self).entries().len() == 0
                    &&& *self == *old(self)
                },
                StreamingIndexFinishResult::One { children } => {
                    &&& children@ == old(self).entries()
                    &&& 0 < children.len() <= old(self).capacity
                    &&& descriptor_sequence_wf(children@)
                },
                StreamingIndexFinishResult::Two { left, right } => {
                    &&& old(self).entries() =~= left@ + right@
                    &&& 0 < left.len() <= old(self).capacity
                    &&& 0 < right.len() <= old(self).capacity
                    &&& old(self).capacity <= 2 * left.len()
                    &&& old(self).capacity <= 2 * right.len()
                    &&& descriptor_sequence_wf(left@)
                    &&& descriptor_sequence_wf(right@)
                },
            },
    {
        let ghost self0 = *self;
        proof {
            assert(self.previous.len() <= self.capacity);
            assert(self.current.len() < self.capacity);
            assert(self.previous.len() + self.current.len()
                <= 2 * self.capacity);
            assert(2 * self.capacity
                <= 2 * (u8::MAX as usize + 1));
            assert(2 * (u8::MAX as usize + 1) < usize::MAX);
        }
        let total = self.previous.len() + self.current.len();
        if total == 0 {
            return StreamingIndexFinishResult::Empty;
        }
        if self.previous.len() == 0 || self.current.len() == 0 {
            let children = Self::copy_descriptors(
                &self.previous,
                &self.current,
                0,
                total,
            );
            self.previous.clear();
            self.current.clear();
            proof {
                assert(children@ == self0.entries());
                assert(children.len() <= self0.capacity);
                descriptor_subrange_wf(
                    self0.entries(),
                    0,
                    self0.entries().len() as int,
                );
                assert(self.wf());
            }
            return StreamingIndexFinishResult::One { children };
        }
        let left_size = total / 2 + total % 2;
        let left = Self::copy_descriptors(
            &self.previous,
            &self.current,
            0,
            left_size,
        );
        let right = Self::copy_descriptors(
            &self.previous,
            &self.current,
            left_size,
            total,
        );
        self.previous.clear();
        self.current.clear();
        proof {
            broadcast use group_div_basics;
            lemma_fundamental_div_mod(total as int, 2);
            assert(total as int
                == 2 * (total / 2) as int + (total % 2) as int);
            assert(total % 2 == 0 || total % 2 == 1);
            assert(left_size as int
                == (total / 2) as int + (total % 2) as int);
            assert((total - left_size) as int
                == (total / 2) as int);
            assert(total <= 2 * self0.capacity);
            assert(self0.capacity < total);
            assert(left_size > 0);
            assert(left_size <= self0.capacity);
            assert(total - left_size > 0);
            assert(total - left_size <= self0.capacity);
            assert(self0.capacity <= 2 * (total - left_size)) by {
                if self0.capacity > 2 * (total - left_size) {
                    assert(self0.capacity
                        >= 2 * (total - left_size) + 1);
                    if total % 2 == 0 {
                        assert(total == 2 * (total - left_size));
                    } else {
                        assert(total == 2 * (total - left_size) + 1);
                    }
                    assert(false);
                }
            }
            assert(total - left_size <= left_size);
            assert(self0.capacity <= 2 * left_size);
            assert(self0.entries() =~= left@ + right@) by {
                assert_seqs_equal!(self0.entries(), left@ + right@, i => {});
            }
            descriptor_subrange_wf(
                self0.entries(),
                0,
                left_size as int,
            );
            descriptor_subrange_wf(
                self0.entries(),
                left_size as int,
                total as int,
            );
            assert(self.wf());
        }
        StreamingIndexFinishResult::Two { left, right }
    }
}

pub enum StreamingPendingPage {
    Leaf {
        entries: Vec<MemtableEntry>,
        parent_level: usize,
    },
    Index {
        children: Vec<BranchChildDescriptor>,
        parent_level: usize,
    },
}

pub enum StreamingBranchPhase {
    Reading,
    Finishing { level: usize },
    ReadyLeafRoot,
    ReadyIndexRoot,
    Empty,
    Sealed,
}

pub enum StreamingBuilderInputResult {
    Accepted,
    PageReady,
}

pub struct StreamingStagedPage {
    pub node: IBranchNode,
    pub descriptor: BranchChildDescriptor,
}

pub enum StreamingFinishInputResult {
    Empty,
    RootReady,
    Continue,
}

pub enum StreamingFinishLevelResult {
    Empty,
    Advanced,
    PagesReady,
    RootReady,
}

pub struct StreamingBranchBuilder {
    pub leaf_tail: StreamingLeafTail,
    pub levels: Vec<StreamingIndexTail>,
    pub pending: Option<StreamingPendingPage>,
    pub deferred: Option<StreamingPendingPage>,
    pub phase: StreamingBranchPhase,
    pub index_fanout: usize,
    pub root_leaf: Vec<MemtableEntry>,
    pub root_children: Vec<BranchChildDescriptor>,
    pub has_staged_leaf: bool,
    pub source_entries: Ghost<Seq<MemtableEntry>>,
    pub leaf_prefix: Ghost<Seq<MemtableEntry>>,
    pub staged_nodes: Ghost<LoadedBranch>,
}

pub open spec fn streaming_pending_parent_level(
    pending: StreamingPendingPage,
) -> usize {
    match pending {
        StreamingPendingPage::Leaf { parent_level, .. } => parent_level,
        StreamingPendingPage::Index { parent_level, .. } => parent_level,
    }
}

pub open spec fn streaming_pending_leaf_entries(
    pending: Option<StreamingPendingPage>,
) -> Seq<MemtableEntry> {
    match pending {
        Some(StreamingPendingPage::Leaf { entries, .. }) => entries@,
        _ => Seq::empty(),
    }
}

pub open spec fn streaming_pending_descriptors_at(
    pending: Option<StreamingPendingPage>,
    level: int,
) -> Seq<BranchChildDescriptor> {
    match pending {
        Some(StreamingPendingPage::Index {
            children,
            parent_level,
        }) if parent_level as int == level => children@,
        _ => Seq::empty(),
    }
}

pub open spec fn streaming_levels_frontier(
    levels: Seq<StreamingIndexTail>,
    pending: Option<StreamingPendingPage>,
    deferred: Option<StreamingPendingPage>,
    count: nat,
) -> Seq<BranchChildDescriptor>
    recommends count <= levels.len(),
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let level = (count - 1) as nat;
        levels[level as int].entries()
            + streaming_pending_descriptors_at(pending, level as int)
            + streaming_pending_descriptors_at(deferred, level as int)
            + streaming_levels_frontier(
                levels,
                pending,
                deferred,
                level,
            )
    }
}

pub open spec fn streaming_levels_replace_pending(
    levels: Seq<StreamingIndexTail>,
    pending: Option<StreamingPendingPage>,
    deferred: Option<StreamingPendingPage>,
    count: nat,
    target: int,
    descriptor: BranchChildDescriptor,
) -> Seq<BranchChildDescriptor>
    recommends
        count <= levels.len(),
        0 <= target < count,
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let level = (count - 1) as nat;
        if level as int == target {
            levels[level as int].entries()
                + Seq::empty().push(descriptor)
                + streaming_pending_descriptors_at(deferred, level as int)
                + streaming_levels_frontier(
                    levels,
                    pending,
                    deferred,
                    level,
                )
        } else {
            levels[level as int].entries()
                + streaming_pending_descriptors_at(pending, level as int)
                + streaming_pending_descriptors_at(deferred, level as int)
                + streaming_levels_replace_pending(
                    levels,
                    pending,
                    deferred,
                    level,
                    target,
                    descriptor,
                )
        }
    }
}

pub open spec fn descriptor_frontier_collapse_witness(
    old_frontier: Seq<BranchChildDescriptor>,
    children: Seq<BranchChildDescriptor>,
    descriptor: BranchChildDescriptor,
    new_frontier: Seq<BranchChildDescriptor>,
    prefix: Seq<BranchChildDescriptor>,
    suffix: Seq<BranchChildDescriptor>,
) -> bool {
    old_frontier == prefix + children + suffix
        && new_frontier == prefix.push(descriptor) + suffix
}

pub open spec fn descriptor_frontier_collapse(
    old_frontier: Seq<BranchChildDescriptor>,
    children: Seq<BranchChildDescriptor>,
    descriptor: BranchChildDescriptor,
    new_frontier: Seq<BranchChildDescriptor>,
) -> bool {
    exists |prefix: Seq<BranchChildDescriptor>,
        suffix: Seq<BranchChildDescriptor>|
        #[trigger] descriptor_frontier_collapse_witness(
            old_frontier,
            children,
            descriptor,
            new_frontier,
            prefix,
            suffix,
        )
}

proof fn streaming_replace_pending_is_collapse(
    levels: Seq<StreamingIndexTail>,
    pending: StreamingPendingPage,
    deferred: Option<StreamingPendingPage>,
    count: nat,
    target: int,
    descriptor: BranchChildDescriptor,
)
    requires
        count <= levels.len(),
        0 <= target < count,
        pending is Index,
        streaming_pending_parent_level(pending) as int == target,
    ensures
        descriptor_frontier_collapse(
            streaming_levels_frontier(
                levels,
                Some(pending),
                deferred,
                count,
            ),
            streaming_pending_descriptors_at(Some(pending), target),
            descriptor,
            streaming_levels_replace_pending(
                levels,
                Some(pending),
                deferred,
                count,
                target,
                descriptor,
            ),
        ),
    decreases count,
{
    reveal_with_fuel(streaming_levels_frontier, 2);
    reveal_with_fuel(streaming_levels_replace_pending, 2);
    let top = (count - 1) as nat;
    let level_entries = levels[top as int].entries();
    let pending_entries = streaming_pending_descriptors_at(
        Some(pending),
        top as int,
    );
    let deferred_entries = streaming_pending_descriptors_at(
        deferred,
        top as int,
    );
    let old_lower = streaming_levels_frontier(
        levels,
        Some(pending),
        deferred,
        top,
    );
    if top as int == target {
        let new_lower = old_lower;
        let prefix = level_entries;
        let suffix = deferred_entries + old_lower;
        assert(pending_entries
            == streaming_pending_descriptors_at(
                Some(pending),
                target,
            ));
        assert(streaming_levels_frontier(
            levels,
            Some(pending),
            deferred,
            count,
        ) == prefix + pending_entries + suffix) by {
            assert_seqs_equal!(
                streaming_levels_frontier(
                    levels,
                    Some(pending),
                    deferred,
                    count,
                ),
                prefix + pending_entries + suffix,
                i => {}
            );
        }
        assert(streaming_levels_replace_pending(
            levels,
            Some(pending),
            deferred,
            count,
            target,
            descriptor,
        ) == prefix.push(descriptor) + suffix) by {
            assert_seqs_equal!(
                streaming_levels_replace_pending(
                    levels,
                    Some(pending),
                    deferred,
                    count,
                    target,
                    descriptor,
                ),
                prefix.push(descriptor) + suffix,
                i => {}
            );
        }
        assert(descriptor_frontier_collapse_witness(
            streaming_levels_frontier(
                levels,
                Some(pending),
                deferred,
                count,
            ),
            streaming_pending_descriptors_at(Some(pending), target),
            descriptor,
            streaming_levels_replace_pending(
                levels,
                Some(pending),
                deferred,
                count,
                target,
                descriptor,
            ),
            prefix,
            suffix,
        ));
    } else {
        let new_lower = streaming_levels_replace_pending(
            levels,
            Some(pending),
            deferred,
            top,
            target,
            descriptor,
        );
        assert(top as int > target);
        assert(pending_entries
            == Seq::<BranchChildDescriptor>::empty());
        streaming_replace_pending_is_collapse(
            levels,
            pending,
            deferred,
            top,
            target,
            descriptor,
        );
        let (low_prefix, low_suffix) = choose |
                low_prefix: Seq<BranchChildDescriptor>,
                low_suffix: Seq<BranchChildDescriptor>|
            #[trigger] descriptor_frontier_collapse_witness(
                old_lower,
                streaming_pending_descriptors_at(
                    Some(pending),
                    target,
                ),
                descriptor,
                new_lower,
                low_prefix,
                low_suffix,
            );
        assert(descriptor_frontier_collapse_witness(
            old_lower,
            streaming_pending_descriptors_at(
                Some(pending),
                target,
            ),
            descriptor,
            new_lower,
            low_prefix,
            low_suffix,
        ));
        let head = level_entries + deferred_entries;
        let prefix = head + low_prefix;
        assert(streaming_levels_frontier(
            levels,
            Some(pending),
            deferred,
            count,
        ) == head + old_lower) by {
            assert_seqs_equal!(
                streaming_levels_frontier(
                    levels,
                    Some(pending),
                    deferred,
                    count,
                ),
                head + old_lower,
                i => {}
            );
        }
        assert(streaming_levels_frontier(
            levels,
            Some(pending),
            deferred,
            count,
        ) == prefix
            + streaming_pending_descriptors_at(
                Some(pending),
                target,
            )
            + low_suffix) by {
            assert_seqs_equal!(
                streaming_levels_frontier(
                    levels,
                    Some(pending),
                    deferred,
                    count,
                ),
                prefix
                    + streaming_pending_descriptors_at(
                        Some(pending),
                        target,
                    )
                    + low_suffix,
                i => {}
            );
        }
        assert(streaming_levels_replace_pending(
            levels,
            Some(pending),
            deferred,
            count,
            target,
            descriptor,
        ) == prefix.push(descriptor) + low_suffix) by {
            assert_seqs_equal!(
                streaming_levels_replace_pending(
                    levels,
                    Some(pending),
                    deferred,
                    count,
                    target,
                    descriptor,
                ),
                prefix.push(descriptor) + low_suffix,
                i => {}
            );
        }
        assert(descriptor_frontier_collapse_witness(
            streaming_levels_frontier(
                levels,
                Some(pending),
                deferred,
                count,
            ),
            streaming_pending_descriptors_at(Some(pending), target),
            descriptor,
            streaming_levels_replace_pending(
                levels,
                Some(pending),
                deferred,
                count,
                target,
                descriptor,
            ),
            prefix,
            low_suffix,
        ));
    }
}

proof fn streaming_move_deferred_to_pending(
    levels: Seq<StreamingIndexTail>,
    blocker: StreamingPendingPage,
    deferred: Option<StreamingPendingPage>,
    count: nat,
)
    requires
        count <= levels.len(),
        streaming_pending_parent_level(blocker) as nat >= count,
    ensures
        streaming_levels_frontier(
            levels,
            Some(blocker),
            deferred,
            count,
        ) == streaming_levels_frontier(
            levels,
            deferred,
            None,
            count,
        ),
    decreases count,
{
    reveal_with_fuel(streaming_levels_frontier, 2);
    if count > 0 {
        let top = (count - 1) as nat;
        assert(streaming_pending_descriptors_at(
            Some(blocker),
            top as int,
        ) == Seq::<BranchChildDescriptor>::empty());
        streaming_move_deferred_to_pending(
            levels,
            blocker,
            deferred,
            top,
        );
        assert_seqs_equal!(
            streaming_levels_frontier(
                levels,
                Some(blocker),
                deferred,
                count,
            ),
            streaming_levels_frontier(
                levels,
                deferred,
                None,
                count,
            ),
            i => {}
        );
    }
}

proof fn streaming_pending_above_count_invisible(
    levels: Seq<StreamingIndexTail>,
    pending: StreamingPendingPage,
    deferred: Option<StreamingPendingPage>,
    count: nat,
)
    requires
        count <= levels.len(),
        streaming_pending_parent_level(pending) as nat >= count,
    ensures
        streaming_levels_frontier(
            levels,
            Some(pending),
            deferred,
            count,
        ) == streaming_levels_frontier(
            levels,
            None,
            deferred,
            count,
        ),
    decreases count,
{
    reveal_with_fuel(streaming_levels_frontier, 2);
    if count > 0 {
        let top = (count - 1) as nat;
        assert(streaming_pending_descriptors_at(
            Some(pending),
            top as int,
        ) == Seq::<BranchChildDescriptor>::empty());
        streaming_pending_above_count_invisible(
            levels,
            pending,
            deferred,
            top,
        );
    }
}

proof fn streaming_deferred_above_count_invisible(
    levels: Seq<StreamingIndexTail>,
    pending: Option<StreamingPendingPage>,
    deferred: StreamingPendingPage,
    count: nat,
)
    requires
        count <= levels.len(),
        streaming_pending_parent_level(deferred) as nat >= count,
    ensures
        streaming_levels_frontier(
            levels,
            pending,
            Some(deferred),
            count,
        ) == streaming_levels_frontier(
            levels,
            pending,
            None,
            count,
        ),
    decreases count,
{
    reveal_with_fuel(streaming_levels_frontier, 2);
    if count > 0 {
        let top = (count - 1) as nat;
        assert(streaming_pending_descriptors_at(
            Some(deferred),
            top as int,
        ) == Seq::<BranchChildDescriptor>::empty());
        streaming_deferred_above_count_invisible(
            levels,
            pending,
            deferred,
            top,
        );
    }
}

proof fn streaming_frontier_entries_extensional(
    left: Seq<StreamingIndexTail>,
    right: Seq<StreamingIndexTail>,
    pending: Option<StreamingPendingPage>,
    deferred: Option<StreamingPendingPage>,
    count: nat,
)
    requires
        count <= left.len(),
        count <= right.len(),
        forall |i: int| 0 <= i < count
            ==> (#[trigger] left[i]).entries() == right[i].entries(),
    ensures
        streaming_levels_frontier(
            left,
            pending,
            deferred,
            count,
        ) == streaming_levels_frontier(
            right,
            pending,
            deferred,
            count,
        ),
    decreases count,
{
    reveal_with_fuel(streaming_levels_frontier, 2);
    if count > 0 {
        let top = (count - 1) as nat;
        streaming_frontier_entries_extensional(
            left,
            right,
            pending,
            deferred,
            top,
        );
    }
}

proof fn streaming_index_push_accepted_layout(
    old_levels: Seq<StreamingIndexTail>,
    new_levels: Seq<StreamingIndexTail>,
    pending: StreamingPendingPage,
    deferred: Option<StreamingPendingPage>,
    target: int,
    descriptor: BranchChildDescriptor,
    count: nat,
)
    requires
        count <= old_levels.len(),
        new_levels.len() == old_levels.len(),
        0 <= target < count,
        pending is Index,
        streaming_pending_parent_level(pending) as int == target,
        new_levels[target].entries()
            == old_levels[target].entries().push(descriptor),
        forall |i: int| 0 <= i < old_levels.len() && i != target
            ==> (#[trigger] new_levels[i]).entries()
                == old_levels[i].entries(),
    ensures
        streaming_levels_frontier(
            new_levels,
            deferred,
            None,
            count,
        ) == streaming_levels_replace_pending(
            old_levels,
            Some(pending),
            deferred,
            count,
            target,
            descriptor,
        ),
    decreases count,
{
    reveal_with_fuel(streaming_levels_frontier, 2);
    reveal_with_fuel(streaming_levels_replace_pending, 2);
    let top = (count - 1) as nat;
    if top as int == target {
        streaming_move_deferred_to_pending(
            old_levels,
            pending,
            deferred,
            top,
        );
        streaming_frontier_entries_extensional(
            new_levels,
            old_levels,
            deferred,
            None,
            top,
        );
        assert_seqs_equal!(
            streaming_levels_frontier(
                new_levels,
                deferred,
                None,
                count,
            ),
            streaming_levels_replace_pending(
                old_levels,
                Some(pending),
                deferred,
                count,
                target,
                descriptor,
            ),
            i => {}
        );
    } else {
        assert(top as int > target);
        streaming_index_push_accepted_layout(
            old_levels,
            new_levels,
            pending,
            deferred,
            target,
            descriptor,
            top,
        );
        assert(streaming_pending_descriptors_at(
            Some(pending),
            top as int,
        ) == Seq::<BranchChildDescriptor>::empty());
        assert(new_levels[top as int].entries()
            == old_levels[top as int].entries());
        assert_seqs_equal!(
            streaming_levels_frontier(
                new_levels,
                deferred,
                None,
                count,
            ),
            streaming_levels_replace_pending(
                old_levels,
                Some(pending),
                deferred,
                count,
                target,
                descriptor,
            ),
            i => {}
        );
    }
}

proof fn streaming_index_emitted_core_layout(
    old_levels: Seq<StreamingIndexTail>,
    new_levels: Seq<StreamingIndexTail>,
    old_pending: StreamingPendingPage,
    new_pending: StreamingPendingPage,
    deferred: Option<StreamingPendingPage>,
    target: int,
    descriptor: BranchChildDescriptor,
    emitted: Seq<BranchChildDescriptor>,
)
    requires
        0 <= target < old_levels.len(),
        target < new_levels.len(),
        old_pending is Index,
        new_pending is Index,
        streaming_pending_parent_level(old_pending) as int == target,
        streaming_pending_parent_level(new_pending) as int == target + 1,
        match deferred {
            Some(page) => streaming_pending_parent_level(page) as int
                <= target,
            None => true,
        },
        emitted + new_levels[target].entries()
            =~= old_levels[target].entries().push(descriptor),
        forall |i: int| 0 <= i < target
            ==> (#[trigger] new_levels[i]).entries()
                == old_levels[i].entries(),
    ensures
        emitted + streaming_levels_frontier(
            new_levels,
            Some(new_pending),
            deferred,
            (target + 1) as nat,
        ) == streaming_levels_replace_pending(
            old_levels,
            Some(old_pending),
            deferred,
            (target + 1) as nat,
            target,
            descriptor,
        ),
{
    reveal_with_fuel(streaming_levels_frontier, 2);
    reveal_with_fuel(streaming_levels_replace_pending, 2);
    streaming_pending_above_count_invisible(
        new_levels,
        new_pending,
        deferred,
        target as nat,
    );
    streaming_pending_above_count_invisible(
        old_levels,
        old_pending,
        deferred,
        target as nat,
    );
    streaming_frontier_entries_extensional(
        new_levels,
        old_levels,
        None,
        deferred,
        target as nat,
    );
    let new_below = streaming_levels_frontier(
        new_levels,
        Some(new_pending),
        deferred,
        target as nat,
    );
    let old_below = streaming_levels_frontier(
        old_levels,
        Some(old_pending),
        deferred,
        target as nat,
    );
    assert(new_below == old_below) by {
        assert(new_below == streaming_levels_frontier(
            new_levels,
            None,
            deferred,
            target as nat,
        ));
        assert(old_below == streaming_levels_frontier(
            old_levels,
            None,
            deferred,
            target as nat,
        ));
    }
    assert(emitted + new_levels[target].entries()
        == old_levels[target].entries().push(descriptor)) by {
        assert_seqs_equal!(
            emitted + new_levels[target].entries(),
            old_levels[target].entries().push(descriptor),
            i => {}
        );
    }
    let deferred_here = streaming_pending_descriptors_at(
        deferred,
        target,
    );
    assert(streaming_levels_frontier(
        new_levels,
        Some(new_pending),
        deferred,
        (target + 1) as nat,
    ) == new_levels[target].entries() + deferred_here + new_below);
    assert(streaming_levels_replace_pending(
        old_levels,
        Some(old_pending),
        deferred,
        (target + 1) as nat,
        target,
        descriptor,
    ) == old_levels[target].entries()
        + Seq::empty().push(descriptor) + deferred_here + old_below);
    let new_combined = emitted + new_levels[target].entries();
    let old_combined = old_levels[target].entries().push(descriptor);
    let suffix = deferred_here + old_below;
    assert(new_combined == old_combined);
    assert(emitted + streaming_levels_frontier(
        new_levels,
        Some(new_pending),
        deferred,
        (target + 1) as nat,
    ) == new_combined + suffix) by {
        assert_seqs_equal!(
            emitted + streaming_levels_frontier(
                new_levels,
                Some(new_pending),
                deferred,
                (target + 1) as nat,
            ),
            new_combined + suffix,
            i => {}
        );
    }
    assert(streaming_levels_replace_pending(
        old_levels,
        Some(old_pending),
        deferred,
        (target + 1) as nat,
        target,
        descriptor,
    ) == old_combined + suffix) by {
        assert_seqs_equal!(
            streaming_levels_replace_pending(
                old_levels,
                Some(old_pending),
                deferred,
                (target + 1) as nat,
                target,
                descriptor,
            ),
            old_combined + suffix,
            i => {}
        );
    }
}

proof fn streaming_index_push_emitted_layout(
    old_levels: Seq<StreamingIndexTail>,
    new_levels: Seq<StreamingIndexTail>,
    old_pending: StreamingPendingPage,
    new_pending: StreamingPendingPage,
    deferred: Option<StreamingPendingPage>,
    target: int,
    descriptor: BranchChildDescriptor,
    emitted: Seq<BranchChildDescriptor>,
    count: nat,
)
    requires
        old_levels.len() <= new_levels.len()
            <= old_levels.len() + 1,
        old_levels.len() > target,
        new_levels.len() > target + 1,
        target + 1 < count <= new_levels.len(),
        count > old_levels.len() ==> {
            &&& count == old_levels.len() + 1
            &&& old_levels.len() == target + 1
        },
        old_pending is Index,
        new_pending is Index,
        streaming_pending_parent_level(old_pending) as int == target,
        streaming_pending_parent_level(new_pending) as int == target + 1,
        streaming_pending_descriptors_at(
            Some(new_pending),
            target + 1,
        ) == emitted,
        match deferred {
            Some(page) => streaming_pending_parent_level(page) as int
                <= target,
            None => true,
        },
        emitted + new_levels[target].entries()
            =~= old_levels[target].entries().push(descriptor),
        forall |i: int| 0 <= i < old_levels.len() && i != target
            ==> (#[trigger] new_levels[i]).entries()
                == old_levels[i].entries(),
        new_levels.len() == old_levels.len() + 1
            ==> new_levels[new_levels.len() as int - 1].entries().len() == 0,
    ensures
        streaming_levels_frontier(
            new_levels,
            Some(new_pending),
            deferred,
            count,
        ) == streaming_levels_replace_pending(
            old_levels,
            Some(old_pending),
            deferred,
            if count <= old_levels.len() {
                count
            } else {
                old_levels.len()
            },
            target,
            descriptor,
        ),
    decreases count,
{
    reveal_with_fuel(streaming_levels_frontier, 2);
    reveal_with_fuel(streaming_levels_replace_pending, 2);
    let top = (count - 1) as nat;
    if top as int > target + 1 {
        assert(count <= old_levels.len());
        streaming_index_push_emitted_layout(
            old_levels,
            new_levels,
            old_pending,
            new_pending,
            deferred,
            target,
            descriptor,
            emitted,
            top,
        );
        assert(streaming_pending_descriptors_at(
            Some(new_pending),
            top as int,
        ) == Seq::<BranchChildDescriptor>::empty());
        assert(streaming_pending_descriptors_at(
            Some(old_pending),
            top as int,
        ) == Seq::<BranchChildDescriptor>::empty());
        assert(streaming_pending_descriptors_at(
            deferred,
            top as int,
        ) == Seq::<BranchChildDescriptor>::empty());
        assert(new_levels[top as int].entries()
            == old_levels[top as int].entries());
        assert_seqs_equal!(
            streaming_levels_frontier(
                new_levels,
                Some(new_pending),
                deferred,
                count,
            ),
            streaming_levels_replace_pending(
                old_levels,
                Some(old_pending),
                deferred,
                count,
                target,
                descriptor,
            ),
            i => {}
        );
    } else {
        assert(top as int == target + 1);
        let lower_count = (target + 1) as nat;
        streaming_pending_above_count_invisible(
            new_levels,
            new_pending,
            deferred,
            lower_count,
        );
        streaming_pending_above_count_invisible(
            old_levels,
            old_pending,
            deferred,
            target as nat,
        );
        streaming_frontier_entries_extensional(
            new_levels,
            old_levels,
            None,
            deferred,
            target as nat,
        );
        assert(streaming_pending_descriptors_at(
            deferred,
            top as int,
        ) == Seq::<BranchChildDescriptor>::empty());
        streaming_index_emitted_core_layout(
            old_levels,
            new_levels,
            old_pending,
            new_pending,
            deferred,
            target,
            descriptor,
            emitted,
        );
        if count <= old_levels.len() {
            assert(new_levels[top as int].entries()
                == old_levels[top as int].entries());
            assert_seqs_equal!(
                streaming_levels_frontier(
                    new_levels,
                    Some(new_pending),
                    deferred,
                    count,
                ),
                streaming_levels_replace_pending(
                    old_levels,
                    Some(old_pending),
                    deferred,
                    count,
                    target,
                    descriptor,
                ),
                i => {}
            );
        } else {
            assert(old_levels.len() == target + 1);
            assert(new_levels[top as int].entries().len() == 0);
            assert_seqs_equal!(
                streaming_levels_frontier(
                    new_levels,
                    Some(new_pending),
                    deferred,
                    count,
                ),
                streaming_levels_replace_pending(
                    old_levels,
                    Some(old_pending),
                    deferred,
                    old_levels.len(),
                    target,
                    descriptor,
                ),
                i => {}
            );
        }
    }
}

proof fn streaming_finish_pages_layout(
    old_levels: Seq<StreamingIndexTail>,
    new_levels: Seq<StreamingIndexTail>,
    pending: StreamingPendingPage,
    deferred: Option<StreamingPendingPage>,
    target: int,
    count: nat,
)
    requires
        old_levels.len() <= new_levels.len()
            <= old_levels.len() + 1,
        0 <= target < old_levels.len(),
        new_levels.len() > target + 1,
        target + 1 < count <= new_levels.len(),
        count > old_levels.len() ==> {
            &&& count == old_levels.len() + 1
            &&& old_levels.len() == target + 1
        },
        pending is Index,
        streaming_pending_parent_level(pending) as int == target + 1,
        match deferred {
            Some(page) => {
                &&& page is Index
                &&& streaming_pending_parent_level(page) as int
                    == target + 1
            },
            None => true,
        },
        streaming_pending_descriptors_at(
            Some(pending),
            target + 1,
        ) + streaming_pending_descriptors_at(
            deferred,
            target + 1,
        ) == old_levels[target].entries(),
        new_levels[target].entries().len() == 0,
        forall |i: int| 0 <= i < old_levels.len() && i != target
            ==> (#[trigger] new_levels[i]).entries()
                == old_levels[i].entries(),
        new_levels.len() == old_levels.len() + 1
            ==> new_levels[new_levels.len() as int - 1].entries().len() == 0,
    ensures
        streaming_levels_frontier(
            new_levels,
            Some(pending),
            deferred,
            count,
        ) == streaming_levels_frontier(
            old_levels,
            None,
            None,
            if count <= old_levels.len() {
                count
            } else {
                old_levels.len()
            },
        ),
    decreases count,
{
    reveal_with_fuel(streaming_levels_frontier, 2);
    let top = (count - 1) as nat;
    if top as int > target + 1 {
        assert(count <= old_levels.len());
        streaming_finish_pages_layout(
            old_levels,
            new_levels,
            pending,
            deferred,
            target,
            top,
        );
        assert(streaming_pending_descriptors_at(
            Some(pending),
            top as int,
        ) == Seq::<BranchChildDescriptor>::empty());
        assert(streaming_pending_descriptors_at(
            deferred,
            top as int,
        ) == Seq::<BranchChildDescriptor>::empty());
        assert(new_levels[top as int].entries()
            == old_levels[top as int].entries());
    } else {
        assert(top as int == target + 1);
        let below_count = target as nat;
        streaming_pending_above_count_invisible(
            new_levels,
            pending,
            deferred,
            below_count,
        );
        match deferred {
            Some(page) => {
                streaming_deferred_above_count_invisible(
                    new_levels,
                    None,
                    page,
                    below_count,
                );
            },
            None => {},
        }
        streaming_frontier_entries_extensional(
            new_levels,
            old_levels,
            None,
            None,
            below_count,
        );
        let pages = streaming_pending_descriptors_at(
            Some(pending),
            target + 1,
        ) + streaming_pending_descriptors_at(
            deferred,
            target + 1,
        );
        assert(pages == old_levels[target].entries());
        if count <= old_levels.len() {
            assert(new_levels[top as int].entries()
                == old_levels[top as int].entries());
        } else {
            assert(old_levels.len() == target + 1);
            assert(new_levels[top as int].entries().len() == 0);
        }
    }
    assert_seqs_equal!(
        streaming_levels_frontier(
            new_levels,
            Some(pending),
            deferred,
            count,
        ),
        streaming_levels_frontier(
            old_levels,
            None,
            None,
            if count <= old_levels.len() {
                count
            } else {
                old_levels.len()
            },
        ),
        i => {}
    );
}

proof fn streaming_empty_levels_frontier(
    levels: Seq<StreamingIndexTail>,
    count: nat,
)
    requires
        count <= levels.len(),
        forall |i: int| 0 <= i < count
            ==> (#[trigger] levels[i]).entries().len() == 0,
    ensures
        streaming_levels_frontier(
            levels,
            None,
            None,
            count,
        ).len() == 0,
    decreases count,
{
    reveal_with_fuel(streaming_levels_frontier, 2);
    if count > 0 {
        streaming_empty_levels_frontier(levels, (count - 1) as nat);
    }
}

pub open spec fn streaming_descriptor_frontier_wf(
    descriptors: Seq<BranchChildDescriptor>,
) -> bool {
    &&& forall |i: int| 0 <= i < descriptors.len()
        ==> (#[trigger] descriptors[i]).wf()
    &&& forall |i: int, j: int|
        #![trigger descriptors[i], descriptors[j]]
        0 <= i < j < descriptors.len() ==> {
            &&& descriptors[i].receipt@.nodes.dom().disjoint(
                descriptors[j].receipt@.nodes.dom(),
            )
            &&& descriptors[i].receipt@.last_key.0
                < descriptors[j].first_key.0
        }
}

pub open spec fn streaming_pending_page_wf(
    pending: StreamingPendingPage,
    leaf_capacity: usize,
    index_fanout: usize,
) -> bool {
    match pending {
        StreamingPendingPage::Leaf { entries, parent_level } => {
            &&& parent_level == 0
            &&& 0 < entries.len() <= leaf_capacity
            &&& MemtableBucket::strictly_sorted(entries@)
        },
        StreamingPendingPage::Index { children, parent_level } => {
            &&& parent_level > 0
            &&& 0 < children.len() <= index_fanout
            &&& descriptor_sequence_wf(children@)
            &&& forall |i: int| 0 <= i < children@.len()
                ==> (#[trigger] children@[i]).receipt@.height + 1
                    == parent_level as nat
        },
    }
}

proof fn streaming_leaf_pending_does_not_change_frontier(
    levels: Seq<StreamingIndexTail>,
    pending: StreamingPendingPage,
    count: nat,
)
    requires
        pending is Leaf,
        count <= levels.len(),
    ensures
        streaming_levels_frontier(
            levels,
            Some(pending),
            None,
            count,
        ) == streaming_levels_frontier(
            levels,
            None,
            None,
            count,
        ),
    decreases count,
{
    reveal_with_fuel(streaming_levels_frontier, 2);
    if count > 0 {
        let level = (count - 1) as nat;
        assert(streaming_pending_descriptors_at(
            Some(pending),
            level as int,
        ) == Seq::<BranchChildDescriptor>::empty());
        streaming_leaf_pending_does_not_change_frontier(
            levels,
            pending,
            level,
        );
    }
}

proof fn streaming_leaf_pages_do_not_change_frontier(
    levels: Seq<StreamingIndexTail>,
    pending: Option<StreamingPendingPage>,
    deferred: Option<StreamingPendingPage>,
    count: nat,
)
    requires
        count <= levels.len(),
        pending is None || pending->0 is Leaf,
        deferred is None || deferred->0 is Leaf,
    ensures
        streaming_levels_frontier(
            levels,
            pending,
            deferred,
            count,
        ) == streaming_levels_frontier(
            levels,
            None,
            None,
            count,
        ),
    decreases count,
{
    reveal_with_fuel(streaming_levels_frontier, 2);
    if count > 0 {
        let level = (count - 1) as nat;
        assert(streaming_pending_descriptors_at(
            pending,
            level as int,
        ) == Seq::<BranchChildDescriptor>::empty());
        assert(streaming_pending_descriptors_at(
            deferred,
            level as int,
        ) == Seq::<BranchChildDescriptor>::empty());
        streaming_leaf_pages_do_not_change_frontier(
            levels,
            pending,
            deferred,
            level,
        );
    }
}

proof fn streaming_deferred_leaf_does_not_change_frontier(
    levels: Seq<StreamingIndexTail>,
    pending: Option<StreamingPendingPage>,
    deferred: Option<StreamingPendingPage>,
    count: nat,
)
    requires
        count <= levels.len(),
        deferred is None || deferred->0 is Leaf,
    ensures
        streaming_levels_frontier(
            levels,
            pending,
            deferred,
            count,
        ) == streaming_levels_frontier(
            levels,
            pending,
            None,
            count,
        ),
    decreases count,
{
    reveal_with_fuel(streaming_levels_frontier, 2);
    if count > 0 {
        let level = (count - 1) as nat;
        assert(streaming_pending_descriptors_at(
            deferred,
            level as int,
        ) == Seq::<BranchChildDescriptor>::empty());
        streaming_deferred_leaf_does_not_change_frontier(
            levels,
            pending,
            deferred,
            level,
        );
    }
}

proof fn streaming_frontier_descriptor_nodes_subset(
    frontier: Seq<BranchChildDescriptor>,
    index: int,
)
    requires 0 <= index < frontier.len(),
    ensures frontier[index].receipt@.nodes.dom()
        <= descriptor_forest_nodes(frontier).dom(),
    decreases frontier.len(),
{
    if index == frontier.len() - 1 {
        assert(frontier[index] == frontier.last());
    } else {
        assert(index < frontier.drop_last().len());
        streaming_frontier_descriptor_nodes_subset(
            frontier.drop_last(),
            index,
        );
    }
}

proof fn streaming_frontier_descriptor_nodes_submap(
    frontier: Seq<BranchChildDescriptor>,
    index: int,
)
    requires
        streaming_descriptor_frontier_wf(frontier),
        0 <= index < frontier.len(),
    ensures frontier[index].receipt@.nodes
        <= descriptor_forest_nodes(frontier),
    decreases frontier.len(),
{
    if index == frontier.len() - 1 {
        assert(frontier[index] == frontier.last());
        assert forall |addr: Address|
            #[trigger] frontier[index].receipt@.nodes.contains_key(addr)
            implies descriptor_forest_nodes(frontier).contains_key(addr)
                && frontier[index].receipt@.nodes[addr]
                    == descriptor_forest_nodes(frontier)[addr] by {
        }
    } else {
        assert(index < frontier.drop_last().len());
        assert(streaming_descriptor_frontier_wf(
            frontier.drop_last(),
        )) by {
            assert forall |i: int| 0 <= i < frontier.drop_last().len()
                implies (#[trigger] frontier.drop_last()[i]).wf() by {}
            assert forall |i: int, j: int|
                #![trigger frontier.drop_last()[i],
                    frontier.drop_last()[j]]
                0 <= i < j < frontier.drop_last().len()
                implies {
                    &&& frontier.drop_last()[i].receipt@.nodes.dom()
                        .disjoint(
                            frontier.drop_last()[j]
                                .receipt@.nodes.dom(),
                        )
                    &&& frontier.drop_last()[i].receipt@.last_key.0
                        < frontier.drop_last()[j].first_key.0
                } by {}
        }
        streaming_frontier_descriptor_nodes_submap(
            frontier.drop_last(),
            index,
        );
        assert(frontier.drop_last()[index] == frontier[index]);
        assert forall |addr: Address|
            #[trigger] frontier[index].receipt@.nodes.contains_key(addr)
            implies descriptor_forest_nodes(frontier).contains_key(addr)
                && frontier[index].receipt@.nodes[addr]
                    == descriptor_forest_nodes(frontier)[addr] by {
            assert(descriptor_forest_nodes(frontier.drop_last())
                .contains_key(addr));
            assert(!frontier.last().receipt@.nodes.contains_key(addr)) by {
                assert(frontier[index].receipt@.nodes.dom().disjoint(
                    frontier.last().receipt@.nodes.dom(),
                ));
            }
        }
    }
}

proof fn streaming_descriptor_forest_push(
    frontier: Seq<BranchChildDescriptor>,
    descriptor: BranchChildDescriptor,
)
    ensures
        descriptor_forest_nodes(frontier.push(descriptor))
            == descriptor_forest_nodes(frontier).union_prefer_right(
                descriptor.receipt@.nodes,
            ),
        descriptor_forest_contents(frontier.push(descriptor))
            == descriptor_forest_contents(frontier).union_prefer_right(
                descriptor.receipt@.pivot.i().map,
            ),
{
    assert(frontier.push(descriptor).drop_last() == frontier);
    assert(frontier.push(descriptor).last() == descriptor);
}

proof fn streaming_levels_frontier_contains_descriptor(
    levels: Seq<StreamingIndexTail>,
    pending: Option<StreamingPendingPage>,
    deferred: Option<StreamingPendingPage>,
    count: nat,
    level: int,
    index: int,
)
    requires
        count <= levels.len(),
        0 <= level < count,
        0 <= index < levels[level].entries().len(),
    ensures
        streaming_levels_frontier(
            levels,
            pending,
            deferred,
            count,
        ).contains(levels[level].entries()[index]),
    decreases count,
{
    reveal_with_fuel(streaming_levels_frontier, 2);
    let top = (count - 1) as nat;
    let top_prefix = levels[top as int].entries()
        + streaming_pending_descriptors_at(pending, top as int)
        + streaming_pending_descriptors_at(deferred, top as int);
    let lower = streaming_levels_frontier(
        levels,
        pending,
        deferred,
        top,
    );
    assert(streaming_levels_frontier(
        levels,
        pending,
        deferred,
        count,
    ) == top_prefix + lower);
    if level == top as int {
        let position = index;
        assert((top_prefix + lower)[position]
            == levels[level].entries()[index]);
    } else {
        streaming_levels_frontier_contains_descriptor(
            levels,
            pending,
            deferred,
            top,
            level,
            index,
        );
        let lower_index = lower.index_of(levels[level].entries()[index]);
        let position = top_prefix.len() as int + lower_index;
        assert((top_prefix + lower)[position]
            == lower[lower_index]);
    }
}

proof fn streaming_levels_frontier_contains_pending_descriptor(
    levels: Seq<StreamingIndexTail>,
    pending: StreamingPendingPage,
    deferred: Option<StreamingPendingPage>,
    count: nat,
    target: int,
    index: int,
)
    requires
        count <= levels.len(),
        0 <= target < count,
        streaming_pending_parent_level(pending) as int == target,
        0 <= index < streaming_pending_descriptors_at(
            Some(pending),
            target,
        ).len(),
    ensures
        streaming_levels_frontier(
            levels,
            Some(pending),
            deferred,
            count,
        ).contains(streaming_pending_descriptors_at(
            Some(pending),
            target,
        )[index]),
    decreases count,
{
    reveal_with_fuel(streaming_levels_frontier, 2);
    let top = (count - 1) as nat;
    let top_prefix = levels[top as int].entries()
        + streaming_pending_descriptors_at(
            Some(pending),
            top as int,
        )
        + streaming_pending_descriptors_at(deferred, top as int);
    let lower = streaming_levels_frontier(
        levels,
        Some(pending),
        deferred,
        top,
    );
    if top as int == target {
        let pending_entries = streaming_pending_descriptors_at(
            Some(pending),
            target,
        );
        let position = levels[top as int].entries().len() as int + index;
        assert(top_prefix[position] == pending_entries[index]);
        assert((top_prefix + lower)[position] == pending_entries[index]);
    } else {
        assert(top as int > target);
        streaming_levels_frontier_contains_pending_descriptor(
            levels,
            pending,
            deferred,
            top,
            target,
            index,
        );
        let candidate = streaming_pending_descriptors_at(
            Some(pending),
            target,
        )[index];
        let lower_index = lower.index_of(candidate);
        assert((top_prefix + lower)[
            top_prefix.len() as int + lower_index
        ] == candidate);
    }
}

pub open spec fn streaming_order_witness(
    frontier: Seq<BranchChildDescriptor>,
    left_descriptor: BranchChildDescriptor,
    right_descriptor: BranchChildDescriptor,
    left: int,
    right: int,
) -> bool {
    0 <= left < right < frontier.len()
        && frontier[left] == left_descriptor
        && frontier[right] == right_descriptor
}

proof fn streaming_level_entry_precedes_pending(
    levels: Seq<StreamingIndexTail>,
    pending: StreamingPendingPage,
    deferred: Option<StreamingPendingPage>,
    count: nat,
    target: int,
    level_index: int,
    pending_index: int,
) -> (out: (int, int))
    requires
        count <= levels.len(),
        0 <= target < count,
        streaming_pending_parent_level(pending) as int == target,
        0 <= level_index < levels[target].entries().len(),
        0 <= pending_index < streaming_pending_descriptors_at(
            Some(pending),
            target,
        ).len(),
    ensures streaming_order_witness(
        streaming_levels_frontier(
            levels,
            Some(pending),
            deferred,
            count,
        ),
        levels[target].entries()[level_index],
        streaming_pending_descriptors_at(
            Some(pending),
            target,
        )[pending_index],
        out.0,
        out.1,
    ),
    decreases count,
{
    reveal_with_fuel(streaming_levels_frontier, 2);
    let top = (count - 1) as nat;
    let top_prefix = levels[top as int].entries()
        + streaming_pending_descriptors_at(
            Some(pending),
            top as int,
        )
        + streaming_pending_descriptors_at(deferred, top as int);
    let lower = streaming_levels_frontier(
        levels,
        Some(pending),
        deferred,
        top,
    );
    if top as int == target {
        let left = level_index;
        let right = levels[target].entries().len() as int
            + pending_index;
        assert((top_prefix + lower)[left]
            == levels[target].entries()[level_index]);
        assert((top_prefix + lower)[right]
            == streaming_pending_descriptors_at(
                Some(pending),
                target,
            )[pending_index]);
        assert(streaming_order_witness(
            streaming_levels_frontier(
                levels,
                Some(pending),
                deferred,
                count,
            ),
            levels[target].entries()[level_index],
            streaming_pending_descriptors_at(
                Some(pending),
                target,
            )[pending_index],
            left,
            right,
        ));
        (left, right)
    } else {
        assert(top as int > target);
        let lower_out = streaming_level_entry_precedes_pending(
            levels,
            pending,
            deferred,
            top,
            target,
            level_index,
            pending_index,
        );
        let lower_left = lower_out.0;
        let lower_right = lower_out.1;
        let left = top_prefix.len() as int + lower_left;
        let right = top_prefix.len() as int + lower_right;
        assert((top_prefix + lower)[left] == lower[lower_left]);
        assert((top_prefix + lower)[right] == lower[lower_right]);
        assert(streaming_order_witness(
            streaming_levels_frontier(
                levels,
                Some(pending),
                deferred,
                count,
            ),
            levels[target].entries()[level_index],
            streaming_pending_descriptors_at(
                Some(pending),
                target,
            )[pending_index],
            left,
            right,
        ));
        (left, right)
    }
}

proof fn descriptor_forest_nodes_subset_from_members(
    descriptors: Seq<BranchChildDescriptor>,
    nodes: LoadedBranch,
)
    requires
        forall |i: int| 0 <= i < descriptors.len()
            ==> (#[trigger] descriptors[i]).receipt@.nodes <= nodes,
    ensures descriptor_forest_nodes(descriptors) <= nodes,
    decreases descriptors.len(),
{
    if descriptors.len() > 0 {
        descriptor_forest_nodes_subset_from_members(
            descriptors.drop_last(),
            nodes,
        );
        assert(descriptors.drop_last().len()
            == descriptors.len() - 1);
        assert(descriptors.last()
            == descriptors[descriptors.len() - 1]);
        assert(descriptor_forest_nodes(descriptors.drop_last()) <= nodes);
        assert(descriptors.last().receipt@.nodes <= nodes);
        assert forall |addr: Address|
            #[trigger] descriptor_forest_nodes(descriptors)
                .contains_key(addr)
            implies nodes.contains_key(addr)
                && descriptor_forest_nodes(descriptors)[addr]
                    == nodes[addr] by {
            if descriptors.last().receipt@.nodes.contains_key(addr) {
            } else {
                assert(descriptor_forest_nodes(descriptors.drop_last())
                    .contains_key(addr));
            }
        }
    }
}

proof fn descriptor_forest_nodes_contains_member(
    descriptors: Seq<BranchChildDescriptor>,
    addr: Address,
)
    requires descriptor_forest_nodes(descriptors).contains_key(addr),
    ensures exists |i: int| 0 <= i < descriptors.len()
        && (#[trigger] descriptors[i]).receipt@.nodes.contains_key(addr),
    decreases descriptors.len(),
{
    if descriptors.len() > 0 {
        if descriptors.last().receipt@.nodes.contains_key(addr) {
            let i = descriptors.len() - 1;
            assert(descriptors[i] == descriptors.last());
        } else {
            assert(descriptor_forest_nodes(descriptors.drop_last())
                .contains_key(addr));
            descriptor_forest_nodes_contains_member(
                descriptors.drop_last(),
                addr,
            );
            let i = choose |i: int| 0 <= i < descriptors.drop_last().len()
                && (#[trigger] descriptors.drop_last()[i])
                    .receipt@.nodes.contains_key(addr);
            assert(descriptors.drop_last()[i] == descriptors[i]);
        }
    }
}

proof fn streaming_map_union_assoc<K, V>(
    left: Map<K, V>,
    middle: Map<K, V>,
    right: Map<K, V>,
)
    ensures
        left.union_prefer_right(middle).union_prefer_right(right)
            == left.union_prefer_right(
                middle.union_prefer_right(right),
            ),
{
    assert_maps_equal!(
        left.union_prefer_right(middle).union_prefer_right(right),
        left.union_prefer_right(middle.union_prefer_right(right)),
        key => {}
    );
}

proof fn streaming_descriptor_forest_contents_concat(
    left: Seq<BranchChildDescriptor>,
    right: Seq<BranchChildDescriptor>,
)
    ensures
        descriptor_forest_contents(left + right)
            == descriptor_forest_contents(left).union_prefer_right(
                descriptor_forest_contents(right),
            ),
    decreases right.len(),
{
    if right.len() > 0 {
        streaming_descriptor_forest_contents_concat(
            left,
            right.drop_last(),
        );
        assert((left + right).drop_last()
            == left + right.drop_last());
        assert((left + right).last() == right.last());
        streaming_map_union_assoc(
            descriptor_forest_contents(left),
            descriptor_forest_contents(right.drop_last()),
            right.last().receipt@.pivot.i().map,
        );
    }
}

proof fn streaming_descriptor_forest_nodes_concat(
    left: Seq<BranchChildDescriptor>,
    right: Seq<BranchChildDescriptor>,
)
    ensures
        descriptor_forest_nodes(left + right)
            == descriptor_forest_nodes(left).union_prefer_right(
                descriptor_forest_nodes(right),
            ),
    decreases right.len(),
{
    if right.len() > 0 {
        streaming_descriptor_forest_nodes_concat(
            left,
            right.drop_last(),
        );
        assert((left + right).drop_last()
            == left + right.drop_last());
        assert((left + right).last() == right.last());
        streaming_map_union_assoc(
            descriptor_forest_nodes(left),
            descriptor_forest_nodes(right.drop_last()),
            right.last().receipt@.nodes,
        );
    }
}

proof fn streaming_descriptor_forest_singleton(
    descriptor: BranchChildDescriptor,
)
    ensures
        descriptor_forest_contents(Seq::empty().push(descriptor))
            == descriptor.receipt@.pivot.i().map,
        descriptor_forest_nodes(Seq::empty().push(descriptor))
            == descriptor.receipt@.nodes,
{
    reveal_with_fuel(descriptor_forest_contents, 2);
    reveal_with_fuel(descriptor_forest_nodes, 2);
}

proof fn descriptor_frontier_collapse_parts(
    old_frontier: Seq<BranchChildDescriptor>,
    children: Seq<BranchChildDescriptor>,
    descriptor: BranchChildDescriptor,
    new_frontier: Seq<BranchChildDescriptor>,
) -> (out: (
    Seq<BranchChildDescriptor>,
    Seq<BranchChildDescriptor>,
))
    requires descriptor_frontier_collapse(
        old_frontier,
        children,
        descriptor,
        new_frontier,
    ),
    ensures descriptor_frontier_collapse_witness(
        old_frontier,
        children,
        descriptor,
        new_frontier,
        out.0,
        out.1,
    ),
{
    let (prefix, suffix) = choose |
            prefix: Seq<BranchChildDescriptor>,
            suffix: Seq<BranchChildDescriptor>|
        #[trigger] descriptor_frontier_collapse_witness(
            old_frontier,
            children,
            descriptor,
            new_frontier,
            prefix,
            suffix,
        );
    (prefix, suffix)
}

proof fn streaming_frontier_collapse_preserves_wf(
    old_frontier: Seq<BranchChildDescriptor>,
    children: Seq<BranchChildDescriptor>,
    descriptor: BranchChildDescriptor,
    new_frontier: Seq<BranchChildDescriptor>,
    prefix: Seq<BranchChildDescriptor>,
    suffix: Seq<BranchChildDescriptor>,
    addr: Address,
    node: BranchNode,
)
    requires
        streaming_descriptor_frontier_wf(old_frontier),
        descriptor_frontier_collapse_witness(
            old_frontier,
            children,
            descriptor,
            new_frontier,
            prefix,
            suffix,
        ),
        children.len() > 0,
        descriptor.wf(),
        descriptor.first_key == children.first().first_key,
        descriptor.receipt@.last_key
            == children.last().receipt@.last_key,
        descriptor.receipt@.nodes
            == descriptor_forest_nodes(children).insert(addr, node),
        !descriptor_forest_nodes(old_frontier).contains_key(addr),
    ensures streaming_descriptor_frontier_wf(new_frontier),
{
    assert forall |i: int| 0 <= i < new_frontier.len()
        implies (#[trigger] new_frontier[i]).wf() by {
        if i < prefix.len() {
            assert(new_frontier[i] == prefix[i]);
            assert(old_frontier[i] == prefix[i]);
        } else if i == prefix.len() {
            assert(new_frontier[i] == descriptor);
        } else {
            let suffix_index = i - prefix.len() - 1;
            let old_index = prefix.len() as int
                + children.len() as int + suffix_index;
            assert(new_frontier[i] == suffix[suffix_index]);
            assert(old_frontier[old_index] == suffix[suffix_index]);
        }
    }
    assert forall |i: int, j: int|
        #![trigger new_frontier[i], new_frontier[j]]
        0 <= i < j < new_frontier.len()
        implies {
            &&& new_frontier[i].receipt@.nodes.dom().disjoint(
                new_frontier[j].receipt@.nodes.dom(),
            )
            &&& new_frontier[i].receipt@.last_key.0
                < new_frontier[j].first_key.0
        } by {
        if i < prefix.len() && j == prefix.len() {
            let old_descriptor = prefix[i];
            assert(old_frontier[i] == old_descriptor);
            assert(new_frontier[i] == old_descriptor);
            assert(new_frontier[j] == descriptor);
            assert forall |candidate: Address|
                #[trigger] old_descriptor.receipt@.nodes
                    .contains_key(candidate)
                implies !descriptor.receipt@.nodes
                    .contains_key(candidate) by {
                streaming_frontier_descriptor_nodes_submap(
                    old_frontier,
                    i,
                );
                assert(candidate != addr);
                if descriptor_forest_nodes(children).contains_key(candidate) {
                    descriptor_forest_nodes_contains_member(
                        children,
                        candidate,
                    );
                    let child_index = choose |child_index: int|
                        0 <= child_index < children.len()
                        && (#[trigger] children[child_index])
                            .receipt@.nodes.contains_key(candidate);
                    let old_child_index = prefix.len() as int + child_index;
                    assert(old_frontier[old_child_index]
                        == children[child_index]);
                    assert(old_frontier[i].receipt@.nodes.dom().disjoint(
                        old_frontier[old_child_index].receipt@.nodes.dom(),
                    ));
                }
            }
            let first_child_index = prefix.len() as int;
            assert(old_frontier[first_child_index] == children.first());
            assert(old_frontier[i].receipt@.last_key.0
                < old_frontier[first_child_index].first_key.0);
        } else if i == prefix.len() {
            let suffix_index = j - prefix.len() - 1;
            let old_suffix_index = prefix.len() as int
                + children.len() as int + suffix_index;
            assert(new_frontier[i] == descriptor);
            assert(new_frontier[j] == suffix[suffix_index]);
            assert(old_frontier[old_suffix_index]
                == suffix[suffix_index]);
            assert forall |candidate: Address|
                #[trigger] descriptor.receipt@.nodes.contains_key(candidate)
                implies !suffix[suffix_index].receipt@.nodes
                    .contains_key(candidate) by {
                if candidate == addr {
                    streaming_frontier_descriptor_nodes_submap(
                        old_frontier,
                        old_suffix_index,
                    );
                    assert(suffix[suffix_index].receipt@.nodes
                        <= descriptor_forest_nodes(old_frontier));
                } else {
                    assert(descriptor_forest_nodes(children)
                        .contains_key(candidate));
                    descriptor_forest_nodes_contains_member(
                        children,
                        candidate,
                    );
                    let child_index = choose |child_index: int|
                        0 <= child_index < children.len()
                        && (#[trigger] children[child_index])
                            .receipt@.nodes.contains_key(candidate);
                    let old_child_index = prefix.len() as int + child_index;
                    assert(old_frontier[old_child_index]
                        == children[child_index]);
                    assert(old_frontier[old_child_index]
                        .receipt@.nodes.dom().disjoint(
                            old_frontier[old_suffix_index]
                                .receipt@.nodes.dom(),
                        ));
                }
            }
            let last_child_index = prefix.len() as int
                + children.len() as int - 1;
            assert(old_frontier[last_child_index] == children.last());
            assert(old_frontier[last_child_index].receipt@.last_key.0
                < old_frontier[old_suffix_index].first_key.0);
        } else {
            let old_i = if i < prefix.len() {
                i
            } else {
                prefix.len() as int + children.len() as int
                    + (i - prefix.len() - 1)
            };
            let old_j = if j < prefix.len() {
                j
            } else {
                prefix.len() as int + children.len() as int
                    + (j - prefix.len() - 1)
            };
            assert(old_i < old_j);
            assert(new_frontier[i] == old_frontier[old_i]);
            assert(new_frontier[j] == old_frontier[old_j]);
        }
    }
}

proof fn streaming_frontier_push_wf(
    frontier: Seq<BranchChildDescriptor>,
    descriptor: BranchChildDescriptor,
)
    requires
        streaming_descriptor_frontier_wf(frontier),
        descriptor.wf(),
        forall |i: int| 0 <= i < frontier.len() ==> {
            &&& (#[trigger] frontier[i]).receipt@.nodes.dom().disjoint(
                descriptor.receipt@.nodes.dom(),
            )
            &&& frontier[i].receipt@.last_key.0
                < descriptor.first_key.0
        },
    ensures streaming_descriptor_frontier_wf(
        frontier.push(descriptor),
    ),
{
    assert forall |i: int| 0 <= i < frontier.push(descriptor).len()
        implies (#[trigger] frontier.push(descriptor)[i]).wf() by {
        if i == frontier.len() {
            assert(frontier.push(descriptor)[i] == descriptor);
        } else {
            assert(frontier.push(descriptor)[i] == frontier[i]);
        }
    }
    assert forall |i: int, j: int|
        #![trigger frontier.push(descriptor)[i], frontier.push(descriptor)[j]]
        0 <= i < j < frontier.push(descriptor).len()
        implies {
            &&& frontier.push(descriptor)[i].receipt@.nodes.dom().disjoint(
                frontier.push(descriptor)[j].receipt@.nodes.dom(),
            )
            &&& frontier.push(descriptor)[i].receipt@.last_key.0
                < frontier.push(descriptor)[j].first_key.0
        } by {
        if j == frontier.len() {
            assert(frontier.push(descriptor)[j] == descriptor);
            assert(frontier.push(descriptor)[i] == frontier[i]);
        } else {
            assert(frontier.push(descriptor)[i] == frontier[i]);
            assert(frontier.push(descriptor)[j] == frontier[j]);
        }
    }
}

proof fn streaming_level_zero_push_layout(
    old_levels: Seq<StreamingIndexTail>,
    new_levels: Seq<StreamingIndexTail>,
    descriptor: BranchChildDescriptor,
    count: nat,
)
    requires
        0 < count <= old_levels.len(),
        new_levels.len() == old_levels.len(),
        new_levels[0].entries()
            == old_levels[0].entries().push(descriptor),
        forall |i: int| 1 <= i < old_levels.len()
            ==> (#[trigger] new_levels[i]).entries()
                == old_levels[i].entries(),
    ensures
        streaming_levels_frontier(
            new_levels,
            None,
            None,
            count,
        ) == streaming_levels_frontier(
            old_levels,
            None,
            None,
            count,
        ).push(descriptor),
    decreases count,
{
    reveal_with_fuel(streaming_levels_frontier, 2);
    if count > 1 {
        let level = (count - 1) as nat;
        streaming_level_zero_push_layout(
            old_levels,
            new_levels,
            descriptor,
            level,
        );
        assert(new_levels[level as int].entries()
            == old_levels[level as int].entries());
        assert_seqs_equal!(
            streaming_levels_frontier(
                new_levels,
                None,
                None,
                count,
            ),
            streaming_levels_frontier(
                old_levels,
                None,
                None,
                count,
            ).push(descriptor),
            i => {}
        );
    }
}

proof fn streaming_level_zero_reflow_layout(
    old_levels: Seq<StreamingIndexTail>,
    new_levels: Seq<StreamingIndexTail>,
    pending: StreamingPendingPage,
    children: Seq<BranchChildDescriptor>,
    descriptor: BranchChildDescriptor,
    count: nat,
)
    requires
        2 <= count <= old_levels.len(),
        new_levels.len() == old_levels.len(),
        pending is Index,
        streaming_pending_parent_level(pending) == 1,
        streaming_pending_descriptors_at(Some(pending), 1) == children,
        children + new_levels[0].entries()
            =~= old_levels[0].entries().push(descriptor),
        forall |i: int| 1 <= i < old_levels.len()
            ==> (#[trigger] new_levels[i]).entries()
                == old_levels[i].entries(),
    ensures
        streaming_levels_frontier(
            new_levels,
            Some(pending),
            None,
            count,
        ) == streaming_levels_frontier(
            old_levels,
            None,
            None,
            count,
        ).push(descriptor),
    decreases count,
{
    reveal_with_fuel(streaming_levels_frontier, 2);
    if count > 2 {
        let level = (count - 1) as nat;
        assert(streaming_pending_descriptors_at(
            Some(pending),
            level as int,
        ) == Seq::<BranchChildDescriptor>::empty());
        streaming_level_zero_reflow_layout(
            old_levels,
            new_levels,
            pending,
            children,
            descriptor,
            level,
        );
        assert(new_levels[level as int].entries()
            == old_levels[level as int].entries());
        assert_seqs_equal!(
            streaming_levels_frontier(
                new_levels,
                Some(pending),
                None,
                count,
            ),
            streaming_levels_frontier(
                old_levels,
                None,
                None,
                count,
            ).push(descriptor),
            i => {}
        );
    } else {
        assert(streaming_pending_descriptors_at(
            Some(pending),
            1,
        ) == children);
        assert(streaming_pending_descriptors_at(
            Some(pending),
            0,
        ) == Seq::<BranchChildDescriptor>::empty());
        assert(children + new_levels[0].entries()
            == old_levels[0].entries().push(descriptor)) by {
            assert_seqs_equal!(
                children + new_levels[0].entries(),
                old_levels[0].entries().push(descriptor),
                i => {}
            );
        }
        assert(new_levels[1].entries() == old_levels[1].entries());
        let new_frontier = streaming_levels_frontier(
            new_levels,
            Some(pending),
            None,
            count,
        );
        let old_frontier = streaming_levels_frontier(
            old_levels,
            None,
            None,
            count,
        );
        assert(new_frontier == new_levels[1].entries()
            + children + new_levels[0].entries()) by {
            reveal_with_fuel(streaming_levels_frontier, 3);
        }
        assert(old_frontier == old_levels[1].entries()
            + old_levels[0].entries()) by {
            reveal_with_fuel(streaming_levels_frontier, 3);
        }
        assert_seqs_equal!(
            new_levels[1].entries()
                + children + new_levels[0].entries(),
            (old_levels[1].entries()
                + old_levels[0].entries()).push(descriptor),
            i => {}
        );
        assert_seqs_equal!(
            new_frontier,
            old_frontier.push(descriptor),
            i => {}
        );
    }
}

proof fn streaming_level_zero_reflow_new_parent_layout(
    old_levels: Seq<StreamingIndexTail>,
    new_levels: Seq<StreamingIndexTail>,
    pending: StreamingPendingPage,
    children: Seq<BranchChildDescriptor>,
    descriptor: BranchChildDescriptor,
)
    requires
        old_levels.len() == 1,
        new_levels.len() == 2,
        new_levels[1].entries().len() == 0,
        pending is Index,
        streaming_pending_parent_level(pending) == 1,
        streaming_pending_descriptors_at(Some(pending), 1) == children,
        children + new_levels[0].entries()
            =~= old_levels[0].entries().push(descriptor),
    ensures
        streaming_levels_frontier(
            new_levels,
            Some(pending),
            None,
            new_levels.len(),
        ) == streaming_levels_frontier(
            old_levels,
            None,
            None,
            old_levels.len(),
        ).push(descriptor),
{
    reveal_with_fuel(streaming_levels_frontier, 3);
    assert(streaming_pending_descriptors_at(
        Some(pending),
        0,
    ) == Seq::<BranchChildDescriptor>::empty());
    assert(children + new_levels[0].entries()
        == old_levels[0].entries().push(descriptor)) by {
        assert_seqs_equal!(
            children + new_levels[0].entries(),
            old_levels[0].entries().push(descriptor),
            i => {}
        );
    }
}

impl StreamingBranchBuilder {
    pub open spec fn active_frontier(&self) -> Seq<BranchChildDescriptor> {
        match self.phase {
            StreamingBranchPhase::ReadyIndexRoot => self.root_children@,
            StreamingBranchPhase::Sealed => Seq::empty(),
            _ => streaming_levels_frontier(
                self.levels@,
                self.pending,
                self.deferred,
                self.levels@.len(),
            ),
        }
    }

    pub open spec fn unstaged_leaf_entries(&self) -> Seq<MemtableEntry> {
        streaming_pending_leaf_entries(self.pending)
            + streaming_pending_leaf_entries(self.deferred)
            + self.leaf_tail.entries()
    }

    pub closed spec fn layout_wf(&self) -> bool {
        &&& self.leaf_tail.wf()
        &&& self.index_fanout > 1
        &&& self.index_fanout <= u8::MAX as usize + 1
        &&& forall |i: int| 0 <= i < self.levels@.len() ==> {
            &&& (#[trigger] self.levels@[i]).wf()
            &&& self.levels@[i].capacity == self.index_fanout
            &&& forall |j: int|
                0 <= j < self.levels@[i].entries().len()
                ==> {
                    let descriptor = #[trigger] self.levels@[i].entries()[j];
                    descriptor.receipt@.height == i as nat
                }
        }
        &&& match self.pending {
            Some(pending) => {
                &&& streaming_pending_page_wf(
                    pending,
                    self.leaf_tail.capacity,
                    self.index_fanout,
                )
                &&& streaming_pending_parent_level(pending)
                    < self.levels.len()
            },
            None => true,
        }
        &&& match self.deferred {
            Some(deferred) => {
                &&& self.pending is Some
                &&& streaming_pending_parent_level(deferred)
                    <= streaming_pending_parent_level(self.pending->0)
                &&& streaming_pending_page_wf(
                    deferred,
                    self.leaf_tail.capacity,
                    self.index_fanout,
                )
                &&& streaming_pending_parent_level(deferred)
                    < self.levels.len()
            },
            None => true,
        }
    }

    pub closed spec fn stream_wf(&self) -> bool {
        &&& MemtableBucket::strictly_sorted(self.source_entries@)
        &&& MemtableBucket::strictly_sorted(self.leaf_prefix@)
        &&& (self.phase is ReadyLeafRoot
            || self.phase is Sealed
            || self.source_entries@
                =~= self.leaf_prefix@ + self.unstaged_leaf_entries())
        &&& (self.has_staged_leaf
            <==> self.leaf_prefix@.len() > 0)
        &&& (self.has_staged_leaf ==> self.levels.len() > 0)
        &&& streaming_descriptor_frontier_wf(self.active_frontier())
        &&& forall |i: int| 0 <= i < self.active_frontier().len()
            ==> exists |j: int| 0 <= j < self.leaf_prefix@.len()
                && (#[trigger] self.leaf_prefix@[j]).key
                    == (#[trigger] self.active_frontier()[i])
                        .receipt@.last_key
        &&& forall |i: int, j: int|
            0 <= i < self.active_frontier().len()
            && 0 <= j < self.unstaged_leaf_entries().len()
            ==> (#[trigger] self.active_frontier()[i]).receipt@.last_key.0
                < (#[trigger] self.unstaged_leaf_entries()[j]).key.0
        &&& descriptor_forest_contents(self.active_frontier())
            == MemtableBucket::entries_map(self.leaf_prefix@)
        &&& descriptor_forest_nodes(self.active_frontier())
            == self.staged_nodes@
    }

    pub closed spec fn phase_wf(&self) -> bool {
        &&& match self.phase {
            StreamingBranchPhase::Reading => {
                &&& self.root_leaf.len() == 0
                &&& self.root_children.len() == 0
            },
            StreamingBranchPhase::Finishing { level } => {
                &&& level < self.levels.len()
                &&& self.leaf_tail.entries().len() == 0
                &&& forall |i: int| 0 <= i < level
                    ==> (#[trigger] self.levels@[i]).entries().len() == 0
                &&& (self.pending is Some ==>
                    level <= streaming_pending_parent_level(self.pending->0))
                &&& (self.deferred is Some ==>
                    level <= streaming_pending_parent_level(self.deferred->0))
                &&& self.root_leaf.len() == 0
                &&& self.root_children.len() == 0
            },
            StreamingBranchPhase::ReadyLeafRoot => {
                &&& self.pending is None
                &&& self.deferred is None
                &&& self.leaf_prefix@.len() == 0
                &&& self.root_leaf@ == self.source_entries@
                &&& 0 < self.root_leaf.len()
                &&& self.root_leaf.len() <= self.leaf_tail.capacity
                &&& self.root_children.len() == 0
                &&& self.staged_nodes@ == LoadedBranch::empty()
            },
            StreamingBranchPhase::ReadyIndexRoot => {
                &&& self.pending is None
                &&& self.deferred is None
                &&& self.leaf_tail.entries().len() == 0
                &&& self.leaf_prefix@ == self.source_entries@
                &&& self.root_leaf.len() == 0
                &&& 0 < self.root_children.len()
                &&& self.root_children.len() <= self.index_fanout
                &&& descriptor_sequence_wf(self.root_children@)
            },
            StreamingBranchPhase::Empty => {
                &&& self.source_entries@.len() == 0
                &&& self.root_leaf.len() == 0
                &&& self.root_children.len() == 0
                &&& self.staged_nodes@ == LoadedBranch::empty()
            },
            StreamingBranchPhase::Sealed => true,
        }
    }

    pub open spec fn local_wf(&self) -> bool {
        &&& self.layout_wf()
        &&& self.stream_wf()
        &&& self.phase_wf()
    }

    proof fn expose_layout_wf(&self)
        requires self.layout_wf(),
        ensures
            self.leaf_tail.wf(),
            self.index_fanout > 1,
            self.index_fanout <= u8::MAX as usize + 1,
            forall |i: int| 0 <= i < self.levels@.len() ==> {
                &&& (#[trigger] self.levels@[i]).wf()
                &&& self.levels@[i].capacity == self.index_fanout
                &&& forall |j: int|
                    0 <= j < self.levels@[i].entries().len()
                    ==> (#[trigger] self.levels@[i].entries()[j])
                        .receipt@.height == i as nat
            },
            match self.pending {
                Some(pending) => {
                    &&& streaming_pending_page_wf(
                        pending,
                        self.leaf_tail.capacity,
                        self.index_fanout,
                    )
                    &&& streaming_pending_parent_level(pending)
                        < self.levels.len()
                },
                None => true,
            },
            match self.deferred {
            Some(deferred) => {
                &&& self.pending is Some
                &&& streaming_pending_parent_level(deferred)
                    <= streaming_pending_parent_level(self.pending->0)
                &&& streaming_pending_page_wf(
                        deferred,
                        self.leaf_tail.capacity,
                        self.index_fanout,
                    )
                    &&& streaming_pending_parent_level(deferred)
                        < self.levels.len()
                },
                None => true,
            },
    {
        reveal(StreamingBranchBuilder::layout_wf);
    }

    proof fn expose_stream_wf(&self)
        requires self.stream_wf(),
        ensures
            MemtableBucket::strictly_sorted(self.source_entries@),
            MemtableBucket::strictly_sorted(self.leaf_prefix@),
            self.phase is ReadyLeafRoot
                || self.phase is Sealed
                || self.source_entries@
                    =~= self.leaf_prefix@ + self.unstaged_leaf_entries(),
            self.has_staged_leaf
                <==> self.leaf_prefix@.len() > 0,
            self.has_staged_leaf ==> self.levels.len() > 0,
            streaming_descriptor_frontier_wf(self.active_frontier()),
            forall |i: int| 0 <= i < self.active_frontier().len()
                ==> exists |j: int| 0 <= j < self.leaf_prefix@.len()
                    && (#[trigger] self.leaf_prefix@[j]).key
                        == (#[trigger] self.active_frontier()[i])
                            .receipt@.last_key,
            forall |i: int, j: int|
                0 <= i < self.active_frontier().len()
                && 0 <= j < self.unstaged_leaf_entries().len()
                ==> (#[trigger] self.active_frontier()[i])
                        .receipt@.last_key.0
                    < (#[trigger] self.unstaged_leaf_entries()[j]).key.0,
            descriptor_forest_contents(self.active_frontier())
                == MemtableBucket::entries_map(self.leaf_prefix@),
            descriptor_forest_nodes(self.active_frontier())
                == self.staged_nodes@,
    {
        reveal(StreamingBranchBuilder::stream_wf);
    }

    proof fn expose_phase_wf(&self)
        requires self.phase_wf(),
        ensures
            match self.phase {
                StreamingBranchPhase::Reading => {
                    &&& self.root_leaf.len() == 0
                    &&& self.root_children.len() == 0
                },
                StreamingBranchPhase::Finishing { level } => {
                    &&& level < self.levels.len()
                    &&& self.leaf_tail.entries().len() == 0
                    &&& forall |i: int| 0 <= i < level
                        ==> (#[trigger] self.levels@[i]).entries().len() == 0
                    &&& (self.pending is Some ==>
                        level <= streaming_pending_parent_level(
                            self.pending->0,
                        ))
                    &&& (self.deferred is Some ==>
                        level <= streaming_pending_parent_level(
                            self.deferred->0,
                        ))
                    &&& self.root_leaf.len() == 0
                    &&& self.root_children.len() == 0
                },
                StreamingBranchPhase::ReadyLeafRoot => {
                    &&& self.pending is None
                    &&& self.deferred is None
                    &&& self.leaf_prefix@.len() == 0
                    &&& self.root_leaf@ == self.source_entries@
                    &&& 0 < self.root_leaf.len()
                    &&& self.root_leaf.len() <= self.leaf_tail.capacity
                    &&& self.root_children.len() == 0
                    &&& self.staged_nodes@ == LoadedBranch::empty()
                },
                StreamingBranchPhase::ReadyIndexRoot => {
                    &&& self.pending is None
                    &&& self.deferred is None
                    &&& self.leaf_tail.entries().len() == 0
                    &&& self.leaf_prefix@ == self.source_entries@
                    &&& self.root_leaf.len() == 0
                    &&& 0 < self.root_children.len()
                    &&& self.root_children.len() <= self.index_fanout
                    &&& descriptor_sequence_wf(self.root_children@)
                },
                StreamingBranchPhase::Empty => {
                    &&& self.source_entries@.len() == 0
                    &&& self.root_leaf.len() == 0
                    &&& self.root_children.len() == 0
                    &&& self.staged_nodes@ == LoadedBranch::empty()
                },
                StreamingBranchPhase::Sealed => true,
            },
    {
        reveal(StreamingBranchBuilder::phase_wf);
    }

    pub proof fn pending_leaf_has_leaf_deferred(&self)
        requires
            self.local_wf(),
            self.pending is Some,
            self.pending->0 is Leaf,
        ensures
            self.deferred is None || self.deferred->0 is Leaf,
    {
        self.expose_layout_wf();
        if self.deferred is Some && self.deferred->0 is Index {
            assert(streaming_pending_parent_level(self.pending->0) == 0);
            assert(streaming_pending_parent_level(self.deferred->0) > 0);
            assert(streaming_pending_parent_level(self.deferred->0)
                <= streaming_pending_parent_level(self.pending->0));
            assert(false);
        }
    }

    pub proof fn pending_none_has_no_deferred(&self)
        requires
            self.local_wf(),
            self.pending is None,
        ensures self.deferred is None,
    {
        self.expose_layout_wf();
    }

    pub proof fn ready_leaf_has_no_staged_nodes(&self)
        requires
            self.local_wf(),
            self.phase is ReadyLeafRoot,
        ensures
            self.staged_nodes@ == LoadedBranch::empty(),
    {
        self.expose_phase_wf();
    }

    proof fn leaf_descriptor_append_wf(
        &self,
        entries: Seq<MemtableEntry>,
        descriptor: BranchChildDescriptor,
        addr: Address,
        node: BranchNode,
    )
        requires
            self.local_wf(),
            self.pending is Some,
            self.pending->0 is Leaf,
            self.phase is Reading || self.phase is Finishing,
            entries == streaming_pending_leaf_entries(self.pending),
            descriptor.wf(),
            descriptor.first_key == entries[0].key,
            descriptor.receipt@.nodes == map![addr => node],
            descriptor.receipt@.last_key
                == entries[entries.len() - 1].key,
            descriptor.receipt@.height == 0,
            !self.staged_nodes@.contains_key(addr),
        ensures
            descriptor_sequence_wf(
                self.levels@[0].entries().push(descriptor),
            ),
    {
        self.expose_layout_wf();
        self.expose_stream_wf();
        self.expose_phase_wf();
        let old_level_zero = self.levels@[0].entries();
        assert(descriptor_sequence_wf(
            old_level_zero.push(descriptor),
        )) by {
            assert forall |i: int|
                0 <= i < old_level_zero.push(descriptor).len()
                implies (#[trigger] old_level_zero.push(descriptor)[i])
                    .wf() by {
                if i == old_level_zero.len() {
                    assert(old_level_zero.push(descriptor)[i]
                        == descriptor);
                }
            }
            assert forall |i: int, j: int|
                #![trigger old_level_zero.push(descriptor)[i],
                    old_level_zero.push(descriptor)[j]]
                0 <= i < j < old_level_zero.push(descriptor).len()
                implies old_level_zero.push(descriptor)[i]
                    .receipt@.nodes.dom().disjoint(
                        old_level_zero.push(descriptor)[j]
                            .receipt@.nodes.dom(),
                    ) by {
                if j == old_level_zero.len() {
                    assert(old_level_zero.push(descriptor)[j]
                        == descriptor);
                    assert(old_level_zero.push(descriptor)[i]
                        == old_level_zero[i]);
                    streaming_levels_frontier_contains_descriptor(
                        self.levels@,
                        self.pending,
                        self.deferred,
                        self.levels@.len(),
                        0,
                        i,
                    );
                    let frontier_index = self.active_frontier()
                        .index_of(old_level_zero[i]);
                    assert(self.active_frontier()[frontier_index]
                        == old_level_zero[i]);
                    streaming_frontier_descriptor_nodes_subset(
                        self.active_frontier(),
                        frontier_index,
                    );
                    assert(old_level_zero[i].receipt@.nodes.dom()
                        <= self.staged_nodes@.dom());
                    assert(descriptor.receipt@.nodes.dom() == set![addr]);
                }
            }
            assert forall |i: int, j: int|
                #![trigger old_level_zero.push(descriptor)[i],
                    old_level_zero.push(descriptor)[j]]
                0 <= i < j < old_level_zero.push(descriptor).len()
                implies old_level_zero.push(descriptor)[i]
                    .receipt@.last_key.0
                        < old_level_zero.push(descriptor)[j]
                            .first_key.0 by {
                if j == old_level_zero.len() {
                    streaming_levels_frontier_contains_descriptor(
                        self.levels@,
                        self.pending,
                        self.deferred,
                        self.levels@.len(),
                        0,
                        i,
                    );
                    let frontier_index = self.active_frontier()
                        .index_of(old_level_zero[i]);
                    assert(self.active_frontier()[frontier_index]
                        == old_level_zero[i]);
                    let k = choose |k: int|
                        0 <= k < self.leaf_prefix@.len()
                        && self.leaf_prefix@[k].key
                            == self.active_frontier()[frontier_index]
                                .receipt@.last_key;
                    assert(self.source_entries@[k]
                        == self.leaf_prefix@[k]);
                    assert(self.unstaged_leaf_entries()[0]
                        == entries[0]);
                    assert(self.source_entries@[
                        self.leaf_prefix@.len() as int]
                            == entries[0]);
                }
            }
            assert forall |i: int, j: int|
                #![trigger old_level_zero.push(descriptor)[i],
                    old_level_zero.push(descriptor)[j]]
                0 <= i < j < old_level_zero.push(descriptor).len()
                implies old_level_zero.push(descriptor)[i]
                    .receipt@.height
                        == old_level_zero.push(descriptor)[j]
                            .receipt@.height by {
                if j == old_level_zero.len() {
                    assert(descriptor.receipt@.height == 0);
                    assert(old_level_zero[i].receipt@.height == 0);
                }
            }
        }
    }

    proof fn index_descriptor_append_wf(
        &self,
        pending: StreamingPendingPage,
        target: int,
        children: Seq<BranchChildDescriptor>,
        descriptor: BranchChildDescriptor,
        addr: Address,
        node: BranchNode,
    )
        requires
            self.local_wf(),
            self.pending == Some(pending),
            pending is Index,
            self.phase is Reading || self.phase is Finishing,
            streaming_pending_parent_level(pending) as int == target,
            children == streaming_pending_descriptors_at(
                Some(pending),
                target,
            ),
            descriptor.wf(),
            descriptor.first_key == children.first().first_key,
            descriptor.receipt@.nodes
                == descriptor_forest_nodes(children).insert(
                    addr,
                    node,
                ),
            descriptor.receipt@.last_key
                == children.last().receipt@.last_key,
            descriptor.receipt@.height
                == children.first().receipt@.height + 1,
            !self.staged_nodes@.contains_key(addr),
        ensures
            descriptor_sequence_wf(
                self.levels@[target].entries().push(descriptor),
            ),
    {
        self.expose_layout_wf();
        self.expose_stream_wf();
        let old_entries = self.levels@[target].entries();
        assert(descriptor_sequence_wf(
            old_entries.push(descriptor),
        )) by {
            assert forall |i: int| 0 <= i < old_entries.push(descriptor).len()
                implies (#[trigger] old_entries.push(descriptor)[i]).wf() by {
                if i == old_entries.len() {
                    assert(old_entries.push(descriptor)[i] == descriptor);
                }
            }
            assert forall |i: int, j: int|
                #![trigger old_entries.push(descriptor)[i],
                    old_entries.push(descriptor)[j]]
                0 <= i < j < old_entries.push(descriptor).len()
                implies old_entries.push(descriptor)[i]
                    .receipt@.nodes.dom().disjoint(
                        old_entries.push(descriptor)[j]
                            .receipt@.nodes.dom(),
                    ) by {
                if j == old_entries.len() {
                    let old_descriptor = old_entries[i];
                    assert(old_entries.push(descriptor)[j] == descriptor);
                    assert(old_entries.push(descriptor)[i]
                        == old_descriptor);
                    assert forall |candidate: Address|
                        #[trigger] old_descriptor.receipt@.nodes
                            .contains_key(candidate)
                        implies !descriptor.receipt@.nodes
                            .contains_key(candidate) by {
                        assert(candidate != addr) by {
                            let positions = streaming_level_entry_precedes_pending(
                                self.levels@,
                                pending,
                                self.deferred,
                                self.levels@.len(),
                                target,
                                i,
                                0,
                            );
                            let left = positions.0;
                            let right = positions.1;
                            streaming_frontier_descriptor_nodes_submap(
                                self.active_frontier(),
                                left,
                            );
                            assert(self.active_frontier()[left]
                                == old_descriptor);
                            assert(old_descriptor.receipt@.nodes
                                <= self.staged_nodes@);
                        }
                        if descriptor_forest_nodes(children)
                            .contains_key(candidate)
                        {
                            descriptor_forest_nodes_contains_member(
                                children,
                                candidate,
                            );
                            let child_index = choose |child_index: int|
                                0 <= child_index < children.len()
                                && (#[trigger] children[child_index])
                                    .receipt@.nodes.contains_key(candidate);
                            let positions = streaming_level_entry_precedes_pending(
                                self.levels@,
                                pending,
                                self.deferred,
                                self.levels@.len(),
                                target,
                                i,
                                child_index,
                            );
                            let left = positions.0;
                            let right = positions.1;
                            assert(self.active_frontier()[left]
                                .receipt@.nodes.dom().disjoint(
                                    self.active_frontier()[right]
                                        .receipt@.nodes.dom(),
                                ));
                        }
                    }
                }
            }
            assert forall |i: int, j: int|
                #![trigger old_entries.push(descriptor)[i],
                    old_entries.push(descriptor)[j]]
                0 <= i < j < old_entries.push(descriptor).len()
                implies old_entries.push(descriptor)[i]
                    .receipt@.last_key.0
                        < old_entries.push(descriptor)[j]
                            .first_key.0 by {
                if j == old_entries.len() {
                    let positions = streaming_level_entry_precedes_pending(
                        self.levels@,
                        pending,
                        self.deferred,
                        self.levels@.len(),
                        target,
                        i,
                        0,
                    );
                    let left = positions.0;
                    let right = positions.1;
                    assert(self.active_frontier()[left]
                        .receipt@.last_key.0
                            < self.active_frontier()[right].first_key.0);
                }
            }
            assert forall |i: int, j: int|
                #![trigger old_entries.push(descriptor)[i],
                    old_entries.push(descriptor)[j]]
                0 <= i < j < old_entries.push(descriptor).len()
                implies old_entries.push(descriptor)[i]
                    .receipt@.height
                        == old_entries.push(descriptor)[j]
                            .receipt@.height by {
                if j == old_entries.len() {
                    assert(old_entries[i].receipt@.height == target as nat);
                    assert(children.first().receipt@.height + 1
                        == target as nat);
                }
            }
        }
    }

    proof fn leaf_stage_preserves_stream_wf(
        pre: StreamingBranchBuilder,
        post: StreamingBranchBuilder,
        entries: Seq<MemtableEntry>,
        descriptor: BranchChildDescriptor,
        addr: Address,
        node: BranchNode,
    )
        requires
            pre.stream_wf(),
            pre.phase is Reading || pre.phase is Finishing,
            post.phase == pre.phase,
            entries.len() > 0,
            MemtableBucket::strictly_sorted(entries),
            pre.unstaged_leaf_entries()
                =~= entries + post.unstaged_leaf_entries(),
            post.source_entries@ == pre.source_entries@,
            post.leaf_prefix@ == pre.leaf_prefix@ + entries,
            post.has_staged_leaf,
            post.levels.len() > 0,
            post.active_frontier()
                == pre.active_frontier().push(descriptor),
            post.staged_nodes@
                == pre.staged_nodes@.insert(addr, node),
            descriptor.wf(),
            descriptor.first_key == entries[0].key,
            descriptor.receipt@.nodes == map![addr => node],
            descriptor.receipt@.pivot.i().map
                == MemtableBucket::entries_map(entries),
            descriptor.receipt@.last_key
                == entries[entries.len() - 1].key,
            !pre.staged_nodes@.contains_key(addr),
        ensures post.stream_wf(),
    {
        pre.expose_stream_wf();
        let old_frontier = pre.active_frontier();
        let new_frontier = post.active_frontier();
        assert forall |i: int| 0 <= i < old_frontier.len()
            implies {
                &&& (#[trigger] old_frontier[i]).receipt@.nodes.dom()
                    .disjoint(descriptor.receipt@.nodes.dom())
                &&& old_frontier[i].receipt@.last_key.0
                    < descriptor.first_key.0
            } by {
            assert(old_frontier[i].receipt@.nodes.dom()
                <= pre.staged_nodes@.dom()) by {
                streaming_frontier_descriptor_nodes_subset(
                    old_frontier,
                    i,
                );
                assert(descriptor_forest_nodes(old_frontier)
                    == pre.staged_nodes@);
            }
            let k = choose |k: int|
                0 <= k < pre.leaf_prefix@.len()
                && pre.leaf_prefix@[k].key
                    == old_frontier[i].receipt@.last_key;
            assert(pre.source_entries@[k]
                == pre.leaf_prefix@[k]);
            assert(pre.unstaged_leaf_entries()[0] == entries[0]);
            assert(pre.source_entries@[
                pre.leaf_prefix@.len() as int] == entries[0]);
        }
        streaming_frontier_push_wf(old_frontier, descriptor);
        streaming_descriptor_forest_push(old_frontier, descriptor);
        assert(descriptor_forest_contents(new_frontier)
            == descriptor_forest_contents(old_frontier)
                .union_prefer_right(descriptor.receipt@.pivot.i().map));
        assert(entry_sequences_ordered(pre.leaf_prefix@, entries)) by {
            assert forall |i: int, j: int|
                0 <= i < pre.leaf_prefix@.len()
                && 0 <= j < entries.len()
                implies pre.leaf_prefix@[i].key.0
                    < entries[j].key.0 by {
                assert(pre.source_entries@[i]
                    == pre.leaf_prefix@[i]);
                assert(pre.source_entries@[
                    pre.leaf_prefix@.len() as int + j]
                        == entries[j]);
            }
        }
        sorted_concat(pre.leaf_prefix@, entries);
        entries_map_concat(pre.leaf_prefix@, entries);
        assert(descriptor_forest_contents(new_frontier)
            == MemtableBucket::entries_map(post.leaf_prefix@));
        assert(descriptor_forest_nodes(new_frontier)
            == descriptor_forest_nodes(old_frontier)
                .union_prefer_right(descriptor.receipt@.nodes));
        assert(descriptor_forest_nodes(new_frontier)
            == post.staged_nodes@) by {
            assert_maps_equal!(
                descriptor_forest_nodes(new_frontier),
                post.staged_nodes@,
                candidate => {}
            );
        }
        assert(post.source_entries@
            =~= post.leaf_prefix@ + post.unstaged_leaf_entries());
        assert forall |i: int| 0 <= i < new_frontier.len()
            implies exists |j: int|
                0 <= j < post.leaf_prefix@.len()
                && (#[trigger] post.leaf_prefix@[j]).key
                    == (#[trigger] new_frontier[i])
                        .receipt@.last_key by {
            if i == old_frontier.len() {
                let j = post.leaf_prefix@.len() as int - 1;
                assert(new_frontier[i] == descriptor);
                assert(post.leaf_prefix@[j]
                    == entries[entries.len() - 1]);
            } else {
                assert(new_frontier[i] == old_frontier[i]);
                let j = choose |j: int|
                    0 <= j < pre.leaf_prefix@.len()
                    && pre.leaf_prefix@[j].key
                        == old_frontier[i].receipt@.last_key;
                assert(post.leaf_prefix@[j]
                    == pre.leaf_prefix@[j]);
            }
        }
        assert forall |i: int, j: int|
            0 <= i < new_frontier.len()
            && 0 <= j < post.unstaged_leaf_entries().len()
            implies (#[trigger] new_frontier[i]).receipt@.last_key.0
                < (#[trigger] post.unstaged_leaf_entries()[j]).key.0 by {
            let k = choose |k: int|
                0 <= k < post.leaf_prefix@.len()
                && post.leaf_prefix@[k].key
                    == new_frontier[i].receipt@.last_key;
            assert(post.source_entries@[k]
                == post.leaf_prefix@[k]);
            assert(post.source_entries@[
                post.leaf_prefix@.len() as int + j]
                    == post.unstaged_leaf_entries()[j]);
        }
        assert(post.stream_wf()) by {
            reveal(StreamingBranchBuilder::stream_wf);
        }
    }

    proof fn index_stage_preserves_stream_wf(
        pre: StreamingBranchBuilder,
        post: StreamingBranchBuilder,
        children: Seq<BranchChildDescriptor>,
        descriptor: BranchChildDescriptor,
        prefix: Seq<BranchChildDescriptor>,
        suffix: Seq<BranchChildDescriptor>,
        addr: Address,
        node: BranchNode,
    )
        requires
            pre.stream_wf(),
            pre.phase is Reading || pre.phase is Finishing,
            post.phase == pre.phase,
            post.source_entries@ == pre.source_entries@,
            post.leaf_prefix@ == pre.leaf_prefix@,
            post.has_staged_leaf == pre.has_staged_leaf,
            post.unstaged_leaf_entries() == pre.unstaged_leaf_entries(),
            descriptor_frontier_collapse_witness(
                pre.active_frontier(),
                children,
                descriptor,
                post.active_frontier(),
                prefix,
                suffix,
            ),
            children.len() > 0,
            descriptor.wf(),
            descriptor.first_key == children.first().first_key,
            descriptor.receipt@.last_key
                == children.last().receipt@.last_key,
            descriptor.receipt@.nodes
                == descriptor_forest_nodes(children).insert(addr, node),
            descriptor.receipt@.pivot.i().map
                == descriptor_forest_contents(children),
            post.staged_nodes@ == pre.staged_nodes@.insert(addr, node),
            !pre.staged_nodes@.contains_key(addr),
        ensures post.stream_wf(),
    {
        pre.expose_stream_wf();
        let old_frontier = pre.active_frontier();
        let new_frontier = post.active_frontier();
        streaming_frontier_collapse_preserves_wf(
            old_frontier,
            children,
            descriptor,
            new_frontier,
            prefix,
            suffix,
            addr,
            node,
        );
        assert forall |i: int| 0 <= i < new_frontier.len()
            implies exists |j: int|
                0 <= j < post.leaf_prefix@.len()
                && (#[trigger] post.leaf_prefix@[j]).key
                    == (#[trigger] new_frontier[i]).receipt@.last_key by {
            let old_index = if i < prefix.len() {
                i
            } else if i == prefix.len() {
                prefix.len() as int + children.len() as int - 1
            } else {
                prefix.len() as int + children.len() as int
                    + (i - prefix.len() - 1)
            };
            assert(0 <= old_index < old_frontier.len());
            if i < prefix.len() {
                assert(new_frontier[i] == old_frontier[old_index]);
            } else if i == prefix.len() {
                assert(new_frontier[i] == descriptor);
                assert(old_frontier[old_index] == children.last());
            } else {
                assert(new_frontier[i] == old_frontier[old_index]);
            }
            let j = choose |j: int| 0 <= j < pre.leaf_prefix@.len()
                && (#[trigger] pre.leaf_prefix@[j]).key
                    == old_frontier[old_index].receipt@.last_key;
            assert(post.leaf_prefix@[j] == pre.leaf_prefix@[j]);
        }
        assert forall |i: int, j: int|
            0 <= i < new_frontier.len()
            && 0 <= j < post.unstaged_leaf_entries().len()
            implies (#[trigger] new_frontier[i]).receipt@.last_key.0
                < (#[trigger] post.unstaged_leaf_entries()[j]).key.0 by {
            let old_index = if i < prefix.len() {
                i
            } else if i == prefix.len() {
                prefix.len() as int + children.len() as int - 1
            } else {
                prefix.len() as int + children.len() as int
                    + (i - prefix.len() - 1)
            };
            if i < prefix.len() {
                assert(new_frontier[i] == old_frontier[old_index]);
            } else if i == prefix.len() {
                assert(new_frontier[i] == descriptor);
                assert(old_frontier[old_index] == children.last());
            } else {
                assert(new_frontier[i] == old_frontier[old_index]);
            }
        }
        let singleton = Seq::empty().push(descriptor);
        streaming_descriptor_forest_singleton(descriptor);
        assert(prefix.push(descriptor) == prefix + singleton) by {
            assert_seqs_equal!(
                prefix.push(descriptor),
                prefix + singleton,
                i => {}
            );
        }
        streaming_descriptor_forest_contents_concat(prefix, children);
        streaming_descriptor_forest_contents_concat(
            prefix + children,
            suffix,
        );
        streaming_descriptor_forest_contents_concat(prefix, singleton);
        streaming_descriptor_forest_contents_concat(
            prefix + singleton,
            suffix,
        );
        streaming_descriptor_forest_nodes_concat(prefix, children);
        streaming_descriptor_forest_nodes_concat(
            prefix + children,
            suffix,
        );
        streaming_descriptor_forest_nodes_concat(prefix, singleton);
        streaming_descriptor_forest_nodes_concat(
            prefix + singleton,
            suffix,
        );
        assert(descriptor_forest_contents(old_frontier)
            == descriptor_forest_contents(prefix)
                .union_prefer_right(
                    descriptor_forest_contents(children),
                ).union_prefer_right(
                    descriptor_forest_contents(suffix),
                ));
        assert(descriptor_forest_contents(new_frontier)
            == descriptor_forest_contents(prefix)
                .union_prefer_right(
                    descriptor.receipt@.pivot.i().map,
                ).union_prefer_right(
                    descriptor_forest_contents(suffix),
                ));
        assert(descriptor_forest_contents(new_frontier)
            == descriptor_forest_contents(old_frontier));
        assert(descriptor_forest_nodes(old_frontier)
            == descriptor_forest_nodes(prefix)
                .union_prefer_right(
                    descriptor_forest_nodes(children),
                ).union_prefer_right(
                    descriptor_forest_nodes(suffix),
                ));
        assert(descriptor_forest_nodes(new_frontier)
            == descriptor_forest_nodes(prefix)
                .union_prefer_right(
                    descriptor.receipt@.nodes,
                ).union_prefer_right(
                    descriptor_forest_nodes(suffix),
                ));
        assert(descriptor_forest_nodes(new_frontier)
            == descriptor_forest_nodes(old_frontier).insert(addr, node)) by {
            assert_maps_equal!(
                descriptor_forest_nodes(new_frontier),
                descriptor_forest_nodes(old_frontier).insert(addr, node),
                candidate => {}
            );
        }
        assert(descriptor_forest_contents(new_frontier)
            == MemtableBucket::entries_map(post.leaf_prefix@));
        assert(descriptor_forest_nodes(new_frontier)
            == post.staged_nodes@);
        assert(post.stream_wf()) by {
            reveal(StreamingBranchBuilder::stream_wf);
        }
    }

    proof fn same_frontier_preserves_stream_wf(
        pre: StreamingBranchBuilder,
        post: StreamingBranchBuilder,
    )
        requires
            pre.stream_wf(),
            post.source_entries@ == pre.source_entries@,
            post.leaf_prefix@ == pre.leaf_prefix@,
            post.has_staged_leaf == pre.has_staged_leaf,
            post.unstaged_leaf_entries() == pre.unstaged_leaf_entries(),
            post.active_frontier() == pre.active_frontier(),
            post.staged_nodes@ == pre.staged_nodes@,
            !(pre.phase is ReadyLeafRoot),
            !(pre.phase is Sealed),
            !(post.phase is ReadyLeafRoot),
            !(post.phase is Sealed),
            post.has_staged_leaf ==> post.levels.len() > 0,
        ensures post.stream_wf(),
    {
        pre.expose_stream_wf();
        assert(post.stream_wf()) by {
            reveal(StreamingBranchBuilder::stream_wf);
        }
    }

    pub fn new(
        leaf_capacity: usize,
        index_fanout: usize,
    ) -> (out: Option<Self>)
        ensures
            match out {
                Some(builder) => {
                    &&& builder.local_wf()
                    &&& builder.phase is Reading
                    &&& builder.source_entries@.len() == 0
                    &&& builder.staged_nodes@ == LoadedBranch::empty()
                    &&& builder.leaf_tail.capacity == leaf_capacity
                    &&& builder.index_fanout == index_fanout
                },
                None => {
                    ||| leaf_capacity <= 1
                    ||| leaf_capacity > u8::MAX as usize
                    ||| index_fanout <= 1
                    ||| index_fanout > u8::MAX as usize + 1
                },
            },
    {
        let leaf_tail = match StreamingLeafTail::new(leaf_capacity) {
            Some(tail) => tail,
            None => return None,
        };
        if index_fanout <= 1
            || index_fanout > u8::MAX as usize + 1
        {
            return None;
        }
        let out = Self {
            leaf_tail,
            levels: Vec::new(),
            pending: None,
            deferred: None,
            phase: StreamingBranchPhase::Reading,
            index_fanout,
            root_leaf: Vec::new(),
            root_children: Vec::new(),
            has_staged_leaf: false,
            source_entries: Ghost(Seq::empty()),
            leaf_prefix: Ghost(Seq::empty()),
            staged_nodes: Ghost(LoadedBranch::empty()),
        };
        proof {
            assert(streaming_levels_frontier(
                out.levels@,
                out.pending,
                out.deferred,
                out.levels@.len(),
            ) == Seq::<BranchChildDescriptor>::empty());
            assert(streaming_descriptor_frontier_wf(
                out.active_frontier(),
            ));
            assert(descriptor_forest_contents(out.active_frontier())
                == Map::<Key, Message>::empty());
            assert(MemtableBucket::entries_map(out.leaf_prefix@)
                == Map::<Key, Message>::empty());
            assert(descriptor_forest_nodes(out.active_frontier())
                == LoadedBranch::empty());
            assert(out.layout_wf()) by {
                reveal(StreamingBranchBuilder::layout_wf);
            }
            assert(out.stream_wf()) by {
                reveal(StreamingBranchBuilder::stream_wf);
            }
            assert(out.phase_wf()) by {
                reveal(StreamingBranchBuilder::phase_wf);
            }
            assert(out.local_wf());
        }
        Some(out)
    }

    pub fn push_entry(
        &mut self,
        entry: MemtableEntry,
    ) -> (out: StreamingBuilderInputResult)
        requires
            old(self).local_wf(),
            old(self).phase is Reading,
            old(self).pending is None,
            old(self).deferred is None,
            forall |i: int| 0 <= i < old(self).source_entries@.len()
                ==> (#[trigger] old(self).source_entries@[i]).key.0
                    < entry.key.0,
        ensures
            self.local_wf(),
            self.leaf_tail.capacity == old(self).leaf_tail.capacity,
            self.index_fanout == old(self).index_fanout,
            self.phase is Reading,
            self.source_entries@
                == old(self).source_entries@.push(entry),
            self.leaf_prefix@ == old(self).leaf_prefix@,
            self.staged_nodes@ == old(self).staged_nodes@,
            self.active_frontier() == old(self).active_frontier(),
            match out {
                StreamingBuilderInputResult::Accepted => {
                    &&& self.pending is None
                    &&& self.deferred is None
                },
                StreamingBuilderInputResult::PageReady => {
                    &&& self.pending is Some
                    &&& self.pending->0 is Leaf
                    &&& self.deferred is None
                },
            },
    {
        let ghost self0 = *self;
        proof {
            self0.expose_layout_wf();
            self0.expose_stream_wf();
            self0.expose_phase_wf();
        }
        proof {
            assert forall |i: int|
                0 <= i < self0.leaf_tail.entries().len()
                implies (#[trigger] self0.leaf_tail.entries()[i]).key.0
                    < entry.key.0 by {
                assert(self0.unstaged_leaf_entries()
                    == self0.leaf_tail.entries());
                assert(self0.source_entries@
                    =~= self0.leaf_prefix@ + self0.leaf_tail.entries());
                assert(self0.source_entries@[
                    self0.leaf_prefix@.len() as int + i]
                        == self0.leaf_tail.entries()[i]);
            }
        }
        let result = self.leaf_tail.push(entry);
        proof {
            self.source_entries@ = self0.source_entries@.push(entry);
            sorted_push(self0.source_entries@, entry);
        }
        match result {
            StreamingLeafPushResult::Accepted => {
                proof {
                    assert(self.unstaged_leaf_entries()
                        == self0.unstaged_leaf_entries().push(entry));
                    assert(self.source_entries@
                        =~= self.leaf_prefix@ + self.unstaged_leaf_entries());
                    assert(self.active_frontier()
                        == self0.active_frontier());
                    assert forall |i: int, j: int|
                        0 <= i < self.active_frontier().len()
                        && 0 <= j < self.unstaged_leaf_entries().len()
                        implies self.active_frontier()[i]
                            .receipt@.last_key.0
                            < self.unstaged_leaf_entries()[j].key.0 by {
                        if j == self0.unstaged_leaf_entries().len() {
                            let k = choose |k: int|
                                0 <= k < self0.leaf_prefix@.len()
                                && self0.leaf_prefix@[k].key
                                    == self0.active_frontier()[i]
                                        .receipt@.last_key;
                            assert(self0.source_entries@[k]
                                == self0.leaf_prefix@[k]);
                            assert(self.unstaged_leaf_entries()[j] == entry);
                        }
                    }
                    assert(self.layout_wf()) by {
                        reveal(StreamingBranchBuilder::layout_wf);
                    }
                    assert(self.stream_wf()) by {
                        reveal(StreamingBranchBuilder::stream_wf);
                    }
                    assert(self.phase_wf()) by {
                        reveal(StreamingBranchBuilder::phase_wf);
                    }
                    assert(self.local_wf());
                }
                StreamingBuilderInputResult::Accepted
            },
            StreamingLeafPushResult::PageReady { entries } => {
                if self.levels.len() == 0 {
                    let level = StreamingIndexTail::new(
                        self.index_fanout,
                    ).unwrap();
                    self.levels.push(level);
                }
                self.pending = Some(StreamingPendingPage::Leaf {
                    entries,
                    parent_level: 0,
                });
                proof {
                    streaming_leaf_pending_does_not_change_frontier(
                        self.levels@,
                        self.pending.unwrap(),
                        self.levels@.len(),
                    );
                    assert(self.levels.len() == self0.levels.len()
                        || self0.levels.len() == 0
                            && self.levels.len() == 1);
                    assert(self.active_frontier()
                        == self0.active_frontier()) by {
                        if self0.levels.len() == 0 {
                            reveal_with_fuel(streaming_levels_frontier, 2);
                            assert(streaming_pending_descriptors_at(
                                self.pending,
                                0,
                            ) == Seq::<BranchChildDescriptor>::empty());
                            assert(self.levels@[0].entries()
                                == Seq::<BranchChildDescriptor>::empty());
                            assert(streaming_levels_frontier(
                                self.levels@,
                                None,
                                None,
                                self.levels@.len(),
                            ) == Seq::<BranchChildDescriptor>::empty());
                        } else {
                            assert(self.levels@ == self0.levels@);
                        }
                    }
                    assert(self.unstaged_leaf_entries()
                        =~= entries@ + self.leaf_tail.entries());
                    assert(self0.unstaged_leaf_entries().push(entry)
                        =~= self.unstaged_leaf_entries());
                    assert(self.source_entries@
                        =~= self.leaf_prefix@ + self.unstaged_leaf_entries());
                    assert forall |i: int, j: int|
                        0 <= i < self.active_frontier().len()
                        && 0 <= j < self.unstaged_leaf_entries().len()
                        implies self.active_frontier()[i]
                            .receipt@.last_key.0
                            < self.unstaged_leaf_entries()[j].key.0 by {
                        if j == self0.unstaged_leaf_entries().len() {
                            let k = choose |k: int|
                                0 <= k < self0.leaf_prefix@.len()
                                && self0.leaf_prefix@[k].key
                                    == self0.active_frontier()[i]
                                        .receipt@.last_key;
                            assert(self0.source_entries@[k]
                                == self0.leaf_prefix@[k]);
                            assert(self.unstaged_leaf_entries()[j] == entry);
                        } else {
                            assert(j < self0.unstaged_leaf_entries().len());
                            assert(self.unstaged_leaf_entries()[j]
                                == self0.unstaged_leaf_entries().push(entry)[j]);
                        }
                    }
                    assert(self.layout_wf()) by {
                        reveal(StreamingBranchBuilder::layout_wf);
                    }
                    assert(self.stream_wf()) by {
                        reveal(StreamingBranchBuilder::stream_wf);
                    }
                    assert(self.phase_wf()) by {
                        reveal(StreamingBranchBuilder::phase_wf);
                    }
                    assert(self.local_wf());
                }
                StreamingBuilderInputResult::PageReady
            },
        }
    }

    pub fn stage_pending_leaf(
        &mut self,
        addr: IAddress,
    ) -> (out: StreamingStagedPage)
        requires
            old(self).local_wf(),
            old(self).pending is Some,
            old(self).pending->0 is Leaf,
            old(self).phase is Reading
                || old(self).phase is Finishing,
            old(self).deferred is None
                || old(self).deferred->0 is Leaf,
            addr@.wf(),
            !old(self).staged_nodes@.contains_key(addr@),
        ensures
            self.local_wf(),
            self.leaf_tail.capacity == old(self).leaf_tail.capacity,
            self.index_fanout == old(self).index_fanout,
            self.phase == old(self).phase,
            self.source_entries@ == old(self).source_entries@,
            self.leaf_prefix@ == old(self).leaf_prefix@
                + streaming_pending_leaf_entries(old(self).pending),
            self.staged_nodes@
                == old(self).staged_nodes@.insert(addr@, out.node@),
            out.node is Leaf,
            out.node.wf(),
            out.node@.wf(),
            out.node@.keys_strictly_sorted(),
            out.node->keys.len() <= old(self).leaf_tail.capacity,
            out.node->keys.len() <= u8::MAX as usize,
            out.descriptor.wf(),
            out.descriptor.addr == addr,
            out.descriptor.receipt@.root == addr@,
            out.descriptor.receipt@.nodes == map![addr@ => out.node@],
            out.descriptor.receipt@.pivot.i().map
                == MemtableBucket::entries_map(
                    streaming_pending_leaf_entries(old(self).pending),
                ),
            self.active_frontier()
                == old(self).active_frontier().push(out.descriptor),
    {
        let ghost self0 = *self;
        proof {
            self0.expose_layout_wf();
            self0.expose_stream_wf();
            self0.expose_phase_wf();
        }
        let pending = self.pending.take().unwrap();
        let entries = match pending {
            StreamingPendingPage::Leaf { entries, .. } => entries,
            _ => {
                proof { assert(false); }
                unreached()
            },
        };
        let node = crate::implementation::BranchBulkBuilderImpl_v::
            leaf_from_entries(entries.clone());
        let ghost receipt = make_leaf_receipt(addr@, node@);
        let descriptor = BranchChildDescriptor {
            first_key: entries[0].key,
            addr,
            receipt: Ghost(receipt),
        };
        proof {
            leaf_entries_contents(entries@, node@);
            assert(descriptor.wf());
            assert(receipt.pivot.i().map
                == MemtableBucket::entries_map(entries@));
            assert(receipt.last_key
                == entries@[entries@.len() - 1].key);
        }

        let ghost old_levels = self.levels@;
        let ghost old_level_zero = self.levels@[0].entries();
        let ghost combined_level_zero = old_level_zero.push(descriptor);
        proof {
            self0.leaf_descriptor_append_wf(
                entries@,
                descriptor,
                addr@,
                node@,
            );
        }
        let mut level_zero = self.levels.remove(0);
        let push_result = level_zero.push(descriptor);
        self.levels.insert(0, level_zero);
        self.has_staged_leaf = true;
        proof {
            self.leaf_prefix@ = self0.leaf_prefix@ + entries@;
            self.staged_nodes@ = self0.staged_nodes@.insert(
                addr@,
                node@,
            );
        }

        match push_result {
            StreamingIndexPushResult::Accepted => {
                self.pending = self.deferred.take();
                proof {
                    streaming_leaf_pages_do_not_change_frontier(
                        old_levels,
                        self0.pending,
                        self0.deferred,
                        old_levels.len(),
                    );
                    streaming_leaf_pages_do_not_change_frontier(
                        self.levels@,
                        self.pending,
                        self.deferred,
                        self.levels@.len(),
                    );
                    streaming_level_zero_push_layout(
                        old_levels,
                        self.levels@,
                        descriptor,
                        old_levels.len(),
                    );
                    assert(self0.active_frontier()
                        == streaming_levels_frontier(
                            old_levels,
                            self0.pending,
                            self0.deferred,
                            old_levels.len(),
                        ));
                    assert(self.active_frontier()
                        == streaming_levels_frontier(
                            self.levels@,
                            self.pending,
                            self.deferred,
                            self.levels@.len(),
                        ));
                    assert forall |i: int| 0 <= i < self.levels@.len()
                        implies {
                            &&& (#[trigger] self.levels@[i]).wf()
                            &&& self.levels@[i].capacity == self.index_fanout
                            &&& forall |j: int|
                                0 <= j < self.levels@[i].entries().len()
                                ==> {
                                    let candidate = #[trigger]
                                        self.levels@[i].entries()[j];
                                    candidate.receipt@.height == i as nat
                                }
                        } by {
                        if i == 0 {
                            assert(self.levels@[i].entries()
                                == combined_level_zero);
                        } else {
                            assert(self.levels@[i].entries()
                                == old_levels[i].entries());
                        }
                    }
                    assert(self.active_frontier()
                        == self0.active_frontier().push(descriptor));
                }
            },
            StreamingIndexPushResult::PageReady { children } => {
                let ghost children_seq = children@;
                if self.levels.len() == 1 {
                    let next = StreamingIndexTail::new(
                        self.index_fanout,
                    ).unwrap();
                    self.levels.push(next);
                }
                self.pending = Some(StreamingPendingPage::Index {
                    children,
                    parent_level: 1,
                });
                proof {
                    streaming_leaf_pages_do_not_change_frontier(
                        old_levels,
                        self0.pending,
                        self0.deferred,
                        old_levels.len(),
                    );
                    streaming_deferred_leaf_does_not_change_frontier(
                        self.levels@,
                        self.pending,
                        self.deferred,
                        self.levels@.len(),
                    );
                    if old_levels.len() == 1 {
                        streaming_level_zero_reflow_new_parent_layout(
                            old_levels,
                            self.levels@,
                            self.pending.unwrap(),
                            children_seq,
                            descriptor,
                        );
                    } else {
                        streaming_level_zero_reflow_layout(
                            old_levels,
                            self.levels@,
                            self.pending.unwrap(),
                            children_seq,
                            descriptor,
                            old_levels.len(),
                        );
                    }
                    assert(self0.active_frontier()
                        == streaming_levels_frontier(
                            old_levels,
                            self0.pending,
                            self0.deferred,
                            old_levels.len(),
                        ));
                    assert(self.active_frontier()
                        == streaming_levels_frontier(
                            self.levels@,
                            self.pending,
                            self.deferred,
                            self.levels@.len(),
                        ));
                    assert forall |i: int| 0 <= i < self.levels@.len()
                        implies {
                            &&& (#[trigger] self.levels@[i]).wf()
                            &&& self.levels@[i].capacity == self.index_fanout
                            &&& forall |j: int|
                                0 <= j < self.levels@[i].entries().len()
                                ==> {
                                    let candidate = #[trigger]
                                        self.levels@[i].entries()[j];
                                    candidate.receipt@.height == i as nat
                                }
                        } by {
                        if i == 0 {
                            assert(combined_level_zero
                                =~= children_seq + self.levels@[0].entries());
                            assert forall |j: int|
                                0 <= j < self.levels@[0].entries().len()
                                implies self.levels@[0].entries()[j]
                                    == combined_level_zero[
                                        children_seq.len() as int + j] by {
                                assert((children_seq
                                    + self.levels@[0].entries())[
                                        children_seq.len() as int + j]
                                            == self.levels@[0].entries()[j]);
                            }
                        } else if i == old_levels.len()
                            && old_levels.len() == 1
                        {
                            assert(self.levels@[i].entries().len() == 0);
                        } else {
                            assert(self.levels@[i].entries()
                                == old_levels[i].entries());
                        }
                    }
                    assert(streaming_pending_page_wf(
                        self.pending.unwrap(),
                        self.leaf_tail.capacity,
                        self.index_fanout,
                    )) by {
                        assert forall |j: int| 0 <= j < children_seq.len()
                            implies children_seq[j].receipt@.height + 1
                                == 1nat by {
                            assert(combined_level_zero
                                =~= children_seq + self.levels@[0].entries());
                            assert(children_seq[j] == combined_level_zero[j]);
                        }
                    }
                    assert(self.active_frontier()
                        == self0.active_frontier().push(descriptor));
                }
            },
        }

        proof {
            assert(self0.unstaged_leaf_entries()
                =~= entries@ + self.unstaged_leaf_entries());
            StreamingBranchBuilder::leaf_stage_preserves_stream_wf(
                self0,
                *self,
                entries@,
                descriptor,
                addr@,
                node@,
            );
            assert(self.layout_wf()) by {
                reveal(StreamingBranchBuilder::layout_wf);
            }
            if self.phase is Finishing {
                assert(self.phase->level == 0);
            }
            assert(self.phase_wf()) by {
                reveal(StreamingBranchBuilder::phase_wf);
            }
            assert(self.local_wf());
        }
        StreamingStagedPage { node, descriptor }
    }

    pub fn stage_pending_index(
        &mut self,
        addr: IAddress,
    ) -> (out: StreamingStagedPage)
        requires
            old(self).local_wf(),
            old(self).pending is Some,
            old(self).pending->0 is Index,
            old(self).phase is Reading
                || old(self).phase is Finishing,
            addr@.wf(),
            !old(self).staged_nodes@.contains_key(addr@),
        ensures
            self.local_wf(),
            self.leaf_tail.capacity == old(self).leaf_tail.capacity,
            self.index_fanout == old(self).index_fanout,
            self.phase == old(self).phase,
            self.source_entries@ == old(self).source_entries@,
            self.leaf_prefix@ == old(self).leaf_prefix@,
            self.staged_nodes@
                == old(self).staged_nodes@.insert(addr@, out.node@),
            out.node is Index,
            out.node.wf(),
            out.node@.wf(),
            out.node@.keys_strictly_sorted(),
            out.node->pivots.len() + 1
                <= old(self).index_fanout,
            out.node->pivots.len() <= u8::MAX as usize,
            out.descriptor.wf(),
            out.descriptor.addr == addr,
            out.descriptor.receipt@.root == addr@,
    {
        let ghost self0 = *self;
        proof {
            self0.expose_layout_wf();
            self0.expose_stream_wf();
            self0.expose_phase_wf();
        }
        let pending = self.pending.take().unwrap();
        let (children, parent_level) = match pending {
            StreamingPendingPage::Index {
                children,
                parent_level,
            } => (children, parent_level),
            _ => {
                proof { assert(false); }
                unreached()
            },
        };
        let ghost children_seq = children@;
        let ghost old_levels = self.levels@;
        let ghost target = parent_level as int;
        proof {
            assert(parent_level < self.levels.len());
            assert(children.len() > 0);
            assert(descriptor_sequence_wf(children_seq));
            assert(descriptor_forest_wf(children_seq));
            assert forall |i: int| 0 <= i < children_seq.len()
                implies (#[trigger] children_seq[i]).receipt@.nodes
                    <= self0.staged_nodes@ by {
                streaming_levels_frontier_contains_pending_descriptor(
                    old_levels,
                    pending,
                    self0.deferred,
                    old_levels.len(),
                    target,
                    i,
                );
                let frontier_index = self0.active_frontier()
                    .index_of(children_seq[i]);
                assert(self0.active_frontier()[frontier_index]
                    == children_seq[i]);
                streaming_frontier_descriptor_nodes_submap(
                    self0.active_frontier(),
                    frontier_index,
                );
                assert(descriptor_forest_nodes(
                    self0.active_frontier(),
                ) == self0.staged_nodes@);
            }
            descriptor_forest_nodes_subset_from_members(
                children_seq,
                self0.staged_nodes@,
            );
            assert(!descriptor_forest_nodes(children_seq)
                .contains_key(addr@));
        }
        let node = index_from_descriptors(
            &children,
            0,
            children.len(),
            None,
        );
        proof {
            assert(descriptor_pivots(children_seq)
                == node@->pivots) by {
                assert_seqs_equal!(
                    descriptor_pivots(children_seq),
                    node@->pivots,
                    i => {}
                );
            }
            assert(children_seq.map(
                |i: int, descriptor: BranchChildDescriptor|
                    descriptor.addr@,
            ) == node@->children) by {
                assert_seqs_equal!(
                    children_seq.map(
                        |i: int, descriptor: BranchChildDescriptor|
                            descriptor.addr@,
                    ),
                    node@->children,
                    i => {}
                );
            }
            assert(node@ == (BranchNode::Index {
                pivots: descriptor_pivots(children_seq),
                children: children_seq.map(
                    |i: int, descriptor: BranchChildDescriptor|
                        descriptor.addr@,
                ),
                aux_ptr: None,
            }));
        }
        let ghost receipt = make_index_receipt(
            children_seq,
            addr@,
            node@,
        );
        let descriptor = BranchChildDescriptor {
            first_key: children[0].first_key,
            addr,
            receipt: Ghost(receipt),
        };
        proof {
            assert(descriptor.wf());
            assert(descriptor.first_key == receipt.first_key);
            assert(descriptor.receipt@.height == target as nat) by {
                assert(children_seq.first().receipt@.height + 1
                    == parent_level as nat);
            }
            self0.index_descriptor_append_wf(
                pending,
                target,
                children_seq,
                descriptor,
                addr@,
                node@,
            );
        }

        let ghost old_target_entries = self.levels@[target].entries();
        let mut target_tail = self.levels.remove(parent_level);
        let push_result = target_tail.push(descriptor);
        self.levels.insert(parent_level, target_tail);
        proof {
            self.staged_nodes@ = self0.staged_nodes@.insert(
                addr@,
                node@,
            );
        }
        match push_result {
            StreamingIndexPushResult::Accepted => {
                self.pending = self.deferred.take();
                proof {
                    streaming_index_push_accepted_layout(
                        old_levels,
                        self.levels@,
                        pending,
                        self0.deferred,
                        target,
                        descriptor,
                        old_levels.len(),
                    );
                    streaming_replace_pending_is_collapse(
                        old_levels,
                        pending,
                        self0.deferred,
                        old_levels.len(),
                        target,
                        descriptor,
                    );
                    assert(descriptor_frontier_collapse(
                        self0.active_frontier(),
                        children_seq,
                        descriptor,
                        self.active_frontier(),
                    ));
                    assert forall |i: int, j: int|
                        0 <= i < self.levels@.len()
                        && 0 <= j < self.levels@[i].entries().len()
                        implies (#[trigger] self.levels@[i].entries()[j])
                            .receipt@.height == i as nat by {
                        if i == target {
                            assert(self.levels@[i].entries()
                                == old_target_entries.push(descriptor));
                        } else {
                            assert(self.levels@[i].entries()
                                == old_levels[i].entries());
                        }
                    }
                    assert(match self.pending {
                        Some(page) => streaming_pending_page_wf(
                            page,
                            self.leaf_tail.capacity,
                            self.index_fanout,
                        ),
                        None => true,
                    });
                }
            },
            StreamingIndexPushResult::PageReady { children: emitted } => {
                let ghost emitted_seq = emitted@;
                if parent_level + 1 == self.levels.len() {
                    let next = StreamingIndexTail::new(
                        self.index_fanout,
                    ).unwrap();
                    self.levels.push(next);
                }
                self.pending = Some(StreamingPendingPage::Index {
                    children: emitted,
                    parent_level: parent_level + 1,
                });
                proof {
                    streaming_index_push_emitted_layout(
                        old_levels,
                        self.levels@,
                        pending,
                        self.pending.unwrap(),
                        self0.deferred,
                        target,
                        descriptor,
                        emitted_seq,
                        self.levels@.len(),
                    );
                    streaming_replace_pending_is_collapse(
                        old_levels,
                        pending,
                        self0.deferred,
                        old_levels.len(),
                        target,
                        descriptor,
                    );
                    assert(descriptor_frontier_collapse(
                        self0.active_frontier(),
                        children_seq,
                        descriptor,
                        self.active_frontier(),
                    ));
                    assert forall |i: int, j: int|
                        0 <= i < self.levels@.len()
                        && 0 <= j < self.levels@[i].entries().len()
                        implies (#[trigger] self.levels@[i].entries()[j])
                            .receipt@.height == i as nat by {
                        if i == target {
                            assert(emitted_seq
                                + self.levels@[i].entries()
                                =~= old_target_entries.push(descriptor));
                            assert(self.levels@[i].entries()[j]
                                == old_target_entries.push(descriptor)[
                                    emitted_seq.len() as int + j
                                ]);
                        } else if i == old_levels.len()
                            && self.levels@.len() == old_levels.len() + 1
                        {
                            assert(self.levels@[i].entries().len() == 0);
                        } else {
                            assert(self.levels@[i].entries()
                                == old_levels[i].entries());
                        }
                    }
                    assert(streaming_pending_page_wf(
                        self.pending.unwrap(),
                        self.leaf_tail.capacity,
                        self.index_fanout,
                    )) by {
                        assert forall |i: int| 0 <= i < emitted_seq.len()
                            implies emitted_seq[i].receipt@.height + 1
                                == parent_level as nat + 1 by {
                            assert(emitted_seq[i]
                                == old_target_entries.push(descriptor)[i]);
                        }
                    }
                }
            },
        }
        proof {
            let parts = descriptor_frontier_collapse_parts(
                self0.active_frontier(),
                children_seq,
                descriptor,
                self.active_frontier(),
            );
            assert(!descriptor_forest_nodes(self0.active_frontier())
                .contains_key(addr@));
            assert(self.unstaged_leaf_entries()
                == self0.unstaged_leaf_entries());
            StreamingBranchBuilder::index_stage_preserves_stream_wf(
                self0,
                *self,
                children_seq,
                descriptor,
                parts.0,
                parts.1,
                addr@,
                node@,
            );
            assert(self.layout_wf()) by {
                reveal(StreamingBranchBuilder::layout_wf);
            }
            if self.phase is Finishing {
                let level = self.phase->level;
                assert(level <= parent_level);
                assert forall |i: int| 0 <= i < level
                    implies (#[trigger] self.levels@[i]).entries()
                        == old_levels[i].entries() by {}
            }
            assert(self.phase_wf()) by {
                reveal(StreamingBranchBuilder::phase_wf);
            }
            assert(self.local_wf());
        }
        StreamingStagedPage { node, descriptor }
    }

    pub fn finish_input(&mut self) -> (out: StreamingFinishInputResult)
        requires
            old(self).local_wf(),
            old(self).phase is Reading,
            old(self).pending is None,
            old(self).deferred is None,
        ensures
            self.local_wf(),
            self.leaf_tail.capacity == old(self).leaf_tail.capacity,
            self.index_fanout == old(self).index_fanout,
            self.source_entries@ == old(self).source_entries@,
            self.staged_nodes@ == old(self).staged_nodes@,
            match out {
                StreamingFinishInputResult::Empty => {
                    &&& self.phase is Empty
                    &&& self.source_entries@.len() == 0
                },
                StreamingFinishInputResult::RootReady => {
                    &&& self.phase is ReadyLeafRoot
                    &&& self.root_leaf@ == self.source_entries@
                },
                StreamingFinishInputResult::Continue => {
                    &&& self.phase is Finishing
                    &&& self.phase->level == 0
                    &&& self.leaf_tail.entries().len() == 0
                    &&& (self.pending is Some
                        || self.leaf_prefix@.len() > 0)
                },
            },
    {
        let ghost self0 = *self;
        proof {
            self0.expose_layout_wf();
            self0.expose_stream_wf();
            self0.expose_phase_wf();
        }
        let tail_result = self.leaf_tail.finish();
        match tail_result {
            StreamingLeafFinishResult::Empty => {
                if !self.has_staged_leaf {
                    self.phase = StreamingBranchPhase::Empty;
                    proof {
                        assert(self0.source_entries@.len() == 0);
                        assert(self0.active_frontier().len() == 0) by {
                            if self0.active_frontier().len() > 0 {
                                let descriptor = self0.active_frontier()[0];
                                assert(exists |j: int|
                                    0 <= j < self0.leaf_prefix@.len()
                                    && self0.leaf_prefix@[j].key
                                        == descriptor.receipt@.last_key);
                            }
                        }
                        assert(self.active_frontier().len() == 0);
                        assert(self.staged_nodes@ == LoadedBranch::empty());
                        assert(self.layout_wf()) by {
                            reveal(StreamingBranchBuilder::layout_wf);
                        }
                        assert(self.stream_wf()) by {
                            reveal(StreamingBranchBuilder::stream_wf);
                        }
                        assert(self.phase_wf()) by {
                            reveal(StreamingBranchBuilder::phase_wf);
                        }
                        assert(self.local_wf());
                    }
                    StreamingFinishInputResult::Empty
                } else {
                    self.phase = StreamingBranchPhase::Finishing {
                        level: 0,
                    };
                    proof {
                        assert(self.levels.len() > 0) by {
                            if self.levels.len() == 0 {
                                assert(self0.active_frontier().len() == 0);
                                assert(descriptor_forest_contents(
                                    self0.active_frontier(),
                                ) == Map::<Key, Message>::empty());
                                assert(MemtableBucket::entries_map(
                                    self0.leaf_prefix@,
                                ) == Map::<Key, Message>::empty());
                                sorted_entries_unique(self0.leaf_prefix@);
                                MemtableBucket::entries_map_empty_implies_entries_empty(
                                    self0.leaf_prefix@,
                                );
                            }
                        }
                        assert(self.active_frontier()
                            == self0.active_frontier());
                        assert(self.unstaged_leaf_entries().len() == 0);
                        assert(self.source_entries@ == self.leaf_prefix@);
                        assert(self.layout_wf()) by {
                            reveal(StreamingBranchBuilder::layout_wf);
                        }
                        assert(self.stream_wf()) by {
                            reveal(StreamingBranchBuilder::stream_wf);
                        }
                        assert(self.phase_wf()) by {
                            reveal(StreamingBranchBuilder::phase_wf);
                        }
                        assert(self.local_wf());
                    }
                    StreamingFinishInputResult::Continue
                }
            },
            StreamingLeafFinishResult::One { entries } => {
                if !self.has_staged_leaf {
                    self.root_leaf = entries;
                    self.phase = StreamingBranchPhase::ReadyLeafRoot;
                    proof {
                        assert(self0.active_frontier().len() == 0) by {
                            if self0.active_frontier().len() > 0 {
                                assert(exists |j: int|
                                    0 <= j < self0.leaf_prefix@.len()
                                    && self0.leaf_prefix@[j].key
                                        == self0.active_frontier()[0]
                                            .receipt@.last_key);
                            }
                        }
                        assert(self.staged_nodes@ == LoadedBranch::empty());
                        assert(self.root_leaf@
                            == self0.unstaged_leaf_entries());
                        assert(self.root_leaf@ == self.source_entries@) by {
                            assert_seqs_equal!(
                                self.root_leaf@,
                                self.source_entries@,
                                i => {}
                            );
                        }
                        assert(self.layout_wf()) by {
                            reveal(StreamingBranchBuilder::layout_wf);
                        }
                        assert(self.stream_wf()) by {
                            reveal(StreamingBranchBuilder::stream_wf);
                        }
                        assert(self.phase_wf()) by {
                            reveal(StreamingBranchBuilder::phase_wf);
                        }
                        assert(self.local_wf());
                    }
                    StreamingFinishInputResult::RootReady
                } else {
                    if self.levels.len() == 0 {
                        let level = StreamingIndexTail::new(
                            self.index_fanout,
                        ).unwrap();
                        self.levels.push(level);
                    }
                    self.pending = Some(StreamingPendingPage::Leaf {
                        entries,
                        parent_level: 0,
                    });
                    self.phase = StreamingBranchPhase::Finishing {
                        level: 0,
                    };
                    proof {
                        streaming_leaf_pages_do_not_change_frontier(
                            self.levels@,
                            self.pending,
                            self.deferred,
                            self.levels@.len(),
                        );
                        assert(self.active_frontier()
                            == self0.active_frontier()) by {
                            if self0.levels.len() == 0 {
                                assert(!self0.has_staged_leaf);
                            }
                        }
                        assert(self.unstaged_leaf_entries()
                            == self0.unstaged_leaf_entries());
                        assert(self.layout_wf()) by {
                            reveal(StreamingBranchBuilder::layout_wf);
                        }
                        assert(self.stream_wf()) by {
                            reveal(StreamingBranchBuilder::stream_wf);
                        }
                        assert(self.phase_wf()) by {
                            reveal(StreamingBranchBuilder::phase_wf);
                        }
                        assert(self.local_wf());
                    }
                    StreamingFinishInputResult::Continue
                }
            },
            StreamingLeafFinishResult::Two { left, right } => {
                if self.levels.len() == 0 {
                    let level = StreamingIndexTail::new(
                        self.index_fanout,
                    ).unwrap();
                    self.levels.push(level);
                }
                self.pending = Some(StreamingPendingPage::Leaf {
                    entries: left,
                    parent_level: 0,
                });
                self.deferred = Some(StreamingPendingPage::Leaf {
                    entries: right,
                    parent_level: 0,
                });
                self.phase = StreamingBranchPhase::Finishing {
                    level: 0,
                };
                proof {
                    streaming_leaf_pages_do_not_change_frontier(
                        self.levels@,
                        self.pending,
                        self.deferred,
                        self.levels@.len(),
                    );
                    assert(self.active_frontier()
                        == self0.active_frontier()) by {
                        if self0.levels.len() == 0 {
                            assert(self0.active_frontier().len() == 0);
                            reveal_with_fuel(streaming_levels_frontier, 2);
                            assert(streaming_pending_descriptors_at(
                                self.pending,
                                0,
                            ) == Seq::<BranchChildDescriptor>::empty());
                            assert(streaming_pending_descriptors_at(
                                self.deferred,
                                0,
                            ) == Seq::<BranchChildDescriptor>::empty());
                            assert(self.levels@[0].entries().len() == 0);
                            assert(self.active_frontier().len() == 0);
                        }
                    }
                    assert(self.unstaged_leaf_entries()
                        =~= self0.unstaged_leaf_entries());
                    assert(self.layout_wf()) by {
                        reveal(StreamingBranchBuilder::layout_wf);
                    }
                    assert(self.stream_wf()) by {
                        reveal(StreamingBranchBuilder::stream_wf);
                    }
                    assert(self.phase_wf()) by {
                        reveal(StreamingBranchBuilder::phase_wf);
                    }
                    assert(self.local_wf());
                }
                StreamingFinishInputResult::Continue
            },
        }
    }

    pub fn finish_level(&mut self) -> (out: StreamingFinishLevelResult)
        requires
            old(self).local_wf(),
            old(self).phase is Finishing,
            old(self).pending is None,
            old(self).deferred is None,
        ensures
            self.local_wf(),
            self.leaf_tail.capacity == old(self).leaf_tail.capacity,
            self.index_fanout == old(self).index_fanout,
            self.source_entries@ == old(self).source_entries@,
            self.leaf_prefix@ == old(self).leaf_prefix@,
            self.staged_nodes@ == old(self).staged_nodes@,
            match out {
                StreamingFinishLevelResult::Empty => {
                    &&& self.phase is Empty
                    &&& self.source_entries@.len() == 0
                },
                StreamingFinishLevelResult::Advanced => {
                    &&& self.phase is Finishing
                    &&& self.phase->level == old(self).phase->level + 1
                    &&& self.pending is None
                    &&& self.deferred is None
                },
                StreamingFinishLevelResult::PagesReady => {
                    &&& self.phase is Finishing
                    &&& self.phase->level == old(self).phase->level + 1
                    &&& self.pending is Some
                    &&& self.pending->0 is Index
                },
                StreamingFinishLevelResult::RootReady => {
                    &&& self.phase is ReadyIndexRoot
                    &&& self.root_children.len() > 0
                },
            },
    {
        let ghost self0 = *self;
        proof {
            self0.expose_layout_wf();
            self0.expose_stream_wf();
            self0.expose_phase_wf();
        }
        let level = match self.phase {
            StreamingBranchPhase::Finishing { level } => level,
            _ => {
                proof { assert(false); }
                unreached()
            },
        };
        let ghost old_levels = self.levels@;
        let ghost old_entries = self.levels@[level as int].entries();
        let mut tail = self.levels.remove(level);
        let finish = tail.finish();
        self.levels.insert(level, tail);
        match finish {
            StreamingIndexFinishResult::Empty => {
                proof {
                    assert(self.levels@ == old_levels) by {
                        assert_seqs_equal!(self.levels@, old_levels, i => {});
                    }
                }
                if level + 1 == self.levels.len() {
                    self.phase = StreamingBranchPhase::Empty;
                    proof {
                        assert forall |i: int| 0 <= i < self.levels@.len()
                            implies (#[trigger] self.levels@[i])
                                .entries().len() == 0 by {
                            if i < level {
                            } else {
                                assert(i == level);
                            }
                        }
                        streaming_empty_levels_frontier(
                            self.levels@,
                            self.levels@.len(),
                        );
                        assert(self0.active_frontier().len() == 0);
                        assert(descriptor_forest_contents(
                            self0.active_frontier(),
                        ) == Map::<Key, Message>::empty());
                        assert(MemtableBucket::entries_map(
                            self0.leaf_prefix@,
                        ) == Map::<Key, Message>::empty());
                        sorted_entries_unique(self0.leaf_prefix@);
                        MemtableBucket::entries_map_empty_implies_entries_empty(
                            self0.leaf_prefix@,
                        );
                        assert(!self0.has_staged_leaf);
                        assert(self.source_entries@.len() == 0);
                        assert(self.staged_nodes@ == LoadedBranch::empty());
                        assert(self.stream_wf()) by {
                            reveal(StreamingBranchBuilder::stream_wf);
                        }
                        assert(self.layout_wf()) by {
                            reveal(StreamingBranchBuilder::layout_wf);
                        }
                        assert(self.phase_wf()) by {
                            reveal(StreamingBranchBuilder::phase_wf);
                        }
                        assert(self.local_wf());
                    }
                    StreamingFinishLevelResult::Empty
                } else {
                    self.phase = StreamingBranchPhase::Finishing {
                        level: level + 1,
                    };
                    proof {
                        assert(self.active_frontier()
                            == self0.active_frontier());
                        assert(self.unstaged_leaf_entries()
                            == self0.unstaged_leaf_entries());
                        StreamingBranchBuilder::same_frontier_preserves_stream_wf(
                            self0,
                            *self,
                        );
                        assert(self.layout_wf()) by {
                            reveal(StreamingBranchBuilder::layout_wf);
                        }
                        assert(self.phase_wf()) by {
                            reveal(StreamingBranchBuilder::phase_wf);
                        }
                        assert(self.local_wf());
                    }
                    StreamingFinishLevelResult::Advanced
                }
            },
            StreamingIndexFinishResult::One { children } => {
                let ghost children_seq = children@;
                if level + 1 == self.levels.len() {
                    self.root_children = children;
                    self.phase = StreamingBranchPhase::ReadyIndexRoot;
                    proof {
                        streaming_empty_levels_frontier(
                            old_levels,
                            level as nat,
                        );
                        reveal_with_fuel(streaming_levels_frontier, 2);
                        assert(self0.active_frontier() == children_seq);
                        assert(self.active_frontier() == children_seq);
                        assert(children_seq.len() > 0);
                        assert(self.unstaged_leaf_entries().len() == 0);
                        assert(self.source_entries@ == self.leaf_prefix@);
                        StreamingBranchBuilder::same_frontier_preserves_stream_wf(
                            self0,
                            *self,
                        );
                        assert(self.layout_wf()) by {
                            reveal(StreamingBranchBuilder::layout_wf);
                        }
                        assert(self.phase_wf()) by {
                            reveal(StreamingBranchBuilder::phase_wf);
                        }
                        assert(self.local_wf());
                    }
                    StreamingFinishLevelResult::RootReady
                } else {
                    self.pending = Some(StreamingPendingPage::Index {
                        children,
                        parent_level: level + 1,
                    });
                    self.phase = StreamingBranchPhase::Finishing {
                        level: level + 1,
                    };
                    proof {
                        streaming_finish_pages_layout(
                            old_levels,
                            self.levels@,
                            self.pending.unwrap(),
                            None,
                            level as int,
                            self.levels@.len(),
                        );
                        assert(self.active_frontier()
                            == self0.active_frontier());
                        assert(self.unstaged_leaf_entries()
                            == self0.unstaged_leaf_entries());
                        StreamingBranchBuilder::same_frontier_preserves_stream_wf(
                            self0,
                            *self,
                        );
                        assert(self.layout_wf()) by {
                            reveal(StreamingBranchBuilder::layout_wf);
                        }
                        assert(self.phase_wf()) by {
                            reveal(StreamingBranchBuilder::phase_wf);
                        }
                        assert(self.local_wf());
                    }
                    StreamingFinishLevelResult::PagesReady
                }
            },
            StreamingIndexFinishResult::Two { left, right } => {
                let ghost left_seq = left@;
                let ghost right_seq = right@;
                if level + 1 == self.levels.len() {
                    let next = StreamingIndexTail::new(
                        self.index_fanout,
                    ).unwrap();
                    self.levels.push(next);
                }
                self.pending = Some(StreamingPendingPage::Index {
                    children: left,
                    parent_level: level + 1,
                });
                self.deferred = Some(StreamingPendingPage::Index {
                    children: right,
                    parent_level: level + 1,
                });
                self.phase = StreamingBranchPhase::Finishing {
                    level: level + 1,
                };
                proof {
                    streaming_finish_pages_layout(
                        old_levels,
                        self.levels@,
                        self.pending.unwrap(),
                        self.deferred,
                        level as int,
                        self.levels@.len(),
                    );
                    assert(left_seq + right_seq == old_entries) by {
                        assert_seqs_equal!(
                            left_seq + right_seq,
                            old_entries,
                            i => {}
                        );
                    }
                    assert forall |i: int| 0 <= i < left_seq.len()
                        implies (#[trigger] left_seq[i]).receipt@.height + 1
                            == (level + 1) as nat by {
                        assert((left_seq + right_seq)[i] == left_seq[i]);
                        assert(old_entries[i] == left_seq[i]);
                    }
                    assert forall |i: int| 0 <= i < right_seq.len()
                        implies (#[trigger] right_seq[i]).receipt@.height + 1
                            == (level + 1) as nat by {
                        let old_index = left_seq.len() as int + i;
                        assert((left_seq + right_seq)[old_index]
                            == right_seq[i]);
                        assert(old_entries[old_index] == right_seq[i]);
                    }
                    assert(streaming_pending_page_wf(
                        self.pending.unwrap(),
                        self.leaf_tail.capacity,
                        self.index_fanout,
                    ));
                    assert(match self.deferred {
                        Some(page) => streaming_pending_page_wf(
                            page,
                            self.leaf_tail.capacity,
                            self.index_fanout,
                        ),
                        None => true,
                    });
                    assert(self.active_frontier()
                        == self0.active_frontier());
                    assert(self.unstaged_leaf_entries()
                        == self0.unstaged_leaf_entries());
                    StreamingBranchBuilder::same_frontier_preserves_stream_wf(
                        self0,
                        *self,
                    );
                    assert(self.layout_wf()) by {
                        reveal(StreamingBranchBuilder::layout_wf);
                    }
                    assert(self.phase_wf()) by {
                        reveal(StreamingBranchBuilder::phase_wf);
                    }
                    assert(self.local_wf());
                }
                StreamingFinishLevelResult::PagesReady
            },
        }
    }

    pub fn ready_to_seal(&self) -> (out: bool)
        ensures
            out == (self.phase is ReadyLeafRoot
                || self.phase is ReadyIndexRoot),
    {
        match self.phase {
            StreamingBranchPhase::ReadyLeafRoot
            | StreamingBranchPhase::ReadyIndexRoot => true,
            _ => false,
        }
    }

    pub fn root_node(
        &self,
        aux_ptr: Option<IAddress>,
    ) -> (out: Option<IBranchNode>)
        requires
            self.local_wf(),
            self.phase is ReadyLeafRoot
                || self.phase is ReadyIndexRoot,
            self.phase is ReadyLeafRoot ==> aux_ptr is None,
            self.phase is ReadyIndexRoot ==> aux_ptr is Some,
        ensures
            out is Some,
            out.unwrap().wf(),
            out.unwrap()@.wf(),
            out.unwrap()@.keys_strictly_sorted(),
            !(out.unwrap() is Auxiliary),
            self.phase is ReadyLeafRoot ==> {
                &&& out.unwrap() is Leaf
                &&& out.unwrap()->keys.len() <= self.leaf_tail.capacity
                &&& out.unwrap()->keys.len() <= u8::MAX as usize
                &&& out.unwrap()@ == (BranchNode::Leaf {
                    keys: self.root_leaf@.map(
                        |i: int, entry: MemtableEntry| entry.key,
                    ),
                    msgs: self.root_leaf@.map(
                        |i: int, entry: MemtableEntry| entry.message,
                    ),
                })
            },
            self.phase is ReadyIndexRoot ==> {
                &&& out.unwrap() is Index
                &&& out.unwrap()->pivots.len() + 1 <= self.index_fanout
                &&& out.unwrap()->pivots.len() <= u8::MAX as usize
                &&& out.unwrap()@ == (BranchNode::Index {
                    pivots: descriptor_pivots(self.root_children@),
                    children: self.root_children@.map(
                        |i: int, descriptor: BranchChildDescriptor|
                            descriptor.addr@,
                    ),
                    aux_ptr: iopt_addr(aux_ptr),
                })
            },
    {
        proof {
            self.expose_phase_wf();
        }
        match self.phase {
            StreamingBranchPhase::ReadyLeafRoot => {
                let entries = self.root_leaf.clone();
                Some(leaf_from_entries(entries))
            },
            StreamingBranchPhase::ReadyIndexRoot => {
                let node = index_from_descriptors(
                    &self.root_children,
                    0,
                    self.root_children.len(),
                    aux_ptr,
                );
                proof {
                    assert(node@->pivots
                        == descriptor_pivots(self.root_children@)) by {
                        assert_seqs_equal!(
                            node@->pivots,
                            descriptor_pivots(self.root_children@),
                            i => {}
                        );
                    }
                    assert(node@->children
                        == self.root_children@.map(
                            |i: int, descriptor: BranchChildDescriptor|
                                descriptor.addr@,
                        )) by {
                        assert_seqs_equal!(
                            node@->children,
                            self.root_children@.map(
                                |i: int, descriptor: BranchChildDescriptor|
                                    descriptor.addr@,
                            ),
                            i => {}
                        );
                    }
                }
                Some(node)
            },
            _ => {
                proof { assert(false); }
                None
            },
        }
    }

    pub proof fn sealed_branch_receipt(
        &self,
        root: Address,
        root_node: BranchNode,
        aux: Option<Address>,
        summary: Summary,
    ) -> (branch: LinkedBranch<Summary>)
        requires
            self.local_wf(),
            self.phase is ReadyLeafRoot
                || self.phase is ReadyIndexRoot,
            root.wf(),
            root_node.wf(),
            !self.staged_nodes@.contains_key(root),
            self.phase is ReadyLeafRoot ==> {
                &&& aux is None
                &&& summary == set![root.au]
                &&& root_node == (BranchNode::Leaf {
                    keys: self.root_leaf@.map(
                        |i: int, entry: MemtableEntry| entry.key,
                    ),
                    msgs: self.root_leaf@.map(
                        |i: int, entry: MemtableEntry| entry.message,
                    ),
                })
            },
            self.phase is ReadyIndexRoot ==> {
                &&& aux is Some
                &&& aux.unwrap().wf()
                &&& aux.unwrap() != root
                &&& !self.staged_nodes@.contains_key(aux.unwrap())
                &&& root_node == (BranchNode::Index {
                    pivots: descriptor_pivots(self.root_children@),
                    children: self.root_children@.map(
                        |i: int, descriptor: BranchChildDescriptor|
                            descriptor.addr@,
                    ),
                    aux_ptr: Some(aux.unwrap()),
                })
            },
            addrs_closed(
                if aux is Some {
                    self.staged_nodes@.dom().insert(root)
                        .insert(aux.unwrap())
                } else {
                    self.staged_nodes@.dom().insert(root)
                },
                summary,
            ),
        ensures
            branch.root == root,
            branch.valid_sealed_branch(),
            branch.tight_disk_view_with_summary(),
            branch.get_summary() == summary,
            branch.i().i().map
                == MemtableBucket::entries_map(self.source_entries@),
            branch.disk_view.entries == if aux is Some {
                self.staged_nodes@.insert(root, root_node).insert(
                    aux.unwrap(),
                    BranchNode::Auxiliary(summary),
                )
            } else {
                self.staged_nodes@.insert(root, root_node)
            },
    {
        self.expose_phase_wf();
        self.expose_stream_wf();
        match self.phase {
            StreamingBranchPhase::ReadyLeafRoot => {
                let receipt = make_leaf_receipt(root, root_node);
                sorted_entries_unique(self.root_leaf@);
                leaf_entries_contents(self.root_leaf@, root_node);
                assert(receipt.pivot.i().map
                    == MemtableBucket::entries_map(self.source_entries@));
                assert(receipt.nodes
                    == self.staged_nodes@.insert(root, root_node));
                let branch = finalize_leaf_seal(receipt);
                assert(branch.get_summary() == summary);
                branch
            },
            StreamingBranchPhase::ReadyIndexRoot => {
                let unsealed = BranchNode::Index {
                    pivots: descriptor_pivots(self.root_children@),
                    children: self.root_children@.map(
                        |i: int, descriptor: BranchChildDescriptor|
                            descriptor.addr@,
                    ),
                    aux_ptr: None,
                };
                assert(descriptor_forest_wf(self.root_children@));
                let receipt = make_index_receipt(
                    self.root_children@,
                    root,
                    unsealed,
                );
                assert(receipt.nodes
                    == self.staged_nodes@.insert(root, unsealed));
                assert(receipt.pivot.i().map
                    == MemtableBucket::entries_map(self.source_entries@));
                let branch = finalize_index_seal(
                    receipt,
                    aux.unwrap(),
                    summary,
                );
                assert(branch.disk_view.entries
                    == self.staged_nodes@.insert(root, root_node).insert(
                        aux.unwrap(),
                        BranchNode::Auxiliary(summary),
                    ));
                branch
            },
            _ => {
                assert(false);
                arbitrary()
            },
        }
    }
}

} // verus!
