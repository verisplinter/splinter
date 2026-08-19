// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::assert_maps_equal;

use crate::abstract_system::MsgHistory_v::{KeyedMessage, MsgHistory};
use crate::abstract_system::StampedMap_v::LSN;
use crate::betree::Buffer_v::SimpleBuffer;
use crate::betree::Memtable_v::Memtable;
use crate::betree::PivotBranch_v::Node as PivotNode;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Delta, Message, nop_delta};

verus! {

#[derive(Clone, Copy, Debug)]
pub struct MemtableEntry {
    pub key: Key,
    pub message: Message,
}

pub struct MemtableBucket {
    pub entries: Vec<MemtableEntry>,
}

pub struct MemtableImpl {
    pub buckets: Vec<MemtableBucket>,
    pub bucket_count: u32,
    pub seq_end: u64,
}

pub struct MemtableIter<'a> {
    memtable: &'a MemtableImpl,
    bucket: usize,
    entry: usize,
}

pub struct MemtableSortedCursor {
    positions: Vec<usize>,
    remaining: Ghost<Map<Key, Message>>,
}

#[derive(Debug)]
pub enum MemtableUpdateResult {
    Applied,
    Noop,
}

impl MemtableBucket {
    pub open spec fn unique_keys(entries: Seq<MemtableEntry>) -> bool {
        forall |i: int, j: int|
            #![trigger entries[i].key, entries[j].key]
            0 <= i < entries.len()
            && 0 <= j < entries.len()
            && entries[i].key == entries[j].key
            ==> i == j
    }

    pub open spec fn strictly_sorted(entries: Seq<MemtableEntry>) -> bool {
        forall |i: int, j: int|
            0 <= i < j < entries.len()
            ==> entries[i].key.0 < entries[j].key.0
    }

    pub open spec fn entries_map(entries: Seq<MemtableEntry>) -> Map<Key, Message>
        recommends Self::unique_keys(entries)
    {
        Map::new(
            |key: Key| exists |i: int| #![auto]
                0 <= i < entries.len() && entries[i].key == key,
            |key: Key| entries[choose |i: int| #![auto]
                0 <= i < entries.len() && entries[i].key == key].message,
        )
    }

    pub open spec fn wf(&self) -> bool {
        &&& Self::unique_keys(self.entries@)
        &&& Self::strictly_sorted(self.entries@)
    }

    pub proof fn entries_map_index(entries: Seq<MemtableEntry>, i: int)
        requires
            Self::unique_keys(entries),
            0 <= i < entries.len(),
        ensures
            Self::entries_map(entries).contains_key(entries[i].key),
            Self::entries_map(entries)[entries[i].key] == entries[i].message,
    {
    }

    pub proof fn entries_map_index_for_key(entries: Seq<MemtableEntry>, key: Key) -> (i: int)
        requires
            Self::unique_keys(entries),
            Self::entries_map(entries).contains_key(key),
        ensures
            0 <= i < entries.len(),
            entries[i].key == key,
            Self::entries_map(entries)[key] == entries[i].message,
    {
        let i = choose |i: int| #![auto]
            0 <= i < entries.len() && entries[i].key == key;
        Self::entries_map_index(entries, i);
        i
    }

    pub proof fn entries_map_empty_implies_entries_empty(entries: Seq<MemtableEntry>)
        requires
            Self::unique_keys(entries),
            Self::entries_map(entries) == Map::<Key, Message>::empty(),
        ensures
            entries.len() == 0,
    {
        if entries.len() > 0 {
            Self::entries_map_index(entries, 0);
        }
    }

    pub proof fn entries_map_after_set(
        old_entries: Seq<MemtableEntry>,
        index: int,
        entry: MemtableEntry,
    )
        requires
            Self::unique_keys(old_entries),
            0 <= index < old_entries.len(),
            old_entries[index].key == entry.key,
        ensures
            Self::unique_keys(old_entries.update(index, entry)),
            Self::entries_map(old_entries.update(index, entry))
                == Self::entries_map(old_entries).insert(entry.key, entry.message),
    {
        let new_entries = old_entries.update(index, entry);
        assert forall |i: int, j: int|
            #![trigger new_entries[i].key, new_entries[j].key]
            0 <= i < new_entries.len()
            && 0 <= j < new_entries.len()
            && new_entries[i].key == new_entries[j].key
            implies i == j by {
            if i != index && j != index {
                assert(new_entries[i] == old_entries[i]);
                assert(new_entries[j] == old_entries[j]);
            } else if i == index && j != index {
                assert(new_entries[i].key == entry.key);
                assert(new_entries[j].key == old_entries[j].key);
                assert(old_entries[index].key == old_entries[j].key);
            } else if i != index && j == index {
                assert(new_entries[i].key == old_entries[i].key);
                assert(new_entries[j].key == entry.key);
                assert(old_entries[i].key == old_entries[index].key);
            }
        }
        assert_maps_equal!(
            Self::entries_map(new_entries),
            Self::entries_map(old_entries).insert(entry.key, entry.message),
            key => {
                if key == entry.key {
                    Self::entries_map_index(new_entries, index);
                } else if Self::entries_map(old_entries).contains_key(key) {
                    let i = Self::entries_map_index_for_key(old_entries, key);
                    assert(i != index);
                    Self::entries_map_index(new_entries, i);
                }
            }
        );
    }

    pub proof fn entries_map_after_push(
        old_entries: Seq<MemtableEntry>,
        entry: MemtableEntry,
    )
        requires
            Self::unique_keys(old_entries),
            !Self::entries_map(old_entries).contains_key(entry.key),
        ensures
            Self::unique_keys(old_entries.push(entry)),
            Self::entries_map(old_entries.push(entry))
                == Self::entries_map(old_entries).insert(entry.key, entry.message),
    {
        let new_entries = old_entries.push(entry);
        assert forall |i: int, j: int|
            #![trigger new_entries[i].key, new_entries[j].key]
            0 <= i < new_entries.len()
            && 0 <= j < new_entries.len()
            && new_entries[i].key == new_entries[j].key
            implies i == j by {
            if i < old_entries.len() && j < old_entries.len() {
                assert(new_entries[i] == old_entries[i]);
                assert(new_entries[j] == old_entries[j]);
            } else if i == old_entries.len() && j < old_entries.len() {
                assert(new_entries[i] == entry);
                assert(Self::entries_map(old_entries).contains_key(old_entries[j].key));
            } else if i < old_entries.len() && j == old_entries.len() {
                assert(new_entries[j] == entry);
                assert(Self::entries_map(old_entries).contains_key(old_entries[i].key));
            }
        }
        assert_maps_equal!(
            Self::entries_map(new_entries),
            Self::entries_map(old_entries).insert(entry.key, entry.message),
            key => {
                if key == entry.key {
                    Self::entries_map_index(new_entries, old_entries.len() as int);
                } else if Self::entries_map(old_entries).contains_key(key) {
                    let i = Self::entries_map_index_for_key(old_entries, key);
                    Self::entries_map_index(new_entries, i);
                }
            }
        );
    }

    pub proof fn entries_map_after_insert(
        old_entries: Seq<MemtableEntry>,
        index: int,
        entry: MemtableEntry,
    )
        requires
            Self::unique_keys(old_entries),
            0 <= index <= old_entries.len(),
            !Self::entries_map(old_entries).contains_key(entry.key),
        ensures
            Self::unique_keys(old_entries.insert(index, entry)),
            Self::entries_map(old_entries.insert(index, entry))
                == Self::entries_map(old_entries).insert(entry.key, entry.message),
    {
        let inserted = old_entries.insert(index, entry);
        assert forall |i: int, j: int|
            #![trigger inserted[i].key, inserted[j].key]
            0 <= i < inserted.len()
            && 0 <= j < inserted.len()
            && inserted[i].key == inserted[j].key
            implies i == j by {
            if i == index || j == index {
                if i == index && j != index {
                    let old_j = if j < index { j } else { j - 1 };
                    assert(0 <= old_j < old_entries.len());
                    assert(inserted[i] == entry);
                    assert(inserted[j] == old_entries[old_j]);
                    Self::entries_map_index(old_entries, old_j);
                } else if i != index && j == index {
                    let old_i = if i < index { i } else { i - 1 };
                    assert(0 <= old_i < old_entries.len());
                    assert(inserted[i] == old_entries[old_i]);
                    assert(inserted[j] == entry);
                    Self::entries_map_index(old_entries, old_i);
                }
            } else {
                let old_i = if i < index { i } else { i - 1 };
                let old_j = if j < index { j } else { j - 1 };
                assert(0 <= old_i < old_entries.len());
                assert(0 <= old_j < old_entries.len());
                assert(inserted[i] == old_entries[old_i]);
                assert(inserted[j] == old_entries[old_j]);
                assert(old_i == old_j);
                if i != j {
                    assert(false);
                }
            }
        }
        assert_maps_equal!(
            Self::entries_map(inserted),
            Self::entries_map(old_entries).insert(entry.key, entry.message),
            key => {
                if key == entry.key {
                    Self::entries_map_index(inserted, index);
                } else if Self::entries_map(old_entries).contains_key(key) {
                    let old_i = Self::entries_map_index_for_key(old_entries, key);
                    let new_i = if old_i < index { old_i } else { old_i + 1 };
                    assert(0 <= new_i < inserted.len());
                    assert(inserted[new_i] == old_entries[old_i]);
                    Self::entries_map_index(inserted, new_i);
                }
            }
        );
    }

    pub proof fn sorted_after_insert(
        old_entries: Seq<MemtableEntry>,
        index: int,
        entry: MemtableEntry,
    )
        requires
            Self::strictly_sorted(old_entries),
            0 <= index <= old_entries.len(),
            forall |i: int| 0 <= i < index
                ==> old_entries[i].key.0 < entry.key.0,
            forall |i: int| index <= i < old_entries.len()
                ==> entry.key.0 < old_entries[i].key.0,
        ensures
            Self::strictly_sorted(old_entries.insert(index, entry)),
    {
        let inserted = old_entries.insert(index, entry);
        assert forall |i: int, j: int|
            0 <= i < j < inserted.len()
            implies inserted[i].key.0 < inserted[j].key.0 by {
            if i == index {
                assert(j > index);
                assert(inserted[i] == entry);
                assert(inserted[j] == old_entries[j - 1]);
            } else if j == index {
                assert(i < index);
                assert(inserted[i] == old_entries[i]);
                assert(inserted[j] == entry);
            } else if j < index {
                assert(inserted[i] == old_entries[i]);
                assert(inserted[j] == old_entries[j]);
            } else if index < i {
                assert(inserted[i] == old_entries[i - 1]);
                assert(inserted[j] == old_entries[j - 1]);
            } else {
                assert(i < index < j);
                assert(inserted[i] == old_entries[i]);
                assert(inserted[j] == old_entries[j - 1]);
                assert(i < j - 1);
            }
        }
    }

    pub proof fn sorted_after_set_same_key(
        old_entries: Seq<MemtableEntry>,
        index: int,
        entry: MemtableEntry,
    )
        requires
            Self::strictly_sorted(old_entries),
            0 <= index < old_entries.len(),
            old_entries[index].key == entry.key,
        ensures
            Self::strictly_sorted(old_entries.update(index, entry)),
    {
        let updated = old_entries.update(index, entry);
        assert forall |i: int, j: int|
            0 <= i < j < updated.len()
            implies updated[i].key.0 < updated[j].key.0 by {
            assert(updated[i].key == old_entries[i].key);
            assert(updated[j].key == old_entries[j].key);
        }
    }

    pub proof fn unique_keys_after_swap(
        entries: Seq<MemtableEntry>,
        left: int,
        right: int,
    )
        requires
            Self::unique_keys(entries),
            0 <= left < entries.len(),
            0 <= right < entries.len(),
        ensures
            Self::unique_keys(
                entries.update(left, entries[right])
                    .update(right, entries[left]),
            ),
    {
        let swapped = entries.update(left, entries[right])
            .update(right, entries[left]);
        assert forall |i: int, j: int|
            #![trigger swapped[i].key, swapped[j].key]
            0 <= i < swapped.len()
            && 0 <= j < swapped.len()
            && swapped[i].key == swapped[j].key
            implies i == j by {
            let old_i = if i == left { right } else if i == right { left } else { i };
            let old_j = if j == left { right } else if j == right { left } else { j };
            assert(0 <= old_i < entries.len());
            assert(0 <= old_j < entries.len());
            assert(swapped[i] == entries[old_i]);
            assert(swapped[j] == entries[old_j]);
            assert(old_i == old_j);
            if i != j {
                if i == left {
                    assert(old_i == right);
                    if j == right {
                        assert(old_j == left);
                        assert(left != right);
                    }
                } else if i == right {
                    assert(old_i == left);
                }
                assert(false);
            }
        }
    }

    pub proof fn entries_map_after_swap(
        entries: Seq<MemtableEntry>,
        left: int,
        right: int,
    )
        requires
            Self::unique_keys(entries),
            0 <= left < entries.len(),
            0 <= right < entries.len(),
        ensures
            Self::entries_map(
                entries.update(left, entries[right])
                    .update(right, entries[left]),
            ) == Self::entries_map(entries),
    {
        let swapped = entries.update(left, entries[right])
            .update(right, entries[left]);
        Self::unique_keys_after_swap(entries, left, right);
        assert_maps_equal!(
            Self::entries_map(swapped),
            Self::entries_map(entries),
            key => {
                if Self::entries_map(entries).contains_key(key) {
                    let old_index = Self::entries_map_index_for_key(entries, key);
                    let new_index = if old_index == left {
                        right
                    } else if old_index == right {
                        left
                    } else {
                        old_index
                    };
                    assert(0 <= new_index < swapped.len());
                    assert(swapped[new_index] == entries[old_index]);
                    Self::entries_map_index(swapped, new_index);
                }
                if Self::entries_map(swapped).contains_key(key) {
                    let new_index = Self::entries_map_index_for_key(swapped, key);
                    let old_index = if new_index == left {
                        right
                    } else if new_index == right {
                        left
                    } else {
                        new_index
                    };
                    assert(0 <= old_index < entries.len());
                    assert(swapped[new_index] == entries[old_index]);
                    Self::entries_map_index(entries, old_index);
                }
            }
        );
    }

    pub proof fn sorted_entries_form_buffer(
        entries: Seq<MemtableEntry>,
        buffer: SimpleBuffer,
    )
        requires
            Self::unique_keys(entries),
            Self::strictly_sorted(entries),
            Self::entries_map(entries) == buffer.map,
            entries.len() > 0,
        ensures
            (PivotNode::Leaf {
                keys: entries.map(
                    |i: int, entry: MemtableEntry| entry.key,
                ),
                msgs: entries.map(
                    |i: int, entry: MemtableEntry| entry.message,
                ),
            }).i() == buffer,
    {
        let keys = entries.map(
            |i: int, entry: MemtableEntry| entry.key,
        );
        let msgs = entries.map(
            |i: int, entry: MemtableEntry| entry.message,
        );
        let leaf = PivotNode::Leaf { keys, msgs };
        assert(Key::is_strictly_sorted(keys)) by {
            assert forall |i: int, j: int| 0 <= i < j < keys.len()
                implies Key::lt(keys[i], keys[j]) by {
                assert(keys[i] == entries[i].key);
                assert(keys[j] == entries[j].key);


            }
        }
        assert(leaf.wf());
        broadcast use PivotNode::route_ensures;
        assert_maps_equal!(leaf.i().map, buffer.map, key => {
            if Self::entries_map(entries).contains_key(key) {
                let i = Self::entries_map_index_for_key(entries, key);
                assert(keys[i] == key);
                assert(keys.contains(key));
                assert(leaf.route(key) == i);
                assert(msgs[i] == entries[i].message);
                assert(leaf.i().map.contains_key(key));
                assert(leaf.i().map[key] == msgs[i]);
            }
            if leaf.i().map.contains_key(key) {
                assert(keys.contains(key));
                let i = choose |i: int| 0 <= i < keys.len()
                    && #[trigger] keys[i] == key;
                assert(entries[i].key == key);
                Self::entries_map_index(entries, i);
            }
        });
    }

    fn new() -> (out: Self)
        ensures
            out.wf(),
            out@ == Map::<Key, Message>::empty(),
            out.entries@ == Seq::<MemtableEntry>::empty(),
    {
        let out = Self { entries: Vec::new() };
        assert(out@ == Map::<Key, Message>::empty());
        out
    }

    fn query(&self, key: Key) -> (out: Message)
        requires
            self.wf(),
        ensures
            out == if self@.contains_key(key) {
                self@[key]
            } else {
                Message::Update { delta: nop_delta() }
            },
    {
        let mut index = 0usize;
        while index < self.entries.len()
            invariant
                self.wf(),
                index <= self.entries.len(),
                forall |i: int| #![auto]
                    0 <= i < index ==> self.entries@[i].key != key,
            decreases self.entries.len() - index,
        {
            if self.entries[index].key.0 == key.0 {
                proof {
                    assert(self.entries@[index as int].key == key);
                    Self::entries_map_index(self.entries@, index as int);
                }
                return self.entries[index].message;
            }
            index += 1;
        }
        proof {
            assert(!self@.contains_key(key)) by {
                if self@.contains_key(key) {
                    let i = Self::entries_map_index_for_key(self.entries@, key);
                    assert(i < index);
                }
            }
            assert(nop_delta() == Delta(0));
        }
        Message::Update { delta: Delta(0) }
    }

    fn insert(&mut self, key: Key, message: Message)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self@ == old(self)@.insert(key, message),
            forall |i: int| #![trigger self.entries@[i]]
                0 <= i < self.entries@.len()
                ==> self.entries@[i].key == key
                    || exists |old_i: int| #![auto]
                        0 <= old_i < old(self).entries@.len()
                        && old(self).entries@[old_i].key == self.entries@[i].key,
    {
        let ghost old_entries = self.entries@;
        let mut index = 0usize;
        while index < self.entries.len()
            invariant
                self.wf(),
                self.entries@ == old_entries,
                index <= self.entries.len(),
                forall |i: int| #![auto]
                    0 <= i < index ==> self.entries@[i].key.0 < key.0,
            decreases self.entries.len() - index,
        {
            if self.entries[index].key.0 == key.0 {
                proof {
                    assert(self.entries@[index as int].key == key);
                }
                self.entries[index] = MemtableEntry { key, message };
                proof {
                    assert(self.entries@ == old_entries.update(
                        index as int,
                        MemtableEntry { key, message },
                    ));
                    Self::entries_map_after_set(
                        old_entries,
                        index as int,
                        MemtableEntry { key, message },
                    );
                    Self::sorted_after_set_same_key(
                        old_entries,
                        index as int,
                        MemtableEntry { key, message },
                    );
                    assert forall |i: int| #![trigger self.entries@[i]]
                        0 <= i < self.entries@.len()
                        implies self.entries@[i].key == key
                            || exists |old_i: int| #![auto]
                                0 <= old_i < old_entries.len()
                                && old_entries[old_i].key == self.entries@[i].key by {
                        if i != index {
                            assert(self.entries@[i] == old_entries[i]);
                        }
                    }
                }
                return;
            }
            if key.0 < self.entries[index].key.0 {
                proof {
                    assert(!Self::entries_map(old_entries).contains_key(key)) by {
                        if Self::entries_map(old_entries).contains_key(key) {
                            let i = Self::entries_map_index_for_key(old_entries, key);
                            if i < index {
                                assert(old_entries[i].key.0 < key.0);
                            } else if i == index {
                                assert(old_entries[i].key.0 > key.0);
                            } else {
                                assert(old_entries[index as int].key.0
                                    < old_entries[i].key.0);
                            }
                        }
                    }
                    assert forall |i: int| index <= i < old_entries.len()
                        implies key.0 < old_entries[i].key.0 by {
                        if i > index {
                            assert(old_entries[index as int].key.0
                                < old_entries[i].key.0);
                        }
                    }
                }
                self.entries.insert(index, MemtableEntry { key, message });
                proof {
                    Self::entries_map_after_insert(
                        old_entries,
                        index as int,
                        MemtableEntry { key, message },
                    );
                    Self::sorted_after_insert(
                        old_entries,
                        index as int,
                        MemtableEntry { key, message },
                    );
                    assert forall |i: int| #![trigger self.entries@[i]]
                        0 <= i < self.entries@.len()
                        implies self.entries@[i].key == key
                            || exists |old_i: int| #![auto]
                                0 <= old_i < old_entries.len()
                                && old_entries[old_i].key == self.entries@[i].key by {
                        if i != index {
                            let old_i = if i < index { i } else { i - 1 };
                            assert(self.entries@[i] == old_entries[old_i]);
                        }
                    }
                }
                return;
            }
            index += 1;
        }

        proof {
            assert(!Self::entries_map(old_entries).contains_key(key)) by {
                if Self::entries_map(old_entries).contains_key(key) {
                    let i = Self::entries_map_index_for_key(old_entries, key);
                    assert(i < index);
                }
            }
        }
        self.entries.push(MemtableEntry { key, message });
        proof {
            Self::entries_map_after_push(old_entries, MemtableEntry { key, message });
            Self::sorted_after_insert(
                old_entries,
                old_entries.len() as int,
                MemtableEntry { key, message },
            );
            assert(self.entries@ == old_entries.insert(
                old_entries.len() as int,
                MemtableEntry { key, message },
            ));
            assert forall |i: int| #![trigger self.entries@[i]]
                0 <= i < self.entries@.len()
                implies self.entries@[i].key == key
                    || exists |old_i: int| #![auto]
                        0 <= old_i < old_entries.len()
                        && old_entries[old_i].key == self.entries@[i].key by {
                if i < old_entries.len() {
                    assert(self.entries@[i] == old_entries[i]);
                } else {
                    assert(i == old_entries.len());
                }
            }
        }
    }
}

impl View for MemtableBucket {
    type V = Map<Key, Message>;

    open spec fn view(&self) -> Map<Key, Message> {
        Self::entries_map(self.entries@)
    }
}

impl MemtableImpl {
    pub open spec fn bucket_index(key: Key, bucket_count: nat) -> nat
        recommends bucket_count > 0
    {
        key.0 as nat % bucket_count
    }

    pub open spec fn buckets_map(
        buckets: Seq<MemtableBucket>,
        bucket_count: nat,
    ) -> Map<Key, Message>
        recommends
            bucket_count > 0,
            buckets.len() == bucket_count,
            forall |i: int| #![trigger buckets[i]]
                0 <= i < buckets.len() ==> buckets[i].wf(),
    {
        Map::new(
            |key: Key| buckets[Self::bucket_index(key, bucket_count) as int]@
                .contains_key(key),
            |key: Key| buckets[Self::bucket_index(key, bucket_count) as int]@[key],
        )
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.bucket_count > 0
        &&& self.buckets@.len() == self.bucket_count as nat
        &&& forall |bucket: int| #![trigger self.buckets@[bucket]]
            0 <= bucket < self.buckets@.len() ==> self.buckets@[bucket].wf()
        &&& forall |bucket: int, entry: int|
            #![trigger self.buckets@[bucket].entries@[entry]]
            0 <= bucket < self.buckets@.len()
            && 0 <= entry < self.buckets@[bucket].entries@.len()
            ==> Self::bucket_index(
                self.buckets@[bucket].entries@[entry].key,
                self.bucket_count as nat,
            ) == bucket
    }

    proof fn entry_is_in_selected_bucket(&self, bucket: int, entry: int)
        requires
            self.wf(),
            0 <= bucket < self.buckets@.len(),
            0 <= entry < self.buckets@[bucket].entries@.len(),
        ensures
            Self::bucket_index(
                self.buckets@[bucket].entries@[entry].key,
                self.bucket_count as nat,
            ) == bucket,
    {
    }

    proof fn buckets_update_refines(
        old_buckets: Seq<MemtableBucket>,
        new_buckets: Seq<MemtableBucket>,
        bucket_count: nat,
        bucket: int,
        key: Key,
        message: Message,
    )
        requires
            bucket_count > 0,
            old_buckets.len() == bucket_count,
            new_buckets.len() == bucket_count,
            0 <= bucket < old_buckets.len(),
            bucket == Self::bucket_index(key, bucket_count),
            forall |i: int| #![trigger old_buckets[i]]
                0 <= i < old_buckets.len() ==> old_buckets[i].wf(),
            forall |i: int| #![trigger new_buckets[i]]
                0 <= i < new_buckets.len() ==> new_buckets[i].wf(),
            new_buckets[bucket]@ == old_buckets[bucket]@.insert(key, message),
            forall |i: int| #![trigger new_buckets[i]]
                0 <= i < new_buckets.len() && i != bucket
                ==> new_buckets[i]@ == old_buckets[i]@,
        ensures
            Self::buckets_map(new_buckets, bucket_count)
                == Self::buckets_map(old_buckets, bucket_count).insert(key, message),
    {
        assert_maps_equal!(
            Self::buckets_map(new_buckets, bucket_count),
            Self::buckets_map(old_buckets, bucket_count).insert(key, message),
            other_key => {
                let other_bucket = Self::bucket_index(other_key, bucket_count) as int;
                if other_key == key {
                    assert(other_bucket == bucket);
                } else if other_bucket == bucket {
                    assert(new_buckets[bucket]@ == old_buckets[bucket]@.insert(key, message));
                } else {
                    assert(new_buckets[other_bucket]@ == old_buckets[other_bucket]@);
                }
            }
        );
    }

    fn exec_bucket_index(key: Key, bucket_count: u32) -> (out: usize)
        requires
            bucket_count > 0,
        ensures
            out as nat == Self::bucket_index(key, bucket_count as nat),
            out < bucket_count as usize,
    {
        (key.0 % bucket_count as u64) as usize
    }

    fn empty_buckets(bucket_count: u32) -> (out: Vec<MemtableBucket>)
        requires
            bucket_count > 0,
        ensures
            out@.len() == bucket_count as nat,
            forall |i: int| #![trigger out@[i]]
                0 <= i < out@.len()
                ==> out@[i].wf() && out@[i]@ == Map::<Key, Message>::empty(),
            forall |i: int| #![trigger out@[i]]
                0 <= i < out@.len() ==> out@[i].entries@.len() == 0,
    {
        let mut out: Vec<MemtableBucket> = Vec::new();
        let mut index = 0usize;
        while index < bucket_count as usize
            invariant
                index <= bucket_count as usize,
                out@.len() == index,
                forall |i: int| #![trigger out@[i]]
                    0 <= i < out@.len()
                    ==> out@[i].wf() && out@[i]@ == Map::<Key, Message>::empty(),
                forall |i: int| #![trigger out@[i]]
                    0 <= i < out@.len() ==> out@[i].entries@.len() == 0,
            decreases bucket_count as usize - index,
        {
            out.push(MemtableBucket::new());
            index += 1;
        }
        out
    }

    pub fn new(bucket_count: u32, seq_end: u64) -> (out: Self)
        requires
            bucket_count > 0,
        ensures
            out.wf(),
            out@ == Memtable::empty_memtable(seq_end as LSN),
            out.bucket_count == bucket_count,
    {
        let buckets = Self::empty_buckets(bucket_count);
        let out = Self { buckets, bucket_count, seq_end };
        proof {
            assert(out@.buffer.map == Map::<Key, Message>::empty());
            assert(out@ == Memtable::empty_memtable(seq_end as LSN));
        }
        out
    }

    pub fn query(&self, key: Key) -> (out: Message)
        requires
            self.wf(),
        ensures
            out == self@.query(key),
    {
        let bucket = Self::exec_bucket_index(key, self.bucket_count);
        self.buckets[bucket].query(key)
    }

    pub fn put(&mut self, km: KeyedMessage) -> (result: MemtableUpdateResult)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self.bucket_count == old(self).bucket_count,
            match result {
                MemtableUpdateResult::Applied => {
                    &&& old(self).seq_end < u64::MAX
                    &&& self.seq_end == old(self).seq_end + 1
                    &&& self@ == old(self)@.apply_put(km)
                },
                MemtableUpdateResult::Noop => {
                    &&& old(self).seq_end == u64::MAX
                    &&& self.buckets@ == old(self).buckets@
                    &&& self.bucket_count == old(self).bucket_count
                    &&& self.seq_end == old(self).seq_end
                    &&& self@ == old(self)@
                },
            },
    {
        if self.seq_end == u64::MAX {
            return MemtableUpdateResult::Noop;
        }

        let bucket = Self::exec_bucket_index(km.key, self.bucket_count);
        let ghost old_buckets = self.buckets@;
        let mut selected_bucket = self.buckets.remove(bucket);
        let old_message = selected_bucket.query(km.key);
        let merged = memtable_merge_messages(old_message, km.message);
        selected_bucket.insert(km.key, merged);
        self.buckets.insert(bucket, selected_bucket);
        self.seq_end = self.seq_end + 1;

        proof {
            assert forall |i: int| #![trigger self.buckets@[i]]
                0 <= i < self.buckets@.len() && i != bucket
                implies self.buckets@[i]@ == old_buckets[i]@ by { }
            Self::buckets_update_refines(
                old_buckets,
                self.buckets@,
                self.bucket_count as nat,
                bucket as int,
                km.key,
                merged,
            );
            assert forall |b: int, e: int|
                #![trigger self.buckets@[b].entries@[e]]
                0 <= b < self.buckets@.len()
                && 0 <= e < self.buckets@[b].entries@.len()
                implies Self::bucket_index(
                    self.buckets@[b].entries@[e].key,
                    self.bucket_count as nat,
                ) == b by {
                if b == bucket {
                    if self.buckets@[b].entries@[e].key == km.key {
                        assert(Self::bucket_index(km.key, self.bucket_count as nat) == bucket);
                    } else {
                        assert(exists |old_e: int| #![auto]
                            0 <= old_e < old_buckets[b].entries@.len()
                            && old_buckets[b].entries@[old_e].key
                                == self.buckets@[b].entries@[e].key);
                        let old_e = choose |old_e: int| #![auto]
                            0 <= old_e < old_buckets[b].entries@.len()
                            && old_buckets[b].entries@[old_e].key
                                == self.buckets@[b].entries@[e].key;
                        assert(Self::bucket_index(
                            old_buckets[b].entries@[old_e].key,
                            self.bucket_count as nat,
                        ) == b);
                    }
                } else {
                    assert(self.buckets@[b].entries@ == old_buckets[b].entries@);
                }
            }
            assert(self@.buffer.map == old(self)@.buffer.map.insert(km.key, merged));
            assert(old_message == old(self)@.query(km.key));
            assert(merged == old(self)@.query(km.key).merge(km.message));
            assert(self@ == old(self)@.apply_put(km));
        }
        MemtableUpdateResult::Applied
    }

    pub open spec fn history_from_seq(start_lsn: LSN, puts: Seq<KeyedMessage>) -> MsgHistory {
        MsgHistory {
            msgs: Map::new(
                |lsn: LSN| start_lsn <= lsn < start_lsn + puts.len(),
                |lsn: LSN| puts[(lsn - start_lsn) as int],
            ),
            seq_start: start_lsn,
            seq_end: start_lsn + puts.len(),
        }
    }

    pub open spec fn flatten_prefix(
        buckets: Seq<MemtableBucket>,
        count: nat,
    ) -> Seq<MemtableEntry>
        recommends count <= buckets.len()
        decreases count
    {
        if count == 0 {
            Seq::empty()
        } else {
            Self::flatten_prefix(buckets, (count - 1) as nat)
                + buckets[(count - 1) as int].entries@
        }
    }

    proof fn flatten_prefix_origin(
        buckets: Seq<MemtableBucket>,
        count: nat,
        index: int,
    ) -> (origin: (int, int))
        requires
            count <= buckets.len(),
            0 <= index < Self::flatten_prefix(buckets, count).len(),
        ensures
            0 <= origin.0 < count,
            0 <= origin.1 < buckets[origin.0].entries@.len(),
            Self::flatten_prefix(buckets, count)[index]
                == buckets[origin.0].entries@[origin.1],
        decreases count,
    {
        if count == 0 {
            return proof_from_false();
        }
        let prefix = Self::flatten_prefix(buckets, (count - 1) as nat);
        if index < prefix.len() {
            Self::flatten_prefix_origin(buckets, (count - 1) as nat, index)
        } else {
            let entry = index - prefix.len();
            assert(Self::flatten_prefix(buckets, count)[index]
                == buckets[(count - 1) as int].entries@[entry]);
            ((count - 1) as int, entry)
        }
    }

    proof fn flatten_prefix_contains(
        buckets: Seq<MemtableBucket>,
        count: nat,
        bucket: int,
        entry: int,
    ) -> (index: int)
        requires
            count <= buckets.len(),
            0 <= bucket < count,
            0 <= entry < buckets[bucket].entries@.len(),
        ensures
            0 <= index < Self::flatten_prefix(buckets, count).len(),
            Self::flatten_prefix(buckets, count)[index] == buckets[bucket].entries@[entry],
        decreases count,
    {
        if bucket < count - 1 {
            Self::flatten_prefix_contains(buckets, (count - 1) as nat, bucket, entry)
        } else {
            assert(bucket == count - 1);
            let prefix = Self::flatten_prefix(buckets, (count - 1) as nat);
            let index = prefix.len() + entry;
            assert(Self::flatten_prefix(buckets, count)[index]
                == buckets[bucket].entries@[entry]);
            index
        }
    }

    proof fn flatten_prefix_embeds(
        buckets: Seq<MemtableBucket>,
        small: nat,
        large: nat,
    )
        requires
            small <= large <= buckets.len(),
        ensures
            Self::flatten_prefix(buckets, small).len()
                <= Self::flatten_prefix(buckets, large).len(),
            forall |i: int|
                #![trigger Self::flatten_prefix(buckets, small)[i]]
                0 <= i < Self::flatten_prefix(buckets, small).len()
                ==> Self::flatten_prefix(buckets, small)[i]
                    == Self::flatten_prefix(buckets, large)[i],
        decreases large - small,
    {
        if small < large {
            Self::flatten_prefix_embeds(buckets, small, (large - 1) as nat);
            let small_prefix = Self::flatten_prefix(buckets, small);
            let previous = Self::flatten_prefix(buckets, (large - 1) as nat);
            let current = Self::flatten_prefix(buckets, large);
            assert(current == previous + buckets[(large - 1) as int].entries@);
            assert forall |i: int|
                #![trigger small_prefix[i]]
                0 <= i < small_prefix.len()
                implies small_prefix[i] == current[i] by {
                assert(small_prefix[i] == previous[i]);
                assert(previous[i] == current[i]);
            }
        }
    }

    proof fn flatten_prefix_unique(
        buckets: Seq<MemtableBucket>,
        count: nat,
        bucket_count: nat,
    )
        requires
            bucket_count > 0,
            count <= buckets.len(),
            forall |bucket: int| #![trigger buckets[bucket]]
                0 <= bucket < count ==> buckets[bucket].wf(),
            forall |bucket: int, entry: int|
                #![trigger buckets[bucket].entries@[entry]]
                0 <= bucket < count
                && 0 <= entry < buckets[bucket].entries@.len()
                ==> Self::bucket_index(
                    buckets[bucket].entries@[entry].key,
                    bucket_count,
                ) == bucket,
        ensures
            MemtableBucket::unique_keys(Self::flatten_prefix(buckets, count)),
        decreases count,
    {
        if count == 0 {
            return;
        }
        Self::flatten_prefix_unique(buckets, (count - 1) as nat, bucket_count);
        let previous = Self::flatten_prefix(buckets, (count - 1) as nat);
        let current = buckets[(count - 1) as int].entries@;
        let flattened = previous + current;
        assert forall |i: int, j: int|
            #![trigger flattened[i].key, flattened[j].key]
            0 <= i < flattened.len()
            && 0 <= j < flattened.len()
            && flattened[i].key == flattened[j].key
            implies i == j by {
            if i < previous.len() && j < previous.len() {
                assert(previous[i].key == previous[j].key);
            } else if previous.len() <= i && previous.len() <= j {
                let current_i = i - previous.len();
                let current_j = j - previous.len();
                assert(current[current_i].key == current[current_j].key);
                assert(current_i == current_j);
            } else if i < previous.len() && previous.len() <= j {
                let origin = Self::flatten_prefix_origin(buckets, (count - 1) as nat, i);
                let current_j = j - previous.len();
                assert(Self::bucket_index(previous[i].key, bucket_count) == origin.0);
                assert(Self::bucket_index(current[current_j].key, bucket_count) == count - 1);
                assert(origin.0 < count - 1);
            } else {
                let origin = Self::flatten_prefix_origin(buckets, (count - 1) as nat, j);
                let current_i = i - previous.len();
                assert(Self::bucket_index(previous[j].key, bucket_count) == origin.0);
                assert(Self::bucket_index(current[current_i].key, bucket_count) == count - 1);
                assert(origin.0 < count - 1);
            }
        }
    }

    proof fn flatten_represents(&self)
        requires
            self.wf(),
        ensures
            MemtableBucket::unique_keys(Self::flatten_prefix(
                self.buckets@,
                self.buckets@.len(),
            )),
            MemtableBucket::entries_map(Self::flatten_prefix(
                self.buckets@,
                self.buckets@.len(),
            )) == self@.buffer.map,
    {
        let flattened = Self::flatten_prefix(self.buckets@, self.buckets@.len());
        Self::flatten_prefix_unique(
            self.buckets@,
            self.buckets@.len(),
            self.bucket_count as nat,
        );
        assert_maps_equal!(
            MemtableBucket::entries_map(flattened),
            self@.buffer.map,
            key => {
                if MemtableBucket::entries_map(flattened).contains_key(key) {
                    let flat_index = MemtableBucket::entries_map_index_for_key(flattened, key);
                    let origin = Self::flatten_prefix_origin(
                        self.buckets@,
                        self.buckets@.len(),
                        flat_index,
                    );
                    let entry = self.buckets@[origin.0].entries@[origin.1];
                    assert(flattened[flat_index] == entry);
                    assert(Self::bucket_index(key, self.bucket_count as nat) == origin.0);
                    MemtableBucket::entries_map_index(
                        self.buckets@[origin.0].entries@,
                        origin.1,
                    );
                    assert(self@.buffer.map.contains_key(key));
                    assert(self@.buffer.map[key] == entry.message);
                }
                if self@.buffer.map.contains_key(key) {
                    let bucket = Self::bucket_index(key, self.bucket_count as nat) as int;
                    let entry = MemtableBucket::entries_map_index_for_key(
                        self.buckets@[bucket].entries@,
                        key,
                    );
                    let flat_index = Self::flatten_prefix_contains(
                        self.buckets@,
                        self.buckets@.len(),
                        bucket,
                        entry,
                    );
                    MemtableBucket::entries_map_index(flattened, flat_index);
                    assert(MemtableBucket::entries_map(flattened).contains_key(key));
                    assert(MemtableBucket::entries_map(flattened)[key]
                        == self.buckets@[bucket].entries@[entry].message);
                }
            }
        );
    }

    pub proof fn history_from_seq_wf(start_lsn: LSN, puts: Seq<KeyedMessage>)
        ensures
            Self::history_from_seq(start_lsn, puts).wf(),
            Self::history_from_seq(start_lsn, puts).seq_start == start_lsn,
            Self::history_from_seq(start_lsn, puts).seq_end == start_lsn + puts.len(),
    {
    }

    proof fn history_from_seq_push(
        start_lsn: LSN,
        puts: Seq<KeyedMessage>,
        km: KeyedMessage,
    )
        ensures
            Self::history_from_seq(start_lsn, puts.push(km)).discard_recent(
                start_lsn + puts.len(),
            ) == Self::history_from_seq(start_lsn, puts),
            Self::history_from_seq(start_lsn, puts.push(km)).msgs[
                start_lsn + puts.len()
            ] == km,
    {
        let whole = Self::history_from_seq(start_lsn, puts.push(km));
        let prefix = Self::history_from_seq(start_lsn, puts);
        let prefix_end = start_lsn + puts.len();
        Self::history_from_seq_wf(start_lsn, puts);
        Self::history_from_seq_wf(start_lsn, puts.push(km));
        assert(whole.can_discard_to(prefix_end));
        assert_maps_equal!(whole.discard_recent(prefix_end).msgs, prefix.msgs, lsn => { });
        assert(whole.discard_recent(prefix_end) == prefix);
        assert(whole.msgs[prefix_end] == puts.push(km)[puts.len() as int]);
    }

    proof fn apply_puts_push(
        memtable: Memtable,
        start_lsn: LSN,
        puts: Seq<KeyedMessage>,
        km: KeyedMessage,
    )
        requires
            start_lsn == memtable.seq_end,
        ensures
            memtable.apply_puts(Self::history_from_seq(start_lsn, puts.push(km)))
                == memtable.apply_puts(Self::history_from_seq(start_lsn, puts)).apply_put(km),
    {
        let whole = Self::history_from_seq(start_lsn, puts.push(km));
        let prefix = Self::history_from_seq(start_lsn, puts);
        let prefix_end = start_lsn + puts.len();
        Self::history_from_seq_wf(start_lsn, puts);
        Self::history_from_seq_wf(start_lsn, puts.push(km));
        Self::history_from_seq_push(start_lsn, puts, km);
        assert(prefix.can_follow(memtable.seq_end));
        memtable.apply_puts_end(prefix);
        assert(whole.seq_end - 1 == prefix_end);
        assert(whole.discard_recent(prefix_end) == prefix);
        assert(whole.msgs[prefix_end] == km);
        assert(memtable.apply_puts(whole)
            == memtable.apply_puts(prefix).apply_put(km));
    }

    pub fn apply_puts(
        &mut self,
        start_lsn: u64,
        puts: &Vec<KeyedMessage>,
    ) -> (result: MemtableUpdateResult)
        requires
            old(self).wf(),
            start_lsn == old(self).seq_end,
        ensures
            self.wf(),
            match result {
                MemtableUpdateResult::Applied => {
                    &&& self@ == old(self)@.apply_puts(Self::history_from_seq(
                        start_lsn as LSN,
                        puts@,
                    ))
                    &&& self.bucket_count == old(self).bucket_count
                    &&& self.seq_end as nat == start_lsn as nat + puts@.len()
                },
                MemtableUpdateResult::Noop => {
                    &&& (u64::MAX as nat - start_lsn as nat) < puts@.len()
                    &&& self.buckets@ == old(self).buckets@
                    &&& self.bucket_count == old(self).bucket_count
                    &&& self.seq_end == old(self).seq_end
                    &&& self@ == old(self)@
                },
            },
    {
        let ghost initial = self@;
        let ghost initial_buckets = self.buckets@;
        let initial_bucket_count = self.bucket_count;
        let initial_seq_end = self.seq_end;

        let mut checked = 0usize;
        let mut remaining = u64::MAX - self.seq_end;
        while checked < puts.len()
            invariant
                self.wf(),
                self.buckets@ == initial_buckets,
                self.bucket_count == initial_bucket_count,
                self.seq_end == initial_seq_end,
                checked <= puts.len(),
                remaining as nat + checked as nat
                    == u64::MAX as nat - initial_seq_end as nat,
            decreases puts.len() - checked,
        {
            if remaining == 0 {
                return MemtableUpdateResult::Noop;
            }
            remaining = remaining - 1;
            checked += 1;
        }

        proof {
            assert(start_lsn as nat + puts@.len() <= u64::MAX as nat);
            Self::history_from_seq_wf(start_lsn as LSN, puts@);
        }

        let mut index = 0usize;
        while index < puts.len()
            invariant
                self.wf(),
                self.bucket_count == initial_bucket_count,
                self.seq_end as nat == start_lsn as nat + index as nat,
                index <= puts.len(),
                start_lsn as nat + puts@.len() <= u64::MAX as nat,
                self@ == initial.apply_puts(Self::history_from_seq(
                    start_lsn as LSN,
                    puts@.subrange(0, index as int),
                )),
            decreases puts.len() - index,
        {
            proof {
                assert(self.seq_end < u64::MAX);
                Self::history_from_seq_wf(
                    start_lsn as LSN,
                    puts@.subrange(0, index as int),
                );
                Self::apply_puts_push(
                    initial,
                    start_lsn as LSN,
                    puts@.subrange(0, index as int),
                    puts@[index as int],
                );
            }
            let update = self.put(puts[index]);
            match update {
                MemtableUpdateResult::Applied => { },
                MemtableUpdateResult::Noop => {
                    proof {
                        assert(false);
                    }
                    return MemtableUpdateResult::Noop;
                },
            }
            proof {
                assert(puts@.subrange(0, index as int).push(puts@[index as int])
                    == puts@.subrange(0, index as int + 1));
            }
            index += 1;
        }
        proof {
            assert(puts@.subrange(0, index as int) == puts@);
            let history = Self::history_from_seq(start_lsn as LSN, puts@);
            initial.apply_puts_end(history);
        }
        MemtableUpdateResult::Applied
    }

    pub fn is_empty(&self) -> (out: bool)
        requires
            self.wf(),
        ensures
            out == self@.is_empty(),
    {
        let mut bucket = 0usize;
        while bucket < self.buckets.len()
            invariant
                self.wf(),
                bucket <= self.buckets.len(),
                forall |i: int| #![trigger self.buckets@[i]]
                    0 <= i < bucket ==> self.buckets@[i].entries@.len() == 0,
            decreases self.buckets.len() - bucket,
        {
            if self.buckets[bucket].entries.len() != 0 {
                proof {
                    let entry = self.buckets@[bucket as int].entries@[0];
                    MemtableBucket::entries_map_index(
                        self.buckets@[bucket as int].entries@,
                        0,
                    );
                    self.entry_is_in_selected_bucket(bucket as int, 0);
                    assert(self@.buffer.map.contains_key(entry.key));
                    assert(self@.buffer != SimpleBuffer::empty());
                }
                return false;
            }
            bucket += 1;
        }
        proof {
            assert(self@.buffer.map == Map::<Key, Message>::empty()) by {
                assert forall |key: Key| !self@.buffer.map.contains_key(key) by {
                    let selected = Self::bucket_index(key, self.bucket_count as nat) as int;
                    assert(self.buckets@[selected].entries@.len() == 0);
                }
            }
            assert(self@.is_empty());
        }
        true
    }

    pub fn drain(&mut self)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self@ == old(self)@.drain(),
            self.bucket_count == old(self).bucket_count,
            self.seq_end == old(self).seq_end,
            self.buckets@.len() == old(self).buckets@.len(),
    {
        let buckets = Self::empty_buckets(self.bucket_count);
        self.buckets = buckets;
        proof {
            assert(self@.buffer.map == Map::<Key, Message>::empty());
            assert(self@ == old(self)@.drain());
        }
    }

    pub fn flatten(&self) -> (out: Vec<MemtableEntry>)
        requires
            self.wf(),
        ensures
            MemtableBucket::unique_keys(out@),
            MemtableBucket::entries_map(out@) == self@.buffer.map,
            out@ == Self::flatten_prefix(self.buckets@, self.buckets@.len()),
    {
        let mut out: Vec<MemtableEntry> = Vec::new();
        let mut bucket = 0usize;
        while bucket < self.buckets.len()
            invariant
                self.wf(),
                bucket <= self.buckets.len(),
                out@ == Self::flatten_prefix(self.buckets@, bucket as nat),
            decreases self.buckets.len() - bucket,
        {
            let mut entry = 0usize;
            let bucket_len = self.buckets[bucket].entries.len();
            while entry < bucket_len
                invariant
                    self.wf(),
                    bucket < self.buckets.len(),
                    bucket_len == self.buckets@[bucket as int].entries@.len(),
                    entry <= bucket_len,
                    out@ == Self::flatten_prefix(self.buckets@, bucket as nat)
                        + self.buckets@[bucket as int].entries@.subrange(0, entry as int),
                decreases bucket_len - entry,
            {
                out.push(self.buckets[bucket].entries[entry]);
                entry += 1;
            }
            proof {
                assert(self.buckets@[bucket as int].entries@.subrange(0, entry as int)
                    == self.buckets@[bucket as int].entries@);
                assert(Self::flatten_prefix(self.buckets@, bucket as nat + 1)
                    == Self::flatten_prefix(self.buckets@, bucket as nat)
                        + self.buckets@[bucket as int].entries@);
            }
            bucket += 1;
        }
        proof {
            assert(bucket == self.buckets.len());
            self.flatten_represents();
        }
        out
    }

    pub fn flatten_sorted(&self) -> (out: Vec<MemtableEntry>)
        requires
            self.wf(),
        ensures
            MemtableBucket::unique_keys(out@),
            MemtableBucket::strictly_sorted(out@),
            Key::is_strictly_sorted(
                out@.map(|i: int, entry: MemtableEntry| entry.key),
            ),
            MemtableBucket::entries_map(out@) == self@.buffer.map,
    {
        let mut out = self.flatten();
        let mut sorted = 0usize;
        while sorted < out.len()
            invariant
                self.wf(),
                sorted <= out.len(),
                MemtableBucket::unique_keys(out@),
                MemtableBucket::entries_map(out@) == self@.buffer.map,
                forall |i: int, j: int|
                    0 <= i < j < sorted
                    ==> out@[i].key.0 < out@[j].key.0,
                forall |i: int, j: int|
                    0 <= i < sorted <= j < out@.len()
                    ==> out@[i].key.0 < out@[j].key.0,
            decreases out.len() - sorted,
        {
            let mut min_idx = sorted;
            let mut scan = sorted + 1;
            while scan < out.len()
                invariant
                    self.wf(),
                    sorted < out.len(),
                    sorted <= min_idx < scan <= out.len(),
                    MemtableBucket::unique_keys(out@),
                    MemtableBucket::entries_map(out@) == self@.buffer.map,
                    forall |i: int, j: int|
                        0 <= i < j < sorted
                        ==> out@[i].key.0 < out@[j].key.0,
                    forall |i: int, j: int|
                        0 <= i < sorted <= j < out@.len()
                        ==> out@[i].key.0 < out@[j].key.0,
                    forall |i: int|
                        sorted <= i < scan
                        ==> out@[min_idx as int].key.0 <= out@[i].key.0,
                decreases out.len() - scan,
            {
                if out[scan].key.0 < out[min_idx].key.0 {
                    min_idx = scan;
                }
                scan += 1;
            }
            proof {
                assert forall |i: int|
                    sorted <= i < out@.len()
                    implies out@[min_idx as int].key.0 <= out@[i].key.0 by {
                    assert(scan == out.len());
                }
            }
            let ghost before = out@;
            let left_entry = out[sorted];
            let right_entry = out[min_idx];
            out.set(sorted, right_entry);
            out.set(min_idx, left_entry);
            proof {
                assert(out@ == before.update(
                    sorted as int,
                    before[min_idx as int],
                ).update(
                    min_idx as int,
                    before[sorted as int],
                ));
                MemtableBucket::unique_keys_after_swap(
                    before,
                    sorted as int,
                    min_idx as int,
                );
                MemtableBucket::entries_map_after_swap(
                    before,
                    sorted as int,
                    min_idx as int,
                );
                assert forall |j: int|
                    sorted < j < out@.len()
                    implies out@[sorted as int].key.0 < out@[j].key.0 by {
                    let source_j = if j == min_idx as int {
                        sorted as int
                    } else {
                        j
                    };
                    assert(sorted as int <= source_j < before.len());
                    assert(out@[j] == before[source_j]);
                    assert(out@[sorted as int] == before[min_idx as int]);
                    assert(before[min_idx as int].key.0
                        <= before[source_j].key.0);
                    if before[min_idx as int].key.0
                        == before[source_j].key.0
                    {
                        assert(before[min_idx as int].key
                            == before[source_j].key);
                        assert(min_idx as int == source_j);
                        assert(false);
                    }
                }
                assert forall |i: int, j: int|
                    0 <= i < sorted < j < out@.len()
                    implies out@[i].key.0 < out@[j].key.0 by {
                    let source_j = if j == min_idx as int {
                        sorted as int
                    } else {
                        j
                    };
                    assert(out@[i] == before[i]);
                    assert(out@[j] == before[source_j]);
                }
            }
            sorted += 1;
        }
        proof {
            assert(sorted == out.len());
            assert(MemtableBucket::strictly_sorted(out@));
            let keys = out@.map(
                |i: int, entry: MemtableEntry| entry.key,
            );
            assert forall |i: int, j: int|
                0 <= i < j < keys.len()
                implies Key::lt(keys[i], keys[j]) by {
                assert(keys[i] == out@[i].key);
                assert(keys[j] == out@[j].key);


            }
        }
        out
    }

    pub fn scan<'a>(&'a self) -> (out: MemtableIter<'a>)
        requires
            self.wf(),
        ensures
            out.wf(),
            out@ == Self::flatten_prefix(self.buckets@, self.buckets@.len()),
            MemtableBucket::unique_keys(out@),
            MemtableBucket::entries_map(out@) == self@.buffer.map,
    {
        let out = MemtableIter {
            memtable: self,
            bucket: 0,
            entry: 0,
        };
        proof {
            self.flatten_represents();
            assert(out@ == Self::flatten_prefix(
                self.buckets@,
                self.buckets@.len(),
            ));
            assert_maps_equal!(
                MemtableBucket::entries_map(out@),
                self@.buffer.map,
                key => {}
            );
        }
        out
    }

    fn zero_positions(bucket_count: usize) -> (out: Vec<usize>)
        ensures
            out@.len() == bucket_count,
            forall |i: int| 0 <= i < out@.len() ==> out@[i] == 0,
    {
        let mut out = Vec::new();
        let mut bucket = 0usize;
        while bucket < bucket_count
            invariant
                bucket <= bucket_count,
                out@.len() == bucket,
                forall |i: int| 0 <= i < out@.len() ==> out@[i] == 0,
            decreases bucket_count - bucket,
        {
            out.push(0usize);
            bucket += 1;
        }
        out
    }

    pub fn sorted_scan(&self) -> (out: MemtableSortedCursor)
        requires
            self.wf(),
        ensures
            out.wf(self),
            out@ == self@.buffer.map,
    {
        let positions = Self::zero_positions(self.buckets.len());
        let out = MemtableSortedCursor {
            positions,
            remaining: Ghost(self@.buffer.map),
        };
        proof {
            let remaining = MemtableSortedCursor::remaining_map(
                self,
                positions@,
            );
            assert_maps_equal!(remaining, self@.buffer.map, key => {
                let bucket = Self::bucket_index(
                    key,
                    self.bucket_count as nat,
                ) as int;
                if self@.buffer.map.contains_key(key) {
                    let index = MemtableBucket::entries_map_index_for_key(
                        self.buckets@[bucket].entries@,
                        key,
                    );
                    assert(remaining.contains_key(key));
                    assert(remaining[key]
                        == self.buckets@[bucket].entries@[index].message);
                }
                if remaining.contains_key(key) {
                    let index = MemtableSortedCursor::remaining_index_for_key(
                        self,
                        positions@,
                        key,
                    );
                    MemtableBucket::entries_map_index(
                        self.buckets@[bucket].entries@,
                        index,
                    );
                }
            });
            assert(out.remaining@ == remaining);
            assert(out.wf(self));
        }
        out
    }
}

impl MemtableSortedCursor {
    pub open spec fn positions_wf(
        memtable: &MemtableImpl,
        positions: Seq<usize>,
    ) -> bool {
        &&& memtable.wf()
        &&& positions.len() == memtable.buckets@.len()
        &&& forall |bucket: int| 0 <= bucket < positions.len()
            ==> positions[bucket] <= memtable.buckets@[bucket].entries@.len()
    }

    pub open spec fn remaining_map(
        memtable: &MemtableImpl,
        positions: Seq<usize>,
    ) -> Map<Key, Message>
        recommends Self::positions_wf(memtable, positions)
    {
        Map::new(
            |key: Key| {
                let bucket = MemtableImpl::bucket_index(
                    key,
                    memtable.bucket_count as nat,
                ) as int;
                exists |entry: int|
                    positions[bucket] <= entry
                    && entry < memtable.buckets@[bucket].entries@.len()
                    && memtable.buckets@[bucket].entries@[entry].key == key
            },
            |key: Key| {
                let bucket = MemtableImpl::bucket_index(
                    key,
                    memtable.bucket_count as nat,
                ) as int;
                let entry = choose |entry: int|
                    positions[bucket] <= entry
                    && entry < memtable.buckets@[bucket].entries@.len()
                    && memtable.buckets@[bucket].entries@[entry].key == key;
                memtable.buckets@[bucket].entries@[entry].message
            },
        )
    }

    pub open spec fn bucket_active(
        memtable: &MemtableImpl,
        positions: Seq<usize>,
        bucket: int,
    ) -> bool
        recommends Self::positions_wf(memtable, positions)
    {
        0 <= bucket < positions.len()
            && positions[bucket]
                < memtable.buckets@[bucket].entries@.len()
    }

    pub open spec fn remaining_count_prefix(
        memtable: &MemtableImpl,
        positions: Seq<usize>,
        count: nat,
    ) -> nat
        recommends
            Self::positions_wf(memtable, positions),
            count <= positions.len(),
        decreases count,
    {
        if count == 0 {
            0
        } else {
            let bucket = (count - 1) as int;
            Self::remaining_count_prefix(
                memtable,
                positions,
                (count - 1) as nat,
            ) + (memtable.buckets@[bucket].entries@.len()
                - positions[bucket] as nat) as nat
        }
    }

    pub open spec fn remaining_count(
        memtable: &MemtableImpl,
        positions: Seq<usize>,
    ) -> nat
        recommends Self::positions_wf(memtable, positions)
    {
        Self::remaining_count_prefix(memtable, positions, positions.len())
    }

    pub open spec fn min_bucket_prefix(
        memtable: &MemtableImpl,
        positions: Seq<usize>,
        count: nat,
    ) -> Option<int>
        recommends
            Self::positions_wf(memtable, positions),
            count <= positions.len(),
        decreases count,
    {
        if count == 0 {
            None
        } else {
            let bucket = (count - 1) as int;
            let previous = Self::min_bucket_prefix(
                memtable,
                positions,
                (count - 1) as nat,
            );
            if !Self::bucket_active(memtable, positions, bucket) {
                previous
            } else if previous is None {
                Some(bucket)
            } else {
                let selected = previous.unwrap();
                let candidate_entry = memtable.buckets@[bucket].entries@[
                    positions[bucket] as int
                ];
                let selected_entry = memtable.buckets@[selected].entries@[
                    positions[selected] as int
                ];
                if candidate_entry.key.0 < selected_entry.key.0 {
                    Some(bucket)
                } else {
                    previous
                }
            }
        }
    }

    pub open spec fn min_bucket(
        memtable: &MemtableImpl,
        positions: Seq<usize>,
    ) -> Option<int>
        recommends Self::positions_wf(memtable, positions)
    {
        Self::min_bucket_prefix(memtable, positions, positions.len())
    }

    pub closed spec fn wf(&self, memtable: &MemtableImpl) -> bool {
        &&& Self::positions_wf(memtable, self.positions@)
        &&& self.remaining@ == Self::remaining_map(memtable, self.positions@)
    }

    pub closed spec fn count(&self, memtable: &MemtableImpl) -> nat
        recommends self.wf(memtable)
    {
        Self::remaining_count(memtable, self.positions@)
    }

    pub proof fn remaining_index_for_key(
        memtable: &MemtableImpl,
        positions: Seq<usize>,
        key: Key,
    ) -> (entry: int)
        requires
            Self::positions_wf(memtable, positions),
            Self::remaining_map(memtable, positions).contains_key(key),
        ensures ({
            let bucket = MemtableImpl::bucket_index(
                key,
                memtable.bucket_count as nat,
            ) as int;
            &&& positions[bucket] <= entry
            &&& entry < memtable.buckets@[bucket].entries@.len()
            &&& memtable.buckets@[bucket].entries@[entry].key == key
            &&& Self::remaining_map(memtable, positions)[key]
                == memtable.buckets@[bucket].entries@[entry].message
        }),
    {
        let bucket = MemtableImpl::bucket_index(
            key,
            memtable.bucket_count as nat,
        ) as int;
        let entry = choose |entry: int|
            positions[bucket] <= entry
            && entry < memtable.buckets@[bucket].entries@.len()
            && memtable.buckets@[bucket].entries@[entry].key == key;
        assert(Self::remaining_map(memtable, positions)[key]
            == memtable.buckets@[bucket].entries@[entry].message);
        entry
    }

    proof fn min_bucket_prefix_properties(
        memtable: &MemtableImpl,
        positions: Seq<usize>,
        count: nat,
    )
        requires
            Self::positions_wf(memtable, positions),
            count <= positions.len(),
        ensures
            Self::min_bucket_prefix(memtable, positions, count) is Some
                <==> exists |bucket: int| 0 <= bucket < count
                    && Self::bucket_active(memtable, positions, bucket),
            Self::min_bucket_prefix(memtable, positions, count) is Some ==> {
                let selected = Self::min_bucket_prefix(
                    memtable,
                    positions,
                    count,
                ).unwrap();
                &&& 0 <= selected < count
                &&& Self::bucket_active(memtable, positions, selected)
                &&& forall |bucket: int| 0 <= bucket < count
                    && Self::bucket_active(memtable, positions, bucket)
                    ==> memtable.buckets@[selected].entries@[
                            positions[selected] as int
                        ].key.0
                        <= memtable.buckets@[bucket].entries@[
                            positions[bucket] as int
                        ].key.0
            },
        decreases count,
    {
        if count == 0 {
            return;
        }
        Self::min_bucket_prefix_properties(
            memtable,
            positions,
            (count - 1) as nat,
        );
        let bucket = (count - 1) as int;
        let previous = Self::min_bucket_prefix(
            memtable,
            positions,
            (count - 1) as nat,
        );
        let current = Self::min_bucket_prefix(memtable, positions, count);
        if Self::bucket_active(memtable, positions, bucket) {
            if previous is Some {
                let selected = previous.unwrap();
                if current == previous {
                    assert forall |other: int| 0 <= other < count
                        && Self::bucket_active(memtable, positions, other)
                        implies memtable.buckets@[selected].entries@[
                                positions[selected] as int
                            ].key.0
                            <= memtable.buckets@[other].entries@[
                                positions[other] as int
                            ].key.0 by {
                        if other == bucket {
                        } else {
                            assert(other < count - 1);
                        }
                    }
                } else {
                    assert(current == Some(bucket));
                    assert forall |other: int| 0 <= other < count
                        && Self::bucket_active(memtable, positions, other)
                        implies memtable.buckets@[bucket].entries@[
                                positions[bucket] as int
                            ].key.0
                            <= memtable.buckets@[other].entries@[
                                positions[other] as int
                            ].key.0 by {
                        if other != bucket {
                            assert(other < count - 1);
                        }
                    }
                }
            }
        }
    }

    proof fn remaining_count_prefix_active(
        memtable: &MemtableImpl,
        positions: Seq<usize>,
        count: nat,
    )
        requires
            Self::positions_wf(memtable, positions),
            count <= positions.len(),
        ensures
            Self::remaining_count_prefix(memtable, positions, count) > 0
                <==> exists |bucket: int| 0 <= bucket < count
                    && Self::bucket_active(memtable, positions, bucket),
        decreases count,
    {
        if count > 0 {
            Self::remaining_count_prefix_active(
                memtable,
                positions,
                (count - 1) as nat,
            );
            let previous = Self::remaining_count_prefix(
                memtable,
                positions,
                (count - 1) as nat,
            );
            let bucket = (count - 1) as int;
            if Self::remaining_count_prefix(
                memtable,
                positions,
                count,
            ) > 0 {
                if previous > 0 {
                    let witness = choose |candidate: int|
                        0 <= candidate < count - 1
                        && Self::bucket_active(
                            memtable,
                            positions,
                            candidate,
                        );
                    assert(exists |candidate: int| 0 <= candidate < count
                        && Self::bucket_active(
                            memtable,
                            positions,
                            candidate,
                        )) by {
                        assert(witness < count);
                    }
                } else {
                    assert(positions[bucket]
                        < memtable.buckets@[bucket].entries@.len());
                    assert(Self::bucket_active(
                        memtable,
                        positions,
                        bucket,
                    ));
                    assert(exists |candidate: int| 0 <= candidate < count
                        && Self::bucket_active(
                            memtable,
                            positions,
                            candidate,
                        )) by {
                        assert(0 <= bucket < count);
                    }
                }
            }
        }
    }

    proof fn advance_count_decreases(
        memtable: &MemtableImpl,
        positions: Seq<usize>,
        selected: int,
    )
        requires
            Self::positions_wf(memtable, positions),
            Self::bucket_active(memtable, positions, selected),
            positions[selected] < usize::MAX,
        ensures ({
            let advanced = positions.update(
                selected,
                (positions[selected] as nat + 1) as usize,
            );
            Self::remaining_count(memtable, advanced) + 1
                == Self::remaining_count(memtable, positions)
        }),
    {
        assert(positions[selected] as nat + 1 <= usize::MAX as nat);
        assert(((positions[selected] as nat + 1) as usize) as nat
            == positions[selected] as nat + 1);
        let advanced = positions.update(
            selected,
            (positions[selected] as nat + 1) as usize,
        );
        assert(advanced.len() == positions.len());
        assert(Self::positions_wf(memtable, advanced));
        Self::advance_count_prefix(
            memtable,
            positions,
            advanced,
            selected,
            positions.len(),
        );
    }

    proof fn advance_count_prefix(
        memtable: &MemtableImpl,
        positions: Seq<usize>,
        advanced: Seq<usize>,
        selected: int,
        count: nat,
    )
        requires
            Self::positions_wf(memtable, positions),
            Self::positions_wf(memtable, advanced),
            advanced == positions.update(
                selected,
                (positions[selected] as nat + 1) as usize,
            ),
            0 <= selected < positions.len(),
            positions[selected] < usize::MAX,
            count <= positions.len(),
        ensures
            Self::remaining_count_prefix(memtable, advanced, count)
                + (if selected < count { 1nat } else { 0nat })
                == Self::remaining_count_prefix(memtable, positions, count),
        decreases count,
    {
        if count > 0 {
            Self::advance_count_prefix(
                memtable,
                positions,
                advanced,
                selected,
                (count - 1) as nat,
            );
        }
    }

    proof fn remaining_count_prefix_monotonic(
        memtable: &MemtableImpl,
        positions: Seq<usize>,
        small: nat,
        large: nat,
    )
        requires
            Self::positions_wf(memtable, positions),
            small <= large <= positions.len(),
        ensures
            Self::remaining_count_prefix(memtable, positions, small)
                <= Self::remaining_count_prefix(memtable, positions, large),
        decreases large - small,
    {
        if small < large {
            Self::remaining_count_prefix_monotonic(
                memtable,
                positions,
                small,
                (large - 1) as nat,
            );
        }
    }

    pub fn remaining_len_checked(
        &self,
        memtable: &MemtableImpl,
    ) -> (out: Option<usize>)
        requires
            self.wf(memtable),
        ensures
            match out {
                Some(count) => count as nat
                    == self.count(memtable),
                None => self.count(memtable) > usize::MAX as nat,
            },
    {
        let mut total = 0usize;
        let mut bucket = 0usize;
        while bucket < memtable.buckets.len()
            invariant
                self.wf(memtable),
                bucket <= memtable.buckets.len(),
                total as nat == Self::remaining_count_prefix(
                    memtable,
                    self.positions@,
                    bucket as nat,
                ),
            decreases memtable.buckets.len() - bucket,
        {
            let len = memtable.buckets[bucket].entries.len();
            let position = self.positions[bucket];
            let amount = len - position;
            if usize::MAX - total < amount {
                proof {
                    assert(Self::remaining_count_prefix(
                        memtable,
                        self.positions@,
                        bucket as nat + 1,
                    ) > usize::MAX as nat);
                    Self::remaining_count_prefix_monotonic(
                        memtable,
                        self.positions@,
                        bucket as nat + 1,
                        self.positions@.len(),
                    );
                }
                return None;
            }
            total = total + amount;
            bucket += 1;
        }
        Some(total)
    }

    pub proof fn count_zero_implies_empty(&self, memtable: &MemtableImpl)
        requires
            self.wf(memtable),
            self.count(memtable) == 0,
        ensures
            self@ == Map::<Key, Message>::empty(),
    {
        Self::remaining_count_prefix_active(
            memtable,
            self.positions@,
            self.positions@.len(),
        );
        assert_maps_equal!(self@, Map::<Key, Message>::empty(), key => {
            if self@.contains_key(key) {
                let bucket = MemtableImpl::bucket_index(
                    key,
                    memtable.bucket_count as nat,
                ) as int;
                let entry = Self::remaining_index_for_key(
                    memtable,
                    self.positions@,
                    key,
                );
                assert(self.positions@[bucket] <= entry);
                assert(entry < memtable.buckets@[bucket].entries@.len());
                assert(Self::bucket_active(
                    memtable,
                    self.positions@,
                    bucket,
                ));
                assert(exists |active: int|
                    0 <= active < self.positions@.len()
                    && Self::bucket_active(
                        memtable,
                        self.positions@,
                        active,
                    ));
                assert(false);
            }
        });
    }

    pub proof fn count_positive_implies_nonempty(
        &self,
        memtable: &MemtableImpl,
    )
        requires
            self.wf(memtable),
            self.count(memtable) > 0,
        ensures
            self@ != Map::<Key, Message>::empty(),
    {
        Self::remaining_count_prefix_active(
            memtable,
            self.positions@,
            self.positions@.len(),
        );
        let bucket = choose |active: int|
            0 <= active < self.positions@.len()
            && Self::bucket_active(
                memtable,
                self.positions@,
                active,
            );
        let key = memtable.buckets@[bucket].entries@[
            self.positions@[bucket] as int
        ].key;
        assert(self@.contains_key(key));
    }

    proof fn selected_is_least_remaining(
        memtable: &MemtableImpl,
        positions: Seq<usize>,
        selected: int,
    )
        requires
            Self::positions_wf(memtable, positions),
            Self::min_bucket(memtable, positions) == Some(selected),
        ensures ({
            let selected_entry = memtable.buckets@[selected].entries@[
                positions[selected] as int
            ];
            &&& Self::remaining_map(memtable, positions)
                .contains_key(selected_entry.key)
            &&& Self::remaining_map(memtable, positions)[selected_entry.key]
                == selected_entry.message
            &&& forall |key: Key|
                Self::remaining_map(memtable, positions).contains_key(key)
                && key != selected_entry.key
                ==> selected_entry.key.0 < key.0
        }),
    {
        Self::min_bucket_prefix_properties(
            memtable,
            positions,
            positions.len(),
        );
        assert(Self::bucket_active(memtable, positions, selected));
        vstd::std_specs::vec::axiom_spec_len(
            &memtable.buckets[selected].entries,
        );
        assert(memtable.buckets@[selected].entries@.len() <= usize::MAX);
        assert(positions[selected] < usize::MAX);
        assert(positions[selected] as nat + 1 <= usize::MAX as nat);
        assert(((positions[selected] as nat + 1) as usize) as nat
            == positions[selected] as nat + 1);
        let selected_entry = memtable.buckets@[selected].entries@[
            positions[selected] as int
        ];
        assert(Self::remaining_map(memtable, positions)
            .contains_key(selected_entry.key));
        assert(Self::remaining_map(memtable, positions)[selected_entry.key]
            == selected_entry.message);
        assert forall |key: Key|
            Self::remaining_map(memtable, positions).contains_key(key)
            && key != selected_entry.key
            implies selected_entry.key.0 < key.0 by {
            let bucket = MemtableImpl::bucket_index(
                key,
                memtable.bucket_count as nat,
            ) as int;
            let entry = Self::remaining_index_for_key(
                memtable,
                positions,
                key,
            );
            assert(Self::bucket_active(memtable, positions, bucket));
            assert(selected_entry.key.0
                <= memtable.buckets@[bucket].entries@[
                    positions[bucket] as int
                ].key.0);
            if (positions[bucket] as int) < entry {
                assert(memtable.buckets@[bucket].entries@[
                    positions[bucket] as int
                ].key.0 < memtable.buckets@[bucket].entries@[entry].key.0);
            } else {
                assert(positions[bucket] as int == entry);
                if selected_entry.key.0 == key.0 {
                    assert(selected_entry.key == key);
                }
            }
        };
    }

    proof fn advance_removes_selected(
        memtable: &MemtableImpl,
        positions: Seq<usize>,
        selected: int,
    )
        requires
            Self::positions_wf(memtable, positions),
            Self::min_bucket(memtable, positions) == Some(selected),
        ensures ({
            let selected_entry = memtable.buckets@[selected].entries@[
                positions[selected] as int
            ];
            let advanced = positions.update(
                selected,
                (positions[selected] as nat + 1) as usize,
            );
            &&& Self::positions_wf(memtable, advanced)
            &&& Self::remaining_map(memtable, advanced)
                == Self::remaining_map(memtable, positions)
                    .remove(selected_entry.key)
        }),
    {
        Self::min_bucket_prefix_properties(
            memtable,
            positions,
            positions.len(),
        );
        assert(Self::bucket_active(memtable, positions, selected));
        vstd::std_specs::vec::axiom_spec_len(
            &memtable.buckets[selected].entries,
        );
        assert(memtable.buckets@[selected].entries@.len() <= usize::MAX);
        assert(positions[selected] < usize::MAX);
        assert(positions[selected] as nat + 1 <= usize::MAX as nat);
        assert(((positions[selected] as nat + 1) as usize) as nat
            == positions[selected] as nat + 1);
        let selected_entry = memtable.buckets@[selected].entries@[
            positions[selected] as int
        ];
        let advanced = positions.update(
            selected,
            (positions[selected] as nat + 1) as usize,
        );
        assert(advanced[selected]
            == (positions[selected] as nat + 1) as usize);
        assert(Self::positions_wf(memtable, advanced));
        assert_maps_equal!(
            Self::remaining_map(memtable, advanced),
            Self::remaining_map(memtable, positions).remove(selected_entry.key),
            key => {
                let bucket = MemtableImpl::bucket_index(
                    key,
                    memtable.bucket_count as nat,
                ) as int;
                if Self::remaining_map(memtable, positions).contains_key(key) {
                    let entry = Self::remaining_index_for_key(
                        memtable,
                        positions,
                        key,
                    );
                    if key == selected_entry.key {
                        assert(bucket == selected);
                        assert(memtable.buckets@[bucket].entries@[entry].key
                            == memtable.buckets@[selected].entries@[
                                positions[selected] as int
                            ].key);
                        assert(entry == positions[selected] as int) by {
                            assert(memtable.buckets@[selected].wf());
                        }
                        assert(entry == positions[selected] as int);
                        assert(!Self::remaining_map(memtable, advanced)
                            .contains_key(key)) by {
                            if Self::remaining_map(memtable, advanced)
                                .contains_key(key)
                            {
                                let new_entry = Self::remaining_index_for_key(
                                    memtable,
                                    advanced,
                                    key,
                                );
                                assert(advanced[selected] as nat
                                    == positions[selected] as nat + 1);
                                assert(new_entry >= advanced[selected] as int);
                                assert(new_entry > entry);
                                assert(memtable.buckets@[bucket].entries@[new_entry].key
                                    == memtable.buckets@[bucket].entries@[entry].key);
                                assert(false);
                            }
                        }
                    } else {
                        if bucket == selected {
                            assert(entry > positions[selected] as int);
                        }
                        assert(Self::remaining_map(memtable, advanced)
                            .contains_key(key));
                        let new_entry = Self::remaining_index_for_key(
                            memtable,
                            advanced,
                            key,
                        );
                        assert(new_entry == entry);
                    }
                }
                if Self::remaining_map(memtable, advanced).contains_key(key) {
                    let entry = Self::remaining_index_for_key(
                        memtable,
                        advanced,
                        key,
                    );
                    assert(positions[bucket] <= entry) by {
                        if bucket == selected {
                            assert(advanced[bucket]
                                == (positions[bucket] as nat + 1) as usize);
                            assert(advanced[bucket] as nat
                                == positions[bucket] as nat + 1);
                            assert(entry >= advanced[bucket] as int);
                        } else {
                            assert(advanced[bucket] == positions[bucket]);
                        }
                    }
                    assert(Self::remaining_map(memtable, positions)
                        .contains_key(key));
                    assert(key != selected_entry.key);
                    let old_entry = Self::remaining_index_for_key(
                        memtable,
                        positions,
                        key,
                    );
                    assert(old_entry == entry);
                }
            }
        );
    }

    fn find_min_bucket(&self, memtable: &MemtableImpl) -> (out: Option<usize>)
        requires
            self.wf(memtable),
        ensures
            match out {
                Some(bucket) => Self::min_bucket(
                    memtable,
                    self.positions@,
                ) == Some(bucket as int),
                None => Self::min_bucket(
                    memtable,
                    self.positions@,
                ) is None,
            },
    {
        let mut selected: Option<usize> = None;
        let mut bucket = 0usize;
        while bucket < memtable.buckets.len()
            invariant
                self.wf(memtable),
                bucket <= memtable.buckets.len(),
                match selected {
                    Some(value) => Self::min_bucket_prefix(
                        memtable,
                        self.positions@,
                        bucket as nat,
                    ) == Some(value as int),
                    None => Self::min_bucket_prefix(
                        memtable,
                        self.positions@,
                        bucket as nat,
                    ) is None,
                },
            decreases memtable.buckets.len() - bucket,
        {
            if self.positions[bucket]
                < memtable.buckets[bucket].entries.len()
            {
                match selected {
                    None => {
                        selected = Some(bucket);
                    },
                    Some(current) => {
                        proof {
                            Self::min_bucket_prefix_properties(
                                memtable,
                                self.positions@,
                                bucket as nat,
                            );
                            assert(Self::bucket_active(
                                memtable,
                                self.positions@,
                                current as int,
                            ));
                        }
                        let candidate = memtable.buckets[bucket].entries[
                            self.positions[bucket]
                        ];
                        let current_entry = memtable.buckets[current].entries[
                            self.positions[current]
                        ];
                        if candidate.key.0 < current_entry.key.0 {
                            selected = Some(bucket);
                        }
                    },
                }
            }
            bucket += 1;
        }
        selected
    }

    pub fn next<'a>(
        &mut self,
        memtable: &'a MemtableImpl,
    ) -> (out: Option<&'a MemtableEntry>)
        requires
            old(self).wf(memtable),
        ensures
            self.wf(memtable),
            match out {
                Some(entry) => {
                    &&& old(self)@.contains_key(entry.key)
                    &&& old(self)@[entry.key] == entry.message
                    &&& self@ == old(self)@.remove(entry.key)
                    &&& forall |key: Key| self@.contains_key(key)
                        ==> entry.key.0 < key.0
                    &&& self.count(memtable) + 1
                        == old(self).count(memtable)
                },
                None => {
                    &&& old(self)@ == Map::<Key, Message>::empty()
                    &&& self@ == old(self)@
                    &&& old(self).count(memtable) == 0
                },
            },
    {
        let selected = self.find_min_bucket(memtable);
        match selected {
            None => {
                proof {
                    Self::min_bucket_prefix_properties(
                        memtable,
                        self.positions@,
                        self.positions@.len(),
                    );
                    Self::remaining_count_prefix_active(
                        memtable,
                        self.positions@,
                        self.positions@.len(),
                    );
                    assert_maps_equal!(self@, Map::<Key, Message>::empty(), key => {
                        if self@.contains_key(key) {
                            let bucket = MemtableImpl::bucket_index(
                                key,
                                memtable.bucket_count as nat,
                            ) as int;
                            let entry = Self::remaining_index_for_key(
                                memtable,
                                self.positions@,
                                key,
                            );
                            assert(Self::bucket_active(
                                memtable,
                                self.positions@,
                                bucket,
                            ));
                            assert(false);
                        }
                    });
                }
                None
            },
            Some(bucket) => {
                proof {
                    Self::min_bucket_prefix_properties(
                        memtable,
                        self.positions@,
                        self.positions@.len(),
                    );
                    assert(bucket < self.positions.len());
                    assert(Self::bucket_active(
                        memtable,
                        self.positions@,
                        bucket as int,
                    ));
                }
                let entry_index = self.positions[bucket];
                proof {
                    vstd::std_specs::vec::axiom_spec_len(
                        &memtable.buckets[bucket as int].entries,
                    );
                    assert(memtable.buckets@[bucket as int].entries@.len()
                        <= usize::MAX);
                    assert(entry_index < usize::MAX);
                }
                let ghost old_positions = self.positions@;
                let ghost old_remaining = self@;
                proof {
                    Self::selected_is_least_remaining(
                        memtable,
                        old_positions,
                        bucket as int,
                    );
                    Self::advance_removes_selected(
                        memtable,
                        old_positions,
                        bucket as int,
                    );
                    Self::advance_count_decreases(
                        memtable,
                        old_positions,
                        bucket as int,
                    );
                }
                self.positions.set(bucket, entry_index + 1);
                let entry = &memtable.buckets[bucket].entries[entry_index];
                self.remaining = Ghost(old_remaining.remove(entry.key));
                proof {
                    assert(self.positions@ == old_positions.update(
                        bucket as int,
                        (old_positions[bucket as int] as nat + 1) as usize,
                    ));
                    assert forall |key: Key| self@.contains_key(key)
                        implies entry.key.0 < key.0 by {
                        assert(old(self)@.contains_key(key));
                        assert(key != entry.key);
                    }
                }
                Some(entry)
            },
        }
    }
}

impl View for MemtableSortedCursor {
    type V = Map<Key, Message>;

    closed spec fn view(&self) -> Map<Key, Message> {
        self.remaining@
    }
}

impl<'a> MemtableIter<'a> {
    pub closed spec fn wf(&self) -> bool {
        &&& self.memtable.wf()
        &&& self.bucket <= self.memtable.buckets@.len()
        &&& if self.bucket < self.memtable.buckets@.len() {
            self.entry <= self.memtable.buckets@[self.bucket as int].entries@.len()
        } else {
            self.entry == 0
        }
    }

    pub closed spec fn position(&self) -> nat
        recommends self.wf()
    {
        if self.bucket < self.memtable.buckets@.len() {
            MemtableImpl::flatten_prefix(self.memtable.buckets@, self.bucket as nat).len()
                + self.entry as nat
        } else {
            MemtableImpl::flatten_prefix(
                self.memtable.buckets@,
                self.memtable.buckets@.len(),
            ).len()
        }
    }

    pub closed spec fn remaining(&self) -> Seq<MemtableEntry>
        recommends self.wf()
    {
        let flattened = MemtableImpl::flatten_prefix(
            self.memtable.buckets@,
            self.memtable.buckets@.len(),
        );
        flattened.subrange(self.position() as int, flattened.len() as int)
    }

    proof fn position_in_bounds(&self)
        requires
            self.wf(),
        ensures
            self.position() <= MemtableImpl::flatten_prefix(
                self.memtable.buckets@,
                self.memtable.buckets@.len(),
            ).len(),
    {
        if self.bucket < self.memtable.buckets@.len() {
            let prefix = MemtableImpl::flatten_prefix(
                self.memtable.buckets@,
                self.bucket as nat,
            );
            let through_bucket = MemtableImpl::flatten_prefix(
                self.memtable.buckets@,
                self.bucket as nat + 1,
            );
            assert(through_bucket == prefix
                + self.memtable.buckets@[self.bucket as int].entries@);
            assert(prefix.len() + self.entry as nat <= through_bucket.len());
            assert(through_bucket
                == MemtableImpl::flatten_prefix(
                    self.memtable.buckets@,
                    self.bucket as nat + 1,
                ));
            MemtableImpl::flatten_prefix_embeds(
                self.memtable.buckets@,
                self.bucket as nat + 1,
                self.memtable.buckets@.len(),
            );
        }
    }

    pub fn next(&mut self) -> (out: Option<&'a MemtableEntry>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            match out {
                Some(entry) => {
                    &&& old(self)@.len() > 0
                    &&& *entry == old(self)@[0]
                    &&& self@ == old(self)@.subrange(
                        1,
                        old(self)@.len() as int,
                    )
                },
                None => {
                    &&& old(self)@.len() == 0
                    &&& self@.len() == 0
                },
            },
    {
        let ghost original_remaining = self.remaining();
        while self.bucket < self.memtable.buckets.len()
            invariant
                self.wf(),
                self.remaining() == original_remaining,
            decreases self.memtable.buckets.len() - self.bucket,
        {
            if self.entry < self.memtable.buckets[self.bucket].entries.len() {
                let memtable = self.memtable;
                let bucket = self.bucket;
                let entry = self.entry;
                let ghost previous_position = self.position();
                let ghost previous_remaining = self.remaining();
                self.entry = self.entry + 1;
                let out = &memtable.buckets[bucket].entries[entry];
                proof {
                    self.position_in_bounds();
                    let flattened = MemtableImpl::flatten_prefix(
                        memtable.buckets@,
                        memtable.buckets@.len(),
                    );
                    let prefix = MemtableImpl::flatten_prefix(
                        memtable.buckets@,
                        bucket as nat,
                    );
                    let through_bucket = MemtableImpl::flatten_prefix(
                        memtable.buckets@,
                        bucket as nat + 1,
                    );
                    assert(through_bucket == prefix
                        + memtable.buckets@[bucket as int].entries@);
                    assert(through_bucket[(prefix.len() + entry as nat) as int]
                        == memtable.buckets@[bucket as int].entries@[entry as int]);
                    MemtableImpl::flatten_prefix_embeds(
                        memtable.buckets@,
                        bucket as nat + 1,
                        memtable.buckets@.len(),
                    );
                    assert(flattened[(prefix.len() + entry as nat) as int]
                        == through_bucket[(prefix.len() + entry as nat) as int]);
                    assert(self.position() == previous_position + 1);
                    assert(previous_remaining == original_remaining);
                    assert(self.remaining() == original_remaining.subrange(
                        1,
                        original_remaining.len() as int,
                    ));
                }
                return Some(out);
            }
            proof {
                assert(self.entry == self.memtable.buckets@[self.bucket as int].entries@.len());
                let prefix = MemtableImpl::flatten_prefix(
                    self.memtable.buckets@,
                    self.bucket as nat,
                );
                assert(MemtableImpl::flatten_prefix(
                    self.memtable.buckets@,
                    self.bucket as nat + 1,
                ) == prefix + self.memtable.buckets@[self.bucket as int].entries@);
            }
            self.bucket = self.bucket + 1;
            self.entry = 0;
        }
        proof {
            self.position_in_bounds();
            assert(self.remaining().len() == 0);
            assert(original_remaining.len() == 0);
        }
        None
    }
}

impl<'a> View for MemtableIter<'a> {
    type V = Seq<MemtableEntry>;

    closed spec fn view(&self) -> Seq<MemtableEntry> {
        self.remaining()
    }
}

impl View for MemtableImpl {
    type V = Memtable;

    open spec fn view(&self) -> Memtable {
        Memtable {
            buffer: SimpleBuffer {
                map: Self::buckets_map(self.buckets@, self.bucket_count as nat),
            },
            seq_end: self.seq_end as LSN,
        }
    }
}

fn memtable_combine_deltas(new_delta: Delta, old_delta: Delta) -> (out: Delta)
    ensures
        out == Message::combine_deltas(new_delta, old_delta),
{
    if new_delta.0 == 0 {
        proof {
            assert(new_delta == nop_delta());
        }
        old_delta
    } else if old_delta.0 == 0 {
        proof {
            assert(new_delta != nop_delta());
            assert(old_delta == nop_delta());
        }
        new_delta
    } else {
        proof {
            assert(new_delta != nop_delta());
            assert(old_delta != nop_delta());
        }
        new_delta
    }
}

fn memtable_merge_messages(older: Message, newer: Message) -> (out: Message)
    ensures
        out == older.merge(newer),
{
    match newer {
        Message::Define { value } => Message::Define { value },
        Message::Update { delta: new_delta } => {
            match older {
                Message::Define { value } => {
                    proof {
                        assert(Message::apply_delta(new_delta, value) == value);
                    }
                    Message::Define { value }
                },
                Message::Update { delta: old_delta } => {
                    let delta = memtable_combine_deltas(new_delta, old_delta);
                    Message::Update { delta }
                },
            }
        },
    }
}

#[allow(dead_code)]
fn verify_memtable_cases() {
    let mut collision = MemtableImpl::new(2, 0);
    let first = KeyedMessage {
        key: Key(1),
        message: Message::Update { delta: Delta(5) },
    };
    let second = KeyedMessage {
        key: Key(3),
        message: Message::Define {
            value: crate::spec::Messages_t::Value(30),
        },
    };
    let newer = KeyedMessage {
        key: Key(1),
        message: Message::Update { delta: Delta(7) },
    };
    let first_result = collision.put(first);
    let second_result = collision.put(second);
    let newer_result = collision.put(newer);
    proof {
        assert(first_result is Applied);
        assert(second_result is Applied);
        assert(newer_result is Applied);
    }
    let first_value = collision.query(Key(1));
    let second_value = collision.query(Key(3));
    let missing_value = collision.query(Key(9));
    match first_value {
        Message::Update { delta } => {
            proof { assert(delta.0 == 7); }
        },
        _ => { proof { assert(false); } },
    }
    match second_value {
        Message::Define { value } => {
            proof { assert(value.0 == 30); }
        },
        _ => { proof { assert(false); } },
    }
    match missing_value {
        Message::Update { delta } => {
            proof { assert(delta.0 == 0); }
        },
        _ => { proof { assert(false); } },
    }
    let flattened = collision.flatten();
    proof {
        assert(MemtableBucket::unique_keys(flattened@));
        assert(MemtableBucket::entries_map(flattened@) == collision@.buffer.map);
    }
    let mut collision_scan = collision.scan();
    proof {
        assert(collision_scan@ == flattened@);
        assert(collision_scan@.len() > 0) by {
            if collision_scan@.len() == 0 {
                assert(MemtableBucket::entries_map(collision_scan@)
                    == Map::<Key, Message>::empty());
                assert(collision@.buffer.map.contains_key(Key(1)));
            }
        }
    }
    let scanned_first = collision_scan.next();
    match scanned_first {
        Some(entry) => {
            proof {
                assert(*entry == flattened@[0]);
                assert(collision_scan@ == flattened@.subrange(1, flattened@.len() as int));
            }
        },
        None => { proof { assert(false); } },
    }

    let mut replay = MemtableImpl::new(4, 10);
    let mut replay_puts = Vec::new();
    replay_puts.push(first);
    replay_puts.push(newer);
    let replay_result = replay.apply_puts(10, &replay_puts);
    proof {
        assert(replay_result is Applied);
        assert(replay.seq_end == 12);
        assert(replay@ == Memtable::empty_memtable(10).apply_puts(
            MemtableImpl::history_from_seq(10, replay_puts@),
        ));
    }
    let replay_seq_end = replay.seq_end;
    let replay_bucket_count = replay.bucket_count;
    replay.drain();
    proof {
        assert(replay.seq_end == replay_seq_end);
        assert(replay.bucket_count == replay_bucket_count);
        assert(replay.buckets@.len() == replay_bucket_count as nat);
    }
    let drained_empty = replay.is_empty();
    proof { assert(drained_empty); }
    let mut empty_scan = replay.scan();
    proof {
        assert(MemtableBucket::entries_map(empty_scan@)
            == Map::<Key, Message>::empty());
        MemtableBucket::entries_map_empty_implies_entries_empty(empty_scan@);
        assert(empty_scan@.len() == 0);
    }
    let empty_scan_result = empty_scan.next();
    proof {
        assert(empty_scan_result is None);
        assert(empty_scan@.len() == 0);
    }
    let exhausted_again = empty_scan.next();
    proof {
        assert(exhausted_again is None);
        assert(empty_scan@.len() == 0);
    }

    let mut boundary = MemtableImpl::new(1, u64::MAX);
    let empty_puts: Vec<KeyedMessage> = Vec::new();
    let empty_result = boundary.apply_puts(u64::MAX, &empty_puts);
    proof {
        assert(empty_result is Applied);
        assert(boundary.seq_end == u64::MAX);
    }
    let mut overflow_puts = Vec::new();
    overflow_puts.push(first);
    let ghost boundary_before = boundary@;
    let overflow_result = boundary.apply_puts(u64::MAX, &overflow_puts);
    proof {
        assert(overflow_result is Noop);
        assert(boundary@ == boundary_before);
    }
}

} // verus!
