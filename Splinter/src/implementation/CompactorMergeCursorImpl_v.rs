// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::assert_seqs_equal;
use vstd::assert_sets_equal;

use crate::abstract_system::MsgHistory_v::KeyedMessage;
use crate::allocation_layer::AllocationBranchBetree_v::{
    map_with_disjoint_values,
};
use crate::allocation_layer::BranchTypes_v::{BranchNode, Summary};
use crate::betree::BufferDisk_v::BufferDisk;
use crate::disk::GenericDisk_v::{
    AU, Address, set_addrs_disjoint_aus,
};
use crate::implementation::BetreeQueryImpl_v::merge_messages;
use crate::implementation::BranchScanCursorImpl_v::{
    BranchScanCursor, BranchScanStepResult, pivot_branch_entries,
};
use crate::implementation::BranchScanSemantics_v::{
    keyed_entries_contains, keyed_entries_message,
    keyed_entries_query, keyed_entries_query_index,
    linked_branch_entries,
    linked_branch_entries_refine, loaded_branch_forest_wf,
    loaded_branch_in_forest_refines,
};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedBranchBetree_v::{
    loaded_sealed_branch, valid_loaded_sealed_branch,
    valid_loaded_sealed_branches,
};
use crate::implementation::CachedBranch_v::LoadedBranch;
use crate::implementation::CachingDiskBranchBetree_v::to_branch_nodes;
use crate::implementation::CachingDisk_v::addresses_in_aus;
use crate::implementation::CompactionFilterImpl_v::{
    CompactionFilterImpl, CompactionLiveStart,
};
use crate::implementation::FracCacheImpl_v::{FracCacheImpl, MutHandle};
use crate::marshalling::IBranchNodeFormat_v::raw_page_to_branch_node;
use crate::spec::AsyncDisk_t::RawPage;
use crate::spec::ImplDisk_t::IAddress;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Delta, Message};

verus! {

pub open spec fn keyed_entries_strictly_sorted(
    entries: Seq<KeyedMessage>,
) -> bool {
    forall |i: int, j: int| 0 <= i < j < entries.len()
        ==> Key::lt((#[trigger] entries[i]).key, (#[trigger] entries[j]).key)
}

pub open spec fn merge_source_messages(
    sources: Seq<Seq<KeyedMessage>>,
    key: Key,
    start: int,
) -> Message
    recommends 0 <= start <= sources.len(),
    decreases sources.len() - start when start <= sources.len()
{
    if start == sources.len() {
        Message::Update { delta: Delta(0) }
    } else {
        keyed_entries_query(sources[start], key).merge(
            merge_source_messages(sources, key, start + 1),
        )
    }
}

pub open spec fn compact_source_start(
    filter: &CompactionFilterImpl,
    key: Key,
) -> nat {
    filter.target@.make_offset_map().decrement(
        filter.start as nat,
    ).offsets[key]
}

pub open spec fn compact_sources_contain(
    filter: &CompactionFilterImpl,
    sources: Seq<Seq<KeyedMessage>>,
    key: Key,
) -> bool {
    let start = compact_source_start(filter, key);
    &&& filter.target@.key_in_domain(key)
    &&& filter.target@.flushed_ofs(key) <= filter.end as nat
    &&& start <= sources.len()
    &&& exists |i: int| start as int <= i < sources.len()
        && keyed_entries_contains(#[trigger] sources[i], key)
}

pub open spec fn compact_sources_message(
    filter: &CompactionFilterImpl,
    sources: Seq<Seq<KeyedMessage>>,
    key: Key,
) -> Message
    recommends compact_sources_contain(filter, sources, key),
{
    merge_source_messages(
        sources,
        key,
        compact_source_start(filter, key) as int,
    )
}

pub open spec fn output_entries_valid(
    filter: &CompactionFilterImpl,
    sources: Seq<Seq<KeyedMessage>>,
    output: Seq<KeyedMessage>,
) -> bool {
    &&& keyed_entries_strictly_sorted(output)
    &&& forall |i: int| 0 <= i < output.len() ==> {
        let item = #[trigger] output[i];
        &&& compact_sources_contain(filter, sources, item.key)
        &&& item.message == compact_sources_message(
            filter,
            sources,
            item.key,
        )
    }
}

proof fn seq_cancel_left<A>(
    prefix: Seq<A>,
    left: Seq<A>,
    right: Seq<A>,
)
    requires
        prefix + left =~= prefix + right,
        left.len() == right.len(),
    ensures left == right,
{
    assert_seqs_equal!(left, right, i => {
        assert((prefix + left)[prefix.len() as int + i] == left[i]);
        assert((prefix + right)[prefix.len() as int + i] == right[i]);
    });
}

proof fn seq_ext_equal_index<A>(
    left: Seq<A>,
    right: Seq<A>,
    index: int,
)
    requires
        left =~= right,
        left.len() == right.len(),
        0 <= index < left.len(),
    ensures left[index] == right[index],
{
    assert(left[index] == right[index]);
}

proof fn key_lt_lte_transitive(left: Key, middle: Key, right: Key)
    requires
        Key::lt(left, middle),
        Key::lte(middle, right),
    ensures Key::lte(left, right),
{
    assert(left.0 < middle.0);
    assert(middle.0 <= right.0);
}

proof fn key_lte_lt_transitive(left: Key, middle: Key, right: Key)
    requires
        Key::lte(left, middle),
        Key::lt(middle, right),
    ensures Key::lt(left, right),
{
    assert(left.0 <= middle.0);
    assert(middle.0 < right.0);
    assert(left != right);
}

proof fn key_not_lt_reverse(left: Key, right: Key)
    requires !Key::lt(left, right),
    ensures Key::lte(right, left),
{
    if left.0 < right.0 {
        assert(Key::lt(left, right));
    }
}

proof fn strictly_sorted_key_unique(
    entries: Seq<KeyedMessage>,
    key: Key,
    left: int,
    right: int,
)
    requires
        keyed_entries_strictly_sorted(entries),
        0 <= left < entries.len(),
        0 <= right < entries.len(),
        entries[left].key == key,
        entries[right].key == key,
    ensures left == right,
{
    if left < right {
        assert(Key::lt(entries[left].key, entries[right].key));
        assert(false);
    }
    if right < left {
        assert(Key::lt(entries[right].key, entries[left].key));
        assert(false);
    }
}

proof fn sorted_cut_query_lemma(
    entries: Seq<KeyedMessage>,
    prefix: Seq<KeyedMessage>,
    suffix: Seq<KeyedMessage>,
    key: Key,
)
    requires
        keyed_entries_strictly_sorted(entries),
        prefix + suffix =~= entries,
        (prefix + suffix).len() == entries.len(),
        forall |i: int| 0 <= i < prefix.len()
            ==> Key::lt((#[trigger] prefix[i]).key, key),
        suffix.len() == 0 || Key::lte(key, suffix[0].key),
    ensures
        keyed_entries_contains(entries, key)
            <==> suffix.len() > 0 && suffix[0].key == key,
        keyed_entries_query(entries, key) == if suffix.len() > 0
            && suffix[0].key == key {
            suffix[0].message
        } else {
            Message::Update { delta: Delta(0) }
        },
{
    assert forall |j: int| 0 <= j < entries.len()
        && entries[j].key == key
        implies suffix.len() > 0 && suffix[0].key == key by {
        seq_ext_equal_index(prefix + suffix, entries, j);
        if j < prefix.len() {
            assert((prefix + suffix)[j] == prefix[j]);
            assert(Key::lt(prefix[j].key, key));
            assert(false);
        } else {
            let k = j - prefix.len();
            assert(0 <= k < suffix.len());
            assert((prefix + suffix)[j] == suffix[k]);
            if k > 0 {
                assert(prefix.len() < j);
                seq_ext_equal_index(
                    prefix + suffix,
                    entries,
                    prefix.len() as int,
                );
                assert((prefix + suffix)[prefix.len() as int]
                    == suffix[0]);
                assert(Key::lt(suffix[0].key, entries[j].key));
                assert(Key::lte(key, suffix[0].key));
                assert(entries[j].key == key);
                assert(false);
            }
            assert(k == 0);
        }
    }
    if suffix.len() > 0 && suffix[0].key == key {
        let j = prefix.len() as int;
        assert(0 <= j < entries.len());
        seq_ext_equal_index(prefix + suffix, entries, j);
        assert((prefix + suffix)[j] == suffix[0]);
        assert(entries[j].key == key);
        assert(keyed_entries_contains(entries, key));
    }
    if keyed_entries_contains(entries, key) {
        let chosen = choose |i: int| 0 <= i < entries.len()
            && entries[i].key == key;
        let expected = prefix.len() as int;
        assert(suffix.len() > 0 && suffix[0].key == key);
        seq_ext_equal_index(prefix + suffix, entries, expected);
        assert(entries[expected] == suffix[0]);
        strictly_sorted_key_unique(
            entries,
            key,
            chosen,
            expected,
        );
        assert(keyed_entries_message(entries, key)
            == suffix[0].message);
    }
}

proof fn nop_merge_left_identity(message: Message)
    ensures (Message::Update { delta: Delta(0) }).merge(message) == message,
{
    match message {
        Message::Define { .. } => {},
        Message::Update { delta } => {
            assert(Message::combine_deltas(delta, Delta(0)) == delta);
        },
    }
}

proof fn keyed_entries_drop_first_sorted(entries: Seq<KeyedMessage>)
    requires
        keyed_entries_strictly_sorted(entries),
        entries.len() > 0,
    ensures keyed_entries_strictly_sorted(entries.drop_first()),
{
    assert(entries.drop_first()
        == entries.subrange(1, entries.len() as int));
    assert forall |i: int, j: int|
        0 <= i < j < entries.drop_first().len()
        implies Key::lt(
            (#[trigger] entries.drop_first()[i]).key,
            (#[trigger] entries.drop_first()[j]).key,
        ) by {
        assert(entries.drop_first()[i]
            == entries.subrange(1, entries.len() as int)[i]);
        assert(entries.drop_first()[j]
            == entries.subrange(1, entries.len() as int)[j]);
        vstd::seq::axiom_seq_subrange_index(
            entries,
            1,
            entries.len() as int,
            i,
        );
        vstd::seq::axiom_seq_subrange_index(
            entries,
            1,
            entries.len() as int,
            j,
        );
        assert(entries.subrange(1, entries.len() as int)[i]
            == entries[i + 1]);
        assert(entries.subrange(1, entries.len() as int)[j]
            == entries[j + 1]);
        assert(entries.drop_first()[i] == entries[i + 1]);
        assert(entries.drop_first()[j] == entries[j + 1]);
    }
}

proof fn push_head_reassembles<A>(prefix: Seq<A>, suffix: Seq<A>)
    requires suffix.len() > 0,
    ensures
        prefix.push(suffix[0]) + suffix.drop_first()
            =~= prefix + suffix,
{
    assert_seqs_equal!(
        prefix.push(suffix[0]) + suffix.drop_first(),
        prefix + suffix,
        i => {
            if i < prefix.len() {
            } else if i == prefix.len() {
                assert((prefix.push(suffix[0])
                    + suffix.drop_first())[i] == suffix[0]);
                assert((prefix + suffix)[i] == suffix[0]);
            } else {
                let j = i - prefix.len() - 1;
                assert(suffix.drop_first()[j] == suffix[j + 1]);
            }
        }
    );
}

proof fn keyed_entries_push_sorted(
    entries: Seq<KeyedMessage>,
    item: KeyedMessage,
)
    requires
        keyed_entries_strictly_sorted(entries),
        forall |i: int| 0 <= i < entries.len()
            ==> Key::lt((#[trigger] entries[i]).key, item.key),
    ensures keyed_entries_strictly_sorted(entries.push(item)),
{
    assert forall |i: int, j: int|
        0 <= i < j < entries.push(item).len()
        implies Key::lt(
            (#[trigger] entries.push(item)[i]).key,
            (#[trigger] entries.push(item)[j]).key,
        ) by {
        if j == entries.len() {
            assert(entries.push(item)[j] == item);
            assert(entries.push(item)[i] == entries[i]);
        } else {
            assert(entries.push(item)[i] == entries[i]);
            assert(entries.push(item)[j] == entries[j]);
        }
    }
}

pub struct CompactorMergeCursor {
    pub cursors: Vec<BranchScanCursor>,
    pub filter: CompactionFilterImpl,
    pub frontier: Option<Key>,
    pub sources: Ghost<Seq<Seq<KeyedMessage>>>,
    pub output: Ghost<Seq<KeyedMessage>>,
}

pub closed spec fn compactor_source_disks_agree(
    cursors: Seq<BranchScanCursor>,
) -> bool {
    &&& forall |left: int, right: int, addr: Address|
            0 <= left < cursors.len()
            && 0 <= right < cursors.len()
            && cursors[left].source@.disk_view.entries.contains_key(addr)
            && cursors[right].source@.disk_view.entries.contains_key(addr)
            ==> cursors[left].source@.disk_view.entries[addr]
                == cursors[right].source@.disk_view.entries[addr]
    &&& forall |left: int, right: int|
            0 <= left < cursors.len()
            && 0 <= right < cursors.len()
            && cursors[left].source@.root == cursors[right].source@.root
            ==> cursors[left].source@ == cursors[right].source@
}

pub proof fn establish_compactor_source_disks_agree(
    cursors: Seq<BranchScanCursor>,
)
    requires forall |left: int, right: int, addr: Address|
        0 <= left < cursors.len()
        && 0 <= right < cursors.len()
        && cursors[left].source@.disk_view.entries.contains_key(addr)
        && cursors[right].source@.disk_view.entries.contains_key(addr)
        ==> cursors[left].source@.disk_view.entries[addr]
            == cursors[right].source@.disk_view.entries[addr],
        forall |left: int, right: int|
            0 <= left < cursors.len()
            && 0 <= right < cursors.len()
            && cursors[left].source@.root == cursors[right].source@.root
            ==> cursors[left].source@ == cursors[right].source@,
    ensures compactor_source_disks_agree(cursors),
{
    reveal(compactor_source_disks_agree);
}

proof fn compactor_source_disks_agree_preserved(
    old_cursors: Seq<BranchScanCursor>,
    new_cursors: Seq<BranchScanCursor>,
)
    requires
        compactor_source_disks_agree(old_cursors),
        old_cursors.len() == new_cursors.len(),
        forall |i: int| 0 <= i < old_cursors.len()
            ==> (#[trigger] old_cursors[i]).source@
                == new_cursors[i].source@,
    ensures compactor_source_disks_agree(new_cursors),
{
    reveal(compactor_source_disks_agree);
    assert forall |left: int, right: int, addr: Address|
        0 <= left < new_cursors.len()
        && 0 <= right < new_cursors.len()
        && new_cursors[left].source@.disk_view.entries.contains_key(addr)
        && new_cursors[right].source@.disk_view.entries.contains_key(addr)
        implies new_cursors[left].source@.disk_view.entries[addr]
            == new_cursors[right].source@.disk_view.entries[addr] by {
        assert(old_cursors[left].source@ == new_cursors[left].source@);
        assert(old_cursors[right].source@ == new_cursors[right].source@);
        assert(old_cursors[left].source@.disk_view.entries[addr]
            == old_cursors[right].source@.disk_view.entries[addr]);
    }
    assert forall |left: int, right: int|
        0 <= left < new_cursors.len()
        && 0 <= right < new_cursors.len()
        && new_cursors[left].source@.root
            == new_cursors[right].source@.root
        implies new_cursors[left].source@ == new_cursors[right].source@ by {
        assert(old_cursors[left].source@ == new_cursors[left].source@);
        assert(old_cursors[right].source@ == new_cursors[right].source@);
        assert(old_cursors[left].source@ == old_cursors[right].source@);
    }
}

pub open spec fn compactor_scanned_nodes(
    cursors: Seq<BranchScanCursor>,
) -> LoadedBranch {
    Map::new(
        |addr: Address| exists |i: int| 0 <= i < cursors.len()
            && (#[trigger] cursors[i].scanned@).contains(addr),
        |addr: Address| {
            let i = choose |i: int| 0 <= i < cursors.len()
                && cursors[i].scanned@.contains(addr);
            cursors[i].source@.disk_view.entries[addr]
        },
    )
}

proof fn compactor_scanned_nodes_extensional(
    left: Seq<BranchScanCursor>,
    right: Seq<BranchScanCursor>,
)
    requires
        left.len() == right.len(),
        compactor_source_disks_agree(left),
        compactor_source_disks_agree(right),
        forall |i: int| 0 <= i < left.len() ==> {
            &&& (#[trigger] left[i]).source@ == right[i].source@
            &&& left[i].scanned@ == right[i].scanned@
            &&& left[i].wf()
            &&& left[i].receipt_wf()
            &&& right[i].wf()
            &&& right[i].receipt_wf()
        },
    ensures compactor_scanned_nodes(left) == compactor_scanned_nodes(right),
{
    reveal(compactor_source_disks_agree);
    assert_maps_equal!(
        compactor_scanned_nodes(left),
        compactor_scanned_nodes(right),
        addr => {
            if compactor_scanned_nodes(left).contains_key(addr) {
                let i = choose |i: int| 0 <= i < left.len()
                    && left[i].scanned@.contains(addr);
                left[i].receipt_wf_ensures();
                assert(right[i].scanned@.contains(addr));
                assert(compactor_scanned_nodes(right).contains_key(addr));
            }
            if compactor_scanned_nodes(right).contains_key(addr) {
                let i = choose |i: int| 0 <= i < right.len()
                    && right[i].scanned@.contains(addr);
                right[i].receipt_wf_ensures();
                assert(left[i].scanned@.contains(addr));
                assert(compactor_scanned_nodes(left).contains_key(addr));
            }
            if compactor_scanned_nodes(left).contains_key(addr)
                && compactor_scanned_nodes(right).contains_key(addr)
            {
                let left_i = choose |i: int| 0 <= i < left.len()
                    && left[i].scanned@.contains(addr);
                let right_i = choose |i: int| 0 <= i < right.len()
                    && right[i].scanned@.contains(addr);
                left[left_i].receipt_wf_ensures();
                left[right_i].receipt_wf_ensures();
                right[right_i].receipt_wf_ensures();
                assert(left[left_i].source@.disk_view.entries
                    .contains_key(addr));
                assert(left[right_i].source@.disk_view.entries
                    .contains_key(addr));
                assert(left[left_i].source@.disk_view.entries[addr]
                    == left[right_i].source@.disk_view.entries[addr]);
                assert(left[right_i].source@
                    == right[right_i].source@);
            }
        }
    );
}

proof fn compactor_scanned_nodes_update(
    old_cursors: Seq<BranchScanCursor>,
    new_cursors: Seq<BranchScanCursor>,
    index: int,
    reads: Map<Address, RawPage>,
)
    requires
        0 <= index < old_cursors.len(),
        new_cursors.len() == old_cursors.len(),
        compactor_source_disks_agree(old_cursors),
        compactor_source_disks_agree(new_cursors),
        forall |i: int| 0 <= i < old_cursors.len() ==> {
            &&& (#[trigger] old_cursors[i]).wf()
            &&& old_cursors[i].receipt_wf()
        },
        forall |i: int| 0 <= i < new_cursors.len() ==> {
            &&& (#[trigger] new_cursors[i]).wf()
            &&& new_cursors[i].receipt_wf()
        },
        forall |i: int| 0 <= i < old_cursors.len()
            ==> (#[trigger] new_cursors[i]).source@
                == old_cursors[i].source@,
        forall |i: int| 0 <= i < old_cursors.len() && i != index
            ==> (#[trigger] new_cursors[i]).scanned@
                == old_cursors[i].scanned@,
        new_cursors[index].scanned@
            == old_cursors[index].scanned@ + reads.dom(),
        forall |addr: Address| #[trigger] reads.contains_key(addr) ==> {
            &&& new_cursors[index].source@.disk_view.entries
                .contains_key(addr)
            &&& to_branch_nodes(reads)[addr]
                == new_cursors[index].source@.disk_view.entries[addr]
        },
    ensures compactor_scanned_nodes(new_cursors)
        == compactor_scanned_nodes(old_cursors)
            .union_prefer_right(to_branch_nodes(reads)),
{
    reveal(compactor_source_disks_agree);
    assert_maps_equal!(
        compactor_scanned_nodes(new_cursors),
        compactor_scanned_nodes(old_cursors)
            .union_prefer_right(to_branch_nodes(reads)),
        addr => {
            if compactor_scanned_nodes(new_cursors).contains_key(addr) {
                let new_i = choose |i: int| 0 <= i < new_cursors.len()
                    && new_cursors[i].scanned@.contains(addr);
                new_cursors[new_i].receipt_wf_ensures();
                assert(new_cursors[new_i].source@.disk_view.entries
                    .contains_key(addr));
                if reads.contains_key(addr) {
                    assert(new_cursors[index].source@.disk_view.entries
                        .contains_key(addr));
                    assert(new_cursors[new_i].source@.disk_view.entries[addr]
                        == new_cursors[index].source@.disk_view.entries[addr]);
                } else {
                    assert(old_cursors[new_i].scanned@.contains(addr));
                    assert(compactor_scanned_nodes(old_cursors)
                        .contains_key(addr));
                    let old_i = choose |i: int|
                        0 <= i < old_cursors.len()
                        && old_cursors[i].scanned@.contains(addr);
                    old_cursors[old_i].receipt_wf_ensures();
                    assert(old_cursors[old_i].source@.disk_view.entries
                        .contains_key(addr));
                    assert(old_cursors[new_i].source@.disk_view.entries[addr]
                        == old_cursors[old_i].source@.disk_view.entries[addr]);
                }
            }
            if reads.contains_key(addr) {
                assert(new_cursors[index].scanned@.contains(addr));
                assert(compactor_scanned_nodes(new_cursors)
                    .contains_key(addr));
            }
            if compactor_scanned_nodes(old_cursors).contains_key(addr) {
                let old_i = choose |i: int| 0 <= i < old_cursors.len()
                    && old_cursors[i].scanned@.contains(addr);
                if old_i == index {
                    assert(new_cursors[index].scanned@.contains(addr));
                } else {
                    assert(new_cursors[old_i].scanned@.contains(addr));
                }
                assert(compactor_scanned_nodes(new_cursors)
                    .contains_key(addr));
            }
        }
    );
}

pub enum CompactorMergeStepResult {
    ReadAdvanced {
        reads: Ghost<Map<Address, RawPage>>,
    },
    Item { item: KeyedMessage },
    Skipped,
    Done,
    NeedCacheLoad { addr: IAddress, handle: MutHandle },
    CacheFull,
    Blocked,
    InvalidPage,
}

impl CompactorMergeStepResult {
    pub fn is_done(&self) -> (out: bool)
        ensures out == (*self is Done),
    {
        match self {
            Self::Done => true,
            _ => false,
        }
    }
}

impl CompactorMergeCursor {
    pub open spec fn source_aus(&self) -> Set<AU> {
        Set::new(|au: AU| exists |i: int|
            0 <= i < self.cursors@.len()
            && (#[trigger] self.cursors@[i].source@.get_summary())
                .contains(au))
    }

    pub open spec fn scanned_nodes(&self) -> LoadedBranch {
        compactor_scanned_nodes(self.cursors@)
    }

    proof fn source_aus_extensional(&self, other: &Self)
        requires
            self.cursors@.len() == other.cursors@.len(),
            forall |i: int| 0 <= i < self.cursors@.len()
                ==> (#[trigger] self.cursors@[i]).source@
                    == other.cursors@[i].source@,
        ensures self.source_aus() == other.source_aus(),
    {
        assert_sets_equal!(self.source_aus(), other.source_aus(), au => {
            if self.source_aus().contains(au) {
                let i = choose |i: int| 0 <= i < self.cursors@.len()
                    && self.cursors@[i].source@.get_summary().contains(au);
                assert(other.cursors@[i].source@.get_summary().contains(au));
            }
            if other.source_aus().contains(au) {
                let i = choose |i: int| 0 <= i < other.cursors@.len()
                    && other.cursors@[i].source@.get_summary().contains(au);
                assert(self.cursors@[i].source@.get_summary().contains(au));
            }
        });
    }

    pub open spec fn same_logical_state(&self, other: &Self) -> bool {
        &&& self.cursors@ =~= other.cursors@
        &&& self.filter == other.filter
        &&& self.frontier == other.frontier
        &&& self.sources@ == other.sources@
        &&& self.output@ == other.output@
    }

    pub open spec fn cursor_sources_wf(&self) -> bool {
        &&& self.cursors@.len() == self.sources@.len()
        &&& self.cursors@.len()
            == self.filter.end - self.filter.start
        &&& compactor_source_disks_agree(self.cursors@)
        &&& forall |i: int| 0 <= i < self.cursors@.len() ==> {
            &&& (#[trigger] self.cursors@[i]).wf()
            &&& self.cursors@[i].receipt_wf()
            &&& keyed_entries_strictly_sorted(self.sources@[i])
            &&& keyed_entries_strictly_sorted(
                self.cursors@[i].remaining(),
            )
            &&& self.cursors@[i].emitted@
                + self.cursors@[i].remaining()
                =~= self.sources@[i]
            &&& self.cursors@[i].source@.root
                == self.filter.target@.buffers.addrs[
                    self.filter.start as int + i]
        }
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.filter.wf()
        &&& self.cursor_sources_wf()
        &&& output_entries_valid(
            &self.filter,
            self.sources@,
            self.output@,
        )
        &&& match self.frontier {
            Some(frontier) => {
                &&& forall |j: int| 0 <= j < self.output@.len()
                    ==> Key::lte(
                        (#[trigger] self.output@[j]).key,
                        frontier,
                    )
                &&& forall |i: int| 0 <= i < self.cursors@.len()
                    ==> forall |j: int|
                        0 <= j < (#[trigger] self.cursors@[i]).emitted@.len()
                        ==> Key::lte(
                            self.cursors@[i].emitted@[j].key,
                            frontier,
                        )
                &&& forall |i: int| 0 <= i < self.cursors@.len()
                    ==> forall |j: int|
                        0 <= j < (#[trigger] self.cursors@[i]).remaining().len()
                        ==> Key::lt(
                            frontier,
                            self.cursors@[i].remaining()[j].key,
                        )
            },
            None => {
                &&& self.output@.len() == 0
                &&& forall |i: int| 0 <= i < self.cursors@.len()
                    ==> (#[trigger] self.cursors@[i]).emitted@.len() == 0
            },
        }
        &&& forall |key: Key|
            compact_sources_contain(
                &self.filter,
                self.sources@,
                key,
            ) && (exists |i: int| 0 <= i < self.cursors@.len()
                && keyed_entries_contains(
                    (#[trigger] self.cursors@[i]).emitted@,
                    key,
                ))
            ==> keyed_entries_contains(self.output@, key)
    }

    pub open spec fn cache_inv(&self, cache: Cache::State) -> bool {
        forall |i: int| 0 <= i < self.cursors@.len()
            ==> (#[trigger] self.cursors@[i]).cache_inv(cache)
    }

    pub proof fn cache_inv_preserved_by_backward_valid_reads(
        &self,
        pre: Cache::State,
        post: Cache::State,
    )
        requires
            self.cache_inv(pre),
            forall |addr: Address, raw: RawPage|
                post.valid_read(addr, raw)
                    ==> pre.valid_read(addr, raw),
        ensures
            self.cache_inv(post),
    {
        assert forall |i: int| 0 <= i < self.cursors@.len()
            implies (#[trigger] self.cursors@[i]).cache_inv(post) by {
            let cursor = self.cursors@[i];
            assert forall |addr: Address, raw: RawPage|
                cursor.source@.disk_view.entries.contains_key(addr)
                    && #[trigger] post.valid_read(addr, raw)
                implies raw_page_to_branch_node(raw)
                    == cursor.source@.disk_view.entries[addr] by {
                assert(pre.valid_read(addr, raw));
            }
        }
    }

    pub proof fn cache_inv_preserved_by_unrelated_access(
        &self,
        pre: Cache::State,
        prepared: Cache::State,
        post: Cache::State,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    )
        requires
            self.wf(),
            self.cache_inv(pre),
            pre.inv(),
            Cache::State::next(
                pre,
                prepared,
                Cache::Label::Internal,
            ),
            Cache::State::next(
                prepared,
                post,
                Cache::Label::Access { reads, writes },
            ),
            writes.dom().disjoint(addresses_in_aus(self.source_aus())),
        ensures
            self.cache_inv(post),
    {
        Cache::State::inv_next(
            pre,
            prepared,
            Cache::Label::Internal,
        );
        assert forall |i: int| 0 <= i < self.cursors@.len()
            implies (#[trigger] self.cursors@[i]).cache_inv(post) by {
            let cursor = self.cursors@[i];
            cursor.receipt_wf_ensures();
            assert forall |addr: Address, raw: RawPage|
                cursor.source@.disk_view.entries.contains_key(addr)
                    && #[trigger] post.valid_read(addr, raw)
                implies raw_page_to_branch_node(raw)
                    == cursor.source@.disk_view.entries[addr] by {
                assert(cursor.source@.disk_view.entries.dom()
                    == cursor.source@.full_repr());
                assert(cursor.source@.full_repr().contains(addr));
                assert(crate::disk::GenericDisk_v::addrs_closed(
                    cursor.source@.full_repr(),
                    cursor.source@.get_summary(),
                ));
                assert(cursor.source@.get_summary().contains(addr.au));
                assert(self.source_aus().contains(addr.au));
                assert(!writes.contains_key(addr)) by {
                    if writes.contains_key(addr) {
                        assert(addresses_in_aus(
                            self.source_aus(),
                        ).contains(addr));
                        assert(false);
                    }
                }
                Cache::State::access_unwritten_valid_read_backward(
                    prepared,
                    post,
                    reads,
                    writes,
                    addr,
                    raw,
                );
                Cache::State::internal_valid_read_backward(
                    pre,
                    prepared,
                    addr,
                    raw,
                );
            }
        }
    }

    pub open spec fn heads_ready(&self) -> bool {
        forall |i: int| 0 <= i < self.cursors@.len()
            ==> (#[trigger] self.cursors@[i]).current_leaf is Some
                || self.cursors@[i].remaining().len() == 0
    }

    pub open spec fn exhausted(&self) -> bool {
        forall |i: int| 0 <= i < self.cursors@.len()
            ==> (#[trigger] self.cursors@[i]).remaining().len() == 0
    }

    pub open spec fn scan_complete(&self) -> bool {
        forall |i: int| 0 <= i < self.cursors@.len()
            ==> (#[trigger] self.cursors@[i]).scanned@
                == self.cursors@[i].source@.full_repr()
    }

    pub open spec fn source_roots(&self) -> Set<Address> {
        Set::new(|root: Address| exists |i: int|
            0 <= i < self.cursors@.len()
            && (#[trigger] self.cursors@[i]).source@.root == root)
    }

    pub proof fn source_streams_refine(&self)
        requires self.cursor_sources_wf(),
        ensures forall |i: int| 0 <= i < self.sources@.len()
            ==> {
                let source = (#[trigger] self.cursors@[i]).source@;
                &&& forall |key: Key|
                    keyed_entries_contains(self.sources@[i], key)
                        <==> source.i().i().map.contains_key(key)
                &&& forall |key: Key|
                    keyed_entries_query(self.sources@[i], key)
                        == source.i().i().query(key)
            },
    {
        assert forall |i: int| 0 <= i < self.sources@.len()
            implies forall |key: Key|
                keyed_entries_contains(self.sources@[i], key)
                    <==> (#[trigger] self.cursors@[i])
                        .source@.i().i().map.contains_key(key) by {
            let source = self.cursors@[i].source@;
            linked_branch_entries_refine(source);
            assert(self.cursors@[i].ranking@
                == source.the_ranking());
            let cursor_entries = self.cursors@[i].emitted@
                + self.cursors@[i].remaining();
            assert(cursor_entries =~= linked_branch_entries(source));
            assert(self.sources@[i] =~= cursor_entries);
            assert_seqs_equal!(
                self.sources@[i],
                linked_branch_entries(source),
                j => {}
            );
        }
        assert forall |i: int| 0 <= i < self.sources@.len()
            implies forall |key: Key|
                keyed_entries_query(self.sources@[i], key)
                    == (#[trigger] self.cursors@[i])
                        .source@.i().i().query(key) by {
            let source = self.cursors@[i].source@;
            linked_branch_entries_refine(source);
            assert(self.cursors@[i].ranking@
                == source.the_ranking());
            let cursor_entries = self.cursors@[i].emitted@
                + self.cursors@[i].remaining();
            assert(cursor_entries =~= linked_branch_entries(source));
            assert(self.sources@[i] =~= cursor_entries);
            assert_seqs_equal!(
                self.sources@[i],
                linked_branch_entries(source),
                j => {}
            );
        }
    }

    pub proof fn source_roots_match_filter(&self)
        requires
            self.filter.wf(),
            self.cursor_sources_wf(),
        ensures self.source_roots()
            == self.filter.target@.buffers.slice(
                self.filter.start as int,
                self.filter.end as int,
            ).addrs.to_set(),
    {
        let selected = self.filter.target@.buffers.slice(
            self.filter.start as int,
            self.filter.end as int,
        ).addrs;
        assert(selected == self.filter.target@.buffers.addrs.subrange(
            self.filter.start as int,
            self.filter.end as int,
        ));
        assert(0 <= (self.filter.start as int));
        assert((self.filter.start as int) < (self.filter.end as int));
        assert((self.filter.end as int)
            <= self.filter.target@.buffers.addrs.len());
        assert(selected.len()
            == self.filter.end as int - self.filter.start as int);
        assert(self.filter.end as int - self.filter.start as int
            == (self.filter.end - self.filter.start) as int);
        assert(selected.len() == self.filter.end - self.filter.start);
        assert(self.cursors@.len() == selected.len());
        assert_sets_equal!(self.source_roots(), selected.to_set(), root => {
            if self.source_roots().contains(root) {
                let i = choose |i: int| 0 <= i < self.cursors@.len()
                    && self.cursors@[i].source@.root == root;
                assert(0 <= self.filter.start as int + i
                    < self.filter.end as int);
                assert(self.filter.target@.buffers.addrs.subrange(
                    self.filter.start as int,
                    self.filter.end as int,
                )[i]
                    == self.filter.target@.buffers.addrs[
                        self.filter.start as int + i]);
                assert(selected[i]
                    == self.filter.target@.buffers.addrs[
                        self.filter.start as int + i]);
                assert(self.cursors@[i].source@.root == selected[i]);
                assert(selected.to_set().contains(root));
            }
            if selected.to_set().contains(root) {
                let i = choose |i: int| 0 <= i < selected.len()
                    && #[trigger] selected[i] == root;
                assert(0 <= self.filter.start as int + i
                    < self.filter.end as int);
                assert(self.filter.target@.buffers.addrs.subrange(
                    self.filter.start as int,
                    self.filter.end as int,
                )[i]
                    == self.filter.target@.buffers.addrs[
                        self.filter.start as int + i]);
                assert(selected[i]
                    == self.filter.target@.buffers.addrs[
                        self.filter.start as int + i]);
                assert(i < self.cursors@.len());
                assert(self.cursors@[i].source@.root == selected[i]);
                assert(self.source_roots().contains(root));
            }
        });
    }

    proof fn completed_source_receipt(
        &self,
        index: int,
        summaries: Map<AU, Summary>,
    )
        requires
            self.wf(),
            self.scan_complete(),
            0 <= index < self.cursors@.len(),
            set_addrs_disjoint_aus(self.source_roots()),
            map_with_disjoint_values(summaries),
            forall |i: int| 0 <= i < self.cursors@.len() ==> {
                let source = (#[trigger] self.cursors@[i]).source@;
                &&& summaries.contains_key(source.root.au)
                &&& summaries[source.root.au] == source.get_summary()
            },
        ensures
            self.scanned_nodes().restrict(addresses_in_aus(
                summaries[self.cursors@[index].source@.root.au],
            )) == self.cursors@[index].source@.disk_view.entries,
    {
        reveal(compactor_source_disks_agree);
        let source = self.cursors@[index].source@;
        let summary = summaries[source.root.au];
        let restricted = self.scanned_nodes().restrict(
            addresses_in_aus(summary),
        );
        assert_maps_equal!(
            restricted,
            source.disk_view.entries,
            addr => {
                if restricted.contains_key(addr) {
                    assert(self.scanned_nodes().contains_key(addr));
                    let scanned_index = choose |i: int|
                        0 <= i < self.cursors@.len()
                        && self.cursors@[i].scanned@.contains(addr);
                    let scanned_source = self.cursors@[scanned_index].source@;
                    self.cursors@[scanned_index].receipt_wf_ensures();
                    assert(self.cursors@[scanned_index].scanned@
                        == scanned_source.full_repr());
                    assert(scanned_source.disk_view.entries.dom()
                        == scanned_source.full_repr());
                    assert(scanned_source.disk_view.entries
                        .contains_key(addr));
                    assert(addresses_in_aus(summary).contains(addr));
                    assert(summary.contains(addr.au));
                    assert(scanned_source.get_summary().contains(addr.au)) by {
                        assert(crate::disk::GenericDisk_v::addrs_closed(
                            scanned_source.full_repr(),
                            scanned_source.get_summary(),
                        ));
                    }
                    assert(summaries.contains_key(
                        scanned_source.root.au,
                    ));
                    assert(summaries[scanned_source.root.au]
                        == scanned_source.get_summary());
                    if source.root.au != scanned_source.root.au {
                        assert(summary.disjoint(
                            scanned_source.get_summary(),
                        ));
                        assert(false);
                    }
                    assert(self.source_roots().contains(source.root));
                    assert(self.source_roots().contains(scanned_source.root));
                    if source.root != scanned_source.root {
                        assert(crate::disk::GenericDisk_v::
                            addrs_with_different_au(
                                source.root,
                                scanned_source.root,
                            ));
                        assert(false);
                    }
                    assert(source == scanned_source);
                    let selected_index = choose |i: int|
                        0 <= i < self.cursors@.len()
                        && self.cursors@[i].scanned@.contains(addr);
                    assert(self.scanned_nodes()[addr]
                        == self.cursors@[selected_index]
                            .source@.disk_view.entries[addr]);
                    assert(self.cursors@[selected_index]
                        .source@.disk_view.entries.contains_key(addr));
                    assert(self.cursors@[selected_index]
                        .source@.disk_view.entries[addr]
                        == source.disk_view.entries[addr]);
                }
                if source.disk_view.entries.contains_key(addr) {
                    assert(source.disk_view.entries.dom()
                        == source.full_repr());
                    assert(self.cursors@[index].scanned@
                        == source.full_repr());
                    assert(self.scanned_nodes().contains_key(addr));
                    assert(source.get_summary().contains(addr.au)) by {
                        assert(crate::disk::GenericDisk_v::addrs_closed(
                            source.full_repr(),
                            source.get_summary(),
                        ));
                    }
                    assert(addresses_in_aus(summary).contains(addr));
                    assert(restricted.contains_key(addr));
                    let selected_index = choose |i: int|
                        0 <= i < self.cursors@.len()
                        && self.cursors@[i].scanned@.contains(addr);
                    self.cursors@[selected_index].receipt_wf_ensures();
                    assert(self.cursors@[selected_index]
                        .source@.disk_view.entries.contains_key(addr));
                    assert(self.cursors@[selected_index]
                        .source@.disk_view.entries[addr]
                        == source.disk_view.entries[addr]);
                }
            }
        );
    }

    pub proof fn completed_receipt_valid(
        &self,
        summaries: Map<AU, Summary>,
    )
        requires
            self.wf(),
            self.scan_complete(),
            set_addrs_disjoint_aus(self.source_roots()),
            map_with_disjoint_values(summaries),
            forall |i: int| 0 <= i < self.cursors@.len() ==> {
                let source = (#[trigger] self.cursors@[i]).source@;
                &&& summaries.contains_key(source.root.au)
                &&& summaries[source.root.au] == source.get_summary()
            },
        ensures
            self.source_roots() == self.filter.target@.buffers.slice(
                self.filter.start as int,
                self.filter.end as int,
            ).addrs.to_set(),
            valid_loaded_sealed_branches(
                self.source_roots(),
                summaries,
                self.scanned_nodes(),
            ),
    {
        hide(compactor_source_disks_agree);
        let reads = self.scanned_nodes();
        self.source_roots_match_filter();
        assert forall |root: Address|
            #[trigger] self.source_roots().contains(root)
            implies {
                &&& summaries.contains_key(root.au)
                &&& valid_loaded_sealed_branch(
                    root,
                    summaries[root.au],
                    reads.restrict(addresses_in_aus(summaries[root.au])),
                )
            } by {
            let i = choose |i: int| 0 <= i < self.cursors@.len()
                && self.cursors@[i].source@.root == root;
            let source = self.cursors@[i].source@;
            self.completed_source_receipt(i, summaries);
            let restricted = reads.restrict(addresses_in_aus(
                summaries[root.au],
            ));
            assert(restricted == source.disk_view.entries);
            assert_maps_equal!(
                restricted.restrict(addresses_in_aus(summaries[root.au])),
                restricted,
                addr => {
                    if restricted.contains_key(addr) {
                        assert(source.get_summary().contains(addr.au)) by {
                            assert(crate::disk::GenericDisk_v::addrs_closed(
                                source.full_repr(),
                                source.get_summary(),
                            ));
                        }
                    }
                }
            );
            assert(loaded_sealed_branch(
                root,
                restricted.restrict(addresses_in_aus(summaries[root.au])),
            ) == source);
        }
        assert(reads.dom() == Set::new(|addr: Address| exists |root: Address|
            self.source_roots().contains(root)
            && loaded_sealed_branch(
                root,
                reads.restrict(addresses_in_aus(summaries[root.au])),
            ).disk_view.entries.contains_key(addr))) by {
            assert_sets_equal!(
                reads.dom(),
                Set::new(|addr: Address| exists |root: Address|
                    self.source_roots().contains(root)
                    && loaded_sealed_branch(
                        root,
                        reads.restrict(addresses_in_aus(
                            summaries[root.au],
                        )),
                    ).disk_view.entries.contains_key(addr)),
                addr => {
                    if reads.contains_key(addr) {
                        let i = choose |i: int|
                            0 <= i < self.cursors@.len()
                            && self.cursors@[i].scanned@.contains(addr);
                        let source = self.cursors@[i].source@;
                        self.cursors@[i].receipt_wf_ensures();
                        assert(self.cursors@[i].scanned@
                            == source.full_repr());
                        self.completed_source_receipt(i, summaries);
                        assert(self.source_roots().contains(source.root));
                        assert(reads.restrict(addresses_in_aus(
                            summaries[source.root.au],
                        )).contains_key(addr));
                    }
                }
            );
        }
    }

    proof fn completed_source_refines_receipt(
        &self,
        index: int,
        key: Key,
    )
        requires
            self.cursors@.len() == self.sources@.len(),
            0 <= index < self.cursors@.len(),
            self.cursors@[index].source@.valid_sealed_branch(),
            forall |candidate: Key|
                keyed_entries_contains(self.sources@[index], candidate)
                    <==> self.cursors@[index]
                        .source@.i().i().map.contains_key(candidate),
            forall |candidate: Key|
                keyed_entries_query(self.sources@[index], candidate)
                    == self.cursors@[index]
                        .source@.i().i().query(candidate),
            (crate::betree::LinkedBranch_v::DiskView::<Summary> {
                entries: self.scanned_nodes(),
            }).wf(),
            self.scanned_nodes().restrict(addresses_in_aus(
                self.cursors@[index].source@.get_summary(),
            )) == self.cursors@[index].source@.disk_view.entries,
        ensures ({
            let reads = self.scanned_nodes();
            let disk = BufferDisk::<BranchNode> { entries: reads };
            let root = self.cursors@[index].source@.root;
            &&& keyed_entries_contains(self.sources@[index], key)
                <==> disk.buffer_contains(root, key)
            &&& keyed_entries_query(self.sources@[index], key)
                == disk.query(root, key)
        }),
    {
        let reads = self.scanned_nodes();
        let disk = BufferDisk::<BranchNode> { entries: reads };
        let source = self.cursors@[index].source@;
        let root = source.root;
        let summary = source.get_summary();
        let bounded = reads.restrict(addresses_in_aus(summary));
        assert(bounded == source.disk_view.entries);
        assert(bounded.restrict(addresses_in_aus(summary)) == bounded) by {
            assert_maps_equal!(
                bounded.restrict(addresses_in_aus(summary)),
                bounded,
                addr => {}
            );
        }
        assert(valid_loaded_sealed_branch(
            root,
            summary,
            reads.restrict(addresses_in_aus(summary)),
        ));
        loaded_branch_in_forest_refines(root, summary, reads, key);
        assert(loaded_sealed_branch(root, bounded) == source);
        assert(reads.contains_key(root));
    }

    closed spec fn sources_refine_receipt(&self) -> bool {
        let reads = self.scanned_nodes();
        let disk = BufferDisk::<BranchNode> { entries: reads };
        forall |i: int, key: Key|
            #![trigger keyed_entries_contains(self.sources@[i], key)]
            #![trigger keyed_entries_query(self.sources@[i], key)]
            0 <= i < self.sources@.len() ==> {
            let root = self.cursors@[i].source@.root;
            &&& keyed_entries_contains(self.sources@[i], key)
                <==> disk.buffer_contains(root, key)
            &&& keyed_entries_query(self.sources@[i], key)
                == disk.query(root, key)
        }
    }

    proof fn establish_sources_refine_receipt(&self)
        requires
            self.cursors@.len() == self.sources@.len(),
            forall |i: int| 0 <= i < self.sources@.len()
                ==> {
                    let source = (#[trigger] self.cursors@[i]).source@;
                    &&& source.valid_sealed_branch()
                    &&& forall |key: Key|
                        keyed_entries_contains(self.sources@[i], key)
                            <==> source.i().i().map.contains_key(key)
                    &&& forall |key: Key|
                        keyed_entries_query(self.sources@[i], key)
                            == source.i().i().query(key)
                },
            (crate::betree::LinkedBranch_v::DiskView::<Summary> {
                entries: self.scanned_nodes(),
            }).wf(),
            forall |i: int| 0 <= i < self.cursors@.len()
                ==> self.scanned_nodes().restrict(addresses_in_aus(
                    (#[trigger] self.cursors@[i]).source@.get_summary(),
                )) == self.cursors@[i].source@.disk_view.entries,
        ensures self.sources_refine_receipt(),
    {
        hide(compactor_source_disks_agree);
        assert forall |i: int, key: Key|
            #![trigger keyed_entries_contains(self.sources@[i], key)]
            #![trigger keyed_entries_query(self.sources@[i], key)]
            0 <= i < self.sources@.len()
            implies {
                let reads = self.scanned_nodes();
                let disk = BufferDisk::<BranchNode> { entries: reads };
                let root = self.cursors@[i].source@.root;
                &&& keyed_entries_contains(self.sources@[i], key)
                    <==> disk.buffer_contains(root, key)
                &&& keyed_entries_query(self.sources@[i], key)
                    == disk.query(root, key)
            } by {
            self.completed_source_refines_receipt(i, key);
        }
        reveal(CompactorMergeCursor::sources_refine_receipt);
    }

    proof fn sources_refine_receipt_ensures(&self)
        requires self.sources_refine_receipt(),
        ensures forall |i: int, key: Key|
            #![trigger keyed_entries_contains(self.sources@[i], key)]
            #![trigger keyed_entries_query(self.sources@[i], key)]
            0 <= i < self.sources@.len()
            ==> {
                let reads = self.scanned_nodes();
                let disk = BufferDisk::<BranchNode> { entries: reads };
                let root = self.cursors@[i].source@.root;
                &&& keyed_entries_contains(self.sources@[i], key)
                    <==> disk.buffer_contains(root, key)
                &&& keyed_entries_query(self.sources@[i], key)
                    == disk.query(root, key)
            },
    {
        reveal(CompactorMergeCursor::sources_refine_receipt);
    }

    proof fn merge_sources_refines_buffer_query(
        &self,
        key: Key,
        index: int,
    )
        requires
            self.filter.wf(),
            self.cursor_sources_wf(),
            0 <= index <= self.sources@.len(),
            self.sources_refine_receipt(),
        ensures ({
            let reads = self.scanned_nodes();
            let disk = BufferDisk::<BranchNode> { entries: reads };
            let buffers = self.filter.target@.buffers.slice(
                self.filter.start as int,
                self.filter.end as int,
            );
            merge_source_messages(self.sources@, key, index)
                == disk.query_from(buffers, key, index)
        }),
        decreases self.sources@.len() - index,
    {
        self.sources_refine_receipt_ensures();
        let buffers = self.filter.target@.buffers.slice(
            self.filter.start as int,
            self.filter.end as int,
        );
        if index < self.sources@.len() {
            assert(index < self.cursors@.len());
            let root = self.cursors@[index].source@.root;
            assert(root == buffers.addrs[index]);
            self.merge_sources_refines_buffer_query(
                key,
                index + 1,
            );
        }
    }

    /* The original monolithic composition is retained for comparison. The
     * live proof below keeps source, filter, and output obligations modular.
    pub proof fn completed_output_refines_receipt(
        &self,
        summaries: Map<AU, Summary>,
    )
        requires
            self.wf(),
            self.exhausted(),
            self.scan_complete(),
            set_addrs_disjoint_aus(self.source_roots()),
            map_with_disjoint_values(summaries),
            forall |i: int| 0 <= i < self.cursors@.len() ==> {
                let source = (#[trigger] self.cursors@[i]).source@;
                &&& summaries.contains_key(source.root.au)
                &&& summaries[source.root.au] == source.get_summary()
            },
        ensures ({
            let reads = self.scanned_nodes();
            let disk = BufferDisk::<BranchNode> { entries: reads };
            let target = self.filter.target@;
            &&& forall |key: Key|
                keyed_entries_contains(self.output@, key)
                    <==> disk.valid_compact_key_domain(
                        target,
                        self.filter.start as nat,
                        self.filter.end as nat,
                        key,
                    )
            &&& forall |key: Key|
                keyed_entries_contains(self.output@, key)
                    ==> keyed_entries_query(self.output@, key)
                        == disk.compact_key_value(
                            target,
                            self.filter.start as nat,
                            self.filter.end as nat,
                            key,
                        )
        }),
    {
        self.exhausted_output_complete();
        self.source_streams_refine();
        self.completed_receipt_valid(summaries);
        let reads = self.scanned_nodes();
        loaded_branch_forest_wf(
            self.source_roots(),
            summaries,
            reads,
        );
        assert forall |i: int| 0 <= i < self.cursors@.len()
            implies reads.restrict(addresses_in_aus(
                (#[trigger] self.cursors@[i]).source@.get_summary(),
            )) == self.cursors@[i].source@.disk_view.entries by {
            self.completed_source_receipt(i, summaries);
        }
        self.establish_sources_refine_receipt();
        self.sources_refine_receipt_ensures();
        let disk = BufferDisk::<BranchNode> { entries: reads };
        let target = self.filter.target@;
        let buffers = target.buffers.slice(
            self.filter.start as int,
            self.filter.end as int,
        );
        let offset_map = target.make_offset_map().decrement(
            self.filter.start as nat,
        );
        assert(buffers.addrs.len() == self.sources@.len());
        assert forall |key: Key|
            compact_sources_contain(
                &self.filter,
                self.sources@,
                key,
            ) <==> disk.valid_compact_key_domain(
                target,
                self.filter.start as nat,
                self.filter.end as nat,
                key,
            ) by {
            let source_start = compact_source_start(&self.filter, key);
            if compact_sources_contain(
                &self.filter,
                self.sources@,
                key,
            ) {
                let i = choose |i: int|
                    source_start as int <= i < self.sources@.len()
                    && keyed_entries_contains(self.sources@[i], key);
                assert(self.cursors@[i].source@.root
                    == buffers.addrs[i]);
                assert(disk.buffer_contains(buffers.addrs[i], key));
                assert(disk.key_in_buffer_filtered(
                    buffers,
                    offset_map,
                    0,
                    key,
                    i,
                ));
            }
            if disk.valid_compact_key_domain(
                target,
                self.filter.start as nat,
                self.filter.end as nat,
                key,
            ) {
                let i = choose |i: int| #[trigger]
                    disk.key_in_buffer_filtered(
                        buffers,
                        offset_map,
                        0,
                        key,
                        i,
                    );
                assert(0 <= i < self.sources@.len());
                assert(source_start <= i);
                assert(self.cursors@[i].source@.root
                    == buffers.addrs[i]);
                assert(keyed_entries_contains(self.sources@[i], key));
            }
        }
        assert forall |key: Key|
            keyed_entries_contains(self.output@, key)
                <==> disk.valid_compact_key_domain(
                    target,
                    self.filter.start as nat,
                    self.filter.end as nat,
                    key,
                ) by {
            assert(compact_sources_contain(
                &self.filter,
                self.sources@,
                key,
            ) <==> keyed_entries_contains(self.output@, key));
        }
        assert forall |key: Key|
            keyed_entries_contains(self.output@, key)
                implies keyed_entries_query(self.output@, key)
                    == disk.compact_key_value(
                        target,
                        self.filter.start as nat,
                        self.filter.end as nat,
                        key,
                    ) by {
            let output_idx = choose |i: int| 0 <= i < self.output@.len()
                && self.output@[i].key == key;
            strictly_sorted_key_unique(
                self.output@,
                key,
                output_idx,
                choose |i: int| 0 <= i < self.output@.len()
                    && self.output@[i].key == key,
            );
            keyed_entries_query_index(self.output@, output_idx);
            assert(self.output@[output_idx].message
                == compact_sources_message(
                    &self.filter,
                    self.sources@,
                    key,
                ));
            let source_start = compact_source_start(&self.filter, key);
            self.merge_sources_refines_buffer_query(
                key,
                source_start as int,
            );
            assert(source_start == if target.flushed_ofs(key)
                <= self.filter.start as nat {
                0
            } else {
                target.flushed_ofs(key) - self.filter.start as nat
            });
        }
    }
    */

    proof fn establish_completed_sources_refine_receipt(
        &self,
        summaries: Map<AU, Summary>,
    )
        requires
            self.wf(),
            self.scan_complete(),
            set_addrs_disjoint_aus(self.source_roots()),
            map_with_disjoint_values(summaries),
            forall |i: int| 0 <= i < self.cursors@.len() ==> {
                let source = (#[trigger] self.cursors@[i]).source@;
                &&& summaries.contains_key(source.root.au)
                &&& summaries[source.root.au] == source.get_summary()
            },
        ensures self.sources_refine_receipt(),
    {
        self.source_streams_refine();
        self.completed_receipt_valid(summaries);
        let reads = self.scanned_nodes();
        loaded_branch_forest_wf(
            self.source_roots(),
            summaries,
            reads,
        );
        assert forall |i: int| 0 <= i < self.cursors@.len()
            implies reads.restrict(addresses_in_aus(
                (#[trigger] self.cursors@[i]).source@.get_summary(),
            )) == self.cursors@[i].source@.disk_view.entries by {
            self.completed_source_receipt(i, summaries);
        }
        self.establish_sources_refine_receipt();
    }

    proof fn compact_source_domain_refines_receipt(&self)
        requires
            self.wf(),
            self.sources_refine_receipt(),
        ensures ({
            let reads = self.scanned_nodes();
            let disk = BufferDisk::<BranchNode> { entries: reads };
            let target = self.filter.target@;
            forall |key: Key|
                compact_sources_contain(
                    &self.filter,
                    self.sources@,
                    key,
                ) <==> disk.valid_compact_key_domain(
                    target,
                    self.filter.start as nat,
                    self.filter.end as nat,
                    key,
                )
        }),
    {
        self.sources_refine_receipt_ensures();
        let reads = self.scanned_nodes();
        let disk = BufferDisk::<BranchNode> { entries: reads };
        let target = self.filter.target@;
        let buffers = target.buffers.slice(
            self.filter.start as int,
            self.filter.end as int,
        );
        let offset_map = target.make_offset_map().decrement(
            self.filter.start as nat,
        );
        assert(buffers.addrs.len() == self.sources@.len());
        assert forall |key: Key|
            compact_sources_contain(
                &self.filter,
                self.sources@,
                key,
            ) <==> disk.valid_compact_key_domain(
                target,
                self.filter.start as nat,
                self.filter.end as nat,
                key,
            ) by {
            let source_start = compact_source_start(&self.filter, key);
            if compact_sources_contain(
                &self.filter,
                self.sources@,
                key,
            ) {
                let i = choose |i: int|
                    source_start as int <= i < self.sources@.len()
                    && keyed_entries_contains(self.sources@[i], key);
                assert(self.cursors@[i].source@.root
                    == buffers.addrs[i]);
                assert(disk.buffer_contains(buffers.addrs[i], key));
                assert(disk.key_in_buffer_filtered(
                    buffers,
                    offset_map,
                    0,
                    key,
                    i,
                ));
            }
            if disk.valid_compact_key_domain(
                target,
                self.filter.start as nat,
                self.filter.end as nat,
                key,
            ) {
                let i = choose |i: int| #[trigger]
                    disk.key_in_buffer_filtered(
                        buffers,
                        offset_map,
                        0,
                        key,
                        i,
                    );
                assert(0 <= i < self.sources@.len());
                assert(source_start <= i);
                assert(self.cursors@[i].source@.root
                    == buffers.addrs[i]);
                assert(keyed_entries_contains(self.sources@[i], key));
            }
        }
    }

    proof fn compact_source_values_refine_receipt(&self)
        requires
            self.wf(),
            self.sources_refine_receipt(),
        ensures ({
            let reads = self.scanned_nodes();
            let disk = BufferDisk::<BranchNode> { entries: reads };
            let target = self.filter.target@;
            forall |key: Key|
                compact_sources_contain(
                    &self.filter,
                    self.sources@,
                    key,
                ) ==> compact_sources_message(
                    &self.filter,
                    self.sources@,
                    key,
                ) == disk.compact_key_value(
                    target,
                    self.filter.start as nat,
                    self.filter.end as nat,
                    key,
                )
        }),
    {
        assert forall |key: Key|
            compact_sources_contain(
                &self.filter,
                self.sources@,
                key,
            ) implies compact_sources_message(
                &self.filter,
                self.sources@,
                key,
            ) == BufferDisk::<BranchNode> {
                entries: self.scanned_nodes(),
            }.compact_key_value(
                self.filter.target@,
                self.filter.start as nat,
                self.filter.end as nat,
                key,
            ) by {
            let source_start = compact_source_start(&self.filter, key);
            self.merge_sources_refines_buffer_query(
                key,
                source_start as int,
            );
            assert(source_start == if self.filter.target@.flushed_ofs(key)
                <= self.filter.start as nat {
                0
            } else {
                self.filter.target@.flushed_ofs(key)
                    - self.filter.start as nat
            });
        }
    }

    proof fn completed_output_refines_sources(&self)
        requires
            self.wf(),
            self.exhausted(),
        ensures
            forall |key: Key|
                keyed_entries_contains(self.output@, key)
                    <==> compact_sources_contain(
                        &self.filter,
                        self.sources@,
                        key,
                    ),
            forall |key: Key|
                keyed_entries_contains(self.output@, key)
                    ==> keyed_entries_query(self.output@, key)
                        == compact_sources_message(
                            &self.filter,
                            self.sources@,
                            key,
                        ),
    {
        self.exhausted_output_complete();
        assert forall |key: Key|
            keyed_entries_contains(self.output@, key)
                implies keyed_entries_query(self.output@, key)
                    == compact_sources_message(
                        &self.filter,
                        self.sources@,
                        key,
                    ) by {
            let output_idx = choose |i: int| 0 <= i < self.output@.len()
                && self.output@[i].key == key;
            keyed_entries_query_index(self.output@, output_idx);
            assert(self.output@[output_idx].message
                == compact_sources_message(
                    &self.filter,
                    self.sources@,
                    key,
                ));
        }
    }

    pub proof fn completed_output_refines_receipt(
        &self,
        summaries: Map<AU, Summary>,
    )
        requires
            self.wf(),
            self.exhausted(),
            self.scan_complete(),
            set_addrs_disjoint_aus(self.source_roots()),
            map_with_disjoint_values(summaries),
            forall |i: int| 0 <= i < self.cursors@.len() ==> {
                let source = (#[trigger] self.cursors@[i]).source@;
                &&& summaries.contains_key(source.root.au)
                &&& summaries[source.root.au] == source.get_summary()
            },
        ensures ({
            let reads = self.scanned_nodes();
            let disk = BufferDisk::<BranchNode> { entries: reads };
            let target = self.filter.target@;
            &&& forall |key: Key|
                keyed_entries_contains(self.output@, key)
                    <==> disk.valid_compact_key_domain(
                        target,
                        self.filter.start as nat,
                        self.filter.end as nat,
                        key,
                    )
            &&& forall |key: Key|
                keyed_entries_contains(self.output@, key)
                    ==> keyed_entries_query(self.output@, key)
                        == disk.compact_key_value(
                            target,
                            self.filter.start as nat,
                            self.filter.end as nat,
                            key,
                        )
        }),
    {
        self.establish_completed_sources_refine_receipt(summaries);
        self.completed_output_refines_sources();
        self.compact_source_domain_refines_receipt();
        self.compact_source_values_refine_receipt();
    }

    pub fn new(
        cursors: Vec<BranchScanCursor>,
        filter: CompactionFilterImpl,
    ) -> (out: Self)
        requires
            filter.wf(),
            cursors@.len() == filter.end - filter.start,
            forall |i: int| 0 <= i < cursors@.len() ==> {
                &&& (#[trigger] cursors@[i]).wf()
                &&& cursors@[i].receipt_wf()
                &&& cursors@[i].emitted@.len() == 0
                &&& keyed_entries_strictly_sorted(
                    cursors@[i].remaining(),
                )
                &&& cursors@[i].source@.root
                    == filter.target@.buffers.addrs[
                        filter.start as int + i]
            },
            compactor_source_disks_agree(cursors@),
            forall |i: int| 0 <= i < cursors@.len()
                ==> (#[trigger] cursors@[i]).scanned@.is_empty(),
        ensures
            out.wf(),
            out.cursors@ == cursors@,
            out.filter == filter,
            out.output@.len() == 0,
            out.scanned_nodes().is_empty(),
    {
        let ghost sources = Seq::new(
            cursors@.len(),
            |i: int| cursors@[i].remaining(),
        );
        let out = Self {
            cursors,
            filter,
            frontier: None,
            sources: Ghost(sources),
            output: Ghost(Seq::empty()),
        };
        proof {
            assert(output_entries_valid(
                &out.filter,
                out.sources@,
                out.output@,
            ));
            assert(out.wf());
        }
        out
    }

    fn key_lt(left: Key, right: Key) -> (out: bool)
        ensures out == Key::lt(left, right),
    {
        left.0 < right.0
    }

    fn key_eq(left: Key, right: Key) -> (out: bool)
        ensures out == (left == right),
    {
        left.0 == right.0
    }

    fn minimum_key(&self) -> (out: Option<Key>)
        requires
            self.wf(),
            self.heads_ready(),
        ensures
            match out {
                Some(key) => {
                    &&& exists |i: int|
                        0 <= i < self.cursors@.len()
                        && self.cursors@[i].remaining().len() > 0
                        && self.cursors@[i].remaining()[0].key == key
                    &&& forall |i: int|
                        0 <= i < self.cursors@.len()
                        && (#[trigger] self.cursors@[i]).remaining().len() > 0
                        ==> Key::lte(
                            key,
                            self.cursors@[i].remaining()[0].key,
                        )
                },
                None => forall |i: int|
                    0 <= i < self.cursors@.len()
                    ==> (#[trigger] self.cursors@[i]).remaining().len() == 0,
            },
    {
        let mut minimum: Option<Key> = None;
        let mut index = 0usize;
        while index < self.cursors.len()
            invariant
                index <= self.cursors.len(),
                self.wf(),
                self.heads_ready(),
                match minimum {
                    Some(key) => {
                        &&& exists |i: int|
                            0 <= i < index
                            && self.cursors@[i].remaining().len() > 0
                            && self.cursors@[i].remaining()[0].key == key
                        &&& forall |i: int|
                            0 <= i < index
                            && (#[trigger] self.cursors@[i]).remaining().len() > 0
                            ==> Key::lte(
                                key,
                                self.cursors@[i].remaining()[0].key,
                            )
                    },
                    None => forall |i: int|
                        0 <= i < index
                        ==> (#[trigger] self.cursors@[i]).remaining().len() == 0,
                },
            decreases self.cursors.len() - index,
        {
            let item = self.cursors[index].peek();
            match item {
                Some(item) => {
                    minimum = match minimum {
                        Some(old_min) => {
                            if Self::key_lt(item.key, old_min) {
                                proof {
                                    assert forall |i: int|
                                        0 <= i < index
                                        && (#[trigger] self.cursors@[i])
                                            .remaining().len() > 0
                                        implies Key::lte(
                                            item.key,
                                            self.cursors@[i]
                                                .remaining()[0].key,
                                        ) by {
                                        key_lt_lte_transitive(
                                            item.key,
                                            old_min,
                                            self.cursors@[i]
                                                .remaining()[0].key,
                                        );
                                    }
                                }
                                Some(item.key)
                            } else {
                                proof {
                                    key_not_lt_reverse(item.key, old_min);
                                }
                                Some(old_min)
                            }
                        },
                        None => Some(item.key),
                    };
                },
                None => {
                    proof {
                        assert(self.cursors@[index as int]
                            .current_leaf is None);
                        assert(self.cursors@[index as int]
                            .remaining().len() == 0);
                    }
                },
            }
            index += 1;
        }
        minimum
    }

    proof fn exhausted_output_complete(&self)
        requires
            self.wf(),
            forall |i: int| 0 <= i < self.cursors@.len()
                ==> (#[trigger] self.cursors@[i]).remaining().len() == 0,
        ensures
            forall |key: Key|
                compact_sources_contain(
                    &self.filter,
                    self.sources@,
                    key,
                ) <==> keyed_entries_contains(self.output@, key),
    {
        assert forall |key: Key|
            keyed_entries_contains(self.output@, key)
            implies compact_sources_contain(
                &self.filter,
                self.sources@,
                key,
            ) by {
            let j = choose |j: int| 0 <= j < self.output@.len()
                && self.output@[j].key == key;
            assert(compact_sources_contain(
                &self.filter,
                self.sources@,
                self.output@[j].key,
            ));
        }
        assert forall |key: Key|
            compact_sources_contain(
                &self.filter,
                self.sources@,
                key,
            ) implies keyed_entries_contains(self.output@, key) by {
            let start = compact_source_start(&self.filter, key);
            let i = choose |i: int|
                start as int <= i < self.sources@.len()
                && keyed_entries_contains(self.sources@[i], key);
            let j = choose |j: int| 0 <= j < self.sources@[i].len()
                && self.sources@[i][j].key == key;
            assert(0 <= i < self.cursors@.len());
            assert(self.cursors@[i].remaining().len() == 0);
            assert((self.cursors@[i].emitted@
                + self.cursors@[i].remaining()).len()
                == self.sources@[i].len());
            assert(self.cursors@[i].emitted@.len()
                == self.sources@[i].len());
            seq_ext_equal_index(
                self.cursors@[i].emitted@
                    + self.cursors@[i].remaining(),
                self.sources@[i],
                j,
            );
            assert((self.cursors@[i].emitted@
                + self.cursors@[i].remaining())[j]
                == self.cursors@[i].emitted@[j]);
            assert(self.cursors@[i].emitted@[j].key == key);
            assert(keyed_entries_contains(
                self.cursors@[i].emitted@,
                key,
            ));
            assert(keyed_entries_contains(self.output@, key));
        }
    }

    proof fn establish_next_key_queries(&self, key: Key)
        requires
            self.wf(),
            self.heads_ready(),
            exists |i: int|
                0 <= i < self.cursors@.len()
                && self.cursors@[i].remaining().len() > 0
                && self.cursors@[i].remaining()[0].key == key,
            forall |i: int|
                0 <= i < self.cursors@.len()
                && (#[trigger] self.cursors@[i]).remaining().len() > 0
                ==> Key::lte(
                    key,
                    self.cursors@[i].remaining()[0].key,
                ),
        ensures
            forall |i: int| 0 <= i < self.cursors@.len()
                ==> {
                    let suffix = (#[trigger] self.cursors@[i]).remaining();
                    &&& (keyed_entries_contains(self.sources@[i], key)
                        <==> suffix.len() > 0
                            && suffix[0].key == key)
                    &&& keyed_entries_query(self.sources@[i], key)
                        == if suffix.len() > 0
                            && suffix[0].key == key {
                            suffix[0].message
                        } else {
                            Message::Update { delta: Delta(0) }
                        }
                },
    {
        let witness = choose |i: int|
            0 <= i < self.cursors@.len()
            && self.cursors@[i].remaining().len() > 0
            && self.cursors@[i].remaining()[0].key == key;
        match self.frontier {
            Some(frontier) => {
                assert(Key::lt(frontier, key));
            },
            None => {},
        }
        assert forall |i: int| 0 <= i < self.cursors@.len()
            implies {
                let suffix = (#[trigger] self.cursors@[i]).remaining();
                &&& (keyed_entries_contains(self.sources@[i], key)
                    <==> suffix.len() > 0
                        && suffix[0].key == key)
                &&& keyed_entries_query(self.sources@[i], key)
                    == if suffix.len() > 0
                        && suffix[0].key == key {
                        suffix[0].message
                    } else {
                        Message::Update { delta: Delta(0) }
                    }
            } by {
            let prefix = self.cursors@[i].emitted@;
            let suffix = self.cursors@[i].remaining();
            assert forall |j: int| 0 <= j < prefix.len()
                implies Key::lt((#[trigger] prefix[j]).key, key) by {
                match self.frontier {
                    Some(frontier) => {
                        key_lte_lt_transitive(
                            prefix[j].key,
                            frontier,
                            key,
                        );
                    },
                    None => {
                        assert(prefix.len() == 0);
                        assert(false);
                    },
                }
            }
            assert((prefix + suffix).len()
                == self.sources@[i].len());
            sorted_cut_query_lemma(
                self.sources@[i],
                prefix,
                suffix,
                key,
            );
        }
    }

    fn scan_cursor_step(
        &mut self,
        cache: &mut FracCacheImpl,
        index: usize,
    ) -> (out: BranchScanStepResult)
        requires
            old(self).wf(),
            old(cache).wf(),
            old(self).cache_inv(old(cache)@),
            index < old(self).cursors.len(),
        ensures
            self.wf(),
            self.filter == old(self).filter,
            cache.wf(),
            self.cache_inv(cache@),
            cache.valid_load_handles_preserved(*old(cache)),
            forall |addr: Address, raw: RawPage|
                old(cache)@.valid_read(addr, raw)
                ==> cache@.valid_read(addr, raw),
            forall |addr: Address, raw: RawPage|
                cache@.valid_read(addr, raw)
                ==> old(cache)@.valid_read(addr, raw),
            self.filter == old(self).filter,
            self.frontier == old(self).frontier,
            self.sources@ == old(self).sources@,
            self.output@ == old(self).output@,
            self.source_aus() == old(self).source_aus(),
            self.cursors@.len() == old(self).cursors@.len(),
            forall |i: int| 0 <= i < self.cursors@.len()
                ==> (#[trigger] self.cursors@[i]).source@
                    == old(self).cursors@[i].source@,
            match out {
                BranchScanStepResult::Advanced { reads } => {
                    &&& cache@ == old(cache)@
                    &&& reads@.dom().finite()
                    &&& reads@.len() == 1
                    &&& self.scanned_nodes()
                        == old(self).scanned_nodes().union_prefer_right(
                            to_branch_nodes(reads@),
                        )
                    &&& reads@.dom() <= addresses_in_aus(
                        self.cursors@[index as int].source@.get_summary(),
                    )
                    &&& forall |addr: Address|
                        #[trigger] reads@.contains_key(addr) ==> {
                            &&& self.cursors@[index as int]
                                .source@.disk_view.entries.contains_key(addr)
                            &&& crate::marshalling::IBranchNodeFormat_v::
                                raw_page_to_branch_node(reads@[addr])
                                == self.cursors@[index as int]
                                    .source@.disk_view.entries[addr]
                        }
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        Cache::Label::Access {
                            reads: reads@,
                            writes: Map::empty(),
                        },
                    )
                },
                BranchScanStepResult::NeedCacheLoad { addr, handle } => {
                    &&& self.same_logical_state(old(self))
                    &&& old(self).cursors@[index as int]
                        .source@.get_summary().contains(addr@.au)
                    &&& cache.entry_fetched(&addr)
                    &&& cache.valid_load_handle(&addr, handle)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        crate::implementation::FracCacheImpl_v::cache_load_label(
                            &addr,
                        ),
                    )
                },
                BranchScanStepResult::ItemReady => {
                    &&& self.same_logical_state(old(self))
                    &&& cache@ == old(cache)@
                    &&& self.cursors@[index as int].current_leaf is Some
                },
                BranchScanStepResult::Done => {
                    &&& self.same_logical_state(old(self))
                    &&& cache@ == old(cache)@
                    &&& self.cursors@[index as int].remaining().len() == 0
                    &&& self.cursors@[index as int].scanned@
                        == self.cursors@[index as int].source@.full_repr()
                },
                BranchScanStepResult::CacheFull
                | BranchScanStepResult::Blocked
                | BranchScanStepResult::InvalidPage => {
                    &&& self.same_logical_state(old(self))
                    &&& cache@ == old(cache)@
                },
            },
    {
        let ghost self0 = *self;
        let ghost cache0 = *cache;
        let ghost old_cursors = self.cursors@;
        let mut cursor = self.cursors.remove(index);
        let result = cursor.step(cache);
        proof {
            assert forall |addr: Address, raw: RawPage|
                cache0@.valid_read(addr, raw)
                implies cache@.valid_read(addr, raw) by {}
        }
        self.cursors.insert(index, cursor);
        proof {
            assert(self.cursors@.len() == old_cursors.len());
            assert forall |i: int| 0 <= i < self.cursors@.len()
                && i != index as int
                implies self.cursors@[i] == old_cursors[i] by { }
            assert forall |i: int| 0 <= i < self.cursors@.len()
                implies {
                    &&& (#[trigger] self.cursors@[i]).wf()
                    &&& self.cursors@[i].receipt_wf()
                    &&& keyed_entries_strictly_sorted(self.sources@[i])
                    &&& keyed_entries_strictly_sorted(
                        self.cursors@[i].remaining(),
                    )
                    &&& self.cursors@[i].emitted@
                        + self.cursors@[i].remaining()
                        =~= self.sources@[i]
                    &&& self.cursors@[i].source@.root
                        == self.filter.target@.buffers.addrs[
                            self.filter.start as int + i]
                } by {
                if i == index as int {
                    assert(self.cursors@[i].source@
                        == old_cursors[i].source@);
                    assert(self.cursors@[i].ranking@
                        == old_cursors[i].ranking@);
                    assert(self.cursors@[i].emitted@
                        == old_cursors[i].emitted@);
                    assert(self.cursors@[i].emitted@
                        + self.cursors@[i].remaining()
                        =~= pivot_branch_entries(
                            self.cursors@[i].source@.i_internal(
                                self.cursors@[i].ranking@,
                            ),
                            self.cursors@[i].ranking@[
                                self.cursors@[i].source@.root] + 1,
                        ));
                    assert(old_cursors[i].emitted@
                        + old_cursors[i].remaining()
                        =~= pivot_branch_entries(
                            old_cursors[i].source@.i_internal(
                                old_cursors[i].ranking@,
                            ),
                            old_cursors[i].ranking@[
                                old_cursors[i].source@.root] + 1,
                        ));
                    assert((self.cursors@[i].emitted@
                        + self.cursors@[i].remaining()).len()
                        == self.sources@[i].len());
                    assert((old_cursors[i].emitted@
                        + old_cursors[i].remaining()).len()
                        == self.sources@[i].len());
                    assert(self.cursors@[i].remaining().len()
                        == old_cursors[i].remaining().len());
                    seq_cancel_left(
                        self.cursors@[i].emitted@,
                        self.cursors@[i].remaining(),
                        old_cursors[i].remaining(),
                    );
                    assert(self.cursors@[i].remaining()
                        == old_cursors[i].remaining());
                    assert(keyed_entries_strictly_sorted(
                        self.cursors@[i].remaining(),
                    ));
                }
            }
            assert forall |i: int| 0 <= i < self.cursors@.len()
                implies (#[trigger] self.cursors@[i]).remaining()
                    == old_cursors[i].remaining() by {
                if i == index as int {
                    assert(self.cursors@[i].emitted@
                        == old_cursors[i].emitted@);
                    assert(self.cursors@[i].emitted@
                        + self.cursors@[i].remaining()
                        =~= self.sources@[i]);
                    assert(old_cursors[i].emitted@
                        + old_cursors[i].remaining()
                        =~= self.sources@[i]);
                    assert(self.cursors@[i].remaining().len()
                        == old_cursors[i].remaining().len());
                    seq_cancel_left(
                        self.cursors@[i].emitted@,
                        self.cursors@[i].remaining(),
                        old_cursors[i].remaining(),
                    );
                }
            }
            assert forall |i: int, j: int|
                0 <= i < self.cursors@.len()
                && 0 <= j < self.cursors@[i].remaining().len()
                implies match self.frontier {
                    Some(frontier) => Key::lt(
                        frontier,
                        (#[trigger] self.cursors@[i].remaining()[j]).key,
                    ),
                    None => true,
                } by {
                if i == index as int {
                    assert(self.cursors@[i].remaining()
                        == old_cursors[i].remaining());
                    assert(self.cursors@[i].remaining()[j]
                        == old_cursors[i].remaining()[j]);
                }
            }
            compactor_source_disks_agree_preserved(
                old_cursors,
                self.cursors@,
            );
            assert(self.wf());
            assert forall |i: int| 0 <= i < self.cursors@.len()
                implies (#[trigger] self.cursors@[i]).cache_inv(cache@) by {
                if i == index as int {
                } else {
                    crate::implementation::BranchScanCursorImpl_v::cached_branch_scan_valid_preserved(
                        cache0@,
                        cache@,
                        self.cursors@[i].source@,
                    );
                }
            }
            assert(self.cache_inv(cache@));
            self.source_aus_extensional(&self0);
            match result {
                BranchScanStepResult::Advanced { reads } => {
                    assert forall |addr: Address|
                        #[trigger] reads@.contains_key(addr)
                        implies to_branch_nodes(reads@)[addr]
                            == self.cursors@[index as int]
                                .source@.disk_view.entries[addr] by {
                        assert(crate::marshalling::IBranchNodeFormat_v::
                            raw_page_to_branch_node(reads@[addr])
                            == self.cursors@[index as int]
                                .source@.disk_view.entries[addr]);
                    }
                    compactor_scanned_nodes_update(
                        old_cursors,
                        self.cursors@,
                        index as int,
                        reads@,
                    );
                    assert forall |addr: Address|
                        #[trigger] reads@.contains_key(addr)
                        implies addresses_in_aus(
                            self.cursors@[index as int]
                                .source@.get_summary(),
                        ).contains(addr) by {
                        assert(self.cursors@[index as int]
                            .source@.disk_view.entries.contains_key(addr));
                        assert(self.cursors@[index as int]
                            .source@.full_repr().contains(addr));
                        assert(self.cursors@[index as int]
                            .source@.get_summary().contains(addr.au));
                    }
                },
                _ => {
                    assert_seqs_equal!(self.cursors@, old_cursors, i => {
                        if i == index as int {
                        }
                    });
                    assert(self.same_logical_state(&self0));
                },
            }
        }
        result
    }

    fn advance_cursor_at(&mut self, index: usize)
        requires
            old(self).cursor_sources_wf(),
            index < old(self).cursors.len(),
            old(self).cursors@[index as int].current_leaf is Some,
        ensures
            self.cursor_sources_wf(),
            self.filter == old(self).filter,
            self.frontier == old(self).frontier,
            self.sources@ == old(self).sources@,
            self.output@ == old(self).output@,
            self.source_aus() == old(self).source_aus(),
            self.scanned_nodes() == old(self).scanned_nodes(),
            self.cursors@.len() == old(self).cursors@.len(),
            forall |i: int| 0 <= i < self.cursors@.len()
                && i != index as int
                ==> (#[trigger] self.cursors@[i]) == old(self).cursors@[i],
            forall |i: int| 0 <= i < self.cursors@.len()
                ==> (#[trigger] self.cursors@[i]).source@
                    == old(self).cursors@[i].source@,
            forall |i: int| 0 <= i < self.cursors@.len()
                ==> (#[trigger] self.cursors@[i]).scanned@
                    == old(self).cursors@[i].scanned@,
            self.cursors@[index as int].emitted@
                == old(self).cursors@[index as int].emitted@.push(
                    old(self).cursors@[index as int].remaining()[0],
                ),
            self.cursors@[index as int].remaining()
                == old(self).cursors@[index as int].remaining().drop_first(),
    {
        let ghost old_cursors = self.cursors@;
        let ghost old_remaining = old_cursors[index as int].remaining();
        let ghost old_emitted = old_cursors[index as int].emitted@;
        let mut cursor = self.cursors.remove(index);
        let advanced = cursor.advance();
        self.cursors.insert(index, cursor);
        proof {
            assert(advanced);
            keyed_entries_drop_first_sorted(old_remaining);
            push_head_reassembles(old_emitted, old_remaining);
            assert forall |i: int| 0 <= i < self.cursors@.len()
                implies {
                    &&& (#[trigger] self.cursors@[i]).wf()
                    &&& self.cursors@[i].receipt_wf()
                    &&& keyed_entries_strictly_sorted(self.sources@[i])
                    &&& keyed_entries_strictly_sorted(
                        self.cursors@[i].remaining(),
                    )
                    &&& self.cursors@[i].emitted@
                        + self.cursors@[i].remaining()
                        =~= self.sources@[i]
                    &&& self.cursors@[i].source@.root
                        == self.filter.target@.buffers.addrs[
                            self.filter.start as int + i]
                } by {
                if i == index as int {
                    assert(self.cursors@[i].source@
                        == old_cursors[i].source@);
                    assert(self.cursors@[i].remaining()
                        == old_remaining.drop_first());
                    assert(self.cursors@[i].emitted@
                        == old_emitted.push(old_remaining[0]));
                    assert(self.cursors@[i].emitted@
                        + self.cursors@[i].remaining()
                        =~= old_emitted + old_remaining);
                    assert(old_emitted + old_remaining
                        =~= self.sources@[i]);
                }
            }
            compactor_source_disks_agree_preserved(
                old_cursors,
                self.cursors@,
            );
            assert(self.cursor_sources_wf());
            self.source_aus_extensional(old(self));
            assert forall |i: int| 0 <= i < self.cursors@.len()
                implies {
                    &&& (#[trigger] self.cursors@[i]).source@
                        == old_cursors[i].source@
                    &&& self.cursors@[i].scanned@
                        == old_cursors[i].scanned@
                } by {
                if i == index as int {
                    assert(self.cursors@[i].scanned@
                        == old_cursors[i].scanned@);
                }
            }
            compactor_scanned_nodes_extensional(
                self.cursors@,
                old_cursors,
            );
        }
    }

    fn advance_minimum_sources(&mut self, key: Key)
        requires
            old(self).wf(),
            old(self).heads_ready(),
            exists |i: int|
                0 <= i < old(self).cursors@.len()
                && old(self).cursors@[i].remaining().len() > 0
                && old(self).cursors@[i].remaining()[0].key == key,
            forall |i: int|
                0 <= i < old(self).cursors@.len()
                && (#[trigger] old(self).cursors@[i]).remaining().len() > 0
                ==> Key::lte(
                    key,
                    old(self).cursors@[i].remaining()[0].key,
                ),
        ensures
            self.cursor_sources_wf(),
            self.filter == old(self).filter,
            self.frontier == old(self).frontier,
            self.sources@ == old(self).sources@,
            self.output@ == old(self).output@,
            self.source_aus() == old(self).source_aus(),
            self.scanned_nodes() == old(self).scanned_nodes(),
            self.cursors@.len() == old(self).cursors@.len(),
            forall |i: int| 0 <= i < self.cursors@.len()
                ==> (#[trigger] self.cursors@[i]).source@
                    == old(self).cursors@[i].source@,
            forall |i: int| 0 <= i < self.cursors@.len()
                ==> (#[trigger] self.cursors@[i]).scanned@
                    == old(self).cursors@[i].scanned@,
            forall |i: int, j: int|
                0 <= i < self.cursors@.len()
                && 0 <= j < self.cursors@[i].emitted@.len()
                ==> Key::lte(
                    (#[trigger] self.cursors@[i].emitted@[j]).key,
                    key,
                ),
            forall |i: int, j: int|
                0 <= i < self.cursors@.len()
                && 0 <= j < self.cursors@[i].remaining().len()
                ==> Key::lt(
                    key,
                    (#[trigger] self.cursors@[i].remaining()[j]).key,
                ),
            forall |i: int| 0 <= i < self.cursors@.len()
                ==> {
                    let before = #[trigger] old(self).cursors@[i];
                    self.cursors@[i].emitted@ == before.emitted@
                        || {
                            &&& before.remaining().len() > 0
                            &&& before.remaining()[0].key == key
                            &&& self.cursors@[i].emitted@
                                == before.emitted@.push(
                                    before.remaining()[0],
                                )
                        }
                },
    {
        let ghost self0 = *self;
        let ghost cursors_before = self.cursors@;
        proof {
            assert forall |i: int, j: int|
                0 <= i < cursors_before.len()
                && 0 <= j < cursors_before[i].emitted@.len()
                implies Key::lt(
                    (#[trigger] cursors_before[i].emitted@[j]).key,
                    key,
                ) by {
                match self.frontier {
                    Some(frontier) => {
                        let witness = choose |w: int|
                            0 <= w < self.cursors@.len()
                            && self.cursors@[w].remaining().len() > 0
                            && self.cursors@[w].remaining()[0].key == key;
                        assert(Key::lt(frontier, key));
                        key_lte_lt_transitive(
                            cursors_before[i].emitted@[j].key,
                            frontier,
                            key,
                        );
                    },
                    None => {
                        assert(cursors_before[i].emitted@.len() == 0);
                        assert(false);
                    },
                }
            }
        }
        let mut index = 0usize;
        while index < self.cursors.len()
            invariant
                index <= self.cursors.len(),
                self.cursor_sources_wf(),
                self.cursors@.len() == cursors_before.len(),
                self.filter == self0.filter,
                self.frontier == self0.frontier,
                self.sources@ == self0.sources@,
                self.output@ == self0.output@,
                self.scanned_nodes() == self0.scanned_nodes(),
                forall |i: int| 0 <= i < self.cursors@.len()
                    ==> (#[trigger] self.cursors@[i]).source@
                        == cursors_before[i].source@,
                forall |i: int| 0 <= i < self.cursors@.len()
                    ==> (#[trigger] self.cursors@[i]).scanned@
                        == cursors_before[i].scanned@,
                forall |i: int| index <= i < self.cursors@.len()
                    ==> (#[trigger] self.cursors@[i]) == cursors_before[i],
                forall |i: int, j: int|
                    0 <= i < index
                    && 0 <= j < self.cursors@[i].emitted@.len()
                    ==> Key::lte(
                        (#[trigger] self.cursors@[i].emitted@[j]).key,
                        key,
                    ),
                forall |i: int, j: int|
                    0 <= i < index
                    && 0 <= j < self.cursors@[i].remaining().len()
                    ==> Key::lt(
                        key,
                        (#[trigger] self.cursors@[i].remaining()[j]).key,
                    ),
                forall |i: int| 0 <= i < index
                    ==> {
                        let before = #[trigger] cursors_before[i];
                        self.cursors@[i].emitted@ == before.emitted@
                            || {
                                &&& before.remaining().len() > 0
                                &&& before.remaining()[0].key == key
                                &&& self.cursors@[i].emitted@
                                    == before.emitted@.push(
                                        before.remaining()[0],
                                    )
                            }
                    },
            decreases self.cursors.len() - index,
        {
            let ghost cursor_before = self.cursors@[index as int];
            proof {
                assert(cursor_before == cursors_before[index as int]);
                assert(cursor_before.wf());
            }
            let head = self.cursors[index].peek();
            let mut advanced_current = false;
            if let Some(item) = head {
                if Self::key_eq(item.key, key) {
                    self.advance_cursor_at(index);
                    advanced_current = true;
                }
            }
            proof {
                assert forall |i: int| 0 <= i < self.cursors@.len()
                    implies (#[trigger] self.cursors@[i]).source@
                        == cursors_before[i].source@ by { }
                assert forall |i: int| index as int + 1 <= i
                    < self.cursors@.len()
                    implies (#[trigger] self.cursors@[i])
                        == cursors_before[i] by { }
                assert forall |j: int|
                    0 <= j < self.cursors@[index as int].emitted@.len()
                    implies Key::lte(
                        (#[trigger] self.cursors@[index as int]
                            .emitted@[j]).key,
                        key,
                    ) by {
                    if advanced_current
                        && j == cursor_before.emitted@.len() {
                        assert(self.cursors@[index as int].emitted@[j]
                            == cursor_before.remaining()[0]);
                        assert(cursor_before.remaining()[0].key == key);
                    } else {
                        assert(self.cursors@[index as int].emitted@[j]
                            == cursor_before.emitted@[j]);
                        assert(Key::lt(
                            cursor_before.emitted@[j].key,
                            key,
                        ));
                    }
                }
                assert forall |j: int|
                    0 <= j < self.cursors@[index as int].remaining().len()
                    implies Key::lt(
                        key,
                        (#[trigger] self.cursors@[index as int]
                            .remaining()[j]).key,
                    ) by {
                    if advanced_current {
                        assert(self.cursors@[index as int].remaining()[j]
                            == cursor_before.remaining()[j + 1]);
                        assert(Key::lt(
                            cursor_before.remaining()[0].key,
                            cursor_before.remaining()[j + 1].key,
                        ));
                        assert(cursor_before.remaining()[0].key == key);
                    } else {
                        assert(self.cursors@[index as int] == cursor_before);
                        assert(cursor_before.remaining().len() > 0);
                        assert(Key::lte(
                            key,
                            cursor_before.remaining()[0].key,
                        ));
                        assert(cursor_before.remaining()[0].key != key);
                        assert(Key::lt(
                            key,
                            cursor_before.remaining()[0].key,
                        ));
                        if j > 0 {
                            assert(Key::lt(
                                cursor_before.remaining()[0].key,
                                cursor_before.remaining()[j].key,
                            ));
                            key_lte_lt_transitive(
                                key,
                                cursor_before.remaining()[0].key,
                                cursor_before.remaining()[j].key,
                            );
                        }
                    }
                }
                assert(self.cursors@[index as int].emitted@
                        == cursor_before.emitted@
                    || {
                        &&& cursor_before.remaining().len() > 0
                        &&& cursor_before.remaining()[0].key == key
                        &&& self.cursors@[index as int].emitted@
                            == cursor_before.emitted@.push(
                                cursor_before.remaining()[0],
                            )
                    });
            }
            index += 1;
        }
        proof {
            self.source_aus_extensional(&self0);
            assert forall |i: int| 0 <= i < self.cursors@.len()
                implies {
                    &&& (#[trigger] self.cursors@[i]).source@
                        == cursors_before[i].source@
                    &&& self.cursors@[i].scanned@
                        == cursors_before[i].scanned@
                } by {
                if i < index as int {
                }
            }
            compactor_scanned_nodes_extensional(
                self.cursors@,
                cursors_before,
            );
        }
    }

    pub fn step(
        &mut self,
        cache: &mut FracCacheImpl,
    ) -> (out: CompactorMergeStepResult)
        requires
            old(self).wf(),
            old(cache).wf(),
            old(self).cache_inv(old(cache)@),
        ensures
            self.wf(),
            self.filter.target@.buffers.addrs
                == old(self).filter.target@.buffers.addrs,
            self.filter.target@.pivots.pivots
                == old(self).filter.target@.pivots.pivots,
            self.filter.target@.flushed.offsets
                == old(self).filter.target@.flushed.offsets,
            self.filter.start == old(self).filter.start,
            self.filter.end == old(self).filter.end,
            self.sources@ == old(self).sources@,
            self.source_aus() == old(self).source_aus(),
            self.cursors@.len() == old(self).cursors@.len(),
            forall |i: int| 0 <= i < self.cursors@.len()
                ==> (#[trigger] self.cursors@[i]).source@
                    == old(self).cursors@[i].source@,
            cache.wf(),
            self.cache_inv(cache@),
            cache.valid_load_handles_preserved(*old(cache)),
            forall |addr: Address, raw: RawPage|
                old(cache)@.valid_read(addr, raw)
                ==> cache@.valid_read(addr, raw),
            forall |addr: Address, raw: RawPage|
                cache@.valid_read(addr, raw)
                ==> old(cache)@.valid_read(addr, raw),
            match out {
                CompactorMergeStepResult::ReadAdvanced { reads } => {
                    &&& cache@ == old(cache)@
                    &&& reads@.dom().finite()
                    &&& reads@.len() == 1
                    &&& self.output@ == old(self).output@
                    &&& self.scanned_nodes()
                        == old(self).scanned_nodes().union_prefer_right(
                            to_branch_nodes(reads@),
                        )
                    &&& reads@.dom() <= addresses_in_aus(self.source_aus())
                    &&& exists |i: int| 0 <= i < self.cursors@.len()
                        && (#[trigger] self.cursors@[i]).source@.has_root()
                        && forall |addr: Address|
                            #[trigger] reads@.contains_key(addr) ==> {
                                &&& self.cursors@[i]
                                    .source@.disk_view.entries.contains_key(addr)
                                &&& crate::marshalling::IBranchNodeFormat_v::
                                    raw_page_to_branch_node(reads@[addr])
                                    == self.cursors@[i]
                                        .source@.disk_view.entries[addr]
                            }
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        Cache::Label::Access {
                            reads: reads@,
                            writes: Map::empty(),
                        },
                    )
                },
                CompactorMergeStepResult::Item { item } => {
                    &&& cache@ == old(cache)@
                    &&& self.output@ == old(self).output@.push(item)
                    &&& compact_sources_contain(
                        &self.filter,
                        self.sources@,
                        item.key,
                    )
                    &&& item.message == compact_sources_message(
                        &self.filter,
                        self.sources@,
                        item.key,
                    )
                },
                CompactorMergeStepResult::Skipped => {
                    &&& cache@ == old(cache)@
                    &&& self.output@ == old(self).output@
                },
                CompactorMergeStepResult::Done => {
                    &&& self.same_logical_state(old(self))
                    &&& cache@ == old(cache)@
                    &&& self.exhausted()
                    &&& self.scan_complete()
                    &&& forall |key: Key|
                        compact_sources_contain(
                            &self.filter,
                            self.sources@,
                            key,
                        ) <==> keyed_entries_contains(self.output@, key)
                },
                CompactorMergeStepResult::NeedCacheLoad { addr, handle } => {
                    &&& self.output@ == old(self).output@
                    &&& old(self).source_aus().contains(addr@.au)
                    &&& cache.entry_fetched(&addr)
                    &&& cache.valid_load_handle(&addr, handle)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        crate::implementation::FracCacheImpl_v::cache_load_label(
                            &addr,
                        ),
                    )
                },
                CompactorMergeStepResult::CacheFull
                | CompactorMergeStepResult::Blocked
                | CompactorMergeStepResult::InvalidPage => {
                    &&& self.same_logical_state(old(self))
                    &&& cache@ == old(cache)@
                },
            },
            match out {
                CompactorMergeStepResult::ReadAdvanced { .. } => true,
                _ => self.scanned_nodes() == old(self).scanned_nodes(),
            },
    {
        let ghost self0 = *self;
        let ghost cache0 = *cache;
        let mut scan_idx = 0usize;
        while scan_idx < self.cursors.len()
            invariant
                scan_idx <= self.cursors.len(),
                self.wf(),
                cache.wf(),
                self.cache_inv(cache@),
                self.output@ == self0.output@,
                self.frontier == self0.frontier,
                self.sources@ == self0.sources@,
                self.filter == self0.filter,
                self.cursors@ =~= self0.cursors@,
                self.source_aus() == self0.source_aus(),
                cache@ == cache0@,
                cache.valid_load_handles_preserved(cache0),
                forall |i: int| 0 <= i < scan_idx
                    ==> (#[trigger] self.cursors@[i]).current_leaf is Some
                        || {
                            &&& self.cursors@[i].remaining().len() == 0
                            &&& self.cursors@[i].scanned@
                                == self.cursors@[i].source@.full_repr()
                        },
            decreases self.cursors.len() - scan_idx,
        {
            if self.cursors[scan_idx].current_leaf.is_some() {
                scan_idx += 1;
                continue;
            }
            let scan_result = self.scan_cursor_step(cache, scan_idx);
            match scan_result {
                BranchScanStepResult::Advanced { reads } => {
                    proof {
                        assert(self.scanned_nodes()
                            == self0.scanned_nodes().union_prefer_right(
                                to_branch_nodes(reads@),
                            ));
                        assert forall |i: int| 0 <= i < self.cursors@.len()
                            implies (#[trigger] self.cursors@[i]).source@
                                == self0.cursors@[i].source@ by { }
                        assert(self.cursors@[scan_idx as int]
                            .source@.get_summary()
                            <= self.source_aus()) by {
                            assert forall |au: AU|
                                #[trigger] self.cursors@[scan_idx as int]
                                    .source@.get_summary().contains(au)
                                implies self.source_aus().contains(au) by {
                                assert(exists |i: int|
                                    0 <= i < self.cursors@.len()
                                    && self.cursors@[i]
                                        .source@.get_summary().contains(au));
                            }
                        }
                        assert(reads@.dom()
                            <= addresses_in_aus(self.source_aus())) by {
                            assert forall |addr: Address|
                                #[trigger] reads@.dom().contains(addr)
                                implies addresses_in_aus(
                                    self.source_aus(),
                                ).contains(addr) by {
                                assert(addresses_in_aus(
                                    self.cursors@[scan_idx as int]
                                        .source@.get_summary(),
                                ).contains(addr));
                            }
                        }
                    }
                    return CompactorMergeStepResult::ReadAdvanced { reads };
                },
                BranchScanStepResult::ItemReady => {
                    scan_idx += 1;
                },
                BranchScanStepResult::Done => {
                    scan_idx += 1;
                },
                BranchScanStepResult::NeedCacheLoad { addr, handle } => {
                    proof {
                        assert(self.cursors@[scan_idx as int]
                            .source@.get_summary().contains(addr@.au));
                        assert(self.source_aus().contains(addr@.au)) by {
                            assert(exists |i: int|
                                0 <= i < self.cursors@.len()
                                && self.cursors@[i].source@.get_summary()
                                    .contains(addr@.au));
                        }
                    }
                    return CompactorMergeStepResult::NeedCacheLoad {
                        addr,
                        handle,
                    };
                },
                BranchScanStepResult::CacheFull => {
                    return CompactorMergeStepResult::CacheFull;
                },
                BranchScanStepResult::Blocked => {
                    return CompactorMergeStepResult::Blocked;
                },
                BranchScanStepResult::InvalidPage => {
                    return CompactorMergeStepResult::InvalidPage;
                },
            }
        }
        proof {
            assert(self.heads_ready());
        }
        let minimum = self.minimum_key();
        let key = match minimum {
            Some(key) => key,
            None => {
                proof {
                    self.exhausted_output_complete();
                    assert(self.same_logical_state(&self0));
                    assert forall |i: int| 0 <= i < self.cursors@.len()
                        implies (#[trigger] self.cursors@[i]).scanned@
                            == self.cursors@[i].source@.full_repr() by {
                        assert(self.cursors@[i].current_leaf is None);
                    }
                }
                return CompactorMergeStepResult::Done;
            },
        };
        proof {
            self.establish_next_key_queries(key);
        }

        let live_start = self.filter.live_start(key);
        let mut start = self.cursors.len();
        let is_live = match live_start {
            CompactionLiveStart::Live { input_idx } => {
                start = input_idx;
                proof {
                    assert(input_idx <= self.cursors.len());
                }
                true
            },
            CompactionLiveStart::Filtered => false,
        };
        let mut message = Message::Update { delta: Delta(0) };
        let mut found_live = false;
        let mut merge_idx = self.cursors.len();
        while merge_idx > start
            invariant
                start <= merge_idx <= self.cursors.len(),
                self.wf(),
                self.heads_ready(),
                cache@ == cache0@,
                message == merge_source_messages(
                    self.sources@,
                    key,
                    merge_idx as int,
                ),
                found_live == exists |i: int|
                    merge_idx as int <= i < self.sources@.len()
                    && keyed_entries_contains(
                        #[trigger] self.sources@[i],
                        key,
                    ),
            decreases merge_idx - start,
        {
            merge_idx -= 1;
            let head = self.cursors[merge_idx].peek();
            match head {
                Some(item) => {
                    if Self::key_eq(item.key, key) {
                        proof {
                            assert(self.cursors@[merge_idx as int]
                                .remaining()[0] == item);
                            assert(keyed_entries_query(
                                self.sources@[merge_idx as int],
                                key,
                            ) == item.message);
                            assert(keyed_entries_contains(
                                self.sources@[merge_idx as int],
                                key,
                            ));
                        }
                        message = merge_messages(item.message, message);
                        found_live = true;
                    } else {
                        proof {
                            assert(self.cursors@[merge_idx as int]
                                .remaining()[0] == item);
                            assert(!keyed_entries_contains(
                                self.sources@[merge_idx as int],
                                key,
                            ));
                            assert(keyed_entries_query(
                                self.sources@[merge_idx as int],
                                key,
                            ) == Message::Update { delta: Delta(0) });
                            nop_merge_left_identity(message);
                        }
                    }
                },
                None => {
                    proof {
                        assert(self.cursors@[merge_idx as int]
                            .current_leaf is None);
                        assert(self.cursors@[merge_idx as int]
                            .remaining().len() == 0);
                        assert(!keyed_entries_contains(
                            self.sources@[merge_idx as int],
                            key,
                        ));
                        assert(keyed_entries_query(
                            self.sources@[merge_idx as int],
                            key,
                        ) == Message::Update { delta: Delta(0) });
                        nop_merge_left_identity(message);
                    }
                },
            }
            proof {
                assert(message == merge_source_messages(
                    self.sources@,
                    key,
                    merge_idx as int,
                ));
            }
        }
        proof {
            match live_start {
                CompactionLiveStart::Live { input_idx } => {
                    assert(is_live);
                    assert(start == input_idx);
                    assert(start as nat
                        == compact_source_start(&self.filter, key));
                    assert(compact_sources_contain(
                        &self.filter,
                        self.sources@,
                        key,
                    ) == found_live);
                    if found_live {
                        assert(message == compact_sources_message(
                            &self.filter,
                            self.sources@,
                            key,
                        ));
                    }
                },
                CompactionLiveStart::Filtered => {
                    assert(!is_live);
                    assert(!compact_sources_contain(
                        &self.filter,
                        self.sources@,
                        key,
                    ));
                },
            }
            assert((is_live && found_live)
                == compact_sources_contain(
                    &self.filter,
                    self.sources@,
                    key,
                ));
        }

        let ghost cursors_before_advance = self.cursors@;
        self.advance_minimum_sources(key);
        proof {
            assert forall |i: int| 0 <= i < self.cursors@.len()
                implies (#[trigger] self.cursors@[i]).cache_inv(cache@) by {
                assert(self.cursors@[i].source@
                    == cursors_before_advance[i].source@);
                assert(cursors_before_advance[i].cache_inv(cache@));
            }
            assert(self.cache_inv(cache@));
            assert(cursors_before_advance == self0.cursors@);
            assert forall |j: int| 0 <= j < self.output@.len()
                implies Key::lt(
                    (#[trigger] self.output@[j]).key,
                    key,
                ) by {
                match self.frontier {
                    Some(frontier) => {
                        let witness = choose |w: int|
                            0 <= w < cursors_before_advance.len()
                            && cursors_before_advance[w]
                                .remaining().len() > 0
                            && cursors_before_advance[w]
                                .remaining()[0].key == key;
                        assert(Key::lt(frontier, key));
                        key_lte_lt_transitive(
                            self.output@[j].key,
                            frontier,
                            key,
                        );
                    },
                    None => {
                        assert(self.output@.len() == 0);
                        assert(false);
                    },
                }
            }
        }
        self.frontier = Some(key);
        if is_live && found_live {
            let item = KeyedMessage { key, message };
            proof {
                let ghost old_output = self.output@;
                self.output@ = self.output@.push(item);
                keyed_entries_push_sorted(old_output, item);
                assert forall |j: int| 0 <= j < self.output@.len()
                    implies {
                        let output_item = #[trigger] self.output@[j];
                        &&& compact_sources_contain(
                            &self.filter,
                            self.sources@,
                            output_item.key,
                        )
                        &&& output_item.message == compact_sources_message(
                            &self.filter,
                            self.sources@,
                            output_item.key,
                        )
                    } by {
                    if j == old_output.len() {
                        assert(self.output@[j] == item);
                    } else {
                        assert(self.output@[j] == old_output[j]);
                    }
                }
                assert(output_entries_valid(
                    &self.filter,
                    self.sources@,
                    self.output@,
                ));
                assert forall |candidate: Key|
                    compact_sources_contain(
                        &self.filter,
                        self.sources@,
                        candidate,
                    ) && (exists |i: int|
                        0 <= i < self.cursors@.len()
                        && keyed_entries_contains(
                            (#[trigger] self.cursors@[i]).emitted@,
                            candidate,
                        ))
                    implies keyed_entries_contains(
                        self.output@,
                        candidate,
                    ) by {
                    let i = choose |i: int|
                        0 <= i < self.cursors@.len()
                        && keyed_entries_contains(
                            self.cursors@[i].emitted@,
                            candidate,
                        );
                    let j = choose |j: int|
                        0 <= j < self.cursors@[i].emitted@.len()
                        && self.cursors@[i].emitted@[j].key
                            == candidate;
                    let before = cursors_before_advance[i];
                    if self.cursors@[i].emitted@ == before.emitted@ {
                        assert(keyed_entries_contains(
                            self0.cursors@[i].emitted@,
                            candidate,
                        ));
                        assert(keyed_entries_contains(old_output, candidate));
                        let k = choose |k: int|
                            0 <= k < old_output.len()
                            && old_output[k].key == candidate;
                        assert(self.output@[k] == old_output[k]);
                        assert(keyed_entries_contains(
                            self.output@,
                            candidate,
                        ));
                    } else if j < before.emitted@.len() {
                        assert(self.cursors@[i].emitted@[j]
                            == before.emitted@[j]);
                        assert(keyed_entries_contains(
                            self0.cursors@[i].emitted@,
                            candidate,
                        ));
                        assert(keyed_entries_contains(old_output, candidate));
                        let k = choose |k: int|
                            0 <= k < old_output.len()
                            && old_output[k].key == candidate;
                        assert(self.output@[k] == old_output[k]);
                        assert(keyed_entries_contains(
                            self.output@,
                            candidate,
                        ));
                    } else {
                        assert(j == before.emitted@.len());
                        assert(self.cursors@[i].emitted@[j]
                            == before.remaining()[0]);
                        assert(candidate == key);
                        assert(self.output@[old_output.len() as int]
                            == item);
                        assert(keyed_entries_contains(
                            self.output@,
                            candidate,
                        ));
                    }
                }
                assert forall |j: int| 0 <= j < self.output@.len()
                    implies Key::lte(
                        (#[trigger] self.output@[j]).key,
                        key,
                    ) by { }
                assert(self.wf());
            }
            CompactorMergeStepResult::Item { item }
        } else {
            proof {
                assert(!compact_sources_contain(
                    &self.filter,
                    self.sources@,
                    key,
                ));
                assert forall |candidate: Key|
                    compact_sources_contain(
                        &self.filter,
                        self.sources@,
                        candidate,
                    ) && (exists |i: int|
                        0 <= i < self.cursors@.len()
                        && keyed_entries_contains(
                            (#[trigger] self.cursors@[i]).emitted@,
                            candidate,
                        ))
                    implies keyed_entries_contains(
                        self.output@,
                        candidate,
                    ) by {
                    let i = choose |i: int|
                        0 <= i < self.cursors@.len()
                        && keyed_entries_contains(
                            self.cursors@[i].emitted@,
                            candidate,
                        );
                    let j = choose |j: int|
                        0 <= j < self.cursors@[i].emitted@.len()
                        && self.cursors@[i].emitted@[j].key
                            == candidate;
                    let before = cursors_before_advance[i];
                    if self.cursors@[i].emitted@ == before.emitted@ {
                        assert(keyed_entries_contains(
                            self0.cursors@[i].emitted@,
                            candidate,
                        ));
                    } else if j < before.emitted@.len() {
                        assert(self.cursors@[i].emitted@[j]
                            == before.emitted@[j]);
                        assert(keyed_entries_contains(
                            self0.cursors@[i].emitted@,
                            candidate,
                        ));
                    } else {
                        assert(j == before.emitted@.len());
                        assert(self.cursors@[i].emitted@[j]
                            == before.remaining()[0]);
                        assert(candidate == key);
                        assert(false);
                    }
                    assert(keyed_entries_contains(
                        self0.output@,
                        candidate,
                    ));
                }
                assert forall |j: int| 0 <= j < self.output@.len()
                    implies Key::lte(
                        (#[trigger] self.output@[j]).key,
                        key,
                    ) by { }
                assert(self.wf());
            }
            CompactorMergeStepResult::Skipped
        }
    }
}

} // verus!
