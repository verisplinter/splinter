// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::map::*;

use crate::abstract_system::AbstractMap_v::AbstractMap;
use crate::abstract_system::MsgHistory_v::{KeyedMessage, MsgHistory};
use crate::abstract_system::StampedMap_v::{Stamped, StampedMap};
use crate::allocation_layer::AllocationBranch_v::{AllocationBranch, Summary};
use crate::betree::Buffer_v::SimpleBuffer;
use crate::betree::LinkedBranch_v::{LinkedBranch, Path as BranchPath, SplitArg};
use crate::betree::LinkedBranch_v::Refinement_v as LinkedBranchRefinement_v;
use crate::betree::PivotBranchRefinement_v::{
    self,
    AppendLabel as PivotAppendLabel,
    InternalLabel as PivotInternalLabel,
    QueryLabel as PivotQueryLabel,
};
use crate::disk::GenericDisk_v::{Address, Pointer};
use crate::implementation::ConcreteBranch_v::ConcreteBranch;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{default_value, Message, Value};
use crate::spec::TotalKMMap_t::TotalKMMap;

verus! {

pub open spec fn normalize_value(msg: Message) -> Value
{
    match msg {
        Message::Define{value} => value,
        Message::Update{delta} => Message::apply_delta(delta, default_value()),
    }
}

pub open spec fn normalize_message(msg: Message) -> Message
{
    Message::Define{value: normalize_value(msg)}
}

pub open spec fn append_puts(start_lsn: nat, keys: Seq<Key>, msgs: Seq<Message>) -> MsgHistory
    recommends
        keys.len() == msgs.len(),
{
    let seq_end = start_lsn + keys.len();
    let puts = Map::new(
        |lsn: nat| start_lsn <= lsn < seq_end,
        |lsn: nat| {
            let idx = (lsn - start_lsn) as int;
            KeyedMessage{ key: keys[idx], message: normalize_message(msgs[idx]) }
        },
    );
    MsgHistory{ msgs: puts, seq_start: start_lsn, seq_end }
}

pub proof fn append_puts_wf(start_lsn: nat, keys: Seq<Key>, msgs: Seq<Message>)
    requires
        keys.len() == msgs.len(),
    ensures
        append_puts(start_lsn, keys, msgs).wf(),
        append_puts(start_lsn, keys, msgs).seq_start == start_lsn,
        append_puts(start_lsn, keys, msgs).seq_end == start_lsn + keys.len(),
{
    let puts = append_puts(start_lsn, keys, msgs);
    assert(puts.seq_start <= puts.seq_end);
    assert forall |lsn: nat| #[trigger] puts.msgs.dom().contains(lsn) <==> puts.contains(lsn) by { };
}

pub open spec fn buffer_as_kmmap(buffer: SimpleBuffer) -> TotalKMMap
{
    TotalKMMap(Map::new(|k: Key| true, |k: Key| normalize_message(buffer.query(k))))
}

pub open spec fn branch_as_kmmap(branch: LinkedBranch<Summary>) -> TotalKMMap
{
    buffer_as_kmmap(branch.i().i())
}

impl AllocationBranch {
    pub open spec fn buffer_i(self) -> SimpleBuffer
    {
        if self.branch is Some {
            self.branch.unwrap().i().i()
        } else {
            SimpleBuffer::empty()
        }
    }

    pub open spec fn kmmap_i(self) -> TotalKMMap
    {
        buffer_as_kmmap(self.buffer_i())
    }
}

impl ConcreteBranch::State {
    pub open spec fn abstract_map_i(self) -> AbstractMap::State
    {
        AbstractMap::State{
            stamped_map: Stamped{
                value: self.i().kmmap_i(),
                seq_end: self.cached_branch.seq_end,
            }
        }
    }

    pub open spec fn label_to_abstract_map(self, lbl: ConcreteBranch::Label) -> AbstractMap::Label
    {
        match lbl {
            ConcreteBranch::Label::Query{key, msg, depth} =>
                AbstractMap::Label::QueryLabel{
                    end_lsn: self.cached_branch.seq_end,
                    key,
                    value: normalize_value(msg),
                },
            ConcreteBranch::Label::Append{keys, msgs, depth} =>
                AbstractMap::Label::PutLabel{ puts: append_puts(self.cached_branch.seq_end, keys, msgs) },
            ConcreteBranch::Label::Grow{new_root_addr} =>
                AbstractMap::Label::InternalLabel{},
            ConcreteBranch::Label::Split{new_child_addr, pivot, depth, split_arg} =>
                AbstractMap::Label::InternalLabel{},
            ConcreteBranch::Label::Seal{aux_ptr} =>
                AbstractMap::Label::InternalLabel{},
            ConcreteBranch::Label::Internal{} =>
                AbstractMap::Label::InternalLabel{},
        }
    }
}

proof fn allocation_query_refines_to_kmmap(branch: LinkedBranch<Summary>, key: Key)
    requires
        branch.inv(),
    ensures
        branch_as_kmmap(branch)[key] == normalize_message(branch.query(key)),
{
    let msg = branch.query(key);
    LinkedBranchRefinement_v::query_refines(branch, key, msg);
    LinkedBranchRefinement_v::i_internal_wf(branch, branch.the_ranking());
    PivotBranchRefinement_v::query_refines(branch.i(), PivotQueryLabel{key, msg});
    assert(branch.i().i().query(key) == msg);
}

proof fn allocation_grow_preserves_kmmap(pre: AllocationBranch, addr: Address)
    requires
        pre.inv(),
        crate::implementation::ConcreteBranchRefinement_v::allocation_branch_can_grow(pre, addr),
    ensures
        crate::implementation::ConcreteBranchRefinement_v::allocation_branch_grow(pre, addr).kmmap_i() == pre.kmmap_i(),
{
    let pre_branch = pre.branch.unwrap();
    LinkedBranchRefinement_v::grow_refines(pre_branch, addr);
    LinkedBranchRefinement_v::i_wf(pre_branch);
    PivotBranchRefinement_v::grow_refines(pre_branch.i(), PivotInternalLabel{});
    assert(pre_branch.grow(addr).i().i() == pre_branch.i().i());
}

proof fn allocation_split_preserves_kmmap(
    pre: AllocationBranch,
    new_child_addr: Address,
    path: BranchPath<Summary>,
    split_arg: SplitArg,
)
    requires
        pre.inv(),
        pre.can_split(new_child_addr, path, split_arg),
    ensures
        pre.branch_split(new_child_addr, path, split_arg).kmmap_i() == pre.kmmap_i(),
{
    let pre_branch = pre.branch.unwrap();
    let post_branch = pre.branch_split(new_child_addr, path, split_arg).branch.unwrap();
    let ranking = pre_branch.the_ranking();
    let post_ranking = post_branch.the_ranking();
    let pre_i = pre_branch.i_internal(ranking);
    let post_i = post_branch.i_internal(post_ranking);
    let path_i = path.i_internal(ranking);
    let pivot = split_arg.get_pivot();
    let split_child_idx = path.target().root().route(pivot) + 1;
    let split_child = path.target().child_at_idx(split_child_idx);
    LinkedBranchRefinement_v::split_refines(pre_branch, new_child_addr, path, split_arg);
    LinkedBranchRefinement_v::i_internal_wf(pre_branch, ranking);
    LinkedBranchRefinement_v::lemma_path_i_valid(path, ranking);
    LinkedBranchRefinement_v::lemma_path_target(path, ranking);
    assert(post_branch.valid_ranking(post_ranking));
    LinkedBranchRefinement_v::split_refines_internal(
        pre_branch, ranking, post_ranking, new_child_addr, path, split_arg,
    );
    PivotBranchRefinement_v::lemma_path_target_is_wf(path_i);
    broadcast use crate::betree::LinkedBranch_v::Refinement_v::lemma_route_ensures;
    assert(path.target().root().valid_child_index(split_child_idx));
    assert(split_child_idx == path_i.target().route(pivot) + 1);
    assert(path_i.target()->children[split_child_idx] == split_child.i_internal(ranking));
    assert(split_arg.wf(split_child));
    assert(split_arg.i().wf(split_child.i_internal(ranking))) by { }
    assert(path_i.target().can_split_child_of_index(split_arg.i())) by { }
    PivotBranchRefinement_v::split_refines(pre_i, path_i, split_arg.i());
    assert(post_i == pre_i.split(path_i, split_arg.i()));
    assert(post_i.i() == pre_i.split(path_i, split_arg.i()).i());
    assert(pre_i.split(path_i, split_arg.i()).i() == pre_i.i());
    assert(pre_branch.i() == pre_i);
    assert(post_branch.i() == post_i);
    assert(post_branch.i().i() == pre_branch.i().i());
}

proof fn linked_seal_preserves_kmmap(branch: LinkedBranch<Summary>, aux_addr: Address, summary: Summary)
    requires
        branch.inv(),
        branch.root() is Index,
        branch.disk_view.is_fresh(set!{aux_addr}),
    ensures
        branch_as_kmmap(branch.seal(aux_addr, summary)) == branch_as_kmmap(branch),
{
    let sealed = branch.seal(aux_addr, summary);
    let ranking = branch.the_ranking();
    LinkedBranchRefinement_v::i_internal_wf(branch, ranking);

    assert(sealed.wf()) by {
        assert(sealed.disk_view.entries.contains_key(sealed.root));
        assert(!(sealed.root() is Auxiliary));
        assert(sealed.disk_view.entries_wf());
        assert(sealed.disk_view.no_dangling_address());
    }

    assert(sealed.valid_ranking(ranking)) by {
        assert forall |addr| #[trigger] ranking.contains_key(addr) && sealed.disk_view.entries.contains_key(addr)
        implies sealed.disk_view.node_children_respects_rank(ranking, addr) by {
            if addr == branch.root {
                assert(sealed.disk_view.entries.contains_key(branch.root));
                assert(sealed.root() is Index);
                assert(sealed.root()->children == branch.root()->children);
                assert forall |child_idx: int| #[trigger] sealed.root().valid_child_index(child_idx) implies {
                    &&& ranking.contains_key(sealed.root()->children[child_idx])
                    &&& ranking[sealed.root()->children[child_idx]] < ranking[addr]
                } by {
                    assert(branch.root().valid_child_index(child_idx));
                    assert(branch.disk_view.node_children_respects_rank(ranking, addr));
                }
            } else if addr == aux_addr {
                assert(sealed.disk_view.entries[addr] is Auxiliary);
            } else {
                assert(branch.disk_view.entries.remove_keys(set!{branch.root, aux_addr}).contains_key(addr));
                assert(sealed.disk_view.entries[addr] == branch.disk_view.entries[addr]);
                assert forall |child_idx: int| #[trigger] sealed.disk_view.entries[addr].valid_child_index(child_idx) implies {
                    &&& ranking.contains_key(sealed.disk_view.entries[addr]->children[child_idx])
                    &&& ranking[sealed.disk_view.entries[addr]->children[child_idx]] < ranking[addr]
                } by {
                    assert(branch.disk_view.entries[addr].valid_child_index(child_idx));
                    assert(branch.disk_view.node_children_respects_rank(ranking, addr));
                }
            }
        }
        assert(ranking.contains_key(sealed.root));
    }
    assert(sealed.acyclic());
    let post_ranking = sealed.the_ranking();
    let pre_i = branch.i_internal(ranking);
    let post_i = sealed.i_internal(post_ranking);

    assert(branch.disk_view.entries.remove_keys(set!{branch.root, aux_addr})
        == sealed.disk_view.entries.remove_keys(set!{branch.root, aux_addr}));

    assert forall |i| #[trigger] sealed.root().valid_child_index(i)
    implies ({
        &&& branch.root().valid_child_index(i)
        &&& post_i->children[i] == pre_i->children[i]
        &&& branch.child_at_idx(i).reachable_addrs_using_ranking(ranking)
            == sealed.child_at_idx(i).reachable_addrs_using_ranking(post_ranking)
    }) by {
        let pre_child = branch.child_at_idx(i);
        let post_child = sealed.child_at_idx(i);
        assert(pre_child.reachable_addrs_using_ranking(ranking).disjoint(set!{branch.root, aux_addr})) by {
            if pre_child.reachable_addrs_using_ranking(ranking).contains(branch.root) {
                LinkedBranchRefinement_v::lemma_reachable_child_has_smaller_rank(pre_child, ranking, branch.root);
            }
            if pre_child.reachable_addrs_using_ranking(ranking).contains(aux_addr) {
                LinkedBranchRefinement_v::lemma_reachable_implies_valid_address(pre_child, ranking, aux_addr);
            }
        }
        LinkedBranchRefinement_v::lemma_reachable_unchanged_implies_same_i_internal(
            pre_child, ranking, post_child, post_ranking, set!{branch.root, aux_addr},
        );
    }

    assert(post_i->children =~~= pre_i->children);
    assert(post_i == pre_i);
    assert(branch.i() == pre_i);
    assert(sealed.i() == post_i);
    assert(sealed.i() == branch.i());
    assert(sealed.i().i() == branch.i().i());
}

proof fn allocation_append_refines_to_abstract_map(
    pre: AllocationBranch,
    post: AllocationBranch,
    seq_end: nat,
    keys: Seq<Key>,
    msgs: Seq<Message>,
    path: BranchPath<Summary>,
)
    requires
        pre.inv(),
        pre.can_append(keys, msgs, path),
        post == pre.branch_append(keys, msgs, path),
    ensures
        post.kmmap_i().wf(),
        post.kmmap_i() == MsgHistory::map_plus_history(
            Stamped{ value: pre.kmmap_i(), seq_end },
            append_puts(seq_end, keys, msgs),
        ).value,
{
    append_puts_wf(seq_end, keys, msgs);
    MsgHistory::map_plus_history_lemma(
        Stamped{ value: pre.kmmap_i(), seq_end },
        append_puts(seq_end, keys, msgs),
    );
    let pre_branch = pre.branch.unwrap();
    let post_branch = post.branch.unwrap();
    let ranking = pre_branch.the_ranking();
    let pivot_path = path.i_internal(ranking);
    let pivot_lbl = PivotAppendLabel{keys, msgs, path: pivot_path};
    LinkedBranchRefinement_v::append_refines(pre_branch, keys, msgs, path);
    LinkedBranchRefinement_v::lemma_path_i_internal(path, ranking, keys.last());
    PivotBranchRefinement_v::append_refines(pre_branch.i(), pivot_lbl);
    assert(post_branch.i().i()
        == SimpleBuffer{map: pre_branch.i().i().map.union_prefer_right(Map::new(
            |key| keys.contains(key),
            |key| msgs[(crate::betree::PivotBranch_v::Node::Leaf{ keys, msgs }).route(key)],
        ))});
    assert forall |key: Key| #[trigger] post.kmmap_i()[key]
        == MsgHistory::map_plus_history(
            Stamped{ value: pre.kmmap_i(), seq_end },
            append_puts(seq_end, keys, msgs),
        ).value[key] by {
        allocation_append_updates_kmmap_pointwise(pre, post, keys, msgs, path, key);
        append_puts_updates_stamped_map_pointwise(Stamped{ value: pre.kmmap_i(), seq_end }, keys, msgs, key);
    };
    assert(post.kmmap_i().wf());
    assert(MsgHistory::map_plus_history(
        Stamped{ value: pre.kmmap_i(), seq_end },
        append_puts(seq_end, keys, msgs),
    ).value.wf());
    assert(post.kmmap_i().ext_equal(MsgHistory::map_plus_history(
        Stamped{ value: pre.kmmap_i(), seq_end },
        append_puts(seq_end, keys, msgs),
    ).value)) by {
        assert forall |key: Key|
            #[trigger] post.kmmap_i().0.contains_key(key)
            <==> MsgHistory::map_plus_history(
                Stamped{ value: pre.kmmap_i(), seq_end },
                append_puts(seq_end, keys, msgs),
            ).value.0.contains_key(key) by {
        };
        assert forall |key: Key|
            #[trigger] post.kmmap_i().0.contains_key(key)
            implies post.kmmap_i().0[key] == MsgHistory::map_plus_history(
                Stamped{ value: pre.kmmap_i(), seq_end },
                append_puts(seq_end, keys, msgs),
            ).value.0[key] by {
            assert(post.kmmap_i()[key] == MsgHistory::map_plus_history(
                Stamped{ value: pre.kmmap_i(), seq_end },
                append_puts(seq_end, keys, msgs),
            ).value[key]);
        }
    };
    post.kmmap_i().ext_equal_is_equality(MsgHistory::map_plus_history(
        Stamped{ value: pre.kmmap_i(), seq_end },
        append_puts(seq_end, keys, msgs),
    ).value);
    assert(post.kmmap_i() == MsgHistory::map_plus_history(
        Stamped{ value: pre.kmmap_i(), seq_end },
        append_puts(seq_end, keys, msgs),
    ).value);
}

proof fn allocation_append_updates_kmmap_pointwise(
    pre: AllocationBranch,
    post: AllocationBranch,
    keys: Seq<Key>,
    msgs: Seq<Message>,
    path: BranchPath<Summary>,
    key: Key,
)
    requires
        pre.inv(),
        pre.can_append(keys, msgs, path),
        post == pre.branch_append(keys, msgs, path),
    ensures
        post.kmmap_i()[key]
            == if keys.contains(key) {
                normalize_message(msgs[keys.index_of(key)])
            } else {
                pre.kmmap_i()[key]
            },
{
    let pre_branch = pre.branch.unwrap();
    let post_branch = post.branch.unwrap();
    let ranking = pre_branch.the_ranking();
    let pivot_path = path.i_internal(ranking);
    let pivot_lbl = PivotAppendLabel{keys, msgs, path: pivot_path};
    LinkedBranchRefinement_v::append_refines(pre_branch, keys, msgs, path);
    LinkedBranchRefinement_v::lemma_path_i_internal(path, ranking, keys.last());
    PivotBranchRefinement_v::append_refines(pre_branch.i(), pivot_lbl);
    let pre_buffer = pre_branch.i().i();
    let post_buffer =
        SimpleBuffer{map: pre_buffer.map.union_prefer_right(Map::new(
            |k| keys.contains(k),
            |k| msgs[(crate::betree::PivotBranch_v::Node::Leaf{ keys, msgs }).route(k)],
        ))};
    assert(post_branch.i().i() == post_buffer);
    allocation_query_refines_to_kmmap(pre_branch, key);
    if keys.contains(key) {
        Key::strictly_sorted_implies_unique(keys);
        let i = keys.index_of(key);
        assert(0 <= i < keys.len());
        assert(keys[i] == key);
        assert(post_buffer.map.contains_key(key));
        Key::strictly_sorted_implies_sorted(keys);
        let r = (crate::betree::PivotBranch_v::Node::Leaf{ keys, msgs }).route(key);
        Key::largest_lte_ensures(keys, key, r);
        assert(keys[r] == key);
        assert(r == i);
        assert(post_buffer.map[key] == msgs[i]);
        assert(post_buffer.query(key) == msgs[i]);
        assert(post.kmmap_i()[key] == normalize_message(msgs[i]));
    } else {
        assert(!post_buffer.map.contains_key(key) ==> !pre_buffer.map.contains_key(key)) by { };
        if pre_buffer.map.contains_key(key) {
            assert(post_buffer.map[key] == pre_buffer.map[key]);
            assert(post_buffer.query(key) == pre_buffer.query(key));
        } else {
            assert(post_buffer.query(key) == pre_buffer.query(key));
        }
        assert(post.kmmap_i()[key] == pre.kmmap_i()[key]);
    }
}

proof fn append_puts_drop_last_lemma(start_lsn: nat, keys: Seq<Key>, msgs: Seq<Message>)
    requires
        keys.len() == msgs.len(),
        0 < keys.len(),
    ensures
        append_puts(start_lsn, keys, msgs).discard_recent((start_lsn + keys.len() - 1) as nat)
            == append_puts(start_lsn, keys.drop_last(), msgs.drop_last()),
{
    let history = append_puts(start_lsn, keys, msgs);
    let prefix = append_puts(start_lsn, keys.drop_last(), msgs.drop_last());
    let last_lsn = (start_lsn + keys.len() - 1) as nat;
    assert(history.discard_recent(last_lsn).seq_start == prefix.seq_start);
    assert(history.discard_recent(last_lsn).seq_end == prefix.seq_end);
    assert forall |lsn: nat| #[trigger] history.discard_recent(last_lsn).msgs.contains_key(lsn)
        <==> prefix.msgs.contains_key(lsn) by {
    };
    assert forall |lsn: nat| #[trigger] history.discard_recent(last_lsn).msgs.contains_key(lsn)
        implies history.discard_recent(last_lsn).msgs[lsn] == prefix.msgs[lsn] by {
        let idx = (lsn - start_lsn) as int;
        assert(0 <= idx < keys.drop_last().len());
        assert(keys.drop_last()[idx] == keys[idx]);
        assert(msgs.drop_last()[idx] == msgs[idx]);
    };
    assert(history.discard_recent(last_lsn).ext_equal(prefix));
    MsgHistory::ext_equal_is_equality();
}

proof fn append_puts_updates_stamped_map_pointwise(
    stamped_map: StampedMap,
    keys: Seq<Key>,
    msgs: Seq<Message>,
    key: Key,
)
    requires
        stamped_map.value.wf(),
        keys.len() == msgs.len(),
        Key::is_strictly_sorted(keys),
    ensures
        MsgHistory::map_plus_history(stamped_map, append_puts(stamped_map.seq_end, keys, msgs)).value[key]
            == if keys.contains(key) {
                normalize_message(msgs[keys.index_of(key)])
            } else {
                stamped_map.value[key]
            },
    decreases keys.len(),
{
    let history = append_puts(stamped_map.seq_end, keys, msgs);
    append_puts_wf(stamped_map.seq_end, keys, msgs);
    MsgHistory::map_plus_history_lemma(stamped_map, history);
    if keys.len() == 0 {
        assert(MsgHistory::map_plus_history(stamped_map, history) == stamped_map);
        assert(!keys.contains(key));
        assert(MsgHistory::map_plus_history(stamped_map, history).value[key] == stamped_map.value[key]);
    } else {
        let last_lsn = (history.seq_end - 1) as nat;
        let prefix = append_puts(stamped_map.seq_end, keys.drop_last(), msgs.drop_last());
        append_puts_drop_last_lemma(stamped_map.seq_end, keys, msgs);
        append_puts_updates_stamped_map_pointwise(stamped_map, keys.drop_last(), msgs.drop_last(), key);
        reveal_with_fuel(MsgHistory::apply_to_stamped_map, 2);
        let sub_map = prefix.apply_to_stamped_map(stamped_map);
        assert(sub_map == MsgHistory::map_plus_history(stamped_map, prefix));
        assert(history.discard_recent(last_lsn) == prefix);
        assert(history.apply_to_stamped_map(stamped_map)
            == Stamped{
                value: sub_map.value.insert(keys.last(), sub_map.value[keys.last()].merge(normalize_message(msgs.last()))),
                seq_end: sub_map.seq_end + 1,
            });
        if key == keys.last() {
            assert(history.apply_to_stamped_map(stamped_map).value[key]
                == sub_map.value[key].merge(normalize_message(msgs.last())));
            assert(sub_map.value[key].merge(normalize_message(msgs.last())) == normalize_message(msgs.last()));
            assert(keys.contains(key));
            Key::strictly_sorted_implies_unique(keys);
            let i = keys.index_of(key);
            assert(0 <= i < keys.len());
            assert(keys[i] == key);
            assert(i == keys.len() - 1) by {
                if i < keys.len() - 1 {
                    assert(keys[i] == keys.last());
                }
            }
            assert(msgs[i] == msgs.last());
            assert(history.apply_to_stamped_map(stamped_map).value[key]
                == normalize_message(msgs[keys.index_of(key)]));
        } else {
            assert(history.apply_to_stamped_map(stamped_map).value[key] == sub_map.value[key]);
            if keys.contains(key) {
                Key::strictly_sorted_implies_unique(keys);
                let i = keys.index_of(key);
                assert(0 <= i < keys.len());
                assert(keys[i] == key);
                assert(i < keys.len() - 1) by {
                    if i == keys.len() - 1 {
                        assert(keys.last() == key);
                    }
                }
                assert(keys.drop_last()[i] == key);
                assert(keys.drop_last().contains(key));
                assert(msgs.drop_last()[i] == msgs[i]);
                Key::strictly_sorted_implies_unique(keys.drop_last());
                assert(msgs.drop_last()[keys.drop_last().index_of(key)] == msgs[i]);
                assert(sub_map.value[key] == normalize_message(msgs.drop_last()[keys.drop_last().index_of(key)]));
                assert(history.apply_to_stamped_map(stamped_map).value[key]
                    == normalize_message(msgs[keys.index_of(key)]));
            } else {
                assert(!keys.drop_last().contains(key));
                assert(sub_map.value[key] == stamped_map.value[key]);
                assert(history.apply_to_stamped_map(stamped_map).value[key] == stamped_map.value[key]);
            }
        }
    }
}

proof fn allocation_seal_preserves_kmmap(pre: AllocationBranch, aux_ptr: Pointer)
    requires
        pre.inv(),
        crate::implementation::ConcreteBranchRefinement_v::allocation_branch_can_seal(pre, aux_ptr),
    ensures
        crate::implementation::ConcreteBranchRefinement_v::allocation_branch_seal(pre, aux_ptr).kmmap_i() == pre.kmmap_i(),
{
    let post = crate::implementation::ConcreteBranchRefinement_v::allocation_branch_seal(pre, aux_ptr);
    if aux_ptr is Some {
        let branch = pre.branch.unwrap();
        let sealed_branch = branch.seal(aux_ptr.unwrap(), pre.mini_allocator.reserved_aus());
        assert(post.branch == Some(sealed_branch));
        assert(!pre.mini_allocator.page_is_reserved(aux_ptr.unwrap()));
        assert(branch.disk_view.is_fresh(set!{aux_ptr.unwrap()}));
        linked_seal_preserves_kmmap(branch, aux_ptr.unwrap(), pre.mini_allocator.reserved_aus());
        assert(post.kmmap_i() == pre.kmmap_i());
    } else {
        assert(post.branch == pre.branch);
        assert(post.kmmap_i() == pre.kmmap_i());
    }
}

proof fn query_step_refines_to_abstract_map(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
    needed: Set<Address>,
)
    requires
        pre.wf(),
        post.wf(),
        pre.refinement_wf(),
        post.refinement_wf(),
        ConcreteBranch::State::query(pre, post, lbl, reads, needed),
    ensures
        AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
{
    reveal(ConcreteBranch::State::query);
    reveal(ConcreteBranch::State::next);
    reveal(ConcreteBranch::State::next_by);
    reveal(AbstractMap::State::next);
    reveal(AbstractMap::State::next_by);

    assert(ConcreteBranch::State::next_by(pre, post, lbl, ConcreteBranch::Step::query(reads, needed)));
    assert(ConcreteBranch::State::next(pre, post, lbl));
    ConcreteBranch::State::next_refines(pre, post, lbl);

    match lbl {
        ConcreteBranch::Label::Query{key, msg, depth} => {
            let alloc = pre.i();
            let branch = pre.overlay_branch().unwrap();
            assert(alloc.branch == Some(branch));
            allocation_query_refines_to_kmmap(branch, key);
            assert(post.cached_branch == pre.cached_branch);
            assert(post.abstract_map_i() == pre.abstract_map_i());
            assert(pre.abstract_map_i().stamped_map.value[key] == normalize_message(msg));
            assert(AbstractMap::State::next_by(
                pre.abstract_map_i(),
                post.abstract_map_i(),
                pre.label_to_abstract_map(lbl),
                AbstractMap::Step::query(),
            ));
        }
        _ => { assert(false); }
    }
}

proof fn append_step_refines_to_abstract_map(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
    writes: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
    needed: Set<Address>,
    new_cache: crate::implementation::Cache_v::Cache::State,
)
    requires
        pre.wf(),
        post.wf(),
        pre.refinement_wf(),
        post.refinement_wf(),
        ConcreteBranch::State::append(pre, post, lbl, reads, writes, needed, new_cache),
    ensures
        AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
{
    reveal(ConcreteBranch::State::append);
    reveal(ConcreteBranch::State::next);
    reveal(ConcreteBranch::State::next_by);
    reveal(AbstractMap::State::next);
    reveal(AbstractMap::State::next_by);

    assert(ConcreteBranch::State::next_by(pre, post, lbl, ConcreteBranch::Step::append(reads, writes, needed, new_cache)));
    assert(ConcreteBranch::State::next(pre, post, lbl));
    ConcreteBranch::State::next_refines(pre, post, lbl);

    match lbl {
        ConcreteBranch::Label::Append{keys, msgs, depth} => {
            assert(keys.len() > 0);
            let alloc = pre.i();
            let first_key = keys[0];
            let branch = pre.overlay_branch().unwrap();
            assert(alloc.branch == Some(branch));
            let path = BranchPath{branch, key: first_key, depth};
            append_puts_wf(pre.cached_branch.seq_end, keys, msgs);
            allocation_append_refines_to_abstract_map(alloc, post.i(), pre.cached_branch.seq_end, keys, msgs, path);
            assert(post.cached_branch.seq_end == pre.cached_branch.seq_end + keys.len());
            MsgHistory::map_plus_history_lemma(
                pre.abstract_map_i().stamped_map,
                append_puts(pre.cached_branch.seq_end, keys, msgs),
            );
            assert(post.abstract_map_i().stamped_map.value
                == MsgHistory::map_plus_history(pre.abstract_map_i().stamped_map, append_puts(pre.cached_branch.seq_end, keys, msgs)).value);
            assert(post.abstract_map_i().stamped_map.seq_end
                == MsgHistory::map_plus_history(pre.abstract_map_i().stamped_map, append_puts(pre.cached_branch.seq_end, keys, msgs)).seq_end);
            assert(post.abstract_map_i().stamped_map
                == MsgHistory::map_plus_history(pre.abstract_map_i().stamped_map, append_puts(pre.cached_branch.seq_end, keys, msgs)));
            assert(AbstractMap::State::next_by(
                pre.abstract_map_i(),
                post.abstract_map_i(),
                pre.label_to_abstract_map(lbl),
                AbstractMap::Step::put(),
            ));
        }
        _ => { assert(false); }
    }
}

proof fn grow_step_refines_to_abstract_map(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
    writes: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
    new_cache: crate::implementation::Cache_v::Cache::State,
)
    requires
        pre.wf(),
        post.wf(),
        pre.refinement_wf(),
        post.refinement_wf(),
        ConcreteBranch::State::grow(pre, post, lbl, reads, writes, new_cache),
    ensures
        AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
{
    reveal(ConcreteBranch::State::grow);
    reveal(ConcreteBranch::State::next);
    reveal(ConcreteBranch::State::next_by);
    reveal(AbstractMap::State::next);
    reveal(AbstractMap::State::next_by);

    assert(ConcreteBranch::State::next_by(pre, post, lbl, ConcreteBranch::Step::grow(reads, writes, new_cache)));
    assert(ConcreteBranch::State::next(pre, post, lbl));
    ConcreteBranch::State::next_refines(pre, post, lbl);

    match lbl {
        ConcreteBranch::Label::Grow{new_root_addr} => {
            let alloc = pre.i();
            let branch = pre.overlay_branch().unwrap();
            assert(alloc.branch == Some(branch));
            allocation_grow_preserves_kmmap(alloc, new_root_addr);
            assert(post.cached_branch.seq_end == pre.cached_branch.seq_end);
            assert(post.abstract_map_i() == pre.abstract_map_i());
            assert(AbstractMap::State::next_by(
                pre.abstract_map_i(),
                post.abstract_map_i(),
                pre.label_to_abstract_map(lbl),
                AbstractMap::Step::internal(),
            ));
        }
        _ => { assert(false); }
    }
}

proof fn split_step_refines_to_abstract_map(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
    writes: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
    needed: Set<Address>,
    new_cache: crate::implementation::Cache_v::Cache::State,
)
    requires
        pre.wf(),
        post.wf(),
        pre.refinement_wf(),
        post.refinement_wf(),
        ConcreteBranch::State::split(pre, post, lbl, reads, writes, needed, new_cache),
    ensures
        AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
{
    reveal(ConcreteBranch::State::split);
    reveal(ConcreteBranch::State::next);
    reveal(ConcreteBranch::State::next_by);
    reveal(AbstractMap::State::next);
    reveal(AbstractMap::State::next_by);

    assert(ConcreteBranch::State::next_by(pre, post, lbl, ConcreteBranch::Step::split(reads, writes, needed, new_cache)));
    assert(ConcreteBranch::State::next(pre, post, lbl));
    ConcreteBranch::State::next_refines(pre, post, lbl);

    match lbl {
        ConcreteBranch::Label::Split{new_child_addr, pivot, depth, split_arg} => {
            let alloc = pre.i();
            let branch = pre.overlay_branch().unwrap();
            assert(alloc.branch == Some(branch));
            let path = BranchPath{branch, key: pivot, depth};
            allocation_split_preserves_kmmap(alloc, new_child_addr, path, split_arg);
            assert(post.cached_branch.seq_end == pre.cached_branch.seq_end);
            assert(post.abstract_map_i() == pre.abstract_map_i());
            assert(AbstractMap::State::next_by(
                pre.abstract_map_i(),
                post.abstract_map_i(),
                pre.label_to_abstract_map(lbl),
                AbstractMap::Step::internal(),
            ));
        }
        _ => { assert(false); }
    }
}

proof fn seal_step_refines_to_abstract_map(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
    writes: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
    new_cache: crate::implementation::Cache_v::Cache::State,
)
    requires
        pre.wf(),
        post.wf(),
        pre.refinement_wf(),
        post.refinement_wf(),
        ConcreteBranch::State::seal(pre, post, lbl, reads, writes, new_cache),
    ensures
        AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
{
    reveal(ConcreteBranch::State::seal);
    reveal(ConcreteBranch::State::next);
    reveal(ConcreteBranch::State::next_by);
    reveal(AbstractMap::State::next);
    reveal(AbstractMap::State::next_by);

    assert(ConcreteBranch::State::next_by(pre, post, lbl, ConcreteBranch::Step::seal(reads, writes, new_cache)));
    assert(ConcreteBranch::State::next(pre, post, lbl));
    ConcreteBranch::State::next_refines(pre, post, lbl);

    match lbl {
        ConcreteBranch::Label::Seal{aux_ptr} => {
            let alloc = pre.i();
            if alloc.branch is Some {
                assert(pre.overlay_branch() == alloc.branch);
            }
            allocation_seal_preserves_kmmap(alloc, aux_ptr);
            assert(post.cached_branch.seq_end == pre.cached_branch.seq_end);
            assert(post.abstract_map_i() == pre.abstract_map_i());
            assert(AbstractMap::State::next_by(
                pre.abstract_map_i(),
                post.abstract_map_i(),
                pre.label_to_abstract_map(lbl),
                AbstractMap::Step::internal(),
            ));
        }
        _ => { assert(false); }
    }
}

proof fn internal_cache_step_refines_to_abstract_map(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    new_cache: crate::implementation::Cache_v::Cache::State,
)
    requires
        pre.wf(),
        post.wf(),
        pre.refinement_wf(),
        post.refinement_wf(),
        ConcreteBranch::State::internal_cache(pre, post, lbl, new_cache),
    ensures
        AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
{
    reveal(ConcreteBranch::State::internal_cache);
    reveal(ConcreteBranch::State::next);
    reveal(ConcreteBranch::State::next_by);
    reveal(AbstractMap::State::next);
    reveal(AbstractMap::State::next_by);
    assert(ConcreteBranch::State::next_by(pre, post, lbl, ConcreteBranch::Step::internal_cache(new_cache)));
    assert(ConcreteBranch::State::next(pre, post, lbl));
    ConcreteBranch::State::next_refines(pre, post, lbl);
    assert(post.abstract_map_i() == pre.abstract_map_i());
    assert(AbstractMap::State::next_by(
        pre.abstract_map_i(),
        post.abstract_map_i(),
        pre.label_to_abstract_map(lbl),
        AbstractMap::Step::internal(),
    ));
}

proof fn internal_disk_step_refines_to_abstract_map(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    new_disk: crate::spec::AsyncDisk_t::AsyncDisk::State,
)
    requires
        pre.wf(),
        post.wf(),
        pre.refinement_wf(),
        post.refinement_wf(),
        ConcreteBranch::State::internal_disk(pre, post, lbl, new_disk),
    ensures
        AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
{
    reveal(ConcreteBranch::State::internal_disk);
    reveal(ConcreteBranch::State::next);
    reveal(ConcreteBranch::State::next_by);
    reveal(AbstractMap::State::next);
    reveal(AbstractMap::State::next_by);
    assert(ConcreteBranch::State::next_by(pre, post, lbl, ConcreteBranch::Step::internal_disk(new_disk)));
    assert(ConcreteBranch::State::next(pre, post, lbl));
    ConcreteBranch::State::next_refines(pre, post, lbl);
    assert(post.i() == pre.i());
    assert(post.cached_branch == pre.cached_branch);
    assert(post.abstract_map_i().stamped_map.seq_end == pre.abstract_map_i().stamped_map.seq_end);
    assert(post.abstract_map_i().stamped_map.value == pre.abstract_map_i().stamped_map.value);
    assert(post.abstract_map_i() == pre.abstract_map_i());
    assert(AbstractMap::State::next_by(
        pre.abstract_map_i(),
        post.abstract_map_i(),
        pre.label_to_abstract_map(lbl),
        AbstractMap::Step::internal(),
    ));
}

proof fn cache_disk_ops_step_refines_to_abstract_map(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    new_cache: crate::implementation::Cache_v::Cache::State,
    new_disk: crate::spec::AsyncDisk_t::AsyncDisk::State,
    cache_requests: Set<crate::spec::AsyncDisk_t::DiskRequest>,
    cache_responses: Map<Address, crate::spec::AsyncDisk_t::DiskResponse>,
    disk_requests: Map<crate::spec::MapSpec_t::ID, crate::spec::AsyncDisk_t::DiskRequest>,
    disk_responses: Map<crate::spec::MapSpec_t::ID, crate::spec::AsyncDisk_t::DiskResponse>,
)
    requires
        pre.wf(),
        post.wf(),
        pre.refinement_wf(),
        post.refinement_wf(),
        ConcreteBranch::State::cache_disk_ops(
            pre,
            post,
            lbl,
            new_cache,
            new_disk,
            cache_requests,
            cache_responses,
            disk_requests,
            disk_responses,
        ),
    ensures
        AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
{
    reveal(ConcreteBranch::State::cache_disk_ops);
    reveal(ConcreteBranch::State::next);
    reveal(ConcreteBranch::State::next_by);
    reveal(AbstractMap::State::next);
    reveal(AbstractMap::State::next_by);
    assert(ConcreteBranch::State::next_by(
        pre,
        post,
        lbl,
        ConcreteBranch::Step::cache_disk_ops(
            new_cache,
            new_disk,
            cache_requests,
            cache_responses,
            disk_requests,
            disk_responses,
        ),
    ));
    assert(ConcreteBranch::State::next(pre, post, lbl));
    ConcreteBranch::State::next_refines(pre, post, lbl);
    assert(post.abstract_map_i() == pre.abstract_map_i());
    assert(AbstractMap::State::next_by(
        pre.abstract_map_i(),
        post.abstract_map_i(),
        pre.label_to_abstract_map(lbl),
        AbstractMap::Step::internal(),
    ));
}

pub proof fn next_refines_to_abstract_map(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
)
    requires
        pre.wf(),
        post.wf(),
        pre.refinement_wf(),
        post.refinement_wf(),
        ConcreteBranch::State::next(pre, post, lbl),
    ensures
        AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
{
    reveal(ConcreteBranch::State::next);
    reveal(ConcreteBranch::State::next_by);

    let step = choose |step| ConcreteBranch::State::next_by(pre, post, lbl, step);
    match step {
        ConcreteBranch::Step::query(reads, needed) =>
            query_step_refines_to_abstract_map(pre, post, lbl, reads, needed),
        ConcreteBranch::Step::append(reads, writes, needed, new_cache) =>
            append_step_refines_to_abstract_map(pre, post, lbl, reads, writes, needed, new_cache),
        ConcreteBranch::Step::grow(reads, writes, new_cache) =>
            grow_step_refines_to_abstract_map(pre, post, lbl, reads, writes, new_cache),
        ConcreteBranch::Step::split(reads, writes, needed, new_cache) =>
            split_step_refines_to_abstract_map(pre, post, lbl, reads, writes, needed, new_cache),
        ConcreteBranch::Step::seal(reads, writes, new_cache) =>
            seal_step_refines_to_abstract_map(pre, post, lbl, reads, writes, new_cache),
        ConcreteBranch::Step::internal_cache(new_cache) =>
            internal_cache_step_refines_to_abstract_map(pre, post, lbl, new_cache),
        ConcreteBranch::Step::internal_disk(new_disk) =>
            internal_disk_step_refines_to_abstract_map(pre, post, lbl, new_disk),
        ConcreteBranch::Step::cache_disk_ops(
            new_cache,
            new_disk,
            cache_requests,
            cache_responses,
            disk_requests,
            disk_responses,
        ) =>
            cache_disk_ops_step_refines_to_abstract_map(
                pre,
                post,
                lbl,
                new_cache,
                new_disk,
                cache_requests,
                cache_responses,
                disk_requests,
                disk_responses,
            ),
        _ => { }
    }
}

} // verus!
