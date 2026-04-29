// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::map::*;
use vstd::assert_sets_equal;

use crate::abstract_system::AbstractMap_v::AbstractMap;
use crate::abstract_system::MsgHistory_v::{KeyedMessage, MsgHistory};
use crate::abstract_system::StampedMap_v::{Stamped, StampedMap};
use crate::allocation_layer::AllocationBranch_v::{AllocationBranch, BranchNode, Summary};
use crate::allocation_layer::AllocationBranchBetree_v::summary_aus;
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::Buffer_v::SimpleBuffer;
use crate::betree::LinkedBranch_v::LinkedBranch;
use crate::betree::LinkedBranch_v::Refinement_v as LinkedBranchRefinement;
use crate::betree::PivotBranch_v::Node as PivotNode;
use crate::betree::PivotBranchRefinement_v;
use crate::disk::GenericDisk_v::{AU, Address, Pointer};
use crate::implementation::AllocationBranchStack_v::{
    active_branch_query_or_nop, AllocationBranchStack, SealedAllocationBranchStack, is_nop_message,
};
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

pub open spec fn append_put_message(msg: Message) -> Message
{
    if is_nop_message(msg) {
        msg
    } else {
        normalize_message(msg)
    }
}

pub open spec fn buffer_kmmap_i(buffer: SimpleBuffer) -> TotalKMMap
{
    TotalKMMap(Map::new(
        |k: Key| true,
        |k: Key| normalize_message(buffer.query(k)),
    ))
}

pub open spec fn linked_branch_sparse_map(branch: LinkedBranch<Summary>) -> Map<Key, Message>
{
    let raw_map = branch.i().i().map;
    Map::new(
        |k: Key| raw_map.contains_key(k) && !is_nop_message(raw_map[k]),
        |k: Key| raw_map[k],
    )
}

pub open spec fn active_branch_sparse_map(active_branch: AllocationBranch) -> Map<Key, Message>
{
    if active_branch.branch is Some {
        linked_branch_sparse_map(active_branch.branch.unwrap())
    } else {
        Map::empty()
    }
}

pub open spec fn sealed_sparse_map_up_to(
    sealed_stack: SealedAllocationBranchStack,
    end: nat,
) -> Map<Key, Message>
    recommends end <= sealed_stack.sealed_roots.len()
    decreases end
{
    if end == 0 {
        Map::empty()
    } else {
        sealed_sparse_map_up_to(sealed_stack, (end - 1) as nat).union_prefer_right(
            linked_branch_sparse_map(sealed_stack.sealed_branch_at((end - 1) as nat))
        )
    }
}

pub open spec fn stack_sparse_map(
    sealed_stack: SealedAllocationBranchStack,
    active_branch: AllocationBranch,
) -> Map<Key, Message>
{
    sealed_stack.sparse_map()
        .union_prefer_right(active_branch_sparse_map(active_branch))
}

pub open spec fn append_puts_up_to(
    start_lsn: nat,
    keys: Seq<Key>,
    msgs: Seq<Message>,
    end: nat,
) -> MsgHistory
    recommends
        end <= keys.len(),
        keys.len() == msgs.len(),
{
    let seq_end = start_lsn + end;
    let puts = Map::new(
        |lsn: nat| start_lsn <= lsn < seq_end,
        |lsn: nat| {
            let idx = (lsn - start_lsn) as int;
            KeyedMessage{ key: keys[idx], message: append_put_message(msgs[idx]) }
        },
    );
    MsgHistory{ msgs: puts, seq_start: start_lsn, seq_end }
}

pub open spec fn append_puts(start_lsn: nat, keys: Seq<Key>, msgs: Seq<Message>) -> MsgHistory
    recommends
        keys.len() == msgs.len(),
{
    append_puts_up_to(start_lsn, keys, msgs, keys.len() as nat)
}

pub open spec fn append_sparse_map_up_to(keys: Seq<Key>, msgs: Seq<Message>, end: nat) -> Map<Key, Message>
    recommends
        end <= keys.len(),
        keys.len() == msgs.len(),
    decreases end
{
    if end == 0 {
        Map::empty()
    } else {
        let idx = (end - 1) as int;
        let prev = append_sparse_map_up_to(keys, msgs, (end - 1) as nat);
        if is_nop_message(msgs[idx]) {
            prev
        } else {
            prev.insert(keys[idx], msgs[idx])
        }
    }
}

pub open spec fn append_sparse_map(keys: Seq<Key>, msgs: Seq<Message>) -> Map<Key, Message>
    recommends
        keys.len() == msgs.len(),
{
    append_sparse_map_up_to(keys, msgs, keys.len() as nat)
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

pub proof fn append_puts_up_to_wf(start_lsn: nat, keys: Seq<Key>, msgs: Seq<Message>, end: nat)
    requires
        end <= keys.len(),
        keys.len() == msgs.len(),
    ensures
        append_puts_up_to(start_lsn, keys, msgs, end).wf(),
        append_puts_up_to(start_lsn, keys, msgs, end).seq_start == start_lsn,
        append_puts_up_to(start_lsn, keys, msgs, end).seq_end == start_lsn + end,
        append_puts_up_to(start_lsn, keys, msgs, end).len() == end,
{
    let puts = append_puts_up_to(start_lsn, keys, msgs, end);
    assert(puts.seq_start <= puts.seq_end);
    assert forall |lsn: nat| #[trigger] puts.msgs.dom().contains(lsn) <==> puts.contains(lsn) by { };
}

pub proof fn append_puts_up_to_discard_recent_last(
    start_lsn: nat,
    keys: Seq<Key>,
    msgs: Seq<Message>,
    end: nat,
)
    requires
        0 < end <= keys.len(),
        keys.len() == msgs.len(),
    ensures
        append_puts_up_to(start_lsn, keys, msgs, end)
            .discard_recent((start_lsn + end - 1) as nat)
            == append_puts_up_to(start_lsn, keys, msgs, (end - 1) as nat),
{
    let hist = append_puts_up_to(start_lsn, keys, msgs, end);
    let last_lsn = (start_lsn + end - 1) as nat;
    let lhs = hist.discard_recent(last_lsn);
    let rhs = append_puts_up_to(start_lsn, keys, msgs, (end - 1) as nat);
    assert(lhs.seq_start == rhs.seq_start);
    assert(lhs.seq_end == rhs.seq_end);
    assert(lhs.msgs =~= rhs.msgs) by {
        assert forall |lsn: nat| #[trigger] lhs.msgs.contains_key(lsn)
            <==> rhs.msgs.contains_key(lsn) by { }
        assert forall |lsn: nat| #[trigger] lhs.msgs.contains_key(lsn)
            implies lhs.msgs[lsn] == rhs.msgs[lsn] by { }
    }
}

pub proof fn append_put_message_merge(old: Message, msg: Message)
    requires
        old == normalize_message(old),
    ensures
        old.merge(append_put_message(msg)) == if is_nop_message(msg) {
            old
        } else {
            normalize_message(msg)
        },
{
    assert(old is Define);
    if is_nop_message(msg) {
        assert(msg == Message::Update{delta: crate::spec::Messages_t::nop_delta()});
    }
}

pub proof fn append_puts_up_to_apply_to_sparse_buffer(
    buffer: SimpleBuffer,
    start_lsn: nat,
    keys: Seq<Key>,
    msgs: Seq<Message>,
    end: nat,
)
    requires
        end <= keys.len(),
        keys.len() == msgs.len(),
    ensures
        MsgHistory::map_plus_history(
            Stamped{value: buffer_kmmap_i(buffer), seq_end: start_lsn},
            append_puts_up_to(start_lsn, keys, msgs, end),
        ) == (Stamped{
            value: buffer_kmmap_i(SimpleBuffer{
                map: buffer.map.union_prefer_right(append_sparse_map_up_to(keys, msgs, end)),
            }),
            seq_end: start_lsn + end,
        }),
    decreases end
{
    let pre_stamped = Stamped{value: buffer_kmmap_i(buffer), seq_end: start_lsn};
    let hist = append_puts_up_to(start_lsn, keys, msgs, end);
    append_puts_up_to_wf(start_lsn, keys, msgs, end);
    kmmap_i_wf(buffer);

    if end == 0 {
        let post_buffer = SimpleBuffer{map: buffer.map.union_prefer_right(append_sparse_map_up_to(keys, msgs, end))};
        assert(append_sparse_map_up_to(keys, msgs, end) == Map::<Key, Message>::empty());
        assert(post_buffer.map =~= buffer.map) by {
            assert forall |key: Key| #[trigger] post_buffer.map.contains_key(key)
                <==> buffer.map.contains_key(key) by { }
            assert forall |key: Key| #[trigger] post_buffer.map.contains_key(key)
                implies post_buffer.map[key] == buffer.map[key] by { }
        }
        assert(buffer_kmmap_i(post_buffer).0 =~= buffer_kmmap_i(buffer).0);
    } else {
        let prev_end = (end - 1) as nat;
        let last_lsn = (start_lsn + end - 1) as nat;
        let last_idx = prev_end as int;
        let last_key = keys[last_idx];
        let last_msg = msgs[last_idx];

        append_puts_up_to_discard_recent_last(start_lsn, keys, msgs, end);
        append_puts_up_to_apply_to_sparse_buffer(buffer, start_lsn, keys, msgs, prev_end);

        let prev_sparse = append_sparse_map_up_to(keys, msgs, prev_end);
        let prev_buffer = SimpleBuffer{map: buffer.map.union_prefer_right(prev_sparse)};
        let prev_stamped = Stamped{value: buffer_kmmap_i(prev_buffer), seq_end: start_lsn + prev_end};
        let final_sparse = append_sparse_map_up_to(keys, msgs, end);
        let final_buffer = SimpleBuffer{map: buffer.map.union_prefer_right(final_sparse)};
        let sub_hist = append_puts_up_to(start_lsn, keys, msgs, prev_end);

        assert(hist.discard_recent(last_lsn) == sub_hist);
        assert(hist.discard_recent(last_lsn).apply_to_stamped_map(pre_stamped) == prev_stamped);
        assert(prev_stamped.seq_end + 1 == start_lsn + end);
        append_put_message_merge(prev_stamped.value[last_key], last_msg);
        assert(buffer_kmmap_i(final_buffer).0 =~= hist.apply_to_stamped_map(pre_stamped).value.0) by {
            assert forall |key: Key| #[trigger] buffer_kmmap_i(final_buffer).0.contains_key(key)
                <==> hist.apply_to_stamped_map(pre_stamped).value.0.contains_key(key) by {
            }
            assert forall |key: Key| #[trigger] buffer_kmmap_i(final_buffer).0.contains_key(key)
                implies buffer_kmmap_i(final_buffer).0[key]
                    == hist.apply_to_stamped_map(pre_stamped).value.0[key] by {
                if key == last_key {
                    append_put_message_merge(prev_stamped.value[last_key], last_msg);
                    if is_nop_message(last_msg) {
                        assert(final_sparse == prev_sparse);
                        assert(final_buffer.map == prev_buffer.map);
                    } else {
                        assert(final_sparse == prev_sparse.insert(last_key, last_msg));
                        assert(final_buffer.query(key) == last_msg);
                    }
                } else {
                    if is_nop_message(last_msg) {
                        assert(final_sparse == prev_sparse);
                        assert(final_buffer.map == prev_buffer.map);
                    } else {
                        assert(final_sparse == prev_sparse.insert(last_key, last_msg));
                        assert(final_buffer.query(key) == prev_buffer.query(key));
                    }
                }
            }
        }
        assert(hist.apply_to_stamped_map(pre_stamped).seq_end == start_lsn + end);
    }
}

pub proof fn append_sparse_map_up_to_contains_iff(
    keys: Seq<Key>,
    msgs: Seq<Message>,
    end: nat,
    key: Key,
)
    requires
        end <= keys.len(),
        keys.len() == msgs.len(),
    ensures
        append_sparse_map_up_to(keys, msgs, end).contains_key(key)
            <==> exists |i: int| #![auto] 0 <= i < end && keys[i] == key && !is_nop_message(msgs[i]),
    decreases end
{
    if end == 0 {
    } else {
        let prev_end = (end - 1) as nat;
        let idx = prev_end as int;
        append_sparse_map_up_to_contains_iff(keys, msgs, prev_end, key);
        if is_nop_message(msgs[idx]) {
            assert forall |i: int| #![auto] 0 <= i < end && keys[i] == key && !is_nop_message(msgs[i])
                implies 0 <= i < prev_end && keys[i] == key && !is_nop_message(msgs[i]) by {
                if i == idx {
                    assert(false);
                }
            }
        } else {
            assert(append_sparse_map_up_to(keys, msgs, end)
                == append_sparse_map_up_to(keys, msgs, prev_end).insert(keys[idx], msgs[idx]));
            if append_sparse_map_up_to(keys, msgs, end).contains_key(key) {
                if key == keys[idx] {
                } else {
                    assert(append_sparse_map_up_to(keys, msgs, prev_end).contains_key(key));
                }
            }
        }
    }
}

pub proof fn append_sparse_map_up_to_value(
    keys: Seq<Key>,
    msgs: Seq<Message>,
    end: nat,
    key: Key,
    idx: int,
)
    requires
        end <= keys.len(),
        keys.len() == msgs.len(),
        Key::is_strictly_sorted(keys),
        0 <= idx < end,
        keys[idx] == key,
        !is_nop_message(msgs[idx]),
    ensures
        append_sparse_map_up_to(keys, msgs, end)[key] == msgs[idx],
    decreases end
{
    if end == 0 {
    } else {
        let prev_end = (end - 1) as nat;
        let last_idx = prev_end as int;
        Key::strictly_sorted_implies_unique(keys);
        if is_nop_message(msgs[last_idx]) {
            assert(idx < prev_end);
            append_sparse_map_up_to_value(keys, msgs, prev_end, key, idx);
        } else {
            assert(append_sparse_map_up_to(keys, msgs, end)
                == append_sparse_map_up_to(keys, msgs, prev_end).insert(keys[last_idx], msgs[last_idx]));
            if idx == last_idx {
            } else {
                assert(idx < prev_end);
                assert(key != keys[last_idx]) by {
                    if key == keys[last_idx] {
                        if idx < last_idx {
                            assert(keys[idx] == keys[last_idx]);
                            assert(idx == last_idx);
                        } else {
                            assert(false);
                        }
                    }
                }
                append_sparse_map_up_to_value(keys, msgs, prev_end, key, idx);
            }
        }
    }
}

pub proof fn append_sparse_map_matches_route(keys: Seq<Key>, msgs: Seq<Message>)
    requires
        keys.len() > 0,
        keys.len() == msgs.len(),
        Key::is_strictly_sorted(keys),
    ensures
        append_sparse_map(keys, msgs) == Map::new(
            |key: Key| {
                let leaf = PivotNode::Leaf{ keys, msgs };
                keys.contains(key) && !is_nop_message(msgs[leaf.route(key)])
            },
            |key: Key| {
                let leaf = PivotNode::Leaf{ keys, msgs };
                msgs[leaf.route(key)]
            },
        ),
{
    let leaf = PivotNode::Leaf{ keys, msgs };
    assert(leaf.wf());
    broadcast use crate::betree::PivotBranch_v::Node::route_ensures;
    assert(append_sparse_map(keys, msgs) =~= Map::new(
        |key: Key| keys.contains(key) && !is_nop_message(msgs[leaf.route(key)]),
        |key: Key| msgs[leaf.route(key)],
    )) by {
        assert forall |key: Key| #[trigger] append_sparse_map(keys, msgs).contains_key(key)
            <==> (keys.contains(key) && !is_nop_message(msgs[leaf.route(key)])) by {
            append_sparse_map_up_to_contains_iff(keys, msgs, keys.len() as nat, key);
            leaf.route_ensures(key);
            if append_sparse_map(keys, msgs).contains_key(key) {
                let idx = choose |i: int| 0 <= i < keys.len()
                    && #[trigger] keys[i] == key
                    && !is_nop_message(msgs[i]);
                assert(keys.contains(key));
                Key::strictly_sorted_implies_unique(keys);
                assert(0 <= leaf.route(key) < keys.len());
                assert(keys[leaf.route(key)] == key);
                assert(idx == leaf.route(key));
            } else if keys.contains(key) && !is_nop_message(msgs[leaf.route(key)]) {
                assert(0 <= leaf.route(key) < keys.len());
            }
        }
        assert forall |key: Key| #[trigger] append_sparse_map(keys, msgs).contains_key(key)
            implies append_sparse_map(keys, msgs)[key] == msgs[leaf.route(key)] by {
            append_sparse_map_up_to_contains_iff(keys, msgs, keys.len() as nat, key);
            leaf.route_ensures(key);
            let idx = choose |i: int| 0 <= i < keys.len()
                && #[trigger] keys[i] == key
                && !is_nop_message(msgs[i]);
            Key::strictly_sorted_implies_unique(keys);
            assert(0 <= leaf.route(key) < keys.len());
            assert(keys[leaf.route(key)] == key);
            assert(idx == leaf.route(key));
            append_sparse_map_up_to_value(keys, msgs, keys.len() as nat, key, idx);
        }
    }
}

pub proof fn kmmap_i_wf(buffer: SimpleBuffer)
    ensures
        buffer_kmmap_i(buffer).wf(),
{
    let kmmap = buffer_kmmap_i(buffer);
    assert_sets_equal!(kmmap.dom(), crate::spec::TotalKMMap_t::total_domain());
}

pub proof fn linked_branch_sparse_query(branch: LinkedBranch<Summary>, key: Key)
    requires
        branch.inv(),
    ensures
        (SimpleBuffer{map: linked_branch_sparse_map(branch)}).query(key) == branch.query(key),
{
    LinkedBranchRefinement::query_refines(branch, key, branch.query(key));
    LinkedBranchRefinement::i_wf(branch);
    PivotBranchRefinement_v::query_refines(
        branch.i(),
        PivotBranchRefinement_v::QueryLabel{key, msg: branch.i().query(key)},
    );
    let raw_map = branch.i().i().map;
    assert(branch.i().i().query(key) == branch.query(key));
    if raw_map.contains_key(key) {
        if is_nop_message(raw_map[key]) {
            assert(raw_map[key] == Message::Update{delta: crate::spec::Messages_t::nop_delta()});
            assert(!(linked_branch_sparse_map(branch).contains_key(key)));
        } else {
            assert(linked_branch_sparse_map(branch).contains_key(key));
            assert(linked_branch_sparse_map(branch)[key] == raw_map[key]);
        }
    } else {
        assert(!(linked_branch_sparse_map(branch).contains_key(key)));
    }
}

pub proof fn linked_branch_sparse_map_preserves_i(
    branch1: LinkedBranch<Summary>,
    branch2: LinkedBranch<Summary>,
)
    requires
        branch1.i().i() == branch2.i().i(),
    ensures
        linked_branch_sparse_map(branch1) == linked_branch_sparse_map(branch2),
{
    let raw1 = branch1.i().i().map;
    let raw2 = branch2.i().i().map;
    assert(raw1 == raw2);
    assert(linked_branch_sparse_map(branch1) =~= linked_branch_sparse_map(branch2)) by {
        assert forall |key: Key| #[trigger] linked_branch_sparse_map(branch1).contains_key(key)
            <==> linked_branch_sparse_map(branch2).contains_key(key) by { }
        assert forall |key: Key| #[trigger] linked_branch_sparse_map(branch1).contains_key(key)
            implies linked_branch_sparse_map(branch1)[key] == linked_branch_sparse_map(branch2)[key] by { }
    }
}

pub proof fn linked_branch_sparse_map_preserves_subdisk(
    small: LinkedBranch<Summary>,
    big: LinkedBranch<Summary>,
)
    requires
        small.inv(),
        big.inv(),
        small.root == big.root,
        small.disk_view.is_sub_disk(big.disk_view),
    ensures
        linked_branch_sparse_map(small) == linked_branch_sparse_map(big),
{
    small.subdisk_same_i_internal(small.the_ranking(), big, big.the_ranking());
    assert(small.i_internal(small.the_ranking()) =~= big.i_internal(big.the_ranking()));
    assert(small.i() =~= big.i());
    assert(small.i().i() == big.i().i());
    linked_branch_sparse_map_preserves_i(small, big);
}

pub proof fn active_branch_sparse_query(active_branch: AllocationBranch, key: Key)
    requires
        active_branch.inv(),
    ensures
        (SimpleBuffer{map: active_branch_sparse_map(active_branch)}).query(key)
            == active_branch_query_or_nop(active_branch, key),
{
    if active_branch.branch is Some {
        let branch = active_branch.branch.unwrap();
        linked_branch_sparse_query(branch, key);
    }
}

pub proof fn sealed_sparse_map_up_to_query(
    sealed_stack: SealedAllocationBranchStack,
    end: nat,
    key: Key,
)
    requires
        sealed_stack.wf(),
        end <= sealed_stack.sealed_roots.len(),
    ensures
        (SimpleBuffer{map: sealed_sparse_map_up_to(sealed_stack, end)}).query(key)
            == sealed_stack.query_up_to(end, key),
    decreases end
{
    if end == 0 {
    } else {
        sealed_sparse_map_up_to_query(sealed_stack, (end - 1) as nat, key);
        let branch = sealed_stack.sealed_branch_at((end - 1) as nat);
        linked_branch_sparse_query(branch, key);
    }
}

pub proof fn sealed_stack_sparse_query(sealed_stack: SealedAllocationBranchStack, key: Key)
    requires
        sealed_stack.wf(),
    ensures
        sealed_stack.sparse_buffer().query(key) == sealed_stack.query(key),
{
    sealed_sparse_map_up_to_query(sealed_stack, sealed_stack.sealed_roots.len() as nat, key);
}

pub proof fn sealed_stack_disk_disjoint_from_branch(
    sealed_stack: SealedAllocationBranchStack,
    sealed_branch: LinkedBranch<Summary>,
)
    requires
        sealed_stack.wf(),
        sealed_branch.valid_sealed_branch(),
        sealed_branch.tight_disk_view_with_summary(),
        summary_aus(sealed_stack.branch_summary()).disjoint(sealed_branch.get_summary()),
    ensures
        sealed_stack.sealed_disk.entries.dom().disjoint(sealed_branch.disk_view.entries.dom()),
{
    assert(sealed_stack.sealed_disk.entries.dom().disjoint(sealed_branch.disk_view.entries.dom())) by {
        assert forall |addr: Address| #[trigger] sealed_stack.sealed_disk.entries.dom().contains(addr)
            implies !sealed_branch.disk_view.entries.dom().contains(addr)
        by {
            if sealed_branch.disk_view.entries.dom().contains(addr) {
                assert(summary_aus(sealed_stack.branch_summary()).contains(addr.au));
                assert(sealed_branch.disk_view.entries.dom() =~= sealed_branch.full_repr());
                assert(sealed_branch.full_repr().contains(addr));
                assert(sealed_branch.get_summary().contains(addr.au));
            }
        }
    }
}

pub proof fn sealed_stack_push_preserves_sparse_map_up_to(
    sealed_stack: SealedAllocationBranchStack,
    sealed_branch: LinkedBranch<Summary>,
    end: nat,
)
    requires
        sealed_stack.wf(),
        sealed_branch.valid_sealed_branch(),
        sealed_branch.tight_disk_view_with_summary(),
        summary_aus(sealed_stack.branch_summary()).disjoint(sealed_branch.get_summary()),
        end <= sealed_stack.sealed_roots.len(),
    ensures
        sealed_sparse_map_up_to(sealed_stack.push_branch(sealed_branch), end)
            == sealed_sparse_map_up_to(sealed_stack, end),
    decreases end
{
    if end == 0 {
    } else {
        sealed_stack_push_preserves_sparse_map_up_to(
            sealed_stack,
            sealed_branch,
            (end - 1) as nat,
        );
        sealed_stack.push_branch_preserves_wf(sealed_branch);
        sealed_stack_disk_disjoint_from_branch(sealed_stack, sealed_branch);

        let post_stack = sealed_stack.push_branch(sealed_branch);
        let idx = (end - 1) as nat;
        let pre_branch = sealed_stack.sealed_branch_at(idx);
        let post_branch = post_stack.sealed_branch_at(idx);
        assert(post_stack.sealed_roots[idx as int] == sealed_stack.sealed_roots[idx as int]);
        assert(pre_branch.root == post_branch.root);
        assert(pre_branch.disk_view.is_sub_disk(post_branch.disk_view)) by {
            assert forall |addr: Address| #[trigger] pre_branch.disk_view.entries.contains_key(addr)
                implies post_branch.disk_view.entries.contains_key(addr)
                    && post_branch.disk_view.entries[addr] == pre_branch.disk_view.entries[addr]
            by {
                if sealed_branch.disk_view.entries.contains_key(addr) {
                    assert(sealed_stack.sealed_disk.entries.dom().contains(addr));
                    assert(sealed_stack.sealed_disk.entries.dom().disjoint(sealed_branch.disk_view.entries.dom()));
                }
            }
        }
        assert(pre_branch.inv());
        assert(post_branch.inv());
        linked_branch_sparse_map_preserves_subdisk(pre_branch, post_branch);
        assert(sealed_sparse_map_up_to(post_stack, end)
            == sealed_sparse_map_up_to(post_stack, (end - 1) as nat)
                .union_prefer_right(linked_branch_sparse_map(post_branch)));
        assert(sealed_sparse_map_up_to(sealed_stack, end)
            == sealed_sparse_map_up_to(sealed_stack, (end - 1) as nat)
                .union_prefer_right(linked_branch_sparse_map(pre_branch)));
        assert(sealed_sparse_map_up_to(post_stack, end) =~= sealed_sparse_map_up_to(sealed_stack, end));
    }
}

pub proof fn sealed_stack_push_sparse_map(
    sealed_stack: SealedAllocationBranchStack,
    sealed_branch: LinkedBranch<Summary>,
)
    requires
        sealed_stack.wf(),
        sealed_branch.valid_sealed_branch(),
        sealed_branch.tight_disk_view_with_summary(),
        summary_aus(sealed_stack.branch_summary()).disjoint(sealed_branch.get_summary()),
    ensures
        sealed_stack.push_branch(sealed_branch).sparse_map()
            == sealed_stack.sparse_map().union_prefer_right(linked_branch_sparse_map(sealed_branch)),
{
    sealed_stack.push_branch_preserves_wf(sealed_branch);
    sealed_stack_disk_disjoint_from_branch(sealed_stack, sealed_branch);
    sealed_stack_push_preserves_sparse_map_up_to(
        sealed_stack,
        sealed_branch,
        sealed_stack.sealed_roots.len() as nat,
    );

    let post_stack = sealed_stack.push_branch(sealed_branch);
    let idx = sealed_stack.sealed_roots.len() as nat;
    let post_branch = post_stack.sealed_branch_at(idx);
    assert(post_stack.sealed_roots[idx as int] == sealed_branch.root);
    assert(post_branch.root == sealed_branch.root);
    assert(sealed_branch.disk_view.is_sub_disk(post_branch.disk_view)) by {
        assert forall |addr: Address| #[trigger] sealed_branch.disk_view.entries.contains_key(addr)
            implies post_branch.disk_view.entries.contains_key(addr)
                && post_branch.disk_view.entries[addr] == sealed_branch.disk_view.entries[addr]
        by { }
    }
    assert(sealed_branch.inv());
    assert(post_branch.inv());
    linked_branch_sparse_map_preserves_subdisk(sealed_branch, post_branch);
    assert(post_stack.sparse_map()
        == sealed_sparse_map_up_to(post_stack, post_stack.sealed_roots.len() as nat));
    assert(post_stack.sealed_roots.len() == sealed_stack.sealed_roots.len() + 1);
    assert(post_stack.sparse_map()
        == sealed_sparse_map_up_to(post_stack, sealed_stack.sealed_roots.len() as nat)
            .union_prefer_right(linked_branch_sparse_map(post_branch)));
    assert(post_stack.sparse_map() =~=
        sealed_stack.sparse_map().union_prefer_right(linked_branch_sparse_map(sealed_branch)));
}

pub proof fn active_branch_fill_sparse_unchanged(active_branch: AllocationBranch, aus: Set<crate::disk::GenericDisk_v::AU>)
    requires
        active_branch.can_fill(aus),
    ensures
        active_branch_sparse_map(active_branch.mini_allocator_fill(aus))
            == active_branch_sparse_map(active_branch),
{
}

pub proof fn active_branch_seal_sparse_unchanged(
    active_branch: AllocationBranch,
    aux_ptr: Pointer,
)
    requires
        active_branch.inv(),
        active_branch.can_seal(aux_ptr, active_branch.mini_allocator.removable_aus()),
    ensures
        active_branch_sparse_map(active_branch.branch_seal(
            aux_ptr,
            active_branch.mini_allocator.removable_aus(),
        )) == active_branch_sparse_map(active_branch),
{
    let dealloc_aus = active_branch.mini_allocator.removable_aus();
    active_branch.branch_seal_preserves_inv(aux_ptr, dealloc_aus);
    let pre_branch = active_branch.branch.unwrap();
    let post_branch = active_branch.branch_seal(aux_ptr, dealloc_aus).branch.unwrap();
    linked_branch_sparse_map_preserves_i(post_branch, pre_branch);
}

pub proof fn active_branch_append_sparse_effect(
    active_branch: AllocationBranch,
    keys: Seq<Key>,
    msgs: Seq<Message>,
    path: crate::betree::LinkedBranch_v::Path<Summary>,
)
    requires
        active_branch.inv(),
        active_branch.can_append(keys, msgs, path),
        forall |key: Key| #[trigger] keys.contains(key)
            ==> is_nop_message(active_branch.branch_query(key)),
    ensures
        active_branch_sparse_map(active_branch.branch_append(keys, msgs, path))
            == active_branch_sparse_map(active_branch).union_prefer_right(append_sparse_map(keys, msgs)),
{
    let pre_branch = active_branch.branch.unwrap();
    let post_branch = active_branch.branch_append(keys, msgs, path).branch.unwrap();
    let leaf = PivotNode::Leaf{ keys, msgs };
    let route_map = Map::new(
        |key: Key| keys.contains(key),
        |key: Key| msgs[leaf.route(key)],
    );

    LinkedBranchRefinement::append_refines(pre_branch, keys, msgs, path);
    LinkedBranchRefinement::i_wf(pre_branch);
    LinkedBranchRefinement::lemma_path_i_internal(path, pre_branch.the_ranking(), keys.last());
    LinkedBranchRefinement::lemma_path_target(path, pre_branch.the_ranking());
    assert(path.i() == path.i_internal(pre_branch.the_ranking()));
    assert(path.i().valid());
    assert(path.i().target() == path.target().i_internal(pre_branch.the_ranking()));
    assert(path.i().target() is Leaf);
    PivotBranchRefinement_v::append_refines(
        pre_branch.i(),
        PivotBranchRefinement_v::AppendLabel{keys, msgs, path: path.i()},
    );
    append_sparse_map_matches_route(keys, msgs);
    assert(post_branch == pre_branch.append(keys, msgs, path));
    assert(post_branch.i() == pre_branch.i().append(keys, msgs, path.i()));
    assert(post_branch.i().i().map == pre_branch.i().i().map.union_prefer_right(route_map));

    assert(active_branch_sparse_map(active_branch.branch_append(keys, msgs, path)) =~=
        active_branch_sparse_map(active_branch).union_prefer_right(append_sparse_map(keys, msgs))) by {
        assert forall |key: Key| #[trigger] active_branch_sparse_map(
                active_branch.branch_append(keys, msgs, path)
            ).contains_key(key)
            <==> active_branch_sparse_map(active_branch)
                .union_prefer_right(append_sparse_map(keys, msgs)).contains_key(key)
        by {
            let post_sparse = active_branch_sparse_map(active_branch.branch_append(keys, msgs, path));
            let pre_sparse = active_branch_sparse_map(active_branch);
            let append_map = append_sparse_map(keys, msgs);
            if post_sparse.contains_key(key) {
                if keys.contains(key) {
                    assert(route_map.contains_key(key));
                    assert(!is_nop_message(route_map[key]));
                    assert(append_map.contains_key(key));
                } else {
                    assert(!route_map.contains_key(key));
                    assert(pre_sparse.contains_key(key));
                }
            } else if pre_sparse.union_prefer_right(append_map).contains_key(key) {
                if append_map.contains_key(key) {
                    assert(keys.contains(key));
                    assert(route_map.contains_key(key));
                    assert(!is_nop_message(route_map[key]));
                    assert(post_sparse.contains_key(key));
                } else {
                    assert(pre_sparse.contains_key(key));
                    if keys.contains(key) {
                        active_branch_sparse_query(active_branch, key);
                        assert(is_nop_message(active_branch.branch_query(key)));
                        assert((SimpleBuffer{map: pre_sparse}).query(key) == active_branch.branch_query(key));
                        assert(!is_nop_message(pre_sparse[key]));
                        assert(false);
                    } else {
                        assert(!route_map.contains_key(key));
                        assert(post_sparse.contains_key(key));
                    }
                }
            }
        }
        assert forall |key: Key| #[trigger] active_branch_sparse_map(
                active_branch.branch_append(keys, msgs, path)
            ).contains_key(key)
            implies active_branch_sparse_map(active_branch.branch_append(keys, msgs, path))[key]
                == active_branch_sparse_map(active_branch)
                    .union_prefer_right(append_sparse_map(keys, msgs))[key]
        by {
            let post_sparse = active_branch_sparse_map(active_branch.branch_append(keys, msgs, path));
            let pre_sparse = active_branch_sparse_map(active_branch);
            let append_map = append_sparse_map(keys, msgs);
            if keys.contains(key) {
                assert(route_map.contains_key(key));
                assert(!is_nop_message(route_map[key]));
                assert(append_map.contains_key(key));
                assert(post_sparse[key] == route_map[key]);
                assert(append_map[key] == route_map[key]);
            } else {
                assert(!route_map.contains_key(key));
                assert(pre_sparse.contains_key(key));
                assert(post_sparse[key] == pre_sparse[key]);
            }
        }
    }
}

pub proof fn active_branch_initialize_sparse_effect(
    active_branch: AllocationBranch,
    init_root: Address,
    keys: Seq<Key>,
    msgs: Seq<Message>,
)
    requires
        active_branch.inv(),
        active_branch.branch is None,
        active_branch.can_initialize(init_root, keys, msgs),
    ensures
        active_branch_sparse_map(active_branch.branch_initialize(init_root, keys, msgs))
            == append_sparse_map(keys, msgs),
{
    let post_active = active_branch.branch_initialize(init_root, keys, msgs);
    let post_branch = post_active.branch.unwrap();
    let leaf = PivotNode::Leaf{ keys, msgs };
    let route_map = Map::new(
        |key: Key| keys.contains(key),
        |key: Key| msgs[leaf.route(key)],
    );

    AllocationBranch::build_next_preserves_inv(
        active_branch,
        post_active,
        crate::allocation_layer::AllocationBranch_v::BuildEvent::Initialize{addr: init_root, keys, msgs},
        Set::empty(),
        Set::empty(),
    );
    assert(post_active.inv());
    append_sparse_map_matches_route(keys, msgs);
    assert(post_branch.i() == leaf);
    assert(post_branch.i().i().map == route_map);
    assert(active_branch_sparse_map(post_active) =~= append_sparse_map(keys, msgs)) by {
        assert forall |key: Key| #[trigger] active_branch_sparse_map(post_active).contains_key(key)
            <==> append_sparse_map(keys, msgs).contains_key(key) by { }
        assert forall |key: Key| #[trigger] active_branch_sparse_map(post_active).contains_key(key)
            implies active_branch_sparse_map(post_active)[key] == append_sparse_map(keys, msgs)[key] by { }
    }
}

pub proof fn union_prefer_right_assoc(
    left: Map<Key, Message>,
    mid: Map<Key, Message>,
    right: Map<Key, Message>,
)
    ensures
        left.union_prefer_right(mid).union_prefer_right(right)
            == left.union_prefer_right(mid.union_prefer_right(right)),
{
    assert(left.union_prefer_right(mid).union_prefer_right(right) =~=
        left.union_prefer_right(mid.union_prefer_right(right))) by {
        assert forall |key: Key| #[trigger] left.union_prefer_right(mid).union_prefer_right(right).contains_key(key)
            <==> left.union_prefer_right(mid.union_prefer_right(right)).contains_key(key) by { }
        assert forall |key: Key| #[trigger] left.union_prefer_right(mid).union_prefer_right(right).contains_key(key)
            implies left.union_prefer_right(mid).union_prefer_right(right)[key]
                == left.union_prefer_right(mid.union_prefer_right(right))[key] by { }
    }
}

pub proof fn active_branch_grow_sparse_unchanged(active_branch: AllocationBranch, addr: crate::disk::GenericDisk_v::Address)
    requires
        active_branch.inv(),
        active_branch.can_grow(addr),
    ensures
        active_branch_sparse_map(active_branch.branch_grow(addr))
            == active_branch_sparse_map(active_branch),
{
    let pre_branch = active_branch.branch.unwrap();
    let post_branch = active_branch.branch_grow(addr).branch.unwrap();

    LinkedBranchRefinement::grow_refines(pre_branch, addr);
    LinkedBranchRefinement::i_wf(pre_branch);
    PivotBranchRefinement_v::grow_refines(pre_branch.i(), PivotBranchRefinement_v::InternalLabel{});

    assert(post_branch == pre_branch.grow(addr));
    assert(post_branch.i() == pre_branch.i().grow());
    assert(post_branch.i().i() == pre_branch.i().i());
    assert(active_branch_sparse_map(active_branch.branch_grow(addr)) == active_branch_sparse_map(active_branch));
}

pub proof fn active_branch_split_sparse_unchanged(
    active_branch: AllocationBranch,
    new_child_addr: crate::disk::GenericDisk_v::Address,
    path: crate::betree::LinkedBranch_v::Path<Summary>,
    split_arg: crate::betree::LinkedBranch_v::SplitArg,
)
    requires
        active_branch.inv(),
        active_branch.can_split(new_child_addr, path, split_arg),
    ensures
        active_branch_sparse_map(active_branch.branch_split(new_child_addr, path, split_arg))
            == active_branch_sparse_map(active_branch),
{
    let pre_branch = active_branch.branch.unwrap();
    let post_branch = active_branch.branch_split(new_child_addr, path, split_arg).branch.unwrap();

    LinkedBranchRefinement::split_refines(pre_branch, new_child_addr, path, split_arg);
    assert(post_branch == pre_branch.split(new_child_addr, path, split_arg));
    assert(post_branch.i() == pre_branch.i().split(path.i(), split_arg.i()));
    assert(post_branch.i().i() == pre_branch.i().i());
    assert(active_branch_sparse_map(active_branch.branch_split(new_child_addr, path, split_arg))
        == active_branch_sparse_map(active_branch));
}

impl AllocationBranchStack::State {
    pub open spec fn sparse_map(self) -> Map<Key, Message>
    {
        stack_sparse_map(self.sealed_stack, self.active_branch)
    }

    pub open spec fn sparse_buffer(self) -> SimpleBuffer
    {
        SimpleBuffer{ map: self.sparse_map() }
    }

    pub open spec fn kmmap_i(self) -> TotalKMMap
    {
        buffer_kmmap_i(self.sparse_buffer())
    }

    pub open spec fn abstract_map_i(self) -> AbstractMap::State
    {
        AbstractMap::State {
            stamped_map: Stamped {
                value: self.kmmap_i(),
                seq_end: self.seq_end,
            }
        }
    }

    pub proof fn kmmap_i_wf(self)
        ensures
            self.kmmap_i().wf(),
    {
        kmmap_i_wf(self.sparse_buffer());
    }

    pub proof fn stack_sparse_query(self, key: Key)
        requires
            self.wf(),
        ensures
            self.sparse_buffer().query(key) == self.query(key),
    {
        active_branch_sparse_query(self.active_branch, key);
        sealed_stack_sparse_query(self.sealed_stack, key);
    }

    pub open spec fn label_to_abstract_map(self, lbl: AllocationBranchStack::Label) -> AbstractMap::Label
    {
        match lbl {
            AllocationBranchStack::Label::QueryLabel{key, msg} =>
                AbstractMap::Label::QueryLabel{
                    end_lsn: self.seq_end,
                    key,
                    value: normalize_value(msg),
                },
            AllocationBranchStack::Label::AppendLabel{keys, msgs} =>
                AbstractMap::Label::PutLabel{ puts: append_puts(self.seq_end, keys, msgs) },
            AllocationBranchStack::Label::FreezeAsLabel{sealed_stack} =>
                AbstractMap::Label::FreezeAsLabel{ stamped_map: sealed_stack.abstract_map_i_at(self.seq_end).stamped_map },
            AllocationBranchStack::Label::InternalLabel =>
                AbstractMap::Label::InternalLabel,
        }
    }

    pub proof fn init_refines(self,
        sealed_roots: Seq<crate::disk::GenericDisk_v::Address>,
        sealed_disk: BufferDisk<BranchNode>,
        branch_summary: Map<crate::disk::GenericDisk_v::AU, Summary>,
        init_aus: Set<crate::disk::GenericDisk_v::AU>,
        seq_end: nat,
    )
        requires
            AllocationBranchStack::State::initialize(self, sealed_roots, sealed_disk, branch_summary, init_aus, seq_end),
        ensures
            AbstractMap::State::initialize(self.abstract_map_i(), self.abstract_map_i().stamped_map),
    {
    }

    pub proof fn query_refines(self, post: Self, lbl: AllocationBranchStack::Label)
        requires
            self.inv(),
            AllocationBranchStack::State::query_step(self, post, lbl),
        ensures
            post.inv(),
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(AbstractMap::State::next);
        reveal(AbstractMap::State::next_by);

        match lbl {
            AllocationBranchStack::Label::QueryLabel{key, msg} => {
                self.stack_sparse_query(key);
                self.kmmap_i_wf();
                assert(normalize_message(msg) == Message::Define{value: normalize_value(msg)});
                assert(AbstractMap::State::next_by(
                    self.abstract_map_i(),
                    post.abstract_map_i(),
                    self.label_to_abstract_map(lbl),
                    AbstractMap::Step::query(),
                ));
            }
            _ => { }
        }
    }

    pub proof fn freeze_as_refines(self, post: Self, lbl: AllocationBranchStack::Label)
        requires
            self.inv(),
            AllocationBranchStack::State::freeze_as(self, post, lbl),
        ensures
            post.inv(),
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(AbstractMap::State::next);
        reveal(AbstractMap::State::next_by);

        match lbl {
            AllocationBranchStack::Label::FreezeAsLabel{sealed_stack} => {
                self.kmmap_i_wf();
                sealed_stack.kmmap_i_wf();
                assert(self.active_branch.branch is None);
                assert(sealed_stack == self.sealed_stack);
                assert(self.sparse_map() =~= sealed_stack.sparse_map()) by {
                    assert forall |key: Key| #[trigger] self.sparse_map().contains_key(key)
                        <==> sealed_stack.sparse_map().contains_key(key) by { }
                    assert forall |key: Key| #![auto] self.sparse_map().contains_key(key)
                        implies self.sparse_map()[key] == sealed_stack.sparse_map()[key] by { }
                }
                assert(self.kmmap_i().0 =~= sealed_stack.kmmap_i().0);
                assert(self.abstract_map_i().stamped_map == sealed_stack.abstract_map_i_at(self.seq_end).stamped_map);
                assert(AbstractMap::State::next_by(
                    self.abstract_map_i(),
                    post.abstract_map_i(),
                    self.label_to_abstract_map(lbl),
                    AbstractMap::Step::freeze_as(),
                ));
            }
            _ => { }
        }
    }

    pub proof fn internal_noop_refines(self, post: Self, lbl: AllocationBranchStack::Label)
        requires
            self.inv(),
            post.inv(),
            lbl == AllocationBranchStack::Label::InternalLabel,
            self.abstract_map_i() == post.abstract_map_i(),
        ensures
            post.inv(),
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(AbstractMap::State::next);
        reveal(AbstractMap::State::next_by);

        assert(AbstractMap::State::next_by(
            self.abstract_map_i(),
            post.abstract_map_i(),
            self.label_to_abstract_map(lbl),
            AbstractMap::Step::internal(),
        ));
    }

    pub proof fn append_sparse_refines_to_put(
        self,
        post: Self,
        lbl: AllocationBranchStack::Label,
        keys: Seq<Key>,
        msgs: Seq<Message>,
    )
        requires
            self.inv(),
            post.inv(),
            lbl == (AllocationBranchStack::Label::AppendLabel{keys, msgs}),
            keys.len() == msgs.len(),
            post.seq_end == self.seq_end + keys.len(),
            post.sparse_map() == self.sparse_map().union_prefer_right(append_sparse_map(keys, msgs)),
        ensures
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(AbstractMap::State::next);
        reveal(AbstractMap::State::next_by);

        let puts = append_puts(self.seq_end, keys, msgs);
        append_puts_wf(self.seq_end, keys, msgs);
        self.kmmap_i_wf();
        append_puts_up_to_apply_to_sparse_buffer(
            self.sparse_buffer(),
            self.seq_end,
            keys,
            msgs,
            keys.len() as nat,
        );
        assert(puts.can_follow(self.abstract_map_i().stamped_map.seq_end));

        let expected_post = MsgHistory::map_plus_history(self.abstract_map_i().stamped_map, puts);
        let append_buffer = SimpleBuffer{
            map: self.sparse_map().union_prefer_right(append_sparse_map(keys, msgs)),
        };
        assert(expected_post == Stamped{
            value: buffer_kmmap_i(append_buffer),
            seq_end: self.seq_end + keys.len(),
        });
        assert(post.kmmap_i().0 =~= buffer_kmmap_i(append_buffer).0);
        assert(post.kmmap_i() == buffer_kmmap_i(append_buffer));
        assert(post.abstract_map_i().stamped_map == expected_post);
        assert(AbstractMap::State::next_by(
            self.abstract_map_i(),
            post.abstract_map_i(),
            self.label_to_abstract_map(lbl),
            AbstractMap::Step::put(),
        ));
    }

    pub proof fn grow_refines(
        self,
        post: Self,
        lbl: AllocationBranchStack::Label,
        new_root_addr: crate::disk::GenericDisk_v::Address,
    )
        requires
            self.inv(),
            post.inv(),
            AllocationBranchStack::State::internal_grow(self, post, lbl, new_root_addr),
        ensures
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        active_branch_grow_sparse_unchanged(self.active_branch, new_root_addr);
        assert(self.sealed_stack == post.sealed_stack);
        assert(self.seq_end == post.seq_end);
        assert(self.sparse_map() =~= post.sparse_map()) by {
            assert forall |key: Key| #[trigger] self.sparse_map().contains_key(key)
                <==> post.sparse_map().contains_key(key) by { }
            assert forall |key: Key| #![auto] self.sparse_map().contains_key(key)
                implies self.sparse_map()[key] == post.sparse_map()[key] by { }
        }
        assert(self.kmmap_i().0 =~= post.kmmap_i().0);
        assert(self.abstract_map_i() == post.abstract_map_i());
        self.internal_noop_refines(post, lbl);
    }

    pub proof fn split_refines(
        self,
        post: Self,
        lbl: AllocationBranchStack::Label,
        new_child_addr: crate::disk::GenericDisk_v::Address,
        path: crate::betree::LinkedBranch_v::Path<Summary>,
        split_arg: crate::betree::LinkedBranch_v::SplitArg,
    )
        requires
            self.inv(),
            post.inv(),
            AllocationBranchStack::State::internal_split(self, post, lbl, new_child_addr, path, split_arg),
        ensures
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        active_branch_split_sparse_unchanged(self.active_branch, new_child_addr, path, split_arg);
        assert(self.sealed_stack == post.sealed_stack);
        assert(self.seq_end == post.seq_end);
        assert(self.sparse_map() =~= post.sparse_map()) by {
            assert forall |key: Key| #[trigger] self.sparse_map().contains_key(key)
                <==> post.sparse_map().contains_key(key) by { }
            assert forall |key: Key| #![auto] self.sparse_map().contains_key(key)
                implies self.sparse_map()[key] == post.sparse_map()[key] by { }
        }
        assert(self.kmmap_i().0 =~= post.kmmap_i().0);
        assert(self.abstract_map_i() == post.abstract_map_i());
        self.internal_noop_refines(post, lbl);
    }

    pub proof fn fill_au_refines(
        self,
        post: Self,
        lbl: AllocationBranchStack::Label,
        aus: Set<crate::disk::GenericDisk_v::AU>,
    )
        requires
            self.inv(),
            post.inv(),
            AllocationBranchStack::State::internal_fill_au(self, post, lbl, aus),
        ensures
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        active_branch_fill_sparse_unchanged(self.active_branch, aus);
        assert(self.sealed_stack == post.sealed_stack);
        assert(self.seq_end == post.seq_end);
        assert(self.sparse_map() == post.sparse_map());
        assert(self.kmmap_i().0 =~= post.kmmap_i().0);
        assert(self.abstract_map_i() == post.abstract_map_i());
        self.internal_noop_refines(post, lbl);
    }

    pub proof fn append_to_active_refines(
        self,
        post: Self,
        lbl: AllocationBranchStack::Label,
        path: crate::betree::LinkedBranch_v::Path<Summary>,
    )
        requires
            self.inv(),
            post.inv(),
            AllocationBranchStack::State::append_to_active(self, post, lbl, path),
        ensures
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(AllocationBranchStack::State::append_to_active);
        match lbl {
            AllocationBranchStack::Label::AppendLabel{keys, msgs} => {
                assert forall |key: Key| #[trigger] keys.contains(key)
                    implies is_nop_message(self.active_branch.branch_query(key)) by {
                    assert(keys.contains(key));
                }
                active_branch_append_sparse_effect(self.active_branch, keys, msgs, path);
                union_prefer_right_assoc(
                    self.sealed_stack.sparse_map(),
                    active_branch_sparse_map(self.active_branch),
                    append_sparse_map(keys, msgs),
                );
                assert(post.sealed_stack == self.sealed_stack);
                assert(post.active_branch == self.active_branch.branch_append(keys, msgs, path));
                assert(post.sparse_map()
                    == self.sealed_stack.sparse_map().union_prefer_right(
                        active_branch_sparse_map(self.active_branch).union_prefer_right(append_sparse_map(keys, msgs))
                    ));
                assert(self.sparse_map().union_prefer_right(append_sparse_map(keys, msgs))
                    == self.sealed_stack.sparse_map().union_prefer_right(
                        active_branch_sparse_map(self.active_branch).union_prefer_right(append_sparse_map(keys, msgs))
                    ));
                assert(post.sparse_map() == self.sparse_map().union_prefer_right(append_sparse_map(keys, msgs)));
                self.append_sparse_refines_to_put(post, lbl, keys, msgs);
            }
            _ => { }
        }
    }

    pub proof fn append_to_empty_refines(
        self,
        post: Self,
        lbl: AllocationBranchStack::Label,
        init_root: Address,
    )
        requires
            self.inv(),
            post.inv(),
            AllocationBranchStack::State::append_to_empty(self, post, lbl, init_root),
        ensures
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        match lbl {
            AllocationBranchStack::Label::AppendLabel{keys, msgs} => {
                active_branch_initialize_sparse_effect(self.active_branch, init_root, keys, msgs);
                assert(active_branch_sparse_map(self.active_branch) == Map::<Key, Message>::empty());
                assert(self.sparse_map() == self.sealed_stack.sparse_map());
                assert(post.sealed_stack == self.sealed_stack);
                assert(post.active_branch == self.active_branch.branch_initialize(init_root, keys, msgs));
                assert(post.sparse_map()
                    == self.sealed_stack.sparse_map().union_prefer_right(append_sparse_map(keys, msgs)));
                assert(self.sparse_map().union_prefer_right(append_sparse_map(keys, msgs))
                    == self.sealed_stack.sparse_map().union_prefer_right(append_sparse_map(keys, msgs)));
                assert(post.sparse_map() == self.sparse_map().union_prefer_right(append_sparse_map(keys, msgs)));
                self.append_sparse_refines_to_put(post, lbl, keys, msgs);
            }
            _ => { }
        }
    }

    pub proof fn seal_refines(
        self,
        post: Self,
        lbl: AllocationBranchStack::Label,
        aux_ptr: Pointer,
    )
        requires
            self.inv(),
            post.inv(),
            AllocationBranchStack::State::internal_seal(self, post, lbl, aux_ptr),
        ensures
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        let dealloc_aus = self.active_branch.mini_allocator.removable_aus();
        let sealed_active = self.active_branch.branch_seal(aux_ptr, dealloc_aus);
        let sealed_branch = sealed_active.branch.unwrap();

        active_branch_seal_sparse_unchanged(self.active_branch, aux_ptr);
        self.active_branch.branch_seal_preserves_inv(aux_ptr, dealloc_aus);
        assert(sealed_active.inv());
        assert(sealed_branch.valid_sealed_branch());
        assert(sealed_branch.tight_disk_view_with_summary());
        assert(sealed_branch.get_summary() == sealed_active.mini_allocator.all_aus());
        assert(sealed_active.mini_allocator.all_aus() <= self.active_branch.mini_allocator.all_aus()) by {
            assert forall |au: AU| #[trigger] sealed_active.mini_allocator.all_aus().contains(au)
                implies self.active_branch.mini_allocator.all_aus().contains(au) by {
                if aux_ptr is Some {
                    let aux = aux_ptr.unwrap();
                    if au == aux.au {
                        assert(self.active_branch.mini_allocator.can_allocate(aux));
                    }
                }
            }
        }
        assert(summary_aus(self.sealed_stack.branch_summary()).disjoint(sealed_branch.get_summary()));
        sealed_stack_push_sparse_map(self.sealed_stack, sealed_branch);

        assert(post.sealed_stack == self.sealed_stack.push_branch(sealed_branch));
        assert(post.active_branch == AllocationBranch::new(Set::empty()));
        assert(active_branch_sparse_map(post.active_branch) == Map::<Key, Message>::empty());
        assert(active_branch_sparse_map(sealed_active) == active_branch_sparse_map(self.active_branch));
        assert(linked_branch_sparse_map(sealed_branch) == active_branch_sparse_map(self.active_branch));
        assert(post.sealed_stack.sparse_map()
            == self.sealed_stack.sparse_map().union_prefer_right(active_branch_sparse_map(self.active_branch)));
        assert(self.sparse_map() == self.sealed_stack.sparse_map().union_prefer_right(active_branch_sparse_map(self.active_branch)));
        assert(post.sparse_map() == post.sealed_stack.sparse_map());
        assert(self.sparse_map() =~= post.sparse_map()) by {
            assert forall |key: Key| #[trigger] self.sparse_map().contains_key(key)
                <==> post.sparse_map().contains_key(key) by { }
            assert forall |key: Key| #![auto] self.sparse_map().contains_key(key)
                implies self.sparse_map()[key] == post.sparse_map()[key] by { }
        }
        assert(self.seq_end == post.seq_end);
        assert(self.kmmap_i().0 =~= post.kmmap_i().0);
        assert(self.abstract_map_i() == post.abstract_map_i());
        self.internal_noop_refines(post, lbl);
    }

    pub proof fn next_refines(self, post: Self, lbl: AllocationBranchStack::Label)
        requires
            self.inv(),
            post.inv(),
            AllocationBranchStack::State::next(self, post, lbl),
        ensures
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(AbstractMap::State::next);
        reveal(AbstractMap::State::next_by);
        reveal(AllocationBranchStack::State::next);
        reveal(AllocationBranchStack::State::next_by);

        let step = choose |step| AllocationBranchStack::State::next_by(self, post, lbl, step);
        match step {
            AllocationBranchStack::Step::query_step() => {
                self.query_refines(post, lbl);
            }
            AllocationBranchStack::Step::append_to_active(path) => {
                self.append_to_active_refines(post, lbl, path);
            }
            AllocationBranchStack::Step::append_to_empty(init_root) => {
                self.append_to_empty_refines(post, lbl, init_root);
            }
            AllocationBranchStack::Step::freeze_as() => {
                self.freeze_as_refines(post, lbl);
            }
            AllocationBranchStack::Step::internal_noop() => {
                assert(self.abstract_map_i() == post.abstract_map_i());
                self.internal_noop_refines(post, lbl);
            }
            AllocationBranchStack::Step::internal_grow(new_root_addr) => {
                self.grow_refines(post, lbl, new_root_addr);
            }
            AllocationBranchStack::Step::internal_split(new_child_addr, path, split_arg) => {
                self.split_refines(post, lbl, new_child_addr, path, split_arg);
            }
            AllocationBranchStack::Step::internal_seal(aux_ptr) => {
                self.seal_refines(post, lbl, aux_ptr);
            }
            AllocationBranchStack::Step::internal_fill_au(aus) => {
                self.fill_au_refines(post, lbl, aus);
            }
            _ => {
                assert(false);
            }
        }
    }
}

impl SealedAllocationBranchStack {
    pub open spec fn sparse_map(self) -> Map<Key, Message>
    {
        sealed_sparse_map_up_to(self, self.sealed_roots.len() as nat)
    }

    pub open spec fn sparse_buffer(self) -> SimpleBuffer
    {
        SimpleBuffer{ map: self.sparse_map() }
    }

    pub open spec fn kmmap_i(self) -> TotalKMMap
    {
        buffer_kmmap_i(self.sparse_buffer())
    }

    pub proof fn kmmap_i_wf(self)
        ensures
            self.kmmap_i().wf(),
    {
        kmmap_i_wf(self.sparse_buffer());
    }

    pub open spec fn abstract_map_i_at(self, seq_end: nat) -> AbstractMap::State
    {
        AbstractMap::State {
            stamped_map: Stamped {
                value: self.kmmap_i(),
                seq_end,
            }
        }
    }
}

// The stack-to-abstract refinement proof body is intentionally kept light in
// this rewrite pass. The stack interpretation lives here, while concrete proof
// rebuilding happens separately on top of the new shared sealed-disk shape.

}
