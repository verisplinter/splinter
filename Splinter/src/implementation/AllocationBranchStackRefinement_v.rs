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
use crate::betree::LinkedBranch_v::Refinement_v as LinkedBranchRefinement_v;
use crate::betree::PivotBranchRefinement_v::{self, QueryLabel as PivotQueryLabel};
use crate::implementation::AllocationBranchStack_v::{AllocationBranchStack, normalize_message, normalize_value};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{nop_delta, Message};

verus! {

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

pub proof fn branch_sparse_query_refines(branch: AllocationBranch, key: Key)
    requires
        branch.inv(),
    ensures
        AllocationBranchStack::branch_sparse_buffer(branch).query(key)
            == if branch.branch is Some {
                branch.branch_query(key)
            } else {
                Message::Update{delta: nop_delta()}
            },
{
    if branch.branch is Some {
        let linked_branch = branch.branch.unwrap();
        let msg = linked_branch.query(key);
        let raw_buffer = linked_branch.i().i();
        LinkedBranchRefinement_v::i_wf(linked_branch);
        LinkedBranchRefinement_v::query_refines(linked_branch, key, msg);
        PivotBranchRefinement_v::query_refines(linked_branch.i(), PivotQueryLabel{key, msg});
        assert(raw_buffer.query(key) == msg);

        if raw_buffer.map.contains_key(key) {
            assert(raw_buffer.query(key) == raw_buffer.map[key]);
            if AllocationBranchStack::is_nop_message(raw_buffer.map[key]) {
                assert(msg == (Message::Update{delta: nop_delta()}));
                assert(!AllocationBranchStack::branch_sparse_map(branch).contains_key(key));
                assert(AllocationBranchStack::branch_sparse_buffer(branch).query(key)
                    == (Message::Update{delta: nop_delta()}));
            } else {
                assert(AllocationBranchStack::branch_sparse_map(branch).contains_key(key));
                assert(AllocationBranchStack::branch_sparse_map(branch)[key] == raw_buffer.map[key]);
                assert(AllocationBranchStack::branch_sparse_buffer(branch).query(key)
                    == AllocationBranchStack::branch_sparse_map(branch)[key]);
                assert(AllocationBranchStack::branch_sparse_buffer(branch).query(key) == msg);
            }
        } else {
            assert(msg == (Message::Update{delta: nop_delta()}));
            assert(!AllocationBranchStack::branch_sparse_map(branch).contains_key(key));
            assert(AllocationBranchStack::branch_sparse_buffer(branch).query(key)
                == (Message::Update{delta: nop_delta()}));
        }
    } else {
        assert(AllocationBranchStack::branch_sparse_map(branch) == Map::<Key, Message>::empty());
        assert(AllocationBranchStack::branch_sparse_buffer(branch).query(key)
            == (Message::Update{delta: nop_delta()}));
    }
}

pub proof fn query_up_to_refines_sparse_map(branches: Seq<AllocationBranch>, end: nat, key: Key)
    requires
        end <= branches.len(),
    ensures
        AllocationBranchStack::query_up_to(branches, end, key)
            == (SimpleBuffer{ map: AllocationBranchStack::sparse_map_up_to(branches, end) }).query(key),
    decreases end
{
    if end == 0 {
    } else {
        let prev_map = AllocationBranchStack::sparse_map_up_to(branches, (end - 1) as nat);
        let prev_query = AllocationBranchStack::query_up_to(branches, (end - 1) as nat, key);
        let last_branch = branches[(end - 1) as int];
        let last_map = AllocationBranchStack::branch_sparse_map(last_branch);
        let post_map = AllocationBranchStack::sparse_map_up_to(branches, end);

        query_up_to_refines_sparse_map(branches, (end - 1) as nat, key);

        if last_map.contains_key(key) {
            assert(AllocationBranchStack::branch_sparse_buffer(last_branch).query(key) == last_map[key]);
            assert(post_map.contains_key(key));
            assert(post_map[key] == last_map[key]);
            assert(SimpleBuffer{ map: post_map }.query(key) == post_map[key]);
        } else {
            assert(AllocationBranchStack::branch_sparse_buffer(last_branch).query(key)
                == (Message::Update{delta: nop_delta()}));

            assert forall |k: Key| #[trigger] post_map.contains_key(k) <==> (
                prev_map.union_prefer_right(last_map)
            ).contains_key(k) by { };

            if prev_map.contains_key(key) {
                assert(post_map.contains_key(key));
                assert(post_map[key] == prev_map[key]);
                assert(SimpleBuffer{ map: post_map }.query(key) == prev_map[key]);
                assert(SimpleBuffer{ map: prev_map }.query(key) == prev_map[key]);
            } else {
                assert(!post_map.contains_key(key));
                assert((SimpleBuffer{ map: post_map }).query(key) == (Message::Update{delta: nop_delta()}));
                assert((SimpleBuffer{ map: prev_map }).query(key) == (Message::Update{delta: nop_delta()}));
            }
            assert(prev_query == SimpleBuffer{ map: prev_map }.query(key));
        }
    }
}

pub proof fn query_up_to_all_nop(branches: Seq<AllocationBranch>, end: nat, key: Key)
    requires
        end <= branches.len(),
        forall |j: int|
            0 <= j < end ==> #[trigger] AllocationBranchStack::branch_sparse_buffer(branches[j]).query(key)
                == (Message::Update{delta: nop_delta()}),
    ensures
        AllocationBranchStack::query_up_to(branches, end, key) == (Message::Update{delta: nop_delta()}),
    decreases end
{
    if end > 0 {
        let last_branch = branches[(end - 1) as int];
        assert(AllocationBranchStack::branch_sparse_buffer(last_branch).query(key)
            == (Message::Update{delta: nop_delta()}));
        query_up_to_all_nop(branches, (end - 1) as nat, key);
    }
}

pub proof fn query_up_to_from_latest_hit(branches: Seq<AllocationBranch>, end: nat, hit_idx: nat, key: Key, msg: Message)
    requires
        end <= branches.len(),
        hit_idx < end,
        !AllocationBranchStack::is_nop_message(msg),
        AllocationBranchStack::branch_sparse_buffer(branches[hit_idx as int]).query(key) == msg,
        forall |j: int|
            hit_idx < j < end ==> #[trigger] AllocationBranchStack::branch_sparse_buffer(branches[j]).query(key)
                == (Message::Update{delta: nop_delta()}),
    ensures
        AllocationBranchStack::query_up_to(branches, end, key) == msg,
    decreases end
{
    if end == hit_idx + 1 {
        assert(AllocationBranchStack::query_up_to(branches, end, key)
            == AllocationBranchStack::branch_sparse_buffer(branches[hit_idx as int]).query(key));
    } else {
        let last_branch = branches[(end - 1) as int];
        assert(AllocationBranchStack::branch_sparse_buffer(last_branch).query(key)
            == (Message::Update{delta: nop_delta()}));
        query_up_to_from_latest_hit(branches, (end - 1) as nat, hit_idx, key, msg);
    }
}

pub proof fn query_refines_to_kmmap(stack: AllocationBranchStack, key: Key)
    requires
        stack.wf(),
    ensures
        stack.kmmap_i()[key] == normalize_message(stack.query(key)),
{
    query_up_to_refines_sparse_map(stack.branches, stack.branches.len() as nat, key);
}

pub proof fn query_refines_to_abstract_map(stack: AllocationBranchStack, key: Key)
    requires
        stack.wf(),
    ensures
        AbstractMap::State::next(
            stack.abstract_map_i(),
            stack.abstract_map_i(),
            AbstractMap::Label::QueryLabel{
                end_lsn: stack.seq_end,
                key,
                value: normalize_value(stack.query(key)),
            },
        ),
{
    query_refines_to_kmmap(stack, key);
    assert(stack.abstract_map_i().stamped_map.value[key] == normalize_message(stack.query(key)));
    assert(stack.abstract_map_i().stamped_map.value[key] is Define);
    reveal(AbstractMap::State::next);
    reveal(AbstractMap::State::next_by);
    assert(AbstractMap::State::next_by(
        stack.abstract_map_i(),
        stack.abstract_map_i(),
        AbstractMap::Label::QueryLabel{
            end_lsn: stack.seq_end,
            key,
            value: normalize_value(stack.query(key)),
        },
        AbstractMap::Step::query(),
    ));
}

pub proof fn sparse_map_up_to_push_prefix_stable(
    branches: Seq<AllocationBranch>,
    extra_branch: AllocationBranch,
    end: nat,
)
    requires
        end <= branches.len(),
    ensures
        AllocationBranchStack::sparse_map_up_to(branches.push(extra_branch), end)
            == AllocationBranchStack::sparse_map_up_to(branches, end),
    decreases end
{
    if end > 0 {
        sparse_map_up_to_push_prefix_stable(branches, extra_branch, (end - 1) as nat);
        assert(branches.push(extra_branch)[(end - 1) as int] == branches[(end - 1) as int]);
    }
}

pub proof fn sparse_map_up_to_update_last_prefix_stable(
    branches: Seq<AllocationBranch>,
    new_last: AllocationBranch,
    end: nat,
)
    requires
        0 < branches.len(),
        end < branches.len(),
    ensures
        AllocationBranchStack::sparse_map_up_to(branches.update(branches.len() - 1, new_last), end)
            == AllocationBranchStack::sparse_map_up_to(branches, end),
    decreases end
{
    if end > 0 {
        sparse_map_up_to_update_last_prefix_stable(branches, new_last, (end - 1) as nat);
        assert(branches.update(branches.len() - 1, new_last)[(end - 1) as int] == branches[(end - 1) as int]);
    }
}

pub proof fn sparse_map_seal_active_and_push_empty_preserves(
    stack: AllocationBranchStack,
    sealed_active: AllocationBranch,
    empty_branch: AllocationBranch,
)
    requires
        stack.wf(),
        AllocationBranchStack::branch_sparse_map(sealed_active)
            == AllocationBranchStack::branch_sparse_map(stack.active_branch()),
        !empty_branch.sealed,
        empty_branch.branch is None,
        AllocationBranchStack::branch_sparse_map(empty_branch) == Map::<Key, Message>::empty(),
    ensures
        (AllocationBranchStack{
            branches: stack.branches.update(stack.active_idx(), sealed_active).push(empty_branch),
            seq_end: stack.seq_end,
        }).sparse_map() == stack.sparse_map(),
{
    let mid = AllocationBranchStack{
        branches: stack.branches.update(stack.active_idx(), sealed_active),
        seq_end: stack.seq_end,
    };
    let post = AllocationBranchStack{
        branches: stack.branches.update(stack.active_idx(), sealed_active).push(empty_branch),
        seq_end: stack.seq_end,
    };
    sparse_map_update_active_with_same_sparse_map_preserves(stack, sealed_active);
    assert(mid.sparse_map() == stack.sparse_map());
    let post_map = post.sparse_map();
    let mid_map = mid.sparse_map();
    sparse_map_up_to_push_prefix_stable(mid.branches, empty_branch, mid.branches.len() as nat);
    assert forall |k: Key| #[trigger] post_map.contains_key(k) <==> mid_map.contains_key(k) by {
        assert(post_map.contains_key(k) == mid_map.union_prefer_right(Map::<Key, Message>::empty()).contains_key(k));
    };
    assert forall |k: Key| #[trigger] post_map.contains_key(k) implies post_map[k] == mid_map[k] by {
        assert(post_map[k] == mid_map.union_prefer_right(Map::<Key, Message>::empty())[k]);
        assert(mid_map.union_prefer_right(Map::<Key, Message>::empty())[k] == mid_map[k]);
    };
    assert_maps_equal!(post_map, mid_map);
}

pub proof fn sparse_map_update_active_with_same_sparse_map_preserves(
    stack: AllocationBranchStack,
    new_active: AllocationBranch,
)
    requires
        stack.wf(),
        AllocationBranchStack::branch_sparse_map(new_active)
            == AllocationBranchStack::branch_sparse_map(stack.active_branch()),
    ensures
        (AllocationBranchStack{ branches: stack.branches.update(stack.active_idx(), new_active), seq_end: stack.seq_end }).sparse_map()
            == stack.sparse_map(),
{
    let post = AllocationBranchStack{ branches: stack.branches.update(stack.active_idx(), new_active), seq_end: stack.seq_end };
    let post_map = post.sparse_map();
    let pre_map = stack.sparse_map();
    let prefix = AllocationBranchStack::sparse_map_up_to(stack.branches, stack.active_idx() as nat);
    sparse_map_up_to_update_last_prefix_stable(stack.branches, new_active, stack.active_idx() as nat);
    assert forall |k: Key| #[trigger] post_map.contains_key(k) <==> pre_map.contains_key(k) by {
        assert(post_map.contains_key(k)
            == prefix.union_prefer_right(AllocationBranchStack::branch_sparse_map(new_active)).contains_key(k));
        assert(pre_map.contains_key(k)
            == prefix.union_prefer_right(AllocationBranchStack::branch_sparse_map(stack.active_branch())).contains_key(k));
    };
    assert forall |k: Key| #[trigger] post_map.contains_key(k) implies post_map[k] == pre_map[k] by {
        assert(post_map[k]
            == prefix.union_prefer_right(AllocationBranchStack::branch_sparse_map(new_active))[k]);
        assert(pre_map[k]
            == prefix.union_prefer_right(AllocationBranchStack::branch_sparse_map(stack.active_branch()))[k]);
    };
    assert_maps_equal!(post_map, pre_map);
}

pub proof fn sparse_map_up_to_equal_from_pointwise_branch_sparse_map_equal(
    left: Seq<AllocationBranch>,
    right: Seq<AllocationBranch>,
    end: nat,
)
    requires
        end <= left.len(),
        end <= right.len(),
        forall |j: int|
            0 <= j < end
            ==> #[trigger] AllocationBranchStack::branch_sparse_map(left[j])
                == AllocationBranchStack::branch_sparse_map(right[j]),
    ensures
        AllocationBranchStack::sparse_map_up_to(left, end)
            == AllocationBranchStack::sparse_map_up_to(right, end),
    decreases end
{
    if end > 0 {
        sparse_map_up_to_equal_from_pointwise_branch_sparse_map_equal(left, right, (end - 1) as nat);
        let left_map = AllocationBranchStack::sparse_map_up_to(left, end);
        let right_map = AllocationBranchStack::sparse_map_up_to(right, end);
        let left_last = AllocationBranchStack::branch_sparse_map(left[(end - 1) as int]);
        let right_last = AllocationBranchStack::branch_sparse_map(right[(end - 1) as int]);
        assert(left_last == right_last);
        assert forall |k: Key| #[trigger] left_map.contains_key(k) <==> right_map.contains_key(k) by {
            assert(left_map.contains_key(k)
                == AllocationBranchStack::sparse_map_up_to(left, (end - 1) as nat)
                    .union_prefer_right(left_last).contains_key(k));
            assert(right_map.contains_key(k)
                == AllocationBranchStack::sparse_map_up_to(right, (end - 1) as nat)
                    .union_prefer_right(right_last).contains_key(k));
        };
        assert forall |k: Key| #[trigger] left_map.contains_key(k) implies left_map[k] == right_map[k] by {
            assert(left_map[k]
                == AllocationBranchStack::sparse_map_up_to(left, (end - 1) as nat)
                    .union_prefer_right(left_last)[k]);
            assert(right_map[k]
                == AllocationBranchStack::sparse_map_up_to(right, (end - 1) as nat)
                    .union_prefer_right(right_last)[k]);
        };
        assert_maps_equal!(left_map, right_map);
    }
}

pub proof fn sparse_map_equal_from_pointwise_branch_sparse_map_equal(
    left: AllocationBranchStack,
    right: AllocationBranchStack,
)
    requires
        left.branches.len() == right.branches.len(),
        forall |j: int|
            0 <= j < left.branches.len()
            ==> #[trigger] AllocationBranchStack::branch_sparse_map(left.branches[j])
                == AllocationBranchStack::branch_sparse_map(right.branches[j]),
    ensures
        left.sparse_map() == right.sparse_map(),
{
    sparse_map_up_to_equal_from_pointwise_branch_sparse_map_equal(
        left.branches,
        right.branches,
        left.branches.len() as nat,
    );
}

pub proof fn kmmap_equal_from_sparse_map_equal(left: AllocationBranchStack, right: AllocationBranchStack)
    requires
        left.wf(),
        right.wf(),
        left.sparse_map() == right.sparse_map(),
    ensures
        left.kmmap_i() == right.kmmap_i(),
{
    assert forall |k: Key| #[trigger] left.kmmap_i().0.contains_key(k) <==> right.kmmap_i().0.contains_key(k) by { };
    assert forall |k: Key| #[trigger] left.kmmap_i().0.contains_key(k) implies left.kmmap_i().0[k] == right.kmmap_i().0[k] by {
        query_refines_to_kmmap(left, k);
        query_refines_to_kmmap(right, k);
    };
    left.kmmap_i().ext_equal_is_equality(right.kmmap_i());
}

}
