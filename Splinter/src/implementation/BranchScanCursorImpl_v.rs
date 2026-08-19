// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::assert_sets_equal;

use crate::abstract_system::MsgHistory_v::KeyedMessage;
use crate::allocation_layer::BranchTypes_v::Summary;
use crate::betree::LinkedBranch_v::LinkedBranch;
use crate::betree::LinkedBranch_v::Refinement_v as LinkedBranchRefinement;
use crate::betree::PivotBranch_v::Node as PivotBranchNode;
use crate::betree::Utils_v::{
    lemma_set_subset_of_union_seq_of_sets,
    lemma_union_seq_of_sets_contains,
    union_seq_of_sets,
};
use crate::disk::GenericDisk_v::{addrs_closed, Address, Ranking};
use crate::implementation::Cache_v::Cache;
use crate::implementation::FracCacheImpl_v::{
    FetchErrorCode, FracCacheImpl, MutHandle,
};
use crate::implementation::IBranchNode_v::IBranchNode;
use crate::marshalling::IBranchNodeFormat_v::{
    BranchNodePageFmt, raw_page_to_branch_node,
};
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::WF_v::WF;
use crate::spec::AsyncDisk_t::RawPage;
use crate::spec::ImplDisk_t::IAddress;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::Message;

verus! {

pub open spec fn leaf_entries(
    keys: Seq<Key>,
    msgs: Seq<Message>,
) -> Seq<KeyedMessage>
    recommends keys.len() == msgs.len(),
{
    Seq::new(
        keys.len(),
        |i: int| KeyedMessage { key: keys[i], message: msgs[i] },
    )
}


pub open spec fn pivot_branch_entries(
    node: PivotBranchNode,
    fuel: nat,
) -> Seq<KeyedMessage>
    decreases fuel, 0int, 0nat,
{
    match node {
        PivotBranchNode::Leaf { keys, msgs } => leaf_entries(keys, msgs),
        PivotBranchNode::Index { children, .. } => if fuel == 0 {
            Seq::empty()
        } else {
            pivot_children_entries(
                children,
                (fuel - 1) as nat,
            )
        },
    }
}

pub open spec fn pivot_children_entries(
    children: Seq<PivotBranchNode>,
    fuel: nat,
) -> Seq<KeyedMessage>
    decreases fuel, 1int, children.len(),
{
    if children.len() == 0 {
        Seq::empty()
    } else {
        pivot_branch_entries(children[0], fuel)
            + pivot_children_entries(children.drop_first(), fuel)
    }
}


pub open spec fn branch_scan_entries_strictly_sorted(
    entries: Seq<KeyedMessage>,
) -> bool {
    forall |i: int, j: int| 0 <= i < j < entries.len()
        ==> Key::lt(
            (#[trigger] entries[i]).key,
            (#[trigger] entries[j]).key,
        )
}

proof fn key_lt_lte_transitive(left: Key, middle: Key, right: Key)
    requires
        Key::lt(left, middle),
        Key::lte(middle, right),
    ensures Key::lt(left, right),
{
    assert(left.0 < middle.0);
    assert(middle.0 <= right.0);
    assert(left != right);
}

proof fn sorted_entries_concat(
    left: Seq<KeyedMessage>,
    right: Seq<KeyedMessage>,
)
    requires
        branch_scan_entries_strictly_sorted(left),
        branch_scan_entries_strictly_sorted(right),
        forall |i: int, j: int|
            0 <= i < left.len() && 0 <= j < right.len()
            ==> Key::lt(
                (#[trigger] left[i]).key,
                (#[trigger] right[j]).key,
            ),
    ensures branch_scan_entries_strictly_sorted(left + right),
{
    assert forall |i: int, j: int| 0 <= i < j < (left + right).len()
        implies Key::lt(
            (#[trigger] (left + right)[i]).key,
            (#[trigger] (left + right)[j]).key,
        ) by {
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

proof fn pivot_entries_key_is_in_all_keys(
    node: PivotBranchNode,
    fuel: nat,
    item: KeyedMessage,
)
    requires pivot_branch_entries(node, fuel).contains(item),
    ensures node.all_keys().contains(item.key),
    decreases fuel, 0int, 0nat,
{
    match node {
        PivotBranchNode::Leaf { keys, msgs } => {
            let entries = leaf_entries(keys, msgs);
            let i = choose |i: int| 0 <= i < entries.len()
                && entries[i] == item;
            assert(entries[i].key == keys[i]);
            assert(keys.to_set().contains(item.key));
        },
        PivotBranchNode::Index { children, .. } => {
            if fuel > 0 {
                pivot_children_entry_origin(
                    children,
                    (fuel - 1) as nat,
                    item,
                );
                let i = choose |i: int| 0 <= i < children.len()
                    && pivot_branch_entries(
                        children[i],
                        (fuel - 1) as nat,
                    ).contains(item);
                pivot_entries_key_is_in_all_keys(
                    children[i],
                    (fuel - 1) as nat,
                    item,
                );
                assert(node.children_keys().contains(item.key));
            } else {
                assert(false);
            }
        },
    }
}

proof fn pivot_children_entry_origin(
    children: Seq<PivotBranchNode>,
    fuel: nat,
    item: KeyedMessage,
)
    requires pivot_children_entries(children, fuel).contains(item),
    ensures exists |i: int| 0 <= i < children.len()
        && pivot_branch_entries(
            #[trigger] children[i],
            fuel,
        ).contains(item),
    decreases fuel, 1int, children.len(),
{
    reveal_with_fuel(pivot_children_entries, 2);
    if children.len() == 0 {
        assert(false);
    } else if pivot_branch_entries(children[0], fuel).contains(item) {
    } else {
        assert(pivot_children_entries(
            children.drop_first(),
            fuel,
        ).contains(item));
        pivot_children_entry_origin(
            children.drop_first(),
            fuel,
            item,
        );
        let i = choose |i: int| 0 <= i < children.drop_first().len()
            && pivot_branch_entries(
                children.drop_first()[i],
                fuel,
            ).contains(item);
        assert(children.drop_first()[i] == children[i + 1]);
    }
}

proof fn pivot_index_child_keys_ordered(
    node: PivotBranchNode,
    left_idx: int,
    right_idx: int,
    left_key: Key,
    right_key: Key,
)
    requires
        node.wf(),
        node is Index,
        0 <= left_idx < right_idx < node->children.len(),
        node->children[left_idx].all_keys().contains(left_key),
        node->children[right_idx].all_keys().contains(right_key),
    ensures Key::lt(left_key, right_key),
{
    assert(left_idx < node->children.len() - 1);
    assert(node.all_keys_below_bound(left_idx));
    assert(Key::lt(left_key, node->pivots[left_idx]));
    assert(0 < right_idx);
    assert(node.all_keys_above_bound(right_idx));
    assert(Key::lte(node->pivots[right_idx - 1], right_key));
    Key::strictly_sorted_implies_sorted(node->pivots);
    assert(Key::lte(
        node->pivots[left_idx],
        node->pivots[right_idx - 1],
    ));
    key_lt_lte_transitive(
        left_key,
        node->pivots[left_idx],
        node->pivots[right_idx - 1],
    );
    key_lt_lte_transitive(
        left_key,
        node->pivots[right_idx - 1],
        right_key,
    );
}

pub proof fn pivot_branch_entries_sorted(
    node: PivotBranchNode,
    fuel: nat,
)
    requires node.wf(),
    ensures branch_scan_entries_strictly_sorted(
        pivot_branch_entries(node, fuel),
    ),
    decreases fuel, 0int, 0nat,
{
    match node {
        PivotBranchNode::Leaf { keys, msgs } => {
            assert forall |i: int, j: int|
                0 <= i < j < leaf_entries(keys, msgs).len()
                implies Key::lt(
                    (#[trigger] leaf_entries(keys, msgs)[i]).key,
                    (#[trigger] leaf_entries(keys, msgs)[j]).key,
                ) by {
                assert(leaf_entries(keys, msgs)[i].key == keys[i]);
                assert(leaf_entries(keys, msgs)[j].key == keys[j]);
            }
        },
        PivotBranchNode::Index { children, .. } => {
            if fuel == 0 {
            } else {
                pivot_index_children_entries_sorted(
                    node,
                    0,
                    (fuel - 1) as nat,
                );
                assert(node->children.skip(0) == node->children);
                assert(branch_scan_entries_strictly_sorted(
                    pivot_children_entries(
                        node->children,
                        (fuel - 1) as nat,
                    ),
                ));
                assert(pivot_branch_entries(node, fuel)
                    == pivot_children_entries(
                        node->children,
                        (fuel - 1) as nat,
                    ));
                assert(branch_scan_entries_strictly_sorted(
                    pivot_branch_entries(node, fuel),
                ));
            }
        },
    }
}

proof fn pivot_index_children_entries_sorted(
    node: PivotBranchNode,
    start: int,
    fuel: nat,
)
    requires
        node.wf(),
        node is Index,
        0 <= start <= node->children.len(),
    ensures branch_scan_entries_strictly_sorted(
        pivot_children_entries(
            node->children.skip(start),
            fuel,
        ),
    ),
    decreases fuel, 1int, node->children.len() - start,
{
    let children = node->children.skip(start);
    reveal_with_fuel(pivot_children_entries, 2);
    if children.len() == 0 {
        return;
    }
    assert(children[0] == node->children[start]);
    pivot_branch_entries_sorted(children[0], fuel);
    pivot_index_children_entries_sorted(node, start + 1, fuel);
    assert(children.drop_first() == node->children.skip(start + 1));
    let left = pivot_branch_entries(children[0], fuel);
    let right = pivot_children_entries(children.drop_first(), fuel);
    assert forall |i: int, j: int|
        0 <= i < left.len() && 0 <= j < right.len()
        implies Key::lt(
            (#[trigger] left[i]).key,
            (#[trigger] right[j]).key,
        ) by {
        let right_item = right[j];
        pivot_children_entry_origin(
            children.drop_first(),
            fuel,
            right_item,
        );
        let offset = choose |offset: int|
            0 <= offset < children.drop_first().len()
            && pivot_branch_entries(
                children.drop_first()[offset],
                fuel,
            ).contains(right_item);
        let right_idx = start + 1 + offset;
        assert(children.drop_first()[offset]
            == node->children[right_idx]);
        pivot_entries_key_is_in_all_keys(
            children[0],
            fuel,
            left[i],
        );
        pivot_entries_key_is_in_all_keys(
            node->children[right_idx],
            fuel,
            right_item,
        );
        pivot_index_child_keys_ordered(
            node,
            start,
            right_idx,
            left[i].key,
            right_item.key,
        );
    }
    sorted_entries_concat(left, right);
}

/* Proof-only stream semantics moved to BranchScanSemantics_v so these broad
 * key-domain facts do not perturb the executable cursor's local SMT context.
pub proof fn branch_scan_entries_query_index(
    entries: Seq<KeyedMessage>,
    index: int,
)
    requires
        branch_scan_entries_strictly_sorted(entries),
        0 <= index < entries.len(),
    ensures
        branch_scan_entries_contains(entries, entries[index].key),
        branch_scan_entries_query(entries, entries[index].key)
            == entries[index].message,
{
    let key = entries[index].key;
    assert(branch_scan_entries_contains(entries, key));
    let chosen = choose |i: int| 0 <= i < entries.len()
        && entries[i].key == key;
    if chosen < index {
        assert(Key::lt(entries[chosen].key, entries[index].key));
        assert(false);
    }
    if index < chosen {
        assert(Key::lt(entries[index].key, entries[chosen].key));
        assert(false);
    }
    assert(chosen == index);
}

proof fn pivot_child_entry_in_children(
    children: Seq<PivotBranchNode>,
    fuel: nat,
    child_idx: int,
    item: KeyedMessage,
)
    requires
        0 <= child_idx < children.len(),
        pivot_branch_entries(children[child_idx], fuel).contains(item),
    ensures pivot_children_entries(children, fuel).contains(item),
    decreases children.len(),
{
    reveal_with_fuel(pivot_children_entries, 2);
    if child_idx > 0 {
        assert(children.drop_first()[child_idx - 1]
            == children[child_idx]);
        pivot_child_entry_in_children(
            children.drop_first(),
            fuel,
            child_idx - 1,
            item,
        );
        assert(pivot_children_entries(
            children.drop_first(),
            fuel,
        ).contains(item));
        let left = pivot_branch_entries(children[0], fuel);
        let right = pivot_children_entries(children.drop_first(), fuel);
        let i = choose |i: int| 0 <= i < right.len()
            && right[i] == item;
        assert((left + right)[left.len() as int + i] == item);
        assert((left + right).contains(item));
    } else {
        let left = pivot_branch_entries(children[0], fuel);
        let right = pivot_children_entries(children.drop_first(), fuel);
        let i = choose |i: int| 0 <= i < left.len()
            && left[i] == item;
        assert((left + right)[i] == item);
        assert((left + right).contains(item));
    }
}

proof fn pivot_index_child_for_key_is_route(
    node: PivotBranchNode,
    child_idx: int,
    key: Key,
)
    requires
        node.wf(),
        node is Index,
        0 <= child_idx < node->children.len(),
        node->children[child_idx].all_keys().contains(key),
    ensures node.route(key) + 1 == child_idx,
{
    let route = node.route(key);
    PivotBranchNode::route_ensures(node, key);
    Key::strictly_sorted_implies_sorted(node->pivots);
    if child_idx == 0 {
        if route >= 0 {
            assert(node.all_keys_below_bound(0));
            assert(Key::lt(key, node->pivots[0]));
            assert(Key::lte(node->pivots[0], node->pivots[route]));
            assert(Key::lte(node->pivots[route], key));
            assert(false);
        }
    } else {
        assert(node.all_keys_above_bound(child_idx));
        assert(Key::lte(node->pivots[child_idx - 1], key));
        if route < child_idx - 1 {
            assert(Key::lt(key, node->pivots[child_idx - 1]));
            assert(false);
        }
        if child_idx < node->children.len() - 1 {
            assert(node.all_keys_below_bound(child_idx));
            assert(Key::lt(key, node->pivots[child_idx]));
            if route >= child_idx {
                assert(Key::lte(node->pivots[child_idx], key));
                assert(false);
            }
        } else {
            assert(node->pivots.len() == node->children.len() - 1);
            assert(route < child_idx);
        }
    }
}

proof fn pivot_branch_entry_key_refines(
    node: PivotBranchNode,
    fuel: nat,
    key: Key,
)
    requires
        node.wf(),
        pivot_entries_fuel_wf(node, fuel),
    ensures
        branch_scan_entries_contains(
            pivot_branch_entries(node, fuel),
            key,
        ) <==> node.i().map.contains_key(key),
        branch_scan_entries_query(
            pivot_branch_entries(node, fuel),
            key,
        ) == node.i().query(key),
    decreases node,
{
    reveal(pivot_entries_fuel_wf);
    pivot_branch_entries_sorted(node, fuel);
    match node {
        PivotBranchNode::Leaf { keys, msgs } => {
            PivotBranchNode::route_ensures(node, key);
            Key::strictly_sorted_implies_sorted(keys);
            let route = node.route(key);
            if branch_scan_entries_contains(
                leaf_entries(keys, msgs),
                key,
            ) {
                let i = choose |i: int| 0 <= i < keys.len()
                    && leaf_entries(keys, msgs)[i].key == key;
                assert(keys[i] == key);
                Key::largest_lte_is_lemma(keys, key, i);
                assert(route == i);
                assert(node.contains(key));
            }
            if node.contains(key) {
                assert(0 <= route < keys.len());
                assert(keys[route] == key);
                assert(leaf_entries(keys, msgs)[route].key == key);
                branch_scan_entries_query_index(
                    leaf_entries(keys, msgs),
                    route,
                );
            }
            let present = node.contains(key);
            PivotBranchRefinement::contains_refines(node, key, present);
            PivotBranchRefinement::query_refines(
                node,
                crate::betree::PivotBranchRefinement_v::QueryLabel {
                    key,
                    msg: node.query(key),
                },
            );
        },
        PivotBranchNode::Index { pivots, children } => {
            assert(fuel > 0);
            let route = node.route(key);
            PivotBranchNode::route_ensures(node, key);
            assert(0 <= route + 1 < children.len());
            pivot_branch_entry_key_refines(
                children[route + 1],
                (fuel - 1) as nat,
                key,
            );
            PivotBranchRefinement::lemma_index_i_routes(node, key);
            let whole = pivot_children_entries(
                children,
                (fuel - 1) as nat,
            );
            if branch_scan_entries_contains(whole, key) {
                let i = choose |i: int| 0 <= i < whole.len()
                    && whole[i].key == key;
                let item = whole[i];
                pivot_children_entry_origin(
                    children,
                    (fuel - 1) as nat,
                    item,
                );
                let child_idx = choose |j: int|
                    0 <= j < children.len()
                    && pivot_branch_entries(
                        children[j],
                        (fuel - 1) as nat,
                    ).contains(item);
                pivot_entries_key_is_in_all_keys(
                    children[child_idx],
                    (fuel - 1) as nat,
                    item,
                );
                pivot_index_child_for_key_is_route(
                    node,
                    child_idx,
                    key,
                );
                assert(child_idx == route + 1);
                pivot_branch_entry_key_refines(
                    children[child_idx],
                    (fuel - 1) as nat,
                    key,
                );
                assert(children[child_idx].i().map.contains_key(key));
                let child_entries = pivot_branch_entries(
                    children[child_idx],
                    (fuel - 1) as nat,
                );
                let child_i = choose |j: int|
                    0 <= j < child_entries.len()
                    && child_entries[j] == item;
                pivot_branch_entries_sorted(
                    children[child_idx],
                    (fuel - 1) as nat,
                );
                branch_scan_entries_query_index(child_entries, child_i);
                branch_scan_entries_query_index(whole, i);
            }
            if node.i().map.contains_key(key) {
                assert(children[route + 1].i().map.contains_key(key));
                let child_entries = pivot_branch_entries(
                    children[route + 1],
                    (fuel - 1) as nat,
                );
                assert(branch_scan_entries_contains(child_entries, key));
                let child_i = choose |i: int|
                    0 <= i < child_entries.len()
                    && child_entries[i].key == key;
                let item = child_entries[child_i];
                pivot_child_entry_in_children(
                    children,
                    (fuel - 1) as nat,
                    route + 1,
                    item,
                );
                let whole_i = choose |i: int| 0 <= i < whole.len()
                    && whole[i] == item;
                pivot_branch_entries_sorted(
                    children[route + 1],
                    (fuel - 1) as nat,
                );
                branch_scan_entries_query_index(child_entries, child_i);
                branch_scan_entries_query_index(whole, whole_i);
            }
            if !node.i().map.contains_key(key) {
                assert(!children[route + 1].i().map.contains_key(key));
            }
        },
    }
}

pub proof fn pivot_branch_entries_refine(
    node: PivotBranchNode,
    fuel: nat,
)
    requires
        node.wf(),
        pivot_entries_fuel_wf(node, fuel),
    ensures
        forall |key: Key|
            branch_scan_entries_contains(
                pivot_branch_entries(node, fuel),
                key,
            ) <==> node.i().map.contains_key(key),
        forall |key: Key|
            branch_scan_entries_query(
                pivot_branch_entries(node, fuel),
                key,
            ) == node.i().query(key),
{
    assert forall |key: Key|
        branch_scan_entries_contains(
            pivot_branch_entries(node, fuel),
            key,
        ) <==> node.i().map.contains_key(key)
    by {
        pivot_branch_entry_key_refines(node, fuel, key);
    }
    assert forall |key: Key|
        branch_scan_entries_query(
            pivot_branch_entries(node, fuel),
            key,
        ) == node.i().query(key)
    by {
        pivot_branch_entry_key_refines(node, fuel, key);
    }
}

proof fn linked_branch_entries_fuel_wf(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    fuel: nat,
)
    requires
        branch.inv_internal(ranking),
        branch.get_rank(ranking) <= fuel,
    ensures pivot_entries_fuel_wf(
        branch.i_internal(ranking),
        fuel,
    ),
    decreases branch.get_rank(ranking),
{
    reveal(pivot_entries_fuel_wf);
    if branch.root() is Index {
        assert(fuel > 0);
        assert forall |i: int| 0 <= i < branch.root()->children.len()
            implies pivot_entries_fuel_wf(
                #[trigger] branch.i_internal(ranking)->children[i],
                (fuel - 1) as nat,
            ) by {
            assert(branch.root().valid_child_index(i));
            let child = branch.child_at_idx(i);
            assert(branch.i_internal(ranking)->children[i]
                == child.i_internal(ranking));
            assert(child.get_rank(ranking) < branch.get_rank(ranking));
            assert(child.get_rank(ranking) <= fuel - 1);
            linked_branch_entries_fuel_wf(
                child,
                ranking,
                (fuel - 1) as nat,
            );
        }
    }
}

pub proof fn linked_branch_entries_refine(
    branch: LinkedBranch<Summary>,
)
    requires branch.valid_sealed_branch(),
    ensures
        branch_scan_entries_strictly_sorted(linked_branch_entries(branch)),
        forall |key: Key|
            branch_scan_entries_contains(
                linked_branch_entries(branch),
                key,
            ) <==> branch.i().i().map.contains_key(key),
        forall |key: Key|
            branch_scan_entries_query(
                linked_branch_entries(branch),
                key,
            ) == branch.i().i().query(key),
{
    let ranking = branch.the_ranking();
    assert(branch.inv());
    assert(branch.inv_internal(ranking));
    linked_branch_entries_fuel_wf(
        branch,
        ranking,
        ranking[branch.root] + 1,
    );
    LinkedBranchRefinement::i_internal_wf(branch, ranking);
    pivot_branch_entries_refine(
        branch.i_internal(ranking),
        ranking[branch.root] + 1,
    );
    pivot_branch_entries_sorted(
        branch.i_internal(ranking),
        ranking[branch.root] + 1,
    );
    assert(branch.i() == branch.i_internal(ranking));
}
*/

pub open spec fn branch_subtree(
    branch: LinkedBranch<Summary>,
    addr: Address,
) -> LinkedBranch<Summary> {
    LinkedBranch { root: addr, disk_view: branch.disk_view }
}

pub open spec fn pending_reachable_addrs(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    pending: Seq<IAddress>,
) -> Set<Address>
    decreases pending.len(),
{
    if pending.len() == 0 {
        Set::empty()
    } else {
        pending_reachable_addrs(branch, ranking, pending.drop_last())
            + branch_subtree(branch, pending.last()@)
                .reachable_addrs_using_ranking(ranking)
    }
}

proof fn pending_reachable_push(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    pending: Seq<IAddress>,
    addr: IAddress,
)
    ensures pending_reachable_addrs(
        branch,
        ranking,
        pending.push(addr),
    ) == pending_reachable_addrs(branch, ranking, pending)
        + branch_subtree(branch, addr@)
            .reachable_addrs_using_ranking(ranking),
{
    reveal_with_fuel(pending_reachable_addrs, 2);
    assert(pending.push(addr).len() > 0);
    assert(pending.push(addr).drop_last() == pending);
    assert(pending.push(addr).last() == addr);
}

pub open spec fn child_reachable_sets(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    children: Seq<IAddress>,
) -> Seq<Set<Address>> {
    Seq::new(
        children.len(),
        |i: int| branch_subtree(branch, children[i]@)
            .reachable_addrs_using_ranking(ranking),
    )
}

proof fn union_seq_of_sets_push_local<A>(
    sets: Seq<Set<A>>,
    last: Set<A>,
)
    ensures union_seq_of_sets(sets.push(last))
        == union_seq_of_sets(sets) + last,
{
    assert(sets.push(last).drop_last() == sets);
    assert(sets.push(last).last() == last);
}

proof fn union_seq_of_sets_drop_first_local<A>(sets: Seq<Set<A>>)
    requires sets.len() > 0,
    ensures union_seq_of_sets(sets)
        == sets[0] + union_seq_of_sets(sets.drop_first()),
{
    assert_sets_equal!(
        union_seq_of_sets(sets),
        sets[0] + union_seq_of_sets(sets.drop_first()),
        candidate => {
            if union_seq_of_sets(sets).contains(candidate) {
                lemma_union_seq_of_sets_contains(sets, candidate);
                let i = choose |i: int| 0 <= i < sets.len()
                    && (#[trigger] sets[i]).contains(candidate);
                if i > 0 {
                    assert(sets.drop_first()[i - 1] == sets[i]);
                    lemma_set_subset_of_union_seq_of_sets(
                        sets.drop_first(),
                        candidate,
                    );
                }
            }
            if sets[0].contains(candidate) {
                lemma_set_subset_of_union_seq_of_sets(sets, candidate);
            }
            if union_seq_of_sets(sets.drop_first()).contains(candidate) {
                lemma_union_seq_of_sets_contains(
                    sets.drop_first(),
                    candidate,
                );
                let i = choose |i: int|
                    0 <= i < sets.drop_first().len()
                    && (#[trigger] sets.drop_first()[i]).contains(candidate);
                assert(sets[i + 1] == sets.drop_first()[i]);
                lemma_set_subset_of_union_seq_of_sets(sets, candidate);
            }
        }
    );
}

proof fn child_reachable_sets_drop_first(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    children: Seq<IAddress>,
)
    requires children.len() > 0,
    ensures child_reachable_sets(
        branch,
        ranking,
        children.drop_first(),
    ) == child_reachable_sets(branch, ranking, children).drop_first(),
{
    assert(child_reachable_sets(
        branch,
        ranking,
        children.drop_first(),
    ) =~= child_reachable_sets(branch, ranking, children).drop_first());
}

proof fn pending_reachable_append_reverse(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    pending: Seq<IAddress>,
    children: Seq<IAddress>,
)
    ensures pending_reachable_addrs(
        branch,
        ranking,
        pending + children.reverse(),
    ) == pending_reachable_addrs(branch, ranking, pending)
        + union_seq_of_sets(child_reachable_sets(
            branch,
            ranking,
            children,
        )),
    decreases children.len(),
{
    if children.len() == 0 {
        assert(children.reverse().len() == 0);
        assert(child_reachable_sets(branch, ranking, children).len() == 0);
    } else {
        let tail = children.drop_first();
        pending_reachable_append_reverse(
            branch,
            ranking,
            pending,
            tail,
        );
        assert(children.reverse() == tail.reverse().push(children[0]));
        assert(pending + children.reverse()
            == (pending + tail.reverse()).push(children[0]));
        pending_reachable_push(
            branch,
            ranking,
            pending + tail.reverse(),
            children[0],
        );
        child_reachable_sets_drop_first(
            branch,
            ranking,
            children,
        );
        assert(child_reachable_sets(branch, ranking, children).len() > 0);
        assert(child_reachable_sets(branch, ranking, children)[0]
            == branch_subtree(branch, children[0]@)
                .reachable_addrs_using_ranking(ranking));
        union_seq_of_sets_drop_first_local(
            child_reachable_sets(branch, ranking, children),
        );
    }
}

proof fn pending_reachable_replace_index(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    pending: Seq<IAddress>,
    current: IAddress,
    children: Seq<IAddress>,
)
    requires
        branch_subtree(branch, current@).wf(),
        branch_subtree(branch, current@).valid_ranking(ranking),
        branch_subtree(branch, current@).root() is Index,
        branch_subtree(branch, current@).root()->children
            == crate::implementation::IBranchNode_v::iaddr_seq(children),
    ensures pending_reachable_addrs(
        branch,
        ranking,
        pending.push(current),
    ) == set![current@] + pending_reachable_addrs(
        branch,
        ranking,
        pending + children.reverse(),
    ),
{
    let parent = branch_subtree(branch, current@);
    pending_reachable_push(branch, ranking, pending, current);
    pending_reachable_append_reverse(
        branch,
        ranking,
        pending,
        children,
    );
    assert(child_reachable_sets(branch, ranking, children)
        =~= parent.children_reachable_addrs_using_ranking(ranking)) by {
        assert forall |i: int| 0 <= i < children.len()
            implies (#[trigger] child_reachable_sets(
                branch,
                ranking,
                children,
            )[i]) == parent.children_reachable_addrs_using_ranking(
                ranking,
            )[i] by {
            assert(parent.root()->children[i] == children[i]@);
            assert(parent.child_at_idx(i)
                == branch_subtree(branch, children[i]@));
        }
    }
    assert(parent.reachable_addrs_using_ranking(ranking)
        == union_seq_of_sets(
            parent.children_reachable_addrs_using_ranking(ranking),
        ).insert(current@));
    assert_sets_equal!(
        pending_reachable_addrs(
            branch,
            ranking,
            pending.push(current),
        ),
        set![current@] + pending_reachable_addrs(
            branch,
            ranking,
            pending + children.reverse(),
        ),
    );
}

pub open spec fn pending_node_entries(
    pending_nodes: Seq<PivotBranchNode>,
    pending_fuels: Seq<nat>,
) -> Seq<KeyedMessage>
    decreases pending_nodes.len(),
{
    if pending_nodes.len() == 0 {
        Seq::empty()
    } else {
        pivot_branch_entries(
            pending_nodes.last(),
            pending_fuels.last(),
        ) + pending_node_entries(
            pending_nodes.drop_last(),
            pending_fuels.drop_last(),
        )
    }
}

pub open spec fn branch_leaf_suffix(
    leaf: Option<IBranchNode>,
    leaf_index: usize,
) -> Seq<KeyedMessage> {
    match leaf {
        Some(IBranchNode::Leaf { ref keys, ref msgs }) =>
            leaf_entries(keys@, msgs@).subrange(
                leaf_index as int,
                keys.len() as int,
            ),
        _ => Seq::empty(),
    }
}

pub open spec fn cached_branch_scan_valid(
    cache: Cache::State,
    branch: LinkedBranch<Summary>,
) -> bool {
    forall |addr: Address, raw: RawPage|
        branch.disk_view.entries.contains_key(addr)
            && #[trigger] cache.valid_read(addr, raw)
        ==> raw_page_to_branch_node(raw)
            == branch.disk_view.entries[addr]
}

pub proof fn cached_branch_scan_valid_preserved(
    old_cache: Cache::State,
    new_cache: Cache::State,
    branch: LinkedBranch<Summary>,
)
    requires
        cached_branch_scan_valid(old_cache, branch),
        forall |addr: Address, raw: RawPage|
            new_cache.valid_read(addr, raw)
            ==> old_cache.valid_read(addr, raw),
    ensures
        cached_branch_scan_valid(new_cache, branch),
{
    assert forall |addr: Address, raw: RawPage|
        branch.disk_view.entries.contains_key(addr)
            && #[trigger] new_cache.valid_read(addr, raw)
        implies raw_page_to_branch_node(raw)
            == branch.disk_view.entries[addr] by {
        assert(old_cache.valid_read(addr, raw));
    }
}

proof fn scanned_insert_preserves_source(
    scanned: Set<Address>,
    source: LinkedBranch<Summary>,
    addr: Address,
)
    requires
        scanned <= source.full_repr(),
        source.tight_disk_view_with_summary(),
        source.disk_view.entries.contains_key(addr),
    ensures
        scanned.insert(addr) <= source.full_repr(),
{
    assert forall |candidate: Address|
        #[trigger] scanned.insert(addr).contains(candidate)
        implies source.full_repr().contains(candidate) by {
        if candidate == addr {
            assert(source.disk_view.entries.dom() == source.full_repr());
        } else {
            assert(scanned.contains(candidate));
        }
    }
}

proof fn pending_reverse_children_lemma(
    base_nodes: Seq<PivotBranchNode>,
    base_fuels: Seq<nat>,
    children: Seq<PivotBranchNode>,
    fuel: nat,
)
    ensures
        pending_node_entries(
            base_nodes + children.reverse(),
            base_fuels + Seq::new(children.len(), |i: int| fuel),
        ) =~= pivot_children_entries(children, fuel)
            + pending_node_entries(base_nodes, base_fuels),
    decreases children.len(),
{
    reveal_with_fuel(pending_node_entries, 2);
    reveal_with_fuel(pivot_children_entries, 2);
    if children.len() > 0 {
        let tail = children.drop_first();
        pending_reverse_children_lemma(
            base_nodes,
            base_fuels,
            tail,
            fuel,
        );
        assert(children.reverse().last() == children[0]);
        assert(children.reverse().drop_last() =~= tail.reverse());
        assert((base_nodes + children.reverse()).last()
            == children[0]);
        assert((base_nodes + children.reverse()).drop_last()
            =~= base_nodes + tail.reverse());
        assert(Seq::new(children.len(), |i: int| fuel).last()
            == fuel);
        assert(Seq::new(children.len(), |i: int| fuel).drop_last()
            =~= Seq::new(tail.len(), |i: int| fuel));
        assert((base_fuels + Seq::new(
            children.len(),
            |i: int| fuel,
        )).drop_last() =~= base_fuels + Seq::new(
            tail.len(),
            |i: int| fuel,
        ));
    }
}

pub struct BranchScanCursor {
    pub root: IAddress,
    pub pending: Vec<IAddress>,
    pub pending_nodes: Ghost<Seq<PivotBranchNode>>,
    pub pending_fuels: Ghost<Seq<nat>>,
    pub current_leaf_addr: Option<IAddress>,
    pub current_leaf: Option<IBranchNode>,
    pub leaf_index: usize,
    pub source: Ghost<LinkedBranch<Summary>>,
    pub ranking: Ghost<Ranking>,
    pub emitted: Ghost<Seq<KeyedMessage>>,
    pub scanned: Ghost<Set<Address>>,
    pub aux_state: BranchScanAuxState,
}

#[derive(Copy, Clone)]
pub enum BranchScanAuxState {
    AwaitingRoot,
    PendingAux { addr: IAddress },
    Complete,
}

pub open spec fn pending_aux_addrs(
    branch: LinkedBranch<Summary>,
    aux_state: BranchScanAuxState,
) -> Set<Address> {
    match aux_state {
        BranchScanAuxState::AwaitingRoot => {
            if branch.root() is Index {
                set![branch.root()->aux_ptr.unwrap()]
            } else {
                Set::empty()
            }
        },
        BranchScanAuxState::PendingAux { addr } => set![addr@],
        BranchScanAuxState::Complete => Set::empty(),
    }
}

pub enum BranchScanStepResult {
    Advanced {
        reads: Ghost<Map<Address, RawPage>>,
    },
    ItemReady,
    Done,
    NeedCacheLoad { addr: IAddress, handle: MutHandle },
    CacheFull,
    Blocked,
    InvalidPage,
}

impl BranchScanCursor {
    pub open spec fn remaining(&self) -> Seq<KeyedMessage> {
        branch_leaf_suffix(self.current_leaf, self.leaf_index)
            + pending_node_entries(
                self.pending_nodes@,
                self.pending_fuels@,
            )
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.source@.valid_sealed_branch()
        &&& self.source@.tight_disk_view_with_summary()
        &&& self.source@.root == self.root@
        &&& self.source@.valid_ranking(self.ranking@)
        &&& self.ranking@ == self.source@.the_ranking()
        &&& self.pending_nodes@.len() == self.pending@.len()
        &&& self.pending_fuels@.len() == self.pending@.len()
        &&& forall |i: int| 0 <= i < self.pending@.len() ==> {
            let addr = (#[trigger] self.pending@[i])@;
            &&& self.source@.disk_view.entries.contains_key(addr)
            &&& self.ranking@.contains_key(addr)
            &&& !(self.source@.disk_view.entries[addr] is Auxiliary)
            &&& self.ranking@[addr] < self.pending_fuels@[i]
            &&& self.pending_nodes@[i] == branch_subtree(
                self.source@,
                addr,
            ).i_internal(self.ranking@)
        }
        &&& match self.current_leaf {
            Some(ref leaf) => {
                &&& self.current_leaf_addr is Some
                &&& self.source@.disk_view.entries.contains_key(
                    self.current_leaf_addr.unwrap()@,
                )
                &&& leaf.wf()
                &&& leaf is Leaf
                &&& leaf@ == self.source@.disk_view.entries[
                    self.current_leaf_addr.unwrap()@]
                &&& self.leaf_index < leaf->keys.len()
            },
            None => {
                &&& self.current_leaf_addr is None
                &&& self.leaf_index == 0
            },
        }
        &&& (self.emitted@ + self.remaining())
            =~= pivot_branch_entries(
                self.source@.i_internal(self.ranking@),
                self.ranking@[self.source@.root] + 1,
            )
    }

    pub open spec fn receipt_facts(&self) -> bool {
        &&& self.scanned@ <= self.source@.full_repr()
        &&& self.source@.full_repr() == self.scanned@
            + pending_reachable_addrs(
                self.source@,
                self.ranking@,
                self.pending@,
            )
            + pending_aux_addrs(self.source@, self.aux_state)
        &&& match self.aux_state {
            BranchScanAuxState::AwaitingRoot => {
                &&& self.scanned@.is_empty()
                &&& self.pending@ == seq![self.root]
            },
            BranchScanAuxState::PendingAux { addr } => {
                &&& self.source@.root() is Index
                &&& self.source@.root()->aux_ptr == Some(addr@)
                &&& self.source@.disk_view.entries.contains_key(addr@)
                &&& self.source@.disk_view.entries[addr@] is Auxiliary
                &&& !self.scanned@.contains(addr@)
            },
            BranchScanAuxState::Complete => {
                self.source@.root() is Index ==> {
                    &&& self.source@.root()->aux_ptr is Some
                    &&& self.scanned@.contains(
                        self.source@.root()->aux_ptr.unwrap(),
                    )
                }
            },
        }
    }

    pub closed spec fn receipt_wf(&self) -> bool {
        self.receipt_facts()
    }

    pub proof fn receipt_wf_ensures(&self)
        requires self.receipt_wf(),
        ensures self.receipt_facts(),
    {
        reveal(BranchScanCursor::receipt_wf);
    }

    proof fn establish_receipt_wf(&self)
        requires self.receipt_facts(),
        ensures self.receipt_wf(),
    {
        reveal(BranchScanCursor::receipt_wf);
    }

    pub open spec fn cache_inv(&self, cache: Cache::State) -> bool {
        cached_branch_scan_valid(cache, self.source@)
    }

    pub fn new(
        root: IAddress,
        source: Ghost<LinkedBranch<Summary>>,
    ) -> (out: Self)
        requires
            source@.valid_sealed_branch(),
            source@.tight_disk_view_with_summary(),
            source@.root == root@,
        ensures
            out.wf(),
            out.receipt_wf(),
            out.root == root,
            out.source@ == source@,
            out.emitted@ == Seq::<KeyedMessage>::empty(),
            out.scanned@ == Set::<Address>::empty(),
            out.aux_state is AwaitingRoot,
            out.source@.full_repr() == out.scanned@
                + pending_reachable_addrs(
                    out.source@,
                    out.ranking@,
                    out.pending@,
                )
                + pending_aux_addrs(out.source@, out.aux_state),
            out.remaining() =~= pivot_branch_entries(
                source@.i_internal(source@.the_ranking()),
                source@.the_ranking()[source@.root] + 1,
            ),
            branch_scan_entries_strictly_sorted(out.remaining()),
    {
        let mut pending = Vec::new();
        pending.push(root);
        let ghost ranking = source@.the_ranking();
        let ghost pending_nodes = seq![source@.i_internal(ranking)];
        let ghost pending_fuels = seq![ranking[source@.root] + 1];
        let out = Self {
            root,
            pending,
            pending_nodes: Ghost(pending_nodes),
            pending_fuels: Ghost(pending_fuels),
            current_leaf_addr: None,
            current_leaf: None,
            leaf_index: 0,
            source,
            ranking: Ghost(ranking),
            emitted: Ghost(Seq::empty()),
            scanned: Ghost(Set::empty()),
            aux_state: BranchScanAuxState::AwaitingRoot,
        };
        proof {
            reveal_with_fuel(pending_node_entries, 2);
            assert(source@.inv());
            assert(source@.valid_ranking(ranking));
            assert(branch_leaf_suffix(None, 0) =~= Seq::empty());
            assert(pending_nodes.len() == 1);
            assert(pending_fuels.len() == 1);
            assert(pending_nodes.last() == source@.i_internal(ranking));
            assert(pending_fuels.last()
                == ranking[source@.root] + 1);
            assert(pending_node_entries(
                pending_nodes,
                pending_fuels,
            ) =~= pivot_branch_entries(
                source@.i_internal(ranking),
                ranking[source@.root] + 1,
            ));
            assert(out.remaining()
                =~= pivot_branch_entries(
                    source@.i_internal(ranking),
                    ranking[source@.root] + 1,
                ));
            assert(source@.inv_internal(ranking));
            LinkedBranchRefinement::i_internal_wf(source@, ranking);
            pivot_branch_entries_sorted(
                source@.i_internal(ranking),
                ranking[source@.root] + 1,
            );
            assert(branch_scan_entries_strictly_sorted(
                out.remaining(),
            ));
            assert(out.wf());
            pending_reachable_push(
                source@,
                ranking,
                Seq::<IAddress>::empty(),
                root,
            );
            assert(branch_subtree(source@, root@) == source@);
            assert(pending_reachable_addrs(
                source@,
                ranking,
                out.pending@,
            ) == source@.representation());
            assert(pending_aux_addrs(source@, out.aux_state)
                == if source@.root() is Index {
                    set![source@.root()->aux_ptr.unwrap()]
                } else {
                    Set::empty()
                });
            assert(source@.full_repr() == out.scanned@
                + pending_reachable_addrs(
                    source@,
                    ranking,
                    out.pending@,
                )
                + pending_aux_addrs(source@, out.aux_state));
            out.establish_receipt_wf();
        }
        out
    }

    pub fn peek(&self) -> (out: Option<KeyedMessage>)
        requires self.wf(),
        ensures
            match out {
                Some(item) => {
                    &&& self.remaining().len() > 0
                    &&& item == self.remaining()[0]
                },
                None => self.current_leaf is None,
            },
    {
        match &self.current_leaf {
            Some(IBranchNode::Leaf { keys, msgs }) => {
                Some(KeyedMessage {
                    key: keys[self.leaf_index],
                    message: msgs[self.leaf_index],
                })
            },
            _ => None,
        }
    }

    pub fn advance(&mut self) -> (out: bool)
        requires old(self).wf(), old(self).receipt_wf(),
        ensures
            self.wf(),
            self.receipt_wf(),
            self.root == old(self).root,
            self.source@ == old(self).source@,
            self.ranking@ == old(self).ranking@,
            self.scanned@ == old(self).scanned@,
            old(self).current_leaf is Some ==> out,
            out ==> {
                &&& old(self).remaining().len() > 0
                &&& self.emitted@ == old(self).emitted@.push(
                    old(self).remaining()[0],
                )
                &&& self.remaining() == old(self).remaining().drop_first()
            },
            !out ==> *self == *old(self),
    {
        if self.current_leaf.is_none() {
            return false;
        }
        let item = self.peek().unwrap();
        let mut clear_leaf = false;
        match &self.current_leaf {
            Some(IBranchNode::Leaf { keys, .. }) => {
                if self.leaf_index + 1 == keys.len() {
                    clear_leaf = true;
                }
            },
            _ => return false,
        }
        proof {
            self.emitted@ = self.emitted@.push(item);
        }
        if clear_leaf {
            self.current_leaf = None;
            self.current_leaf_addr = None;
            self.leaf_index = 0;
        } else {
            self.leaf_index = self.leaf_index + 1;
        }
        proof {
            assert(self.wf());
            assert(self.receipt_wf() == old(self).receipt_wf());
        }
        true
    }

    fn step_aux(
        &mut self,
        cache: &mut FracCacheImpl,
    ) -> (out: BranchScanStepResult)
        requires
            old(self).wf(),
            old(self).receipt_wf(),
            old(cache).wf(),
            old(self).cache_inv(old(cache)@),
            old(self).pending@.len() == 0,
            old(self).current_leaf is None,
            old(self).aux_state is PendingAux,
        ensures
            self.wf(),
            self.receipt_wf(),
            cache.wf(),
            self.cache_inv(cache@),
            cache.valid_load_handles_preserved(*old(cache)),
            self.root == old(self).root,
            self.source@ == old(self).source@,
            self.ranking@ == old(self).ranking@,
            self.emitted@ == old(self).emitted@,
            forall |addr: Address, raw: RawPage|
                cache@.valid_read(addr, raw)
                ==> old(cache)@.valid_read(addr, raw),
            forall |addr: Address, raw: RawPage|
                old(cache)@.valid_read(addr, raw)
                ==> cache@.valid_read(addr, raw),
            match out {
                BranchScanStepResult::Advanced { reads } => {
                    &&& cache@ == old(cache)@
                    &&& reads@.dom().finite()
                    &&& reads@.len() == 1
                    &&& self.scanned@ == old(self).scanned@ + reads@.dom()
                    &&& forall |addr: Address|
                        #[trigger] reads@.contains_key(addr) ==> {
                            &&& self.source@.disk_view.entries.contains_key(addr)
                            &&& raw_page_to_branch_node(reads@[addr])
                                == self.source@.disk_view.entries[addr]
                        }
                    &&& forall |addr: Address|
                        #[trigger] reads@.contains_key(addr)
                        ==> old(cache)@.valid_read(addr, reads@[addr])
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
                    &&& *self == *old(self)
                    &&& old(self).source@.get_summary().contains(addr@.au)
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
                BranchScanStepResult::CacheFull
                | BranchScanStepResult::Blocked
                | BranchScanStepResult::InvalidPage => {
                    &&& *self == *old(self)
                    &&& cache@ == old(cache)@
                },
                BranchScanStepResult::ItemReady
                | BranchScanStepResult::Done => false,
            },
    {
        let addr = match self.aux_state {
            BranchScanAuxState::PendingAux { addr } => addr,
            _ => return BranchScanStepResult::InvalidPage,
        };
        let ghost cache0 = *cache;
        let ghost cursor0 = *self;
        proof {
            cursor0.receipt_wf_ensures();
        }
        match cache.fetch(&addr, true) {
            FetchErrorCode::LoadInitiate { slot_handle } => {
                proof {
                    assert(self.source@.full_repr().contains(addr@)) by {
                        assert(self.source@.disk_view.entries
                            .contains_key(addr@));
                        assert(self.source@.disk_view.representation()
                            == self.source@.full_repr());
                    }
                    assert(self.source@.get_summary().contains(addr@.au)) by {
                        assert(addrs_closed(
                            self.source@.full_repr(),
                            self.source@.get_summary(),
                        ));
                    }
                    cached_branch_scan_valid_preserved(
                        cache0@,
                        cache@,
                        self.source@,
                    );
                }
                BranchScanStepResult::NeedCacheLoad {
                    addr,
                    handle: slot_handle,
                }
            },
            FetchErrorCode::Success { slot_handle } => {
                let ghost raw = slot_handle.rec@;
                let fmt = BranchNodePageFmt::new();
                let all_slice = Slice::all(&slot_handle.rec);
                let parsed = fmt.try_parse(&all_slice, &slot_handle.rec);
                proof {
                    assert(cache0@.valid_read(addr@, raw));
                    if parsed is Some {
                        assert(fmt == BranchNodePageFmt::spec_new());
                        assert(all_slice@.i(slot_handle.rec@) == raw);
                        assert(fmt.parsable(raw));
                        assert(parsed.unwrap().parsedv() == fmt.parse(raw));
                        assert(raw_page_to_branch_node(raw)
                            == parsed.unwrap()@);
                    }
                }
                cache.handle_release(&addr, slot_handle);
                proof {
                    assert(cache@.entries == cache0@.entries);
                    assert(cache@.lookup_map == cache0@.lookup_map);
                    assert(cache@.status_map == cache0@.status_map);
                    assert(cache@ == cache0@);
                }
                let node = match parsed {
                    Some(node) => node,
                    None => return BranchScanStepResult::InvalidPage,
                };
                match node {
                    IBranchNode::Auxiliary { .. } => {},
                    _ => return BranchScanStepResult::InvalidPage,
                }
                let ghost reads = Map::empty().insert(addr@, raw);
                self.aux_state = BranchScanAuxState::Complete;
                proof {
                    self.scanned@ = cursor0.scanned@.insert(addr@);
                    assert(raw_page_to_branch_node(raw)
                        == cursor0.source@.disk_view.entries[addr@]);
                    scanned_insert_preserves_source(
                        cursor0.scanned@,
                        cursor0.source@,
                        addr@,
                    );
                    assert(self.scanned@ <= self.source@.full_repr());
                    assert(self.wf());
                    assert(pending_reachable_addrs(
                        self.source@,
                        self.ranking@,
                        self.pending@,
                    ).is_empty());
                    assert(pending_aux_addrs(
                        cursor0.source@,
                        cursor0.aux_state,
                    ) == set![addr@]);
                    assert(pending_aux_addrs(
                        self.source@,
                        self.aux_state,
                    ).is_empty());
                    assert(cursor0.source@.full_repr()
                        == cursor0.scanned@ + set![addr@]);
                    assert(self.source@.full_repr()
                        == self.scanned@
                            + pending_reachable_addrs(
                                self.source@,
                                self.ranking@,
                                self.pending@,
                            )
                            + pending_aux_addrs(
                                self.source@,
                                self.aux_state,
                            ));
                    self.establish_receipt_wf();
                    assert(self.cache_inv(cache@));
                    Cache::State::access_read_only_from_valid_reads(
                        cache0@,
                        reads,
                    );
                    assert(reads.dom() == set![addr@]);
                    assert_sets_equal!(
                        self.scanned@,
                        cursor0.scanned@ + reads.dom(),
                        candidate => {
                            if reads.contains_key(candidate) {
                                assert(candidate == addr@);
                            }
                        }
                    );
                }
                BranchScanStepResult::Advanced { reads: Ghost(reads) }
            },
            FetchErrorCode::CacheFull => BranchScanStepResult::CacheFull,
            FetchErrorCode::Awaiting | FetchErrorCode::NotPresent =>
                BranchScanStepResult::Blocked,
        }
    }

    fn accept_leaf(
        &mut self,
        current: IAddress,
        keys: Vec<Key>,
        msgs: Vec<Message>,
    )
        requires
            old(self).wf(),
            old(self).receipt_wf(),
            old(self).current_leaf is None,
            old(self).pending@.len() > 0,
            old(self).pending@.last() == current,
            keys.len() > 0,
            keys.len() == msgs.len(),
            old(self).source@.disk_view.entries[current@]
                == (crate::allocation_layer::BranchTypes_v::BranchNode::Leaf {
                    keys: keys@,
                    msgs: msgs@,
                }),
        ensures
            self.wf(),
            self.receipt_wf(),
            self.root == old(self).root,
            self.source@ == old(self).source@,
            self.ranking@ == old(self).ranking@,
            self.emitted@ == old(self).emitted@,
            self.scanned@ == old(self).scanned@.insert(current@),
            self.remaining() == old(self).remaining(),
            self.current_leaf is Some,
    {
        let ghost cursor0 = *self;
        let pending_idx = self.pending.len() - 1;
        let ghost current_node = self.pending_nodes@[pending_idx as int];
        let ghost current_fuel = self.pending_fuels@[pending_idx as int];
        proof {
            cursor0.receipt_wf_ensures();
            self.scanned@ = cursor0.scanned@.insert(current@);
            scanned_insert_preserves_source(
                cursor0.scanned@,
                cursor0.source@,
                current@,
            );
        }
        self.pending.pop();
        proof {
            self.pending_nodes@ = self.pending_nodes@.drop_last();
            self.pending_fuels@ = self.pending_fuels@.drop_last();
        }
        self.current_leaf_addr = Some(current);
        self.current_leaf = Some(IBranchNode::Leaf { keys, msgs });
        self.leaf_index = 0;
        match self.aux_state {
            BranchScanAuxState::AwaitingRoot => {
                self.aux_state = BranchScanAuxState::Complete;
            },
            _ => {},
        }
        proof {
            reveal_with_fuel(pending_node_entries, 2);
            assert(self.pending@ =~= cursor0.pending@.drop_last());
            assert(self.pending_nodes@
                =~= cursor0.pending_nodes@.drop_last());
            assert(self.pending_fuels@
                =~= cursor0.pending_fuels@.drop_last());
            assert(self.pending_nodes@.len() == self.pending@.len());
            assert(self.pending_fuels@.len() == self.pending@.len());
            assert forall |i: int| 0 <= i < self.pending@.len()
                implies {
                    let addr = (#[trigger] self.pending@[i])@;
                    &&& self.source@.disk_view.entries.contains_key(addr)
                    &&& self.ranking@.contains_key(addr)
                    &&& !(self.source@.disk_view.entries[addr] is Auxiliary)
                    &&& self.ranking@[addr] < self.pending_fuels@[i]
                    &&& self.pending_nodes@[i] == branch_subtree(
                        self.source@,
                        addr,
                    ).i_internal(self.ranking@)
                } by {
                assert(i < cursor0.pending@.len() - 1);
            }
            assert(self.current_leaf->0.wf());
            assert(self.current_leaf->0 is Leaf);
            assert(self.current_leaf->0@
                == self.source@.disk_view.entries[current@]);
            assert(current_node == PivotBranchNode::Leaf {
                keys: self.current_leaf->0@->keys,
                msgs: self.current_leaf->0@->msgs,
            });
            assert(pivot_branch_entries(current_node, current_fuel)
                =~= branch_leaf_suffix(self.current_leaf, 0));
            assert(self.remaining() =~= cursor0.remaining());
            assert((self.emitted@ + self.remaining())
                =~= (cursor0.emitted@ + cursor0.remaining()));
            pending_reachable_push(
                cursor0.source@,
                cursor0.ranking@,
                self.pending@,
                current,
            );
            assert(cursor0.pending@ == self.pending@.push(current));
            assert(branch_subtree(
                cursor0.source@,
                current@,
            ).reachable_addrs_using_ranking(cursor0.ranking@)
                == set![current@]);
            assert(pending_aux_addrs(
                cursor0.source@,
                cursor0.aux_state,
            ) == pending_aux_addrs(
                self.source@,
                self.aux_state,
            ));
            assert(self.source@.full_repr()
                == self.scanned@
                    + pending_reachable_addrs(
                        self.source@,
                        self.ranking@,
                        self.pending@,
                    )
                    + pending_aux_addrs(
                        self.source@,
                        self.aux_state,
                    ));
            assert(self.wf());
            self.establish_receipt_wf();
        }
    }

    fn accept_index(
        &mut self,
        current: IAddress,
        pivots: Vec<Key>,
        children: Vec<IAddress>,
        aux_ptr: Option<IAddress>,
    )
        requires
            old(self).wf(),
            old(self).receipt_wf(),
            old(self).current_leaf is None,
            old(self).pending@.len() > 0,
            old(self).pending@.last() == current,
            children.len() > 0,
            old(self).aux_state is AwaitingRoot ==> aux_ptr is Some,
            old(self).source@.disk_view.entries[current@]
                == (crate::allocation_layer::BranchTypes_v::BranchNode::Index {
                    pivots: pivots@,
                    children: crate::implementation::IBranchNode_v::iaddr_seq(
                        children@,
                    ),
                    aux_ptr: crate::implementation::IBranchNode_v::iopt_addr(
                        aux_ptr,
                    ),
                }),
        ensures
            self.wf(),
            self.receipt_wf(),
            self.root == old(self).root,
            self.source@ == old(self).source@,
            self.ranking@ == old(self).ranking@,
            self.emitted@ == old(self).emitted@,
            self.scanned@ == old(self).scanned@.insert(current@),
            self.remaining() == old(self).remaining(),
            self.current_leaf is None,
    {
        let ghost cursor0 = *self;
        let pending_idx = self.pending.len() - 1;
        let ghost current_node = self.pending_nodes@[pending_idx as int];
        let ghost current_fuel = self.pending_fuels@[pending_idx as int];
        proof {
            cursor0.receipt_wf_ensures();
            self.scanned@ = cursor0.scanned@.insert(current@);
            scanned_insert_preserves_source(
                cursor0.scanned@,
                cursor0.source@,
                current@,
            );
            assert(current_node == branch_subtree(
                cursor0.source@,
                current@,
            ).i_internal(cursor0.ranking@));
            assert(cursor0.source@.disk_view.entries[current@] is Index);
            assert(current_node is Index);
            assert(current_node->children.len() == children.len());
            assert(current_fuel > 0);
            assert forall |j: int| 0 <= j < children@.len()
                implies {
                    let child_addr = (#[trigger] children@[j])@;
                    &&& cursor0.source@.disk_view.entries
                        .contains_key(child_addr)
                    &&& cursor0.ranking@.contains_key(child_addr)
                    &&& !(cursor0.source@.disk_view.entries[child_addr]
                        is Auxiliary)
                    &&& cursor0.ranking@[child_addr]
                        < (current_fuel - 1) as nat
                    &&& current_node->children[j] == branch_subtree(
                        cursor0.source@,
                        child_addr,
                    ).i_internal(cursor0.ranking@)
                } by {
                let ghost parent = branch_subtree(cursor0.source@, current@);
                assert(parent.root().valid_child_index(j));
                assert(parent.disk_view.node_children_respects_rank(
                    cursor0.ranking@,
                    current@,
                ));
                assert(parent.child_at_idx(j).root == children@[j]@);
            }
        }
        match self.aux_state {
            BranchScanAuxState::AwaitingRoot => {
                self.aux_state = BranchScanAuxState::PendingAux {
                    addr: aux_ptr.unwrap(),
                };
            },
            _ => {},
        }
        self.pending.pop();
        proof {
            self.pending_nodes@ = self.pending_nodes@.drop_last();
            self.pending_fuels@ = self.pending_fuels@.drop_last();
        }
        let ghost base_pending = self.pending@;
        let ghost base_nodes = self.pending_nodes@;
        let ghost base_fuels = self.pending_fuels@;
        let ghost child_fuel = (current_fuel - 1) as nat;
        let ghost scanned_after_read = self.scanned@;
        let aux_after_read = self.aux_state;
        let mut idx = children.len();
        while idx > 0
            invariant
                idx <= children.len(),
                self.source@ == cursor0.source@,
                self.ranking@ == cursor0.ranking@,
                self.root == cursor0.root,
                self.emitted@ == cursor0.emitted@,
                self.current_leaf == cursor0.current_leaf,
                self.current_leaf_addr == cursor0.current_leaf_addr,
                self.leaf_index == cursor0.leaf_index,
                self.scanned@ == scanned_after_read,
                self.scanned@ <= self.source@.full_repr(),
                self.aux_state == aux_after_read,
                current_node is Index,
                current_node->children.len() == children.len(),
                child_fuel == (current_fuel - 1) as nat,
                self.pending@ =~= base_pending + children@.subrange(
                    idx as int,
                    children.len() as int,
                ).reverse(),
                self.pending_nodes@ =~= base_nodes
                    + current_node->children.subrange(
                        idx as int,
                        children.len() as int,
                    ).reverse(),
                self.pending_fuels@ =~= base_fuels + Seq::new(
                    (children.len() - idx) as nat,
                    |i: int| child_fuel,
                ),
                self.pending_nodes@.len() == self.pending@.len(),
                self.pending_fuels@.len() == self.pending@.len(),
                forall |i: int| 0 <= i < self.pending@.len() ==> {
                    let addr = (#[trigger] self.pending@[i])@;
                    &&& self.source@.disk_view.entries.contains_key(addr)
                    &&& self.ranking@.contains_key(addr)
                    &&& !(self.source@.disk_view.entries[addr] is Auxiliary)
                    &&& self.ranking@[addr] < self.pending_fuels@[i]
                    &&& self.pending_nodes@[i] == branch_subtree(
                        self.source@,
                        addr,
                    ).i_internal(self.ranking@)
                },
            decreases idx,
        {
            idx -= 1;
            self.pending.push(children[idx]);
            proof {
                self.pending_nodes@ = self.pending_nodes@.push(
                    current_node->children[idx as int],
                );
                self.pending_fuels@ = self.pending_fuels@.push(child_fuel);
                assert(self.pending@.last() == children@[idx as int]);
                assert(self.pending_nodes@.last()
                    == current_node->children[idx as int]);
                assert(self.pending_fuels@.last() == child_fuel);
                assert forall |i: int| 0 <= i < self.pending@.len()
                    implies {
                        let addr = (#[trigger] self.pending@[i])@;
                        &&& self.source@.disk_view.entries.contains_key(addr)
                        &&& self.ranking@.contains_key(addr)
                        &&& !(self.source@.disk_view.entries[addr]
                            is Auxiliary)
                        &&& self.ranking@[addr] < self.pending_fuels@[i]
                        &&& self.pending_nodes@[i] == branch_subtree(
                            self.source@,
                            addr,
                        ).i_internal(self.ranking@)
                    } by {
                    let addr = self.pending@[i]@;
                    if i == self.pending@.len() - 1 {
                        assert(addr == children@[idx as int]@);
                    }
                }
            }
        }
        proof {
            reveal_with_fuel(pending_node_entries, 2);
            assert(idx == 0);
            assert(self.current_leaf is None);
            assert(self.current_leaf_addr is None);
            assert(self.leaf_index == 0);
            assert(pivot_branch_entries(current_node, current_fuel)
                =~= pivot_children_entries(
                    current_node->children,
                    child_fuel,
                ));
            pending_reverse_children_lemma(
                base_nodes,
                base_fuels,
                current_node->children,
                child_fuel,
            );
            assert(self.pending_nodes@
                =~= base_nodes + current_node->children.reverse());
            assert(self.pending_fuels@ =~= base_fuels + Seq::new(
                current_node->children.len(),
                |i: int| child_fuel,
            ));
            assert(pending_node_entries(
                cursor0.pending_nodes@,
                cursor0.pending_fuels@,
            ) =~= pivot_branch_entries(
                current_node,
                current_fuel,
            ) + pending_node_entries(base_nodes, base_fuels));
            assert(self.remaining() =~= cursor0.remaining());
            assert((self.emitted@ + self.remaining())
                =~= (cursor0.emitted@ + cursor0.remaining()));
            assert(cursor0.pending@ == base_pending.push(current));
            assert(self.pending@ == base_pending + children@.reverse());
            let parent = branch_subtree(cursor0.source@, current@);
            assert(parent.wf());
            assert(parent.valid_ranking(cursor0.ranking@));
            assert(parent.root() is Index);
            assert(parent.root()->children
                == crate::implementation::IBranchNode_v::iaddr_seq(children@));
            pending_reachable_replace_index(
                cursor0.source@,
                cursor0.ranking@,
                base_pending,
                current,
                children@,
            );
            assert(pending_aux_addrs(
                cursor0.source@,
                cursor0.aux_state,
            ) == pending_aux_addrs(
                self.source@,
                self.aux_state,
            ));
            assert(self.source@.full_repr()
                == self.scanned@
                    + pending_reachable_addrs(
                        self.source@,
                        self.ranking@,
                        self.pending@,
                    )
                    + pending_aux_addrs(
                        self.source@,
                        self.aux_state,
                    ));
            assert(self.wf());
            self.establish_receipt_wf();
        }
    }

    fn step_tree(
        &mut self,
        cache: &mut FracCacheImpl,
    ) -> (out: BranchScanStepResult)
        requires
            old(self).wf(),
            old(self).receipt_wf(),
            old(cache).wf(),
            old(self).cache_inv(old(cache)@),
            old(self).current_leaf is None,
            old(self).pending@.len() > 0,
        ensures
            self.wf(),
            self.receipt_wf(),
            cache.wf(),
            self.cache_inv(cache@),
            cache.valid_load_handles_preserved(*old(cache)),
            self.root == old(self).root,
            self.source@ == old(self).source@,
            self.ranking@ == old(self).ranking@,
            self.emitted@ == old(self).emitted@,
            forall |addr: Address, raw: RawPage|
                cache@.valid_read(addr, raw)
                ==> old(cache)@.valid_read(addr, raw),
            forall |addr: Address, raw: RawPage|
                old(cache)@.valid_read(addr, raw)
                ==> cache@.valid_read(addr, raw),
            match out {
                BranchScanStepResult::Advanced { reads } => {
                    &&& cache@ == old(cache)@
                    &&& reads@.dom().finite()
                    &&& reads@.len() == 1
                    &&& self.scanned@ == old(self).scanned@ + reads@.dom()
                    &&& forall |addr: Address|
                        #[trigger] reads@.contains_key(addr) ==> {
                            &&& self.source@.disk_view.entries.contains_key(addr)
                            &&& raw_page_to_branch_node(reads@[addr])
                                == self.source@.disk_view.entries[addr]
                        }
                    &&& forall |addr: Address|
                        #[trigger] reads@.contains_key(addr)
                        ==> old(cache)@.valid_read(addr, reads@[addr])
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        Cache::Label::Access {
                            reads: reads@,
                            writes: Map::empty(),
                        },
                    )
                },
                BranchScanStepResult::ItemReady => {
                    &&& *self == *old(self)
                    &&& cache@ == old(cache)@
                    &&& self.current_leaf is Some
                },
                BranchScanStepResult::Done => {
                    &&& *self == *old(self)
                    &&& cache@ == old(cache)@
                    &&& self.remaining().len() == 0
                    &&& self.scanned@ == self.source@.full_repr()
                },
                BranchScanStepResult::NeedCacheLoad { addr, handle } => {
                    &&& *self == *old(self)
                    &&& old(self).source@.get_summary().contains(addr@.au)
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
                BranchScanStepResult::CacheFull
                | BranchScanStepResult::Blocked
                | BranchScanStepResult::InvalidPage => {
                    &&& *self == *old(self)
                    &&& cache@ == old(cache)@
                },
            },
    {
        let pending_idx = self.pending.len() - 1;
        let current = self.pending[pending_idx];
        let ghost current_node = self.pending_nodes@[pending_idx as int];
        let ghost current_fuel = self.pending_fuels@[pending_idx as int];
        let ghost cache0 = *cache;
        let ghost cursor0 = *self;
        proof {
            cursor0.receipt_wf_ensures();
        }
        match cache.fetch(&current, true) {
            FetchErrorCode::LoadInitiate { slot_handle } => {
                proof {
                    assert(self.pending@
                        == self.pending@.drop_last().push(current));
                    pending_reachable_push(
                        self.source@,
                        self.ranking@,
                        self.pending@.drop_last(),
                        current,
                    );
                    assert(pending_reachable_addrs(
                        self.source@,
                        self.ranking@,
                        self.pending@,
                    ).contains(current@));
                    assert(self.source@.full_repr().contains(current@));
                    assert(self.source@.get_summary().contains(current@.au)) by {
                        assert(addrs_closed(
                            self.source@.full_repr(),
                            self.source@.get_summary(),
                        ));
                    }
                    cached_branch_scan_valid_preserved(
                        cache0@,
                        cache@,
                        self.source@,
                    );
                }
                return BranchScanStepResult::NeedCacheLoad {
                    addr: current,
                    handle: slot_handle,
                };
            },
            FetchErrorCode::Success { slot_handle } => {
                let ghost raw = slot_handle.rec@;
                let ghost fetched_slot = slot_handle.idx;
                let fmt = BranchNodePageFmt::new();
                let all_slice = Slice::all(&slot_handle.rec);
                let parsed = fmt.try_parse(&all_slice, &slot_handle.rec);
                proof {
                    assert(cache0@.valid_read(current@, raw));
                    if parsed is Some {
                        assert(fmt == BranchNodePageFmt::spec_new());
                        assert(all_slice@.i(slot_handle.rec@) == raw);
                        assert(fmt.parsable(all_slice@.i(slot_handle.rec@)));
                        assert(BranchNodePageFmt::spec_new().parsable(raw));
                        assert(parsed.unwrap().parsedv() == fmt.parse(raw));
                        assert(raw_page_to_branch_node(raw)
                            == parsed.unwrap()@);
                    }
                }
                cache.handle_release(&current, slot_handle);
                proof {
                    assert(cache@.entries == cache0@.entries);
                    assert(cache@.lookup_map == cache0@.lookup_map);
                    assert(cache@.status_map == cache0@.status_map);
                    assert(cache@ == cache0@);
                }
                let node = match parsed {
                    Some(node) => node,
                    None => return BranchScanStepResult::InvalidPage,
                };
                proof {
                    assert(cursor0.source@.disk_view.entries
                        .contains_key(current@));
                    assert(node@ == cursor0.source@.disk_view.entries[current@]);
                }
                let ghost reads = Map::empty().insert(current@, raw);
                match node {
                    IBranchNode::Leaf { keys, msgs } => {
                        if keys.len() == 0 || keys.len() != msgs.len() {
                            return BranchScanStepResult::InvalidPage;
                        }
                        self.accept_leaf(current, keys, msgs);
                    },
                    IBranchNode::Index { pivots, children, aux_ptr } => {
                        let awaiting_root = match self.aux_state {
                            BranchScanAuxState::AwaitingRoot => true,
                            _ => false,
                        };
                        if children.len() == 0
                            || (awaiting_root && aux_ptr.is_none())
                        {
                            return BranchScanStepResult::InvalidPage;
                        }
                        self.accept_index(
                            current,
                            pivots,
                            children,
                            aux_ptr,
                        );
                    },
                    IBranchNode::Auxiliary { .. } => {
                        return BranchScanStepResult::InvalidPage;
                    },
                }
                /* Retained inline traversal proof, superseded by the
                 * accept_leaf/accept_index modular contracts above.
                let awaiting_root = match self.aux_state {
                    BranchScanAuxState::AwaitingRoot => true,
                    _ => false,
                };
                match &node {
                    IBranchNode::Leaf { keys, msgs } => {
                        if keys.len() == 0 || keys.len() != msgs.len() {
                            return BranchScanStepResult::InvalidPage;
                        }
                    },
                    IBranchNode::Index { children, aux_ptr, .. } => {
                        if children.len() == 0
                            || (awaiting_root && aux_ptr.is_none())
                        {
                            return BranchScanStepResult::InvalidPage;
                        }
                    },
                    IBranchNode::Auxiliary { .. } => {
                        return BranchScanStepResult::InvalidPage;
                    },
                }
                */
                /* Retained former inline traversal body.
                proof {
                    assert(cursor0.source@.disk_view.entries
                        .contains_key(current@));
                    assert(node@ == cursor0.source@.disk_view.entries[current@]);
                    assert(self.source@ == cursor0.source@);
                    assert(self.ranking@ == cursor0.ranking@);
                    assert(self.root == cursor0.root);
                    assert(self.emitted@ == cursor0.emitted@);
                }
                let ghost reads = Map::empty().insert(current@, raw);
                proof {
                    self.scanned@ = cursor0.scanned@.insert(current@);
                    scanned_insert_preserves_source(
                        cursor0.scanned@,
                        cursor0.source@,
                        current@,
                    );
                    assert(self.scanned@ <= self.source@.full_repr());
                }
                match node {
                    IBranchNode::Leaf { keys, msgs } => {
                        self.pending.pop();
                        proof {
                            self.pending_nodes@ = self.pending_nodes@.drop_last();
                            self.pending_fuels@ = self.pending_fuels@.drop_last();
                        }
                        self.current_leaf_addr = Some(current);
                        self.current_leaf = Some(IBranchNode::Leaf { keys, msgs });
                        self.leaf_index = 0;
                        match self.aux_state {
                            BranchScanAuxState::AwaitingRoot => {
                                self.aux_state = BranchScanAuxState::Complete;
                            },
                            _ => {},
                        }
                        proof {
                            reveal_with_fuel(pending_node_entries, 2);
                            assert(self.source@ == cursor0.source@);
                            assert(self.ranking@ == cursor0.ranking@);
                            assert(self.root == cursor0.root);
                            assert(self.emitted@ == cursor0.emitted@);
                            assert(self.pending@
                                =~= cursor0.pending@.drop_last());
                            assert(self.pending_nodes@
                                =~= cursor0.pending_nodes@.drop_last());
                            assert(self.pending_fuels@
                                =~= cursor0.pending_fuels@.drop_last());
                            assert(self.pending_nodes@.len()
                                == self.pending@.len());
                            assert(self.pending_fuels@.len()
                                == self.pending@.len());
                            assert forall |i: int|
                                0 <= i < self.pending@.len()
                                implies {
                                    let addr = (#[trigger] self.pending@[i])@;
                                    &&& self.source@.disk_view.entries
                                        .contains_key(addr)
                                    &&& self.ranking@.contains_key(addr)
                                    &&& !(self.source@.disk_view.entries[addr]
                                        is Auxiliary)
                                    &&& self.ranking@[addr]
                                        < self.pending_fuels@[i]
                                    &&& self.pending_nodes@[i]
                                        == branch_subtree(
                                            self.source@,
                                            addr,
                                        ).i_internal(self.ranking@)
                                } by {
                                assert(i < cursor0.pending@.len() - 1);
                            }
                            assert(self.current_leaf->0.wf());
                            assert(self.current_leaf->0 is Leaf);
                            assert(self.current_leaf->0@
                                == self.source@.disk_view.entries[current@]);
                            assert(current_node == PivotBranchNode::Leaf {
                                keys: self.current_leaf->0@->keys,
                                msgs: self.current_leaf->0@->msgs,
                            });
                            assert(pivot_branch_entries(
                                current_node,
                                current_fuel,
                            ) =~= branch_leaf_suffix(
                                self.current_leaf,
                                0,
                            ));
                            assert(self.remaining() =~= cursor0.remaining());
                            assert((self.emitted@ + self.remaining())
                                =~= (cursor0.emitted@ + cursor0.remaining()));
                            assert(self.wf());
                            self.establish_receipt_wf();
                        }
                    },
                    IBranchNode::Index { pivots: _, children, aux_ptr } => {
                        match self.aux_state {
                            BranchScanAuxState::AwaitingRoot => {
                                let aux = aux_ptr.unwrap();
                                self.aux_state = BranchScanAuxState::PendingAux {
                                    addr: aux,
                                };
                            },
                            _ => {},
                        }
                        proof {
                            self.establish_receipt_wf();
                        }
                        proof {
                            assert(current_node == branch_subtree(
                                cursor0.source@,
                                current@,
                            ).i_internal(cursor0.ranking@));
                            assert(cursor0.source@.disk_view.entries[current@]
                                is Index);
                            assert(current_node is Index);
                            assert(current_node->children.len()
                                == children.len());
                            assert(current_fuel > 0);
                            assert forall |j: int|
                                0 <= j < children@.len()
                                implies {
                                    let child_addr = (#[trigger] children@[j])@;
                                    &&& cursor0.source@.disk_view.entries
                                        .contains_key(child_addr)
                                    &&& cursor0.ranking@.contains_key(child_addr)
                                    &&& !(cursor0.source@.disk_view.entries[
                                        child_addr] is Auxiliary)
                                    &&& cursor0.ranking@[child_addr]
                                        < (current_fuel - 1) as nat
                                    &&& current_node->children[j]
                                        == branch_subtree(
                                            cursor0.source@,
                                            child_addr,
                                        ).i_internal(cursor0.ranking@)
                                } by {
                                let ghost parent = branch_subtree(
                                    cursor0.source@,
                                    current@,
                                );
                                assert(parent.root().valid_child_index(j));
                                assert(parent.disk_view.node_children_respects_rank(
                                    cursor0.ranking@,
                                    current@,
                                ));
                                assert(parent.child_at_idx(j).root
                                    == children@[j]@);
                            }
                        }
                        self.pending.pop();
                        proof {
                            self.pending_nodes@ = self.pending_nodes@.drop_last();
                            self.pending_fuels@ = self.pending_fuels@.drop_last();
                        }
                        let ghost base_pending = self.pending@;
                        let ghost base_nodes = self.pending_nodes@;
                        let ghost base_fuels = self.pending_fuels@;
                        let ghost child_fuel = (current_fuel - 1) as nat;
                        let ghost scanned_after_read = self.scanned@;
                        let aux_after_read = self.aux_state;
                        let mut idx = children.len();
                        while idx > 0
                            invariant
                                idx <= children.len(),
                                self.source@ == cursor0.source@,
                                self.ranking@ == cursor0.ranking@,
                                self.root == cursor0.root,
                                self.emitted@ == cursor0.emitted@,
                                self.current_leaf == cursor0.current_leaf,
                                self.current_leaf_addr
                                    == cursor0.current_leaf_addr,
                                self.leaf_index == cursor0.leaf_index,
                                self.scanned@ == scanned_after_read,
                                self.scanned@ <= self.source@.full_repr(),
                                self.aux_state == aux_after_read,
                                current_node is Index,
                                current_node->children.len() == children.len(),
                                child_fuel == (current_fuel - 1) as nat,
                                self.pending@ =~= base_pending
                                    + children@.subrange(
                                        idx as int,
                                        children.len() as int,
                                    ).reverse(),
                                self.pending_nodes@ =~= base_nodes
                                    + current_node->children.subrange(
                                        idx as int,
                                        children.len() as int,
                                    ).reverse(),
                                self.pending_fuels@ =~= base_fuels
                                    + Seq::new(
                                        (children.len() - idx) as nat,
                                        |i: int| child_fuel,
                                    ),
                                self.pending_nodes@.len()
                                    == self.pending@.len(),
                                self.pending_fuels@.len()
                                    == self.pending@.len(),
                                forall |i: int|
                                    0 <= i < self.pending@.len()
                                    ==> {
                                        let addr = (#[trigger] self.pending@[i])@;
                                        &&& self.source@.disk_view.entries
                                            .contains_key(addr)
                                        &&& self.ranking@.contains_key(addr)
                                        &&& !(self.source@.disk_view.entries[addr]
                                            is Auxiliary)
                                        &&& self.ranking@[addr]
                                            < self.pending_fuels@[i]
                                        &&& self.pending_nodes@[i]
                                            == branch_subtree(
                                                self.source@,
                                                addr,
                                            ).i_internal(self.ranking@)
                                    },
                            decreases idx,
                        {
                            idx -= 1;
                            self.pending.push(children[idx]);
                            proof {
                                self.pending_nodes@ = self.pending_nodes@.push(
                                    current_node->children[idx as int],
                                );
                                self.pending_fuels@ = self.pending_fuels@.push(
                                    (current_fuel - 1) as nat,
                                );
                                assert(self.pending@.last()
                                    == children@[idx as int]);
                                assert(self.pending_nodes@.last()
                                    == current_node->children[idx as int]);
                                assert(self.pending_fuels@.last()
                                    == child_fuel);
                                assert forall |i: int|
                                    0 <= i < self.pending@.len()
                                    implies {
                                        let addr = (#[trigger] self.pending@[i])@;
                                        &&& self.source@.disk_view.entries
                                            .contains_key(addr)
                                        &&& self.ranking@.contains_key(addr)
                                        &&& !(self.source@.disk_view.entries[addr]
                                            is Auxiliary)
                                        &&& self.ranking@[addr]
                                            < self.pending_fuels@[i]
                                        &&& self.pending_nodes@[i]
                                            == branch_subtree(
                                                self.source@,
                                                addr,
                                            ).i_internal(self.ranking@)
                                    } by {
                                    let addr = self.pending@[i]@;
                                    if i == self.pending@.len() - 1 {
                                        assert(addr == children@[idx as int]@);
                                    }
                                }
                            }
                        }
                        proof {
                            reveal_with_fuel(pending_node_entries, 2);
                            assert(idx == 0);
                            assert(self.current_leaf is None);
                            assert(self.current_leaf_addr is None);
                            assert(self.leaf_index == 0);
                            assert(pivot_branch_entries(
                                current_node,
                                current_fuel,
                            ) =~= pivot_children_entries(
                                current_node->children,
                                child_fuel,
                            ));
                            pending_reverse_children_lemma(
                                base_nodes,
                                base_fuels,
                                current_node->children,
                                child_fuel,
                            );
                            assert(self.pending_nodes@ =~= base_nodes
                                + current_node->children.reverse());
                            assert(self.pending_fuels@ =~= base_fuels
                                + Seq::new(
                                    current_node->children.len(),
                                    |i: int| child_fuel,
                                ));
                            assert(pending_node_entries(
                                cursor0.pending_nodes@,
                                cursor0.pending_fuels@,
                            ) =~= pivot_branch_entries(
                                current_node,
                                current_fuel,
                            ) + pending_node_entries(
                                base_nodes,
                                base_fuels,
                            ));
                            assert(self.remaining() =~= cursor0.remaining());
                            assert((self.emitted@ + self.remaining())
                                =~= (cursor0.emitted@ + cursor0.remaining()));
                            assert(self.wf());
                            self.establish_receipt_wf();
                        }
                    },
                    IBranchNode::Auxiliary { .. } => {
                        return BranchScanStepResult::InvalidPage;
                    },
                }
                */
                proof {
                    assert(self.source@ == cursor0.source@);
                    assert(self.ranking@ == cursor0.ranking@);
                    assert(self.root == cursor0.root);
                    assert(self.emitted@ == cursor0.emitted@);
                    assert(self.source@.valid_sealed_branch());
                    assert(self.source@.tight_disk_view_with_summary());
                    assert(self.source@.valid_ranking(self.ranking@));
                    assert(self.wf());
                    self.establish_receipt_wf();
                    assert(self.cache_inv(cache@));
                    Cache::State::access_read_only_from_valid_reads(
                        cache0@,
                        reads,
                    );
                    assert(reads.dom() == set![current@]);
                    assert_sets_equal!(
                        self.scanned@,
                        cursor0.scanned@ + reads.dom(),
                        candidate => {
                            if reads.contains_key(candidate) {
                                assert(candidate == current@);
                            }
                        }
                    );
                    assert forall |addr: Address|
                        #[trigger] reads.contains_key(addr)
                        implies {
                            &&& self.source@.disk_view.entries
                                .contains_key(addr)
                            &&& raw_page_to_branch_node(reads[addr])
                                == self.source@.disk_view.entries[addr]
                        } by {
                        assert(addr == current@);
                    }
                }
                BranchScanStepResult::Advanced { reads: Ghost(reads) }
            },
            FetchErrorCode::CacheFull => BranchScanStepResult::CacheFull,
            FetchErrorCode::Awaiting | FetchErrorCode::NotPresent =>
                BranchScanStepResult::Blocked,
        }
    }

    pub fn step(
        &mut self,
        cache: &mut FracCacheImpl,
    ) -> (out: BranchScanStepResult)
        requires
            old(self).wf(),
            old(self).receipt_wf(),
            old(cache).wf(),
            old(self).cache_inv(old(cache)@),
        ensures
            self.wf(),
            self.receipt_wf(),
            cache.wf(),
            self.cache_inv(cache@),
            cache.valid_load_handles_preserved(*old(cache)),
            self.root == old(self).root,
            self.source@ == old(self).source@,
            self.ranking@ == old(self).ranking@,
            self.emitted@ == old(self).emitted@,
            forall |addr: Address, raw: RawPage|
                cache@.valid_read(addr, raw)
                ==> old(cache)@.valid_read(addr, raw),
            forall |addr: Address, raw: RawPage|
                old(cache)@.valid_read(addr, raw)
                ==> cache@.valid_read(addr, raw),
            match out {
                BranchScanStepResult::Advanced { reads } => {
                    &&& cache@ == old(cache)@
                    &&& reads@.dom().finite()
                    &&& reads@.len() == 1
                    &&& self.scanned@ == old(self).scanned@ + reads@.dom()
                    &&& forall |addr: Address|
                        #[trigger] reads@.contains_key(addr) ==> {
                            &&& self.source@.disk_view.entries.contains_key(addr)
                            &&& raw_page_to_branch_node(reads@[addr])
                                == self.source@.disk_view.entries[addr]
                        }
                    &&& forall |addr: Address|
                        #[trigger] reads@.contains_key(addr)
                        ==> old(cache)@.valid_read(addr, reads@[addr])
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        Cache::Label::Access {
                            reads: reads@,
                            writes: Map::empty(),
                        },
                    )
                },
                BranchScanStepResult::ItemReady => {
                    &&& *self == *old(self)
                    &&& cache@ == old(cache)@
                    &&& self.current_leaf is Some
                },
                BranchScanStepResult::Done => {
                    &&& *self == *old(self)
                    &&& cache@ == old(cache)@
                    &&& self.remaining().len() == 0
                    &&& self.scanned@ == self.source@.full_repr()
                },
                BranchScanStepResult::NeedCacheLoad { addr, handle } => {
                    &&& *self == *old(self)
                    &&& old(self).source@.get_summary().contains(addr@.au)
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
                BranchScanStepResult::CacheFull
                | BranchScanStepResult::Blocked
                | BranchScanStepResult::InvalidPage => {
                    &&& *self == *old(self)
                    &&& cache@ == old(cache)@
                },
            },
    {
        if self.current_leaf.is_some() {
            return BranchScanStepResult::ItemReady;
        }
        if self.pending.len() > 0 {
            return self.step_tree(cache);
        }
        match self.aux_state {
            BranchScanAuxState::Complete => {
                proof {
                    self.receipt_wf_ensures();
                    assert(pending_reachable_addrs(
                        self.source@,
                        self.ranking@,
                        self.pending@,
                    ).is_empty());
                    assert(pending_aux_addrs(
                        self.source@,
                        self.aux_state,
                    ).is_empty());
                    assert_sets_equal!(
                        self.scanned@,
                        self.source@.full_repr(),
                    );
                }
                BranchScanStepResult::Done
            },
            BranchScanAuxState::AwaitingRoot => {
                BranchScanStepResult::InvalidPage
            },
            BranchScanAuxState::PendingAux { .. } => self.step_aux(cache),
        }
    }
}

} // verus!
