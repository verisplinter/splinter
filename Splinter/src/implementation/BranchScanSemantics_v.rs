// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::assert_maps_equal;

use crate::abstract_system::MsgHistory_v::KeyedMessage;
use crate::allocation_layer::BranchTypes_v::{BranchNode, Summary};
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::Buffer_v::Buffer;
use crate::betree::LinkedBranch_v::{DiskView, LinkedBranch};
use crate::betree::LinkedBranch_v::Refinement_v as LinkedBranchRefinement;
use crate::betree::PivotBranch_v::Node as PivotBranchNode;
use crate::betree::PivotBranchRefinement_v as PivotBranchRefinement;
use crate::disk::GenericDisk_v::{AU, Address, Ranking};
use crate::implementation::BranchScanCursorImpl_v::{
    branch_scan_entries_strictly_sorted, leaf_entries,
    pivot_branch_entries, pivot_branch_entries_sorted,
    pivot_children_entries,
};
use crate::implementation::CachedBranchBetree_v::{
    loaded_sealed_branch, valid_loaded_sealed_branch,
    valid_loaded_sealed_branches,
};
use crate::implementation::CachedBranch_v::LoadedBranch;
use crate::implementation::CachingDisk_v::addresses_in_aus;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Delta, Message};

verus! {

pub open spec fn keyed_entries_contains(
    entries: Seq<KeyedMessage>,
    key: Key,
) -> bool {
    exists |i: int| 0 <= i < entries.len()
        && (#[trigger] entries[i]).key == key
}

pub open spec fn keyed_entries_message(
    entries: Seq<KeyedMessage>,
    key: Key,
) -> Message
    recommends keyed_entries_contains(entries, key),
{
    let i = choose |i: int| 0 <= i < entries.len()
        && entries[i].key == key;
    entries[i].message
}

pub open spec fn keyed_entries_query(
    entries: Seq<KeyedMessage>,
    key: Key,
) -> Message {
    if keyed_entries_contains(entries, key) {
        keyed_entries_message(entries, key)
    } else {
        Message::Update { delta: Delta(0) }
    }
}

pub open spec fn linked_branch_entries(
    branch: LinkedBranch<Summary>,
) -> Seq<KeyedMessage> {
    let ranking = branch.the_ranking();
    linked_branch_entries_at(branch, ranking)
}

pub open spec fn linked_branch_entries_at(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
) -> Seq<KeyedMessage> {
    pivot_branch_entries(
        branch.i_internal(ranking),
        ranking[branch.root] + 1,
    )
}

closed spec fn pivot_entries_fuel_wf(
    node: PivotBranchNode,
    fuel: nat,
) -> bool
    decreases node,
{
    match node {
        PivotBranchNode::Leaf { .. } => true,
        PivotBranchNode::Index { children, .. } => {
            &&& fuel > 0
            &&& forall |i: int| 0 <= i < children.len()
                ==> pivot_entries_fuel_wf(
                    #[trigger] children[i],
                    (fuel - 1) as nat,
                )
        },
    }
}

pub proof fn keyed_entries_query_index(
    entries: Seq<KeyedMessage>,
    index: int,
)
    requires
        branch_scan_entries_strictly_sorted(entries),
        0 <= index < entries.len(),
    ensures
        keyed_entries_contains(entries, entries[index].key),
        keyed_entries_query(entries, entries[index].key)
            == entries[index].message,
{
    let key = entries[index].key;
    assert(keyed_entries_contains(entries, key));
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
    let left = pivot_branch_entries(children[0], fuel);
    let right = pivot_children_entries(children.drop_first(), fuel);
    if child_idx > 0 {
        assert(children.drop_first()[child_idx - 1]
            == children[child_idx]);
        pivot_child_entry_in_children(
            children.drop_first(),
            fuel,
            child_idx - 1,
            item,
        );
        let i = choose |i: int| 0 <= i < right.len()
            && right[i] == item;
        assert((left + right)[left.len() as int + i] == item);
    } else {
        let i = choose |i: int| 0 <= i < left.len()
            && left[i] == item;
        assert((left + right)[i] == item);
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
        keyed_entries_contains(
            pivot_branch_entries(node, fuel),
            key,
        ) <==> node.i().map.contains_key(key),
        keyed_entries_query(
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
            if keyed_entries_contains(leaf_entries(keys, msgs), key) {
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
                keyed_entries_query_index(leaf_entries(keys, msgs), route);
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
        PivotBranchNode::Index { children, .. } => {
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
            if keyed_entries_contains(whole, key) {
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
                keyed_entries_query_index(child_entries, child_i);
                keyed_entries_query_index(whole, i);
            }
            if node.i().map.contains_key(key) {
                assert(children[route + 1].i().map.contains_key(key));
                let child_entries = pivot_branch_entries(
                    children[route + 1],
                    (fuel - 1) as nat,
                );
                assert(keyed_entries_contains(child_entries, key));
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
                keyed_entries_query_index(child_entries, child_i);
                keyed_entries_query_index(whole, whole_i);
            }
        },
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

pub proof fn linked_branch_entries_at_refine(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
)
    requires branch.inv_internal(ranking),
    ensures
        branch_scan_entries_strictly_sorted(
            linked_branch_entries_at(branch, ranking),
        ),
        forall |key: Key|
            keyed_entries_contains(
                linked_branch_entries_at(branch, ranking),
                key,
            ) <==> branch.i_internal(ranking).i().map.contains_key(key),
        forall |key: Key|
            keyed_entries_query(
                linked_branch_entries_at(branch, ranking),
                key,
            ) == branch.i_internal(ranking).i().query(key),
{
    linked_branch_entries_fuel_wf(
        branch,
        ranking,
        ranking[branch.root] + 1,
    );
    LinkedBranchRefinement::i_internal_wf(branch, ranking);
    assert forall |key: Key|
        keyed_entries_contains(
            pivot_branch_entries(
                branch.i_internal(ranking),
                ranking[branch.root] + 1,
            ),
            key,
        ) <==> branch.i_internal(ranking).i().map.contains_key(key)
    by {
        pivot_branch_entry_key_refines(
            branch.i_internal(ranking),
            ranking[branch.root] + 1,
            key,
        );
    }
    assert forall |key: Key|
        keyed_entries_query(
            pivot_branch_entries(
                branch.i_internal(ranking),
                ranking[branch.root] + 1,
            ),
            key,
        ) == branch.i_internal(ranking).i().query(key)
    by {
        pivot_branch_entry_key_refines(
            branch.i_internal(ranking),
            ranking[branch.root] + 1,
            key,
        );
    }
    pivot_branch_entries_sorted(
        branch.i_internal(ranking),
        ranking[branch.root] + 1,
    );
}

pub proof fn linked_branch_entries_refine(
    branch: LinkedBranch<Summary>,
)
    requires branch.valid_sealed_branch(),
    ensures
        branch_scan_entries_strictly_sorted(linked_branch_entries(branch)),
        forall |key: Key|
            keyed_entries_contains(
                linked_branch_entries(branch),
                key,
            ) <==> branch.i().i().map.contains_key(key),
        forall |key: Key|
            keyed_entries_query(
                linked_branch_entries(branch),
                key,
            ) == branch.i().i().query(key),
{
    let ranking = branch.the_ranking();
    assert(branch.inv());
    linked_branch_entries_at_refine(branch, ranking);
    assert(branch.i() == branch.i_internal(ranking));
}

pub proof fn loaded_branch_forest_wf(
    roots: Set<Address>,
    summaries: Map<AU, Summary>,
    reads: LoadedBranch,
)
    requires valid_loaded_sealed_branches(roots, summaries, reads),
    ensures (DiskView::<Summary> { entries: reads }).wf(),
{
    let disk = DiskView::<Summary> { entries: reads };
    assert forall |addr: Address| #[trigger] reads.contains_key(addr)
        implies reads[addr].wf() by {
        let root = choose |root: Address| roots.contains(root)
            && loaded_sealed_branch(
                root,
                reads.restrict(addresses_in_aus(summaries[root.au])),
            ).disk_view.entries.contains_key(addr);
        assert(summaries.contains_key(root.au));
        let bounded = reads.restrict(
            addresses_in_aus(summaries[root.au]),
        );
        assert(bounded.restrict(addresses_in_aus(summaries[root.au]))
            == bounded) by {
            assert_maps_equal!(
                bounded.restrict(addresses_in_aus(summaries[root.au])),
                bounded,
                candidate => {}
            );
        }
        let branch = loaded_sealed_branch(root, bounded);
        assert(branch.valid_sealed_branch());
        assert(branch.disk_view.entries.contains_key(addr));
        assert(branch.disk_view.entries[addr] == reads[addr]);
    }
    assert forall |addr: Address| #[trigger] reads.contains_key(addr)
        implies disk.node_has_valid_child_address(reads[addr]) by {
        let root = choose |root: Address| roots.contains(root)
            && loaded_sealed_branch(
                root,
                reads.restrict(addresses_in_aus(summaries[root.au])),
            ).disk_view.entries.contains_key(addr);
        let bounded = reads.restrict(
            addresses_in_aus(summaries[root.au]),
        );
        assert(bounded.restrict(addresses_in_aus(summaries[root.au]))
            == bounded) by {
            assert_maps_equal!(
                bounded.restrict(addresses_in_aus(summaries[root.au])),
                bounded,
                candidate => {}
            );
        }
        let branch = loaded_sealed_branch(root, bounded);
        assert(branch.valid_sealed_branch());
        assert(branch.disk_view.entries[addr] == reads[addr]);
        assert(branch.disk_view.wf());
        if reads[addr] is Index {
            assert(branch.disk_view.node_has_valid_child_address(
                branch.disk_view.entries[addr],
            ));
            assert forall |idx: int| 0 <= idx < reads[addr]->children.len()
                implies {
                    let child = #[trigger] reads[addr]->children[idx];
                    &&& reads.contains_key(child)
                    &&& !(reads[child] is Auxiliary)
                } by {
                let child = reads[addr]->children[idx];
                assert(branch.disk_view.entries.contains_key(child));
                assert(branch.disk_view.entries[child] == reads[child]);
            }
        }
    }
}

/* The generic version lives at the linked-branch refinement boundary, where
 * the closed public query can be related to its ranked traversal.
proof fn subdisk_query_same(
    small: LinkedBranch<Summary>,
    small_ranking: Ranking,
    big: LinkedBranch<Summary>,
    big_ranking: Ranking,
    key: Key,
)
    requires
        small.inv_internal(small_ranking),
        big.wf(),
        big.valid_ranking(big_ranking),
        small.root == big.root,
        small.disk_view.entries <= big.disk_view.entries,
    ensures
        small.contains_internal(small_ranking, key)
            == big.contains_internal(big_ranking, key),
        small.query_internal(key, small_ranking)
            == big.query_internal(key, big_ranking),
    decreases small.get_rank(small_ranking),
{
    assert(small.root() == big.root());
    let route = small.root().route(key);
    if small.root() is Index {
        LinkedBranchRefinement::lemma_route_ensures(
            small.root(),
            key,
        );
        assert(small.root().valid_child_index(route + 1));
        assert(big.root().valid_child_index(route + 1));
        let small_child = small.child_at_idx(route + 1);
        let big_child = big.child_at_idx(route + 1);
        assert(small_child.root == big_child.root);
        assert(small_child.disk_view.entries <= big_child.disk_view.entries);
        assert(small_child.inv_internal(small_ranking));
        assert(big_child.wf());
        assert(big_child.valid_ranking(big_ranking));
        subdisk_query_same(
            small_child,
            small_ranking,
            big_child,
            big_ranking,
            key,
        );
    }
}
*/

proof fn restricted_source_ranking_valid_for_superdisk(
    source: LinkedBranch<Summary>,
    big: LinkedBranch<Summary>,
) -> (ranking: Ranking)
    requires
        source.inv(),
        big.wf(),
        source.root == big.root,
        source.disk_view.entries <= big.disk_view.entries,
    ensures big.valid_ranking(ranking),
{
    let source_ranking = source.the_ranking();
    let ranking = source_ranking.restrict(
        source.disk_view.entries.dom(),
    );
    assert(ranking.contains_key(big.root));
    assert forall |addr: Address|
        #[trigger] ranking.contains_key(addr)
            && big.disk_view.entries.contains_key(addr)
        implies big.disk_view.node_children_respects_rank(
            ranking,
            addr,
        ) by {
        assert(source_ranking.contains_key(addr));
        assert(source.disk_view.entries.contains_key(addr));
        assert(source.disk_view.entries[addr]
            == big.disk_view.entries[addr]);
        assert(source.disk_view.node_children_respects_rank(
            source_ranking,
            addr,
        ));
        assert forall |child_idx: int|
            #[trigger] big.disk_view.entries[addr]
                .valid_child_index(child_idx)
            implies {
                let child = big.disk_view.entries[addr]->children[child_idx];
                &&& ranking.contains_key(child)
                &&& ranking[child] < ranking[addr]
            } by {
            let child = big.disk_view.entries[addr]->children[child_idx];
            assert(source.disk_view.entries.contains_key(child));
            assert(source_ranking.contains_key(child));
            assert(ranking.contains_key(child));
        }
    }
    ranking
}

pub proof fn loaded_branch_in_forest_refines(
    root: Address,
    summary: Summary,
    reads: LoadedBranch,
    key: Key,
)
    requires
        (DiskView::<Summary> { entries: reads }).wf(),
        valid_loaded_sealed_branch(
            root,
            summary,
            reads.restrict(addresses_in_aus(summary)),
        ),
    ensures ({
        let bounded = reads.restrict(addresses_in_aus(summary));
        let source = loaded_sealed_branch(root, bounded);
        let disk = BufferDisk::<BranchNode> { entries: reads };
        &&& disk.entries[root].linked_contains(disk, root, key)
            <==> source.i().i().map.contains_key(key)
        &&& disk.entries[root].linked_query(disk, root, key)
            == source.i().i().query(key)
    }),
{
    let bounded = reads.restrict(addresses_in_aus(summary));
    assert(bounded.restrict(addresses_in_aus(summary)) == bounded) by {
        assert_maps_equal!(
            bounded.restrict(addresses_in_aus(summary)),
            bounded,
            candidate => {}
        );
    }
    let source = loaded_sealed_branch(root, bounded);
    let big = LinkedBranch::<Summary> {
        root,
        disk_view: DiskView { entries: reads },
    };
    assert(source.valid_sealed_branch());
    assert(source.disk_view.entries <= big.disk_view.entries);
    assert(big.disk_view.entries.contains_key(root));
    assert(big.disk_view.entries[root] == source.root());
    assert(big.wf());
    let ranking = restricted_source_ranking_valid_for_superdisk(
        source,
        big,
    );
    assert(big.acyclic());
    LinkedBranchRefinement::subdisk_same_query_and_contains(
        source,
        big,
        key,
    );
    let present = source.contains_internal(source.the_ranking(), key);
    LinkedBranchRefinement::i_wf(source);
    LinkedBranchRefinement::contains_internal_refines(
        source,
        source.the_ranking(),
        key,
        present,
    );
    PivotBranchRefinement::contains_refines(
        source.i(),
        key,
        present,
    );
    let message = source.query(key);
    LinkedBranchRefinement::query_refines(
        source,
        key,
        message,
    );
    PivotBranchRefinement::query_refines(
        source.i(),
        crate::betree::PivotBranchRefinement_v::QueryLabel {
            key,
            msg: message,
        },
    );
}

/// Relates the exact immutable disk of a sealed branch to its SimpleBuffer
/// interpretation. Completion uses this after the streaming builder seals its
/// output, so it does not need to read the output pages back through the cache.
pub proof fn sealed_branch_refines_buffer(
    branch: LinkedBranch<Summary>,
    key: Key,
)
    requires
        branch.valid_sealed_branch(),
        branch.tight_disk_view_with_summary(),
    ensures ({
        let disk = BufferDisk::<BranchNode> {
            entries: branch.disk_view.entries,
        };
        &&& branch.root().linked_contains(disk, branch.root, key)
            <==> branch.i().i().map.contains_key(key)
        &&& branch.root().linked_query(disk, branch.root, key)
            == branch.i().i().query(key)
    }),
{
    let reads = branch.disk_view.entries;
    let summary = branch.get_summary();
    assert(reads.restrict(addresses_in_aus(summary)) == reads) by {
        assert_maps_equal!(
            reads.restrict(addresses_in_aus(summary)),
            reads,
            addr => {
                if reads.contains_key(addr) {
                    assert(branch.full_repr().contains(addr));
                    assert(summary.contains(addr.au)) by {
                        assert(crate::disk::GenericDisk_v::addrs_closed(
                            branch.full_repr(),
                            summary,
                        ));
                    }
                }
            }
        );
    }
    assert(loaded_sealed_branch(branch.root, reads) == branch);
    assert(valid_loaded_sealed_branch(branch.root, summary, reads));
    loaded_branch_in_forest_refines(branch.root, summary, reads, key);
}

}
