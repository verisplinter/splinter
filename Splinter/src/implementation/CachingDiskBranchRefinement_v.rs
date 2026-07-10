// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Refinement from CachingDiskBranch to AllocationBranchStack.

#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::map::*;
use vstd::map_lib::lemma_values_finite;
use vstd::assert_maps_equal;

use crate::allocation_layer::AllocationBranch_v::{AllocationBranch, BranchNode, Summary};
use crate::allocation_layer::AllocationBranchBetree_v::{branch_summary_insert_ensures, summary_aus};
use crate::allocation_layer::Likes_v::restrict_domain_au;
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::Utils_v::{
    lemma_union_set_of_sets_contains, lemma_union_set_of_sets_subset,
};
use crate::betree::LinkedBranch_v::{
    DiskView, LinkedBranch, Path, Refinement_v as LinkedBranchRefinement, SplitArg,
};
use crate::betree::PivotBranchRefinement_v::{self as PivotBranchRefinement, QueryLabel};
use crate::disk::GenericDisk_v::{Ranking, addrs_closed, to_aus};
use crate::implementation::CachedBranch_v::{
    CachedBranch, LoadedBranch, LoadedPathReceipt, loaded_append_ready,
    loaded_append_write_nodes, loaded_grow_write_nodes, loaded_initialize_write_nodes,
    loaded_seal_write_nodes, loaded_split_ready, loaded_split_write_nodes,
    receipt_valid_implies_tail_valid, root_summary_from_read, root_summary_read_valid,
};
use crate::implementation::AllocationBranchStack_v::*;
use crate::implementation::CachingDiskBranch_v::*;
use crate::implementation::CachingDisk_v::{addresses_in_aus, CachingDisk, PageStatus};
use crate::spec::AsyncDisk_t::{AU, Address, RawPage};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Message, nop_delta};

verus!{

pub open spec fn query_from_receipts_with_base(
    base: Message,
    receipts: Seq<LoadedPathReceipt>,
    end: nat,
) -> Message
    recommends
        end <= receipts.len(),
    decreases end
{
    if end == 0 {
        base
    } else {
        let idx = (end - 1) as int;
        query_from_receipts_with_base(base, receipts, (end - 1) as nat)
            .merge(receipts[idx].result())
    }
}

pub open spec fn stack_branch_query_at(
    state: CachingDiskBranch::State,
    idx: nat,
    key: Key,
) -> Message
    recommends
        idx < query_roots(state.sealed_roots, state.active_branch).len(),
{
    if idx < state.sealed_roots.len() {
        state.sealed_stack_i().sealed_branch_at(state.interpreted_branch_summary(), idx).query(key)
    } else {
        active_branch_query_or_nop(state.i().active_branch, key)
    }
}

pub open spec fn stack_query_roots_up_to(
    state: CachingDiskBranch::State,
    end: nat,
    key: Key,
) -> Message
    recommends
        end <= query_roots(state.sealed_roots, state.active_branch).len(),
    decreases end
{
    if end == 0 {
        Message::Update{delta: nop_delta()}
    } else {
        stack_query_roots_up_to(state, (end - 1) as nat, key)
            .merge(stack_branch_query_at(state, (end - 1) as nat, key))
    }
}

proof fn child_branch_inv_internal_from_parent(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    child_idx: int,
)
    requires
        branch.inv_internal(ranking),
        branch.root().valid_child_index(child_idx),
    ensures
        branch.child_at_idx(child_idx).inv_internal(ranking),
{
    assert(branch.child_at_idx(child_idx).valid_ranking(ranking)) by {
        assert(branch.disk_view.valid_ranking(ranking));
        assert(ranking.contains_key(branch.root));
        assert(branch.disk_view.node_children_respects_rank(ranking, branch.root));
        assert(ranking.contains_key(branch.root()->children[child_idx]));
    };
    assert(branch.child_at_idx(child_idx).keys_strictly_sorted_internal(ranking));
    assert(branch.child_at_idx(child_idx).all_keys_in_range_internal(ranking));
}

proof fn local_i_internal_query_descends_to_child(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    key: Key,
)
    requires
        branch.inv_internal(ranking),
        branch.root() is Index,
    ensures
        branch.i_internal(ranking).query(key)
            == branch.child_at_idx(branch.root().route(key) + 1).i_internal(ranking).query(key),
{
    let node = branch.root();
    let r = node.route(key);
    let branch_i = branch.i_internal(ranking);
    let child_i = branch.child_at_idx(r + 1).i_internal(ranking);
    LinkedBranchRefinement::i_internal_wf(branch, ranking);
    LinkedBranchRefinement::lemma_route_ensures(node, key);
    assert(node.valid_child_index(r + 1));
    assert(branch_i is Index);
    assert(branch_i->pivots == node->pivots);
    assert(branch_i.route(key) == node.route(key));
    assert(branch_i->children[r + 1] == child_i);
    PivotBranchRefinement::query_refines(
        branch_i,
        QueryLabel{key, msg: branch_i.query(key)},
    );
    PivotBranchRefinement::query_refines_to_routed_child(
        branch_i,
        QueryLabel{key, msg: branch_i.query(key)},
    );
    PivotBranchRefinement::query_refines(
        child_i,
        QueryLabel{key, msg: child_i.query(key)},
    );
    assert(branch_i.i().query(key) == branch_i.query(key));
    assert(child_i.i().query(key) == branch_i.query(key));
    assert(child_i.i().query(key) == child_i.query(key));
}

proof fn local_query_internal_descends_to_child(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    key: Key,
)
    requires
        branch.inv_internal(ranking),
        branch.root() is Index,
    ensures
        branch.query_internal(key, ranking)
            == branch.child_at_idx(branch.root().route(key) + 1).query_internal(key, ranking),
{
    let node = branch.root();
    let r = node.route(key);
    let child = branch.child_at_idx(r + 1);
    LinkedBranchRefinement::lemma_route_ensures(node, key);
    assert(node.valid_child_index(r + 1));
    child_branch_inv_internal_from_parent(branch, ranking, r + 1);
    LinkedBranchRefinement::query_internal_refines(
        branch,
        ranking,
        key,
        branch.query_internal(key, ranking),
    );
    LinkedBranchRefinement::query_internal_refines(
        child,
        ranking,
        key,
        child.query_internal(key, ranking),
    );
    local_i_internal_query_descends_to_child(branch, ranking, key);
    assert(branch.query_internal(key, ranking) == branch.i_internal(ranking).query(key));
    assert(child.query_internal(key, ranking) == child.i_internal(ranking).query(key));
    assert(branch.child_at_idx(branch.root().route(key) + 1) == child);
    assert(branch.i_internal(ranking).query(key) == child.i_internal(ranking).query(key));
}

proof fn query_read_node_matches_visible(
    disk: CachingDisk::State,
    reads: Map<Address, RawPage>,
    addr: Address,
)
    requires
        disk.inv(),
        reads <= disk.cache,
        reads.contains_key(addr),
        disk.visible().contains_key(addr),
    ensures
        to_branch_nodes(disk.visible()).contains_key(addr),
        to_branch_nodes(reads)[addr] == to_branch_nodes(disk.visible())[addr],
{
    assert(disk.cache.contains_key(addr));
    assert(reads[addr] == disk.cache[addr]);
    if disk.visible_cache().contains_key(addr) {
        assert(disk.visible()[addr] == disk.cache[addr]);
    } else {
        assert(disk.persistent.contains_key(addr));
        assert(disk.status.contains_key(addr));
        assert(disk.status[addr] == PageStatus::Clean);
        disk.clean_page_agrees(addr);
        assert(disk.persistent[addr] == disk.cache[addr]);
        assert(disk.visible()[addr] == disk.persistent[addr]);
    }
}

proof fn receipt_query_matches_branch_query_internal(
    disk: CachingDisk::State,
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    reads: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
)
    requires
        disk.inv(),
        reads <= disk.cache,
        branch.inv_internal(ranking),
        receipt.valid_for(branch.root, to_branch_nodes(reads)),
        receipt.target().node is Leaf,
        branch.disk_view.entries <= to_branch_nodes(disk.visible()),
    ensures
        branch.query_internal(receipt.key, ranking) == receipt.result(),
    decreases receipt.depth(),
{
    let read_nodes = to_branch_nodes(reads);
    let root = branch.root;
    assert(receipt.needed_addrs().contains(root)) by {
        assert(receipt.lines[0].addr == receipt.root);
        assert(receipt.root == root);
    }
    assert(read_nodes.contains_key(root));
    assert(branch.disk_view.entries.contains_key(root));
    assert(to_branch_nodes(disk.visible()).contains_key(root));
    query_read_node_matches_visible(disk, reads, root);
    assert(read_nodes[root] == branch.disk_view.entries[root]);
    assert(branch.root() == receipt.lines[0].node);

    if receipt.depth() == 0 {
        assert(receipt.lines.len() == 1);
        assert(receipt.target() == receipt.lines[0]);
        assert(branch.root() == receipt.target().node);
        reveal(LinkedBranch::query_internal);
    } else {
        assert(receipt.lines.len() > 1);
        assert(receipt.lines[0].node is Index);
        assert(branch.root() is Index);
        let child_idx = branch.root().route(receipt.key) + 1;
        LinkedBranchRefinement::lemma_route_ensures(branch.root(), receipt.key);
        assert(branch.root().valid_child_index(child_idx));
        let child_branch = branch.child_at_idx(child_idx);
        let child_receipt = receipt.tail();
        receipt_valid_implies_tail_valid(receipt, read_nodes);
        assert(child_branch.root == child_receipt.root) by {
            assert(receipt.lines[0].node->children[child_idx] == receipt.lines[1].addr);
            assert(branch.root()->children[child_idx] == receipt.lines[1].addr);
            assert(child_branch.root == branch.root()->children[child_idx]);
            assert(child_receipt.root == receipt.lines[1].addr);
        }
        assert(child_receipt.target() == receipt.target()) by {
            assert(child_receipt.lines.last() == receipt.lines.last());
        }
        child_branch_inv_internal_from_parent(branch, ranking, child_idx);
        receipt_query_matches_branch_query_internal(
            disk,
            child_branch,
            ranking,
            reads,
            child_receipt,
        );
        local_query_internal_descends_to_child(branch, ranking, receipt.key);
        assert(branch.child_at_idx(branch.root().route(receipt.key) + 1) == child_branch);
        assert(child_branch.query_internal(receipt.key, ranking) == child_receipt.result());
        assert(child_receipt.result() == receipt.result());
    }
}

proof fn receipt_query_matches_branch_query(
    disk: CachingDisk::State,
    branch: LinkedBranch<Summary>,
    reads: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
)
    requires
        disk.inv(),
        reads <= disk.cache,
        branch.inv(),
        receipt.valid_for(branch.root, to_branch_nodes(reads)),
        receipt.target().node is Leaf,
        branch.disk_view.entries <= to_branch_nodes(disk.visible()),
    ensures
        branch.query(receipt.key) == receipt.result(),
{
    let ranking = branch.the_ranking();
    receipt_query_matches_branch_query_internal(disk, branch, ranking, reads, receipt);
    let msg = receipt.result();
    LinkedBranchRefinement::query_internal_refines(branch, ranking, receipt.key, msg);
    LinkedBranchRefinement::query_refines(branch, receipt.key, branch.query(receipt.key));
    assert(branch.i_internal(ranking).query(receipt.key) == msg);
    assert(branch.i().query(receipt.key) == branch.query(receipt.key));
    assert(branch.i() == branch.i_internal(ranking));
    assert(branch.query(receipt.key) == msg);
}

proof fn leaf_append_route_equiv(leaf: BranchNode, keys: Seq<Key>)
    requires
        leaf is Leaf,
        leaf.wf(),
        leaf.keys_strictly_sorted(),
        leaf->keys.len() > 0,
        keys.len() > 0,
        Key::is_strictly_sorted(keys),
        Key::lt(leaf->keys.last(), keys[0]),
    ensures
        leaf.route(keys[0]) == leaf.route(keys.last()),
{
    let last_idx = leaf->keys.len() - 1;
    Key::strictly_sorted_implies_sorted(leaf->keys);
    Key::strictly_sorted_implies_sorted(keys);
    Key::lte_transitive_forall();
    assert(0 <= last_idx < leaf->keys.len());
    assert(Key::lte(leaf->keys[last_idx], keys[0]));
    Key::largest_lte_is_lemma(leaf->keys, keys[0], last_idx);
    assert(Key::lte(keys[0], keys.last()));
    assert(Key::lte(leaf->keys[last_idx], keys.last()));
    Key::largest_lte_is_lemma(leaf->keys, keys.last(), last_idx);
}

proof fn receipt_path_valid_for_append(
    disk: CachingDisk::State,
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    reads: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    keys: Seq<Key>,
    msgs: Seq<Message>,
)
    requires
        disk.inv(),
        reads <= disk.cache,
        branch.inv_internal(ranking),
        receipt.root == branch.root,
        keys.len() > 0,
        loaded_append_ready(receipt, to_branch_nodes(reads), keys, msgs),
        branch.disk_view.entries <= to_branch_nodes(disk.visible()),
    ensures
        ({
            let path = Path{branch, key: keys[0], depth: receipt.depth()};
            &&& path.valid()
            &&& path.target().has_root()
            &&& path.target().root == receipt.target().addr
            &&& path.target().root() == receipt.target().node
            &&& path.target().disk_view == branch.disk_view
            &&& path.path_equiv(keys.last())
        }),
    decreases receipt.depth(),
{
    let read_nodes = to_branch_nodes(reads);
    let path = Path{branch, key: keys[0], depth: receipt.depth()};
    let root = branch.root;

    assert(receipt.valid_for(receipt.root, read_nodes));
    assert(receipt.root == root);
    assert(receipt.key == keys[0]);
    assert(keys.len() > 0);
    assert(receipt.needed_addrs().contains(root)) by {
        assert(receipt.lines[0].addr == receipt.root);
    }
    assert(read_nodes.contains_key(root));
    assert(branch.disk_view.entries.contains_key(root));
    assert(to_branch_nodes(disk.visible()).contains_key(root));
    query_read_node_matches_visible(disk, reads, root);
    assert(read_nodes[root] == branch.disk_view.entries[root]);
    assert(receipt.lines[0].node == branch.root());

    if receipt.depth() == 0 {
        assert(receipt.lines.len() == 1);
        assert(receipt.target() == receipt.lines[0]);
        assert(path.valid());
        assert(path.target() == branch);
        assert(path.target().has_root());
        assert(path.target().root == receipt.target().addr);
        assert(path.target().root() == receipt.target().node);
        leaf_append_route_equiv(receipt.target().node, keys);
        assert(path.path_equiv(keys.last()));
    } else {
        assert(receipt.lines.len() > 1);
        assert(receipt.lines[0].node is Index);
        assert(branch.root() is Index);
        let child_idx = branch.root().route(receipt.key) + 1;
        LinkedBranchRefinement::lemma_route_ensures(branch.root(), receipt.key);
        assert(branch.root().valid_child_index(child_idx));
        let child_branch = branch.child_at_idx(child_idx);
        let child_receipt = receipt.tail();
        receipt_valid_implies_tail_valid(receipt, read_nodes);
        assert(child_branch.root == child_receipt.root) by {
            assert(receipt.lines[0].node->children[child_idx] == receipt.lines[1].addr);
            assert(branch.root()->children[child_idx] == receipt.lines[1].addr);
            assert(child_branch.root == branch.root()->children[child_idx]);
            assert(child_receipt.root == receipt.lines[1].addr);
        }
        assert(child_receipt.target() == receipt.target()) by {
            assert(child_receipt.lines.last() == receipt.lines.last());
        }
        assert(child_receipt.path_equiv(keys.last())) by {
            assert forall |i: int|
                0 <= i < child_receipt.lines.len() - 1
                implies child_receipt.lines[i].node.route(child_receipt.key)
                    == #[trigger] child_receipt.lines[i].node.route(keys.last())
            by {
                assert(child_receipt.lines[i] == receipt.lines[i + 1]);
                assert(0 <= i + 1 < receipt.lines.len() - 1);
            }
        }
        assert(loaded_append_ready(child_receipt, read_nodes, keys, msgs));
        child_branch_inv_internal_from_parent(branch, ranking, child_idx);
        receipt_path_valid_for_append(
            disk,
            child_branch,
            ranking,
            reads,
            child_receipt,
            keys,
            msgs,
        );
        assert(path.subpath() == Path{
            branch: child_branch,
            key: keys[0],
            depth: child_receipt.depth(),
        });
        assert(path.valid());
        assert(path.target() == path.subpath().target());
        assert(path.target().has_root());
        assert(path.target().root == receipt.target().addr);
        assert(path.target().root() == receipt.target().node);
        assert(path.target().disk_view == branch.disk_view);
        assert(receipt.path_equiv(keys.last()));
        assert(branch.root().route(receipt.key) == branch.root().route(keys.last()));
        assert(path.path_equiv(keys.last()));
    }
}

proof fn linked_append_keys_are_path_equiv(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    keys: Seq<Key>,
    path: Path<Summary>,
)
    requires
        branch.inv_internal(ranking),
        path.valid(),
        path.branch == branch,
        keys.len() > 0,
        Key::is_strictly_sorted(keys),
        path.key == keys[0],
        path.path_equiv(keys.last()),
    ensures
        forall |key: Key| #[trigger] keys.contains(key) ==> path.path_equiv(key),
    decreases path.depth,
{
    if 0 < path.depth {
        let child_idx = branch.root().route(path.key) + 1;
        LinkedBranchRefinement::lemma_route_ensures(branch.root(), path.key);
        assert(branch.root().valid_child_index(child_idx));
        child_branch_inv_internal_from_parent(branch, ranking, child_idx);
        assert(path.subpath().branch == branch.child_at_idx(child_idx));
        linked_append_keys_are_path_equiv(branch.child_at_idx(child_idx), ranking, keys, path.subpath());
    }
    Key::strictly_sorted_implies_sorted(keys);
    assert forall |key: Key| #[trigger] keys.contains(key) implies path.path_equiv(key) by {
        let key_idx = choose |i: int| 0 <= i < keys.len() && keys[i] == key;
        assert(0 <= key_idx < keys.len());
        assert(keys[key_idx] == key);
        assert(Key::lte(keys[0], key)) by {
            assert(Key::is_sorted(keys));
            assert(Key::lte(keys[0], keys[key_idx]));
        }
        assert(Key::lte(key, keys.last())) by {
            assert(Key::is_sorted(keys));
            assert(Key::lte(keys[key_idx], keys[keys.len() - 1]));
        }
        LinkedBranchRefinement::lemma_key_lte_implies_route_lte(
            path.branch.root(),
            keys[0],
            key,
        );
        LinkedBranchRefinement::lemma_key_lte_implies_route_lte(
            path.branch.root(),
            key,
            keys.last(),
        );
        assert(path.branch.root().route(keys[0]) <= path.branch.root().route(key));
        assert(path.branch.root().route(key) <= path.branch.root().route(keys.last()));
        assert(path.branch.root().route(keys[0]) == path.branch.root().route(keys.last()));
        if 0 < path.depth {
            assert(path.subpath().path_equiv(key));
        }
    }
}

proof fn branch_query_nop_for_append_key_internal(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    keys: Seq<Key>,
    path: Path<Summary>,
    key: Key,
)
    requires
        branch.inv_internal(ranking),
        path.valid(),
        path.branch == branch,
        keys.len() > 0,
        Key::is_strictly_sorted(keys),
        keys.contains(key),
        path.key == keys[0],
        path.path_equiv(key),
        path.target().root() is Leaf,
        path.target().root()->keys.len() > 0,
        Key::lt(path.target().root()->keys.last(), keys[0]),
    ensures
        branch.query_internal(key, ranking) == (Message::Update{delta: nop_delta()}),
    decreases path.depth,
{
    Key::strictly_sorted_implies_sorted(keys);
    let key_idx = choose |i: int| 0 <= i < keys.len() && keys[i] == key;
    assert(0 <= key_idx < keys.len());
    assert(keys[key_idx] == key);
    assert(Key::lte(keys[0], key)) by {
        assert(Key::is_sorted(keys));
        assert(Key::lte(keys[0], keys[key_idx]));
    }

    if path.depth == 0 {
        assert(path.target() == branch);
        let leaf = branch.root();
        let last_idx = leaf->keys.len() - 1;
        Key::strictly_sorted_implies_sorted(leaf->keys);
        Key::lte_transitive_forall();
        assert(Key::lte(leaf->keys[last_idx], keys[0]));
        assert(Key::lte(leaf->keys[last_idx], key));
        Key::largest_lte_is_lemma(leaf->keys, key, last_idx);
        assert(leaf.route(key) == last_idx);
        assert(leaf->keys[leaf.route(key)] != key) by {
            assert(Key::lt(leaf->keys[last_idx], keys[0]));
            assert(Key::lte(keys[0], key));
            if leaf->keys[last_idx] == key {
                assert(Key::lte(key, leaf->keys[last_idx]));
                assert(Key::lte(keys[0], leaf->keys[last_idx]));
                assert(false);
            }
        }
        reveal(LinkedBranch::query_internal);
    } else {
        assert(branch.root() is Index);
        let child_idx = branch.root().route(path.key) + 1;
        assert(branch.root().route(path.key) == branch.root().route(key));
        LinkedBranchRefinement::lemma_route_ensures(branch.root(), path.key);
        assert(branch.root().valid_child_index(child_idx));
        let child_branch = branch.child_at_idx(child_idx);
        let child_path = path.subpath();
        child_branch_inv_internal_from_parent(branch, ranking, child_idx);
        assert(child_path.branch == child_branch);
        assert(child_path.path_equiv(key));
        assert(child_path.target() == path.target());
        branch_query_nop_for_append_key_internal(child_branch, ranking, keys, child_path, key);
        local_query_internal_descends_to_child(branch, ranking, key);
        assert(branch.child_at_idx(branch.root().route(key) + 1) == child_branch);
    }
}

proof fn branch_query_nop_for_append_key(
    branch: LinkedBranch<Summary>,
    keys: Seq<Key>,
    path: Path<Summary>,
    key: Key,
)
    requires
        branch.inv(),
        path.valid(),
        path.branch == branch,
        keys.len() > 0,
        Key::is_strictly_sorted(keys),
        keys.contains(key),
        path.key == keys[0],
        path.path_equiv(key),
        path.target().root() is Leaf,
        path.target().root()->keys.len() > 0,
        Key::lt(path.target().root()->keys.last(), keys[0]),
    ensures
        branch.query(key) == (Message::Update{delta: nop_delta()}),
{
    let ranking = branch.the_ranking();
    branch_query_nop_for_append_key_internal(branch, ranking, keys, path, key);
    let msg = Message::Update{delta: nop_delta()};
    LinkedBranchRefinement::query_internal_refines(branch, ranking, key, msg);
    LinkedBranchRefinement::query_refines(branch, key, branch.query(key));
    assert(branch.i_internal(ranking).query(key) == msg);
    assert(branch.i().query(key) == branch.query(key));
    assert(branch.i() == branch.i_internal(ranking));
    assert(branch.query(key) == msg);
}

proof fn receipt_path_valid_for_split(
    disk: CachingDisk::State,
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    reads: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    split_arg: SplitArg,
    new_child_addr: Address,
)
    requires
        disk.inv(),
        reads <= disk.cache,
        branch.inv_internal(ranking),
        receipt.root == branch.root,
        loaded_split_ready(receipt, to_branch_nodes(reads), split_arg),
        branch.disk_view.is_fresh(set!{new_child_addr}),
        branch.disk_view.entries <= to_branch_nodes(disk.visible()),
    ensures
        ({
            let path = Path{branch, key: split_arg.get_pivot(), depth: receipt.depth()};
            &&& path.valid()
            &&& path.target().root == receipt.target().addr
            &&& path.target().root() == receipt.target().node
            &&& path.target().disk_view == branch.disk_view
            &&& path.target().can_split_child_of_index(split_arg, new_child_addr)
        }),
    decreases receipt.depth(),
{
    let read_nodes = to_branch_nodes(reads);
    let path = Path{branch, key: split_arg.get_pivot(), depth: receipt.depth()};
    let root = branch.root;

    assert(receipt.valid_for(receipt.root, read_nodes));
    assert(receipt.key == split_arg.get_pivot());
    assert(receipt.needed_addrs().contains(root)) by {
        assert(receipt.lines[0].addr == receipt.root);
    }
    assert(read_nodes.contains_key(root));
    assert(branch.disk_view.entries.contains_key(root));
    assert(to_branch_nodes(disk.visible()).contains_key(root));
    query_read_node_matches_visible(disk, reads, root);
    assert(read_nodes[root] == branch.disk_view.entries[root]);
    assert(receipt.lines[0].node == branch.root());

    if receipt.depth() == 0 {
        assert(receipt.lines.len() == 1);
        assert(receipt.target() == receipt.lines[0]);
        assert(path.valid());
        assert(path.target() == branch);
        assert(path.target().root == receipt.target().addr);
        assert(path.target().root() == receipt.target().node);
        assert(path.target().root() is Index);
        let child_idx = path.target().root().route(split_arg.get_pivot()) + 1;
        LinkedBranchRefinement::lemma_route_ensures(path.target().root(), split_arg.get_pivot());
        assert(path.target().root().valid_child_index(child_idx));
        assert(path.target().root()->children[child_idx] == receipt.child_addr());
        let child_branch = path.target().child_at_idx(child_idx);
        assert(child_branch.root == receipt.child_addr());
        child_branch_inv_internal_from_parent(branch, ranking, child_idx);
        assert(child_branch.disk_view.entries.contains_key(child_branch.root));
        assert(read_nodes.contains_key(receipt.child_addr()));
        assert(to_branch_nodes(disk.visible()).contains_key(receipt.child_addr()));
        query_read_node_matches_visible(disk, reads, receipt.child_addr());
        assert(read_nodes[receipt.child_addr()] == branch.disk_view.entries[receipt.child_addr()]);
        assert(child_branch.root() == read_nodes[receipt.child_addr()]);
        assert(child_branch.has_root()) by {
            assert(crate::implementation::CachedBranch_v::loaded_line_wf(
                read_nodes,
                receipt.child_addr(),
            ));
            assert(!(read_nodes[receipt.child_addr()] is Auxiliary));
        }
        assert(split_arg.wf(child_branch)) by {
            assert(crate::implementation::CachedBranch_v::split_arg_matches_child(
                read_nodes[receipt.child_addr()],
                split_arg,
            ));
            assert(child_branch.root() == read_nodes[receipt.child_addr()]);
        }
        assert(child_branch.disk_view.is_fresh(set!{new_child_addr}));
        assert(path.target().can_split_child_of_index(split_arg, new_child_addr));
    } else {
        assert(receipt.lines.len() > 1);
        assert(receipt.lines[0].node is Index);
        assert(branch.root() is Index);
        let child_idx = branch.root().route(receipt.key) + 1;
        LinkedBranchRefinement::lemma_route_ensures(branch.root(), receipt.key);
        assert(branch.root().valid_child_index(child_idx));
        let child_branch = branch.child_at_idx(child_idx);
        let child_receipt = receipt.tail();
        receipt_valid_implies_tail_valid(receipt, read_nodes);
        assert(child_branch.root == child_receipt.root) by {
            assert(receipt.lines[0].node->children[child_idx] == receipt.lines[1].addr);
            assert(branch.root()->children[child_idx] == receipt.lines[1].addr);
            assert(child_branch.root == branch.root()->children[child_idx]);
            assert(child_receipt.root == receipt.lines[1].addr);
        }
        assert(child_receipt.target() == receipt.target()) by {
            assert(child_receipt.lines.last() == receipt.lines.last());
        }
        assert(child_receipt.child_addr() == receipt.child_addr()) by {
            assert(child_receipt.target() == receipt.target());
        }
        assert(loaded_split_ready(child_receipt, read_nodes, split_arg));
        child_branch_inv_internal_from_parent(branch, ranking, child_idx);
        receipt_path_valid_for_split(
            disk,
            child_branch,
            ranking,
            reads,
            child_receipt,
            split_arg,
            new_child_addr,
        );
        assert(path.subpath() == Path{
            branch: child_branch,
            key: split_arg.get_pivot(),
            depth: child_receipt.depth(),
        });
        assert(path.valid());
        assert(path.target() == path.subpath().target());
        assert(path.target().root == receipt.target().addr);
        assert(path.target().root() == receipt.target().node);
        assert(path.target().disk_view == branch.disk_view);
        assert(path.target().can_split_child_of_index(split_arg, new_child_addr));
    }
}

proof fn message_merge_nop_right(msg: Message)
    ensures
        msg.merge(Message::Update{delta: nop_delta()}) == msg,
{
    match msg {
        Message::Define{value} => {},
        Message::Update{delta} => {},
    }
}

proof fn message_merge_define_absorbs(older: Message, newer: Message)
    requires
        newer is Define,
    ensures
        older.merge(newer) == newer,
{
    match newer {
        Message::Define{value} => {},
        _ => { assert(false); },
    }
}

proof fn query_from_receipts_with_nop_base(
    receipts: Seq<LoadedPathReceipt>,
    end: nat,
)
    requires
        end <= receipts.len(),
    ensures
        query_from_receipts_with_base(Message::Update{delta: nop_delta()}, receipts, end)
            == query_from_receipts_up_to(receipts, end),
    decreases end,
{
    if end > 0 {
        query_from_receipts_with_nop_base(receipts, (end - 1) as nat);
    }
}

proof fn query_from_receipts_with_base_define_absorbs(
    base: Message,
    receipts: Seq<LoadedPathReceipt>,
    end: nat,
)
    requires
        end <= receipts.len(),
        query_from_receipts_up_to(receipts, end) is Define,
    ensures
        query_from_receipts_with_base(base, receipts, end)
            == query_from_receipts_up_to(receipts, end),
    decreases end,
{
    if end == 0 {
        assert(false);
    } else {
        let idx = (end - 1) as int;
        let prev = query_from_receipts_up_to(receipts, (end - 1) as nat);
        let prev_base = query_from_receipts_with_base(base, receipts, (end - 1) as nat);
        let last = receipts[idx].result();
        if last is Define {
            message_merge_define_absorbs(prev, last);
            message_merge_define_absorbs(prev_base, last);
        } else {
            match last {
                Message::Update{delta} => {
                    assert(prev is Define);
                    query_from_receipts_with_base_define_absorbs(
                        base,
                        receipts,
                        (end - 1) as nat,
                    );
                    assert(prev_base == prev);
                },
                _ => { assert(false); },
            }
        }
    }
}

proof fn mini_allocator_all_minus_removable_is_allocated(mini_allocator: MiniAllocator)
    requires
        mini_allocator.wf(),
    ensures
        mini_allocator.all_aus().difference(mini_allocator.removable_aus())
            == mini_allocator.allocated_aus(),
{
    assert(mini_allocator.all_aus().difference(mini_allocator.removable_aus())
        =~= mini_allocator.allocated_aus()) by {
        assert forall |au: AU|
            #![trigger mini_allocator.all_aus().contains(au)]
            #![trigger mini_allocator.allocated_aus().contains(au)]
            mini_allocator.all_aus().difference(mini_allocator.removable_aus()).contains(au)
                <==> mini_allocator.allocated_aus().contains(au)
        by {
            if mini_allocator.all_aus().difference(mini_allocator.removable_aus()).contains(au) {
                assert(mini_allocator.allocs.contains_key(au));
                assert(!mini_allocator.removable_aus().contains(au));
                assert(!mini_allocator.can_remove(au));
                if mini_allocator.allocs[au].has_no_allocated_pages() {
                    assert(mini_allocator.can_remove(au));
                    assert(false);
                }
            } else if mini_allocator.allocated_aus().contains(au) {
                assert(mini_allocator.allocs.contains_key(au));
                assert(!mini_allocator.allocs[au].has_no_allocated_pages());
                assert(!mini_allocator.can_remove(au));
                assert(!mini_allocator.removable_aus().contains(au));
            }
        }
    };
}

impl CachingDiskBranch::State {
    pub open spec(checked) fn semantic_inv(self) -> bool
        recommends
            self.inv(),
    {
        &&& self.sealed_stack_i().wf(self.interpreted_branch_summary())
        &&& self.active_branch_i().inv()
        &&& !self.active_branch_i().sealed
        &&& summary_aus(self.interpreted_branch_summary())
            .disjoint(self.active_branch_i().mini_allocator.all_aus())
    }

    pub open spec(checked) fn refinement_inv(self) -> bool {
        &&& self.inv()
        &&& self.semantic_inv()
    }

    pub proof fn semantic_inv_implies_i_inv(self)
        requires
            self.inv(),
            self.semantic_inv(),
        ensures
            self.i().inv(),
    {
        assert(self.i().wf());
    }

    pub proof fn i_inv_implies_semantic_inv(self)
        requires
            self.inv(),
            self.i().inv(),
        ensures
            self.semantic_inv(),
    {
        assert(self.i().wf());
        assert(self.active_branch_i() == self.i().active_branch);
        assert(self.sealed_stack_i() == self.i().sealed_stack);
        assert(self.interpreted_branch_summary() == self.i().branch_summary);
    }

    pub proof fn init_refines(
        post: Self,
        image: CachingDiskBranchImage,
    )
        requires
            CachingDiskBranch::State::initialize(post, image),
            image.stack_wf(),
        ensures
            post.inv(),
            post.semantic_inv(),
            post.refinement_inv(),
            AllocationBranchStack::State::initialize(
                post.i(),
                image.sealed_roots,
                image.sealed_stack_i().sealed_disk,
                image.branch_summary(),
                Set::<AU>::empty(),
                image.seq_end,
            ),
    {
        CachingDiskBranch::State::initialize_inductive(post, image);
        reveal(CachingDiskBranch::State::initialize);
        reveal(AllocationBranchStack::State::initialize);
        assert(post.sealed_roots == image.sealed_roots);
        assert(post.branch_summary == Map::<AU, Summary>::empty());
        assert(post.persisted_root_count == image.sealed_roots.len());
        assert(post.active_branch == CachedBranch::State::empty_active());
        assert(post.seq_end == image.seq_end);
        assert(post.disk.visible() =~= image.persistent) by {
            assert_maps_equal!(post.disk.visible(), image.persistent, addr => {
                if post.disk.cache.contains_key(addr) {
                    assert(false);
                }
            });
        };
        assert(post.i().sealed_stack.sealed_disk.entries =~=
            image.sealed_stack_i().sealed_disk.entries) by {
            let aus = summary_aus(image.branch_summary());
            assert_maps_equal!(
                post.i().sealed_stack.sealed_disk.entries,
                image.sealed_stack_i().sealed_disk.entries,
                addr => {
                    if post.i().sealed_stack.sealed_disk.entries.contains_key(addr) {
                        assert(addresses_in_aus(aus).contains(addr));
                        assert(image.live_persistent().contains_key(addr));
                    }
                    if image.sealed_stack_i().sealed_disk.entries.contains_key(addr) {
                        assert(image.live_persistent().contains_key(addr));
                        assert(image.persistent.contains_key(addr));
                        assert(addresses_in_aus(aus).contains(addr));
                    }
                }
            );
        };
        assert(post.i().sealed_stack == image.sealed_stack_i());
        assert(post.i().branch_summary == image.branch_summary());
        let empty_alloc = MiniAllocator::empty();
        let initialized_empty_alloc = MiniAllocator::empty().add_aus(Set::<AU>::empty());
        assert(initialized_empty_alloc.allocs =~= empty_alloc.allocs) by {
            assert_maps_equal!(
                initialized_empty_alloc.allocs,
                empty_alloc.allocs,
                au => {
                    if initialized_empty_alloc.allocs.contains_key(au) {
                        assert((Set::<AU>::empty() + empty_alloc.allocs.dom()).contains(au));
                        assert(Set::<AU>::empty().contains(au) || empty_alloc.allocs.dom().contains(au));
                        assert(false);
                    }
                }
            );
        };
        assert(initialized_empty_alloc.curr == empty_alloc.curr);
        assert(initialized_empty_alloc == empty_alloc);
        assert(post.i().active_branch == AllocationBranch::new(Set::<AU>::empty()));
        assert(post.i().seq_end == image.seq_end);
        assert(AllocationBranchStack::State::initialize(
            post.i(),
            image.sealed_roots,
            image.sealed_stack_i().sealed_disk,
            image.branch_summary(),
            Set::<AU>::empty(),
            image.seq_end,
        ));
        assert(post.i().wf());
        assert(post.i().inv());
        post.i_inv_implies_semantic_inv();
        assert(post.refinement_inv());
    }

    proof fn sealed_query_roots_up_to_matches_stack(
        self,
        end: nat,
        key: Key,
    )
        requires
            end <= self.sealed_roots.len(),
        ensures
            stack_query_roots_up_to(self, end, key)
                == self.i().sealed_stack.query_up_to(self.i().branch_summary, end, key),
        decreases end,
    {
        if end > 0 {
            self.sealed_query_roots_up_to_matches_stack((end - 1) as nat, key);
        }
    }

    proof fn stack_query_roots_matches_i_query(self, key: Key)
        requires
            self.inv(),
        ensures
            stack_query_roots_up_to(
                self,
                query_roots(self.sealed_roots, self.active_branch).len() as nat,
                key,
            ) == self.i().query(key),
    {
        let roots = query_roots(self.sealed_roots, self.active_branch);
        self.sealed_query_roots_up_to_matches_stack(self.sealed_roots.len() as nat, key);
        if self.active_branch.root is Some {
            assert(roots.len() == self.sealed_roots.len() + 1);
            assert(stack_branch_query_at(self, self.sealed_roots.len() as nat, key)
                == active_branch_query_or_nop(self.i().active_branch, key));
        } else {
            assert(roots.len() == self.sealed_roots.len());
            message_merge_nop_right(self.i().sealed_stack.query(self.i().branch_summary, key));
        }
        assert(stack_query_roots_up_to(self, roots.len() as nat, key) == self.i().query(key));
    }

    proof fn query_receipt_matches_stack_branch(
        self,
        reads: Map<Address, RawPage>,
        receipts: Seq<LoadedPathReceipt>,
        key: Key,
        receipt_idx: nat,
    )
        requires
            self.inv(),
            reads <= self.disk.cache,
            query_receipts_valid(
                query_roots(self.sealed_roots, self.active_branch),
                receipts,
                to_branch_nodes(reads),
                key,
            ),
            receipt_idx < receipts.len(),
        ensures
            ({
                let roots = query_roots(self.sealed_roots, self.active_branch);
                let root_idx = (roots.len() - receipts.len() + receipt_idx) as nat;
                &&& root_idx < roots.len()
                &&& stack_branch_query_at(self, root_idx, key)
                    == receipts[receipt_idx as int].result()
            }),
    {
        let roots = query_roots(self.sealed_roots, self.active_branch);
        let root_idx = (roots.len() - receipts.len() + receipt_idx) as nat;
        let receipt = receipts[receipt_idx as int];
        assert(root_idx < roots.len());
        assert(receipt.key == key);
        assert(receipt.valid_for(roots[root_idx as int], to_branch_nodes(reads)));
        assert(receipt.target().node is Leaf);

        if root_idx < self.sealed_roots.len() {
            let root = self.sealed_roots[root_idx as int];
            assert(roots[root_idx as int] == root);
            assert(self.sealed_stack_i().wf(self.interpreted_branch_summary()));
            assert(self.sealed_stack_i().sealed_roots.to_set().contains(root));
            self.sealed_stack_i().tight_branch_facts(self.interpreted_branch_summary(), root);
            let branch = self.sealed_stack_i().sealed_branch_at(
                self.interpreted_branch_summary(),
                root_idx,
            );
            assert(branch.root == root);
            assert(branch.root == roots[root_idx as int]);
            assert(self.sealed_stack_i().sealed_roots.to_set().contains(branch.root));
            self.sealed_stack_i().tight_branch_facts(self.interpreted_branch_summary(), branch.root);
            assert(branch.valid_sealed_branch());
            assert(branch.inv());
            assert forall |addr: Address|
                #[trigger] branch.disk_view.entries.contains_key(addr)
                implies branch.disk_view.entries[addr] == to_branch_nodes(self.disk.visible())[addr]
            by {
                assert(self.sealed_stack_i().sealed_disk.entries.contains_key(addr));
                assert(sealed_nodes_of(
                    self.disk.visible(),
                    self.interpreted_branch_summary(),
                ).contains_key(addr));
            }
            assert(branch.disk_view.entries <= to_branch_nodes(self.disk.visible())) by {
                assert forall |addr: Address| #[trigger] branch.disk_view.entries.contains_key(addr)
                    implies {
                        &&& to_branch_nodes(self.disk.visible()).contains_key(addr)
                        &&& branch.disk_view.entries[addr] == to_branch_nodes(self.disk.visible())[addr]
                    } by {
                    assert(self.sealed_stack_i().sealed_disk.entries.contains_key(addr));
                    assert(sealed_nodes_of(
                        self.disk.visible(),
                        self.interpreted_branch_summary(),
                    ).contains_key(addr));
                }
            };
            receipt_query_matches_branch_query(self.disk, branch, reads, receipt);
            assert(stack_branch_query_at(self, root_idx, key) == branch.query(key));
        } else {
            assert(self.active_branch.root is Some);
            assert(root_idx == self.sealed_roots.len());
            let branch = self.i().active_branch.branch.unwrap();
            assert(branch.root == roots[root_idx as int]);
            assert(self.i().active_branch.inv());
            assert(branch.inv());
            assert forall |addr: Address|
                #[trigger] branch.disk_view.entries.contains_key(addr)
                implies branch.disk_view.entries[addr] == to_branch_nodes(self.disk.visible())[addr]
            by {
                active_branch_i_visible_candidate(self.active_branch, self.mini_allocator, self.disk);
                assert(semantic_active_branch_candidate(
                    self.active_branch.root.unwrap(),
                    self.visible_branch_nodes(),
                    self.mini_allocator,
                    branch,
                ));
            }
            active_branch_i_visible_candidate(self.active_branch, self.mini_allocator, self.disk);
            assert(semantic_active_branch_candidate(
                self.active_branch.root.unwrap(),
                self.visible_branch_nodes(),
                self.mini_allocator,
                branch,
            ));
            receipt_query_matches_branch_query(self.disk, branch, reads, receipt);
            assert(stack_branch_query_at(self, root_idx, key) == branch.query(key));
        }
    }

    proof fn query_receipts_with_base_matches_roots(
        self,
        reads: Map<Address, RawPage>,
        receipts: Seq<LoadedPathReceipt>,
        key: Key,
        end: nat,
    )
        requires
            self.inv(),
            reads <= self.disk.cache,
            query_receipts_valid(
                query_roots(self.sealed_roots, self.active_branch),
                receipts,
                to_branch_nodes(reads),
                key,
            ),
            end <= receipts.len(),
        ensures
            ({
                let roots = query_roots(self.sealed_roots, self.active_branch);
                let prefix = (roots.len() - receipts.len()) as nat;
                stack_query_roots_up_to(self, (prefix + end) as nat, key)
                    == query_from_receipts_with_base(
                        stack_query_roots_up_to(self, prefix, key),
                        receipts,
                        end,
                    )
            }),
        decreases end,
    {
        let roots = query_roots(self.sealed_roots, self.active_branch);
        let prefix = (roots.len() - receipts.len()) as nat;
        assert(prefix + end <= roots.len());
        if end > 0 {
            self.query_receipts_with_base_matches_roots(reads, receipts, key, (end - 1) as nat);
            self.query_receipt_matches_stack_branch(reads, receipts, key, (end - 1) as nat);
            assert(stack_branch_query_at(self, (prefix + end - 1) as nat, key)
                == receipts[(end - 1) as int].result());
        }
    }

    pub proof fn next_preserves_visible_prefix_image(
        self,
        post: Self,
        lbl: CachingDiskBranch::Label,
        frozen: CachingDiskBranchMetadata,
    )
        requires
            self.inv(),
            self.semantic_inv(),
            self.metadata_loaded,
            frozen.sealed_roots.len() <= self.sealed_roots.len(),
            self.sealed_roots.subrange(0, frozen.sealed_roots.len() as int)
                == frozen.sealed_roots,
            CachingDiskBranch::State::next(self, post, lbl),
        ensures
            post.visible_image_for_metadata(frozen).sealed_stack_i()
                == self.visible_image_for_metadata(frozen).sealed_stack_i(),
            post.visible_image_for_metadata(frozen).branch_summary()
                == self.visible_image_for_metadata(frozen).branch_summary(),
    {
        CachingDiskBranch::State::inv_next(self, post, lbl);
        CachingDiskBranch::State::next_preserves_loaded_root_prefix(
            self,
            post,
            lbl,
            frozen.sealed_roots,
        );
        self.visible_prefix_image_matches_stack(frozen);
        post.visible_prefix_image_matches_stack(frozen);
        self.next_refines(post, lbl);
        assert(post.semantic_inv());
        assert(self.branch_metadata_loaded());
        assert(post.branch_metadata_loaded());
        assert(self.i().branch_summary == self.branch_summary);
        assert(post.i().branch_summary == post.branch_summary);

        reveal(AllocationBranchStack::State::next);
        reveal(AllocationBranchStack::State::next_by);
        let stack_step = choose |step: AllocationBranchStack::Step|
            AllocationBranchStack::State::next_by(self.i(), post.i(), lbl.i(), step);
        match stack_step {
            AllocationBranchStack::Step::internal_noop() => {
                reveal(AllocationBranchStack::State::internal_noop);
                assert(post.i() == self.i());
            },
            AllocationBranchStack::Step::internal_grow(new_root_addr) => {
                reveal(AllocationBranchStack::State::internal_grow);
                assert(post.i().sealed_stack == self.i().sealed_stack);
            },
            AllocationBranchStack::Step::internal_split(new_child_addr, path, split_arg) => {
                reveal(AllocationBranchStack::State::internal_split);
                assert(post.i().sealed_stack == self.i().sealed_stack);
            },
            AllocationBranchStack::Step::internal_fill_au(aus) => {
                reveal(AllocationBranchStack::State::internal_fill_au);
                assert(post.i().sealed_stack == self.i().sealed_stack);
            },
            AllocationBranchStack::Step::append_to_active(path) => {
                reveal(AllocationBranchStack::State::append_to_active);
                assert(post.i().sealed_stack == self.i().sealed_stack);
            },
            AllocationBranchStack::Step::append_to_empty(init_root) => {
                reveal(AllocationBranchStack::State::append_to_empty);
                assert(post.i().sealed_stack == self.i().sealed_stack);
            },
            AllocationBranchStack::Step::query_step() => {
                reveal(AllocationBranchStack::State::query_step);
                assert(post.i() == self.i());
            },
            AllocationBranchStack::Step::internal_seal(aux_ptr, loose_active_disk) => {
                reveal(AllocationBranchStack::State::internal_seal);
                reveal(CachingDiskBranch::State::next);
                reveal(CachingDiskBranch::State::next_by);
                let cdb_step = choose |step: CachingDiskBranch::Step|
                    CachingDiskBranch::State::next_by(self, post, lbl, step);
                match cdb_step {
                    CachingDiskBranch::Step::internal_seal(written_disk, concrete_aux_ptr, reads, writes) => {
                        reveal(CachingDiskBranch::State::internal_seal);
                        let sealed_root = self.active_branch.root.unwrap();
                        let sealed_summary = self.mini_allocator.allocated_aus();
                        let pre_img = self.visible_image_for_metadata(frozen);
                        let post_img = post.visible_image_for_metadata(frozen);
                        let frozen_roots = frozen.sealed_roots.to_set();
                        let pre_roots = self.sealed_roots.to_set();
                        let post_roots = post.sealed_roots.to_set();
                        let pre_removed = to_aus(pre_roots - frozen_roots);
                        let post_removed = to_aus(post_roots - frozen_roots);

                        assert(post.sealed_roots == self.sealed_roots.push(sealed_root));
                        assert(post.branch_summary == self.branch_summary.insert(sealed_root.au, sealed_summary));
                        let read_nodes = to_branch_nodes(reads);
                        let write_nodes = to_branch_nodes(writes);
                        let branch_lbl = CachedBranch::Label::Seal{
                            mini_allocator: self.mini_allocator,
                            aux_ptr: concrete_aux_ptr,
                            read_nodes,
                            write_nodes,
                        };
                        reveal(CachedBranch::State::next);
                        reveal(CachedBranch::State::next_by);
                        let cb_step = choose |step: CachedBranch::Step|
                            CachedBranch::State::next_by(self.active_branch, self.active_branch, branch_lbl, step);
                        match cb_step {
                            CachedBranch::Step::seal_step() => {
                                reveal(CachedBranch::State::seal_step);
                            },
                            _ => { assert(false); },
                        }
                        assert(write_nodes == loaded_seal_write_nodes(
                            sealed_root,
                            read_nodes,
                            concrete_aux_ptr,
                            sealed_summary,
                        ));
                        assert(self.branch_metadata_loaded());
                        assert(self.branch_summary == self.interpreted_branch_summary());
                        assert(post.branch_metadata_loaded());
                        assert(post.branch_summary == post.interpreted_branch_summary());
                        assert(!frozen_roots.contains(sealed_root)) by {
                            if frozen_roots.contains(sealed_root) {
                                let idx = choose |i: int| 0 <= i < frozen.sealed_roots.len()
                                    && frozen.sealed_roots[i] == sealed_root;
                                assert(self.sealed_roots[idx] == sealed_root);
                                assert(self.sealed_stack_i().wf(self.interpreted_branch_summary()));
                                self.sealed_stack_i().root_au_in_summary(
                                    self.interpreted_branch_summary(),
                                    sealed_root,
                                );
                                assert(self.i().branch_summary == self.branch_summary);
                                assert(summary_aus(self.branch_summary).contains(sealed_root.au));
                                assert(self.mini_allocator.all_aus().contains(sealed_root.au)) by {
                                    assert(self.i().active_branch.branch is Some);
                                    assert(self.i().active_branch.inv());
                                    assert(self.i().active_branch.addrs_closed_under_mini_allocator());
                                    assert(self.i().active_branch.branch.unwrap().disk_view.entries.contains_key(sealed_root));
                                    assert(self.i().active_branch.mini_allocator.page_is_allocated(sealed_root));
                                    assert(self.i().active_branch.mini_allocator == self.mini_allocator);
                                }
                                assert(summary_aus(self.interpreted_branch_summary())
                                    .contains(sealed_root.au));
                                assert(false);
                            }
                        }
                        assert(post_img.branch_summary() == pre_img.branch_summary()) by {
                            assert_maps_equal!(post_img.branch_summary(), pre_img.branch_summary(), au => {
                                if post_img.branch_summary().contains_key(au) {
                                    assert(post_img.branch_summary()
                                        == post.interpreted_branch_summary().remove_keys(post_removed));
                                    assert(post.interpreted_branch_summary().contains_key(au));
                                    assert(!post_removed.contains(au));
                                    assert(au != sealed_root.au) by {
                                        if au == sealed_root.au {
                                            assert(post_roots.contains(sealed_root));
                                            assert((post_roots - frozen_roots).contains(sealed_root));
                                            crate::disk::GenericDisk_v::to_aus_domain(post_roots - frozen_roots);
                                            assert(post_removed.contains(au));
                                            assert(false);
                                        }
                                    }
                                    assert(self.interpreted_branch_summary().contains_key(au));
                                    assert(!pre_removed.contains(au)) by {
                                        if pre_removed.contains(au) {
                                            let old_root = choose |root: Address| #![auto]
                                                (pre_roots - frozen_roots).contains(root) && root.au == au;
                                            assert(post_roots.contains(old_root));
                                            assert((post_roots - frozen_roots).contains(old_root));
                                            crate::disk::GenericDisk_v::to_aus_domain(post_roots - frozen_roots);
                                            assert(post_removed.contains(au));
                                            assert(false);
                                        }
                                    }
                                    assert(pre_img.branch_summary().contains_key(au));
                                }
                                if pre_img.branch_summary().contains_key(au) {
                                    assert(pre_img.branch_summary()
                                        == self.interpreted_branch_summary().remove_keys(pre_removed));
                                    assert(self.interpreted_branch_summary().contains_key(au));
                                    assert(!pre_removed.contains(au));
                                    assert(post.interpreted_branch_summary().contains_key(au));
                                    assert(!post_removed.contains(au)) by {
                                        if post_removed.contains(au) {
                                            let old_root = choose |root: Address| #![auto]
                                                (post_roots - frozen_roots).contains(root) && root.au == au;
                                            if old_root == sealed_root {
                                                assert(au == sealed_root.au);
                                                assert(self.interpreted_branch_summary().contains_key(sealed_root.au));
                                                assert(self.branch_summary.contains_key(sealed_root.au));
                                                assert(summary_aus(self.branch_summary).contains(sealed_root.au)) by {
                                                    assert(self.branch_summary.values().contains(self.branch_summary[sealed_root.au]));
                                                    assert(self.branch_summary[sealed_root.au].contains(sealed_root.au));
                                                    lemma_union_set_of_sets_subset(
                                                        self.branch_summary.values(),
                                                        self.branch_summary[sealed_root.au],
                                                    );
                                                }
                                                assert(self.mini_allocator.all_aus().contains(sealed_root.au)) by {
                                                    assert(self.i().active_branch.branch is Some);
                                                    assert(self.i().active_branch.inv());
                                                    assert(self.i().active_branch.addrs_closed_under_mini_allocator());
                                                    assert(self.i().active_branch.branch.unwrap().disk_view.entries.contains_key(sealed_root));
                                                    assert(self.i().active_branch.mini_allocator.page_is_allocated(sealed_root));
                                                    assert(self.i().active_branch.mini_allocator == self.mini_allocator);
                                                }
                                                assert(false);
                                            } else {
                                                assert(pre_roots.contains(old_root));
                                                assert((pre_roots - frozen_roots).contains(old_root));
                                                crate::disk::GenericDisk_v::to_aus_domain(pre_roots - frozen_roots);
                                                assert(pre_removed.contains(au));
                                                assert(false);
                                            }
                                        }
                                    }
                                    assert(post_img.branch_summary().contains_key(au));
                                }
                            });
                        };
                        assert(post_img.sealed_stack_i().sealed_disk.entries
                            == pre_img.sealed_stack_i().sealed_disk.entries) by {
                            let prefix_aus = summary_aus(pre_img.branch_summary());
                            assert(prefix_aus <= summary_aus(self.branch_summary)) by {
                                assert(pre_img.branch_summary()
                                    == self.interpreted_branch_summary().remove_keys(pre_removed));
                                assert(self.interpreted_branch_summary() == self.branch_summary);
                                assert(pre_img.branch_summary().values() <= self.branch_summary.values()) by {
                                    assert forall |summary: Set<AU>|
                                        #[trigger] pre_img.branch_summary().values().contains(summary)
                                        implies self.branch_summary.values().contains(summary) by {
                                        let root_au = choose |root_au: AU| #![auto]
                                            pre_img.branch_summary().contains_key(root_au)
                                            && pre_img.branch_summary()[root_au] == summary;
                                        assert(self.branch_summary.remove_keys(pre_removed).contains_key(root_au));
                                        assert(self.branch_summary.contains_key(root_au));
                                        assert(self.branch_summary[root_au] == summary);
                                    }
                                };
                                assert forall |au: AU| #[trigger] prefix_aus.contains(au)
                                    implies summary_aus(self.branch_summary).contains(au) by {
                                    let summary = lemma_union_set_of_sets_contains(
                                        pre_img.branch_summary().values(),
                                        au,
                                    );
                                    assert(self.branch_summary.values().contains(summary));
                                    lemma_union_set_of_sets_subset(self.branch_summary.values(), summary);
                                }
                            };
                            assert(writes.dom().disjoint(addresses_in_aus(summary_aus(self.branch_summary)))) by {
                                assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                                    implies !addresses_in_aus(summary_aus(self.branch_summary)).contains(addr) by {
                                    assert(to_branch_nodes(writes).contains_key(addr));
                                    let write_nodes = to_branch_nodes(writes);
                                    if concrete_aux_ptr is Some {
                                        assert(write_nodes == loaded_seal_write_nodes(
                                            sealed_root,
                                            read_nodes,
                                            concrete_aux_ptr,
                                            sealed_summary,
                                        ));
                                        assert(addr == sealed_root || addr == concrete_aux_ptr.unwrap());
                                        if addr == sealed_root {
                                            assert(sealed_summary.contains(addr.au)) by {
                                                assert(self.i().active_branch.inv());
                                                assert(self.i().active_branch.addrs_closed_under_mini_allocator());
                                                assert(self.i().active_branch.branch.unwrap().disk_view.entries.contains_key(sealed_root));
                                                assert(self.i().active_branch.mini_allocator.page_is_allocated(sealed_root));
                                                assert(self.i().active_branch.mini_allocator == self.mini_allocator);
                                                assert(self.mini_allocator.allocated_aus().contains(sealed_root.au));
                                            }
                                        } else {
                                            assert(addr == concrete_aux_ptr.unwrap());
                                            assert(sealed_summary.contains(addr.au));
                                        }
                                    } else {
                                        assert(write_nodes == Map::<Address, BranchNode>::empty());
                                        assert(write_nodes.contains_key(addr));
                                        assert(false);
                                    }
                                    assert(sealed_summary <= self.mini_allocator.all_aus()) by {
                                        assert forall |au: AU| #[trigger] sealed_summary.contains(au)
                                            implies self.mini_allocator.all_aus().contains(au) by {
                                            assert(self.mini_allocator.allocs.contains_key(au));
                                        }
                                    };
                                    assert(summary_aus(self.branch_summary).disjoint(sealed_summary)) by {
                                        assert(summary_aus(self.interpreted_branch_summary())
                                            == summary_aus(self.branch_summary));
                                        assert(self.interpreted_branch_summary()
                                            == self.branch_summary);
                                        assert(summary_aus(self.branch_summary)
                                            .disjoint(self.mini_allocator.all_aus()));
                                    }
                                    if addresses_in_aus(summary_aus(self.branch_summary)).contains(addr) {
                                        assert(sealed_summary.contains(addr.au));
                                        assert(summary_aus(self.branch_summary).contains(addr.au));
                                        assert(false);
                                    }
                                }
                            };
                            CachingDisk::State::access_visible_effect(self.disk, post.disk, reads, writes);
                            assert(post_img.live_persistent() == pre_img.live_persistent()) by {
                                assert_maps_equal!(post_img.live_persistent(), pre_img.live_persistent(), addr => {
                                    if post_img.live_persistent().contains_key(addr) {
                                        assert(addresses_in_aus(prefix_aus).contains(addr));
                                        assert(addresses_in_aus(summary_aus(self.branch_summary)).contains(addr));
                                        assert(!writes.contains_key(addr)) by {
                                            if writes.contains_key(addr) {
                                                assert(writes.dom().contains(addr));
                                                assert(false);
                                            }
                                        }
                                        assert(post.disk.visible()[addr] == self.disk.visible()[addr]);
                                        assert(pre_img.live_persistent().contains_key(addr));
                                    }
                                    if pre_img.live_persistent().contains_key(addr) {
                                        assert(addresses_in_aus(prefix_aus).contains(addr));
                                        assert(addresses_in_aus(summary_aus(self.branch_summary)).contains(addr));
                                        assert(!writes.contains_key(addr)) by {
                                            if writes.contains_key(addr) {
                                                assert(writes.dom().contains(addr));
                                                assert(false);
                                            }
                                        }
                                        assert(post.disk.visible()[addr] == self.disk.visible()[addr]);
                                        assert(post_img.live_persistent().contains_key(addr));
                                    }
                                });
                            };
                            assert_maps_equal!(
                                post_img.sealed_stack_i().sealed_disk.entries,
                                pre_img.sealed_stack_i().sealed_disk.entries,
                                addr => {
                                    if post_img.sealed_stack_i().sealed_disk.entries.contains_key(addr) {
                                        assert(post_img.live_persistent().contains_key(addr));
                                        assert(pre_img.live_persistent().contains_key(addr));
                                    }
                                    if pre_img.sealed_stack_i().sealed_disk.entries.contains_key(addr) {
                                        assert(pre_img.live_persistent().contains_key(addr));
                                        assert(post_img.live_persistent().contains_key(addr));
                                    }
                                }
                            );
                        };
                    },
                    _ => {
                        assert(false);
                    },
                }
                assert(post.visible_image_for_metadata(frozen).sealed_stack_i()
                    == self.visible_image_for_metadata(frozen).sealed_stack_i());
            },
            _ => {
                assert(false);
            },
        }
        if post.i().sealed_stack == self.i().sealed_stack {
            assert(post.sealed_stack_i() == self.sealed_stack_i());
            assert(post.sealed_roots == self.sealed_roots);
            assert(post.interpreted_branch_summary() == self.interpreted_branch_summary());
            assert(post.visible_image_for_metadata(frozen).branch_summary()
                == self.visible_image_for_metadata(frozen).branch_summary());
            assert(post.visible_image_for_metadata(frozen).sealed_stack_i().sealed_disk.entries
                == self.visible_image_for_metadata(frozen).sealed_stack_i().sealed_disk.entries);
            assert(post.visible_image_for_metadata(frozen).sealed_stack_i()
                == self.visible_image_for_metadata(frozen).sealed_stack_i());
        }
    }

    pub proof fn next_refines(self, post: Self, lbl: CachingDiskBranch::Label)
        requires
            self.inv(),
            self.semantic_inv(),
            CachingDiskBranch::State::next(self, post, lbl),
        ensures
            post.inv(),
            post.semantic_inv(),
            post.refinement_inv(),
            AllocationBranchStack::State::next(self.i(), post.i(), lbl.i()),
    {
        CachingDiskBranch::State::inv_next(self, post, lbl);
        self.semantic_inv_implies_i_inv();
        reveal(CachingDiskBranch::State::next);
        reveal(CachingDiskBranch::State::next_by);
        reveal(CachedBranch::State::next);
        reveal(CachedBranch::State::next_by);

        let step = choose |step| CachingDiskBranch::State::next_by(self, post, lbl, step);
        match step {
            CachingDiskBranch::Step::disk_internal(new_disk) => {
                assert(CachingDiskBranch::State::disk_internal(self, post, lbl, new_disk)) by {
                    reveal(CachingDiskBranch::State::disk_internal);
                }
                CachingDisk::State::internal_visible_unchanged(self.disk, post.disk);
                assert(post.sealed_roots == self.sealed_roots);
                assert(post.branch_summary == self.branch_summary);
                assert(post.persisted_root_count == self.persisted_root_count);
                assert(post.active_branch == self.active_branch);
                assert(post.mini_allocator == self.mini_allocator);
                assert(post.seq_end == self.seq_end);
                assert(post.sealed_stack_i() == self.sealed_stack_i());
                assert(post.active_branch_i() == self.active_branch_i());
                assert(post.i() == self.i());

                reveal(AllocationBranchStack::State::next);
                reveal(AllocationBranchStack::State::next_by);
                assert(AllocationBranchStack::State::internal_noop(self.i(), post.i(), lbl.i())) by {
                    reveal(AllocationBranchStack::State::internal_noop);
                }
                assert(AllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    lbl.i(),
                    AllocationBranchStack::Step::internal_noop(),
                ));
            },
            CachingDiskBranch::Step::observe_persisted_roots(target_count) => {
                assert(CachingDiskBranch::State::observe_persisted_roots(self, post, lbl, target_count)) by {
                    reveal(CachingDiskBranch::State::observe_persisted_roots);
                }
                assert(post.sealed_roots == self.sealed_roots);
                assert(post.branch_summary == self.branch_summary);
                assert(post.active_branch == self.active_branch);
                assert(post.mini_allocator == self.mini_allocator);
                assert(post.disk == self.disk);
                assert(post.seq_end == self.seq_end);
                assert(post.sealed_stack_i() == self.sealed_stack_i());
                assert(post.active_branch_i() == self.active_branch_i());
                assert(post.i() == self.i());

                reveal(AllocationBranchStack::State::next);
                reveal(AllocationBranchStack::State::next_by);
                assert(AllocationBranchStack::State::internal_noop(self.i(), post.i(), lbl.i())) by {
                    reveal(AllocationBranchStack::State::internal_noop);
                }
                assert(AllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    lbl.i(),
                    AllocationBranchStack::Step::internal_noop(),
                ));
            },
            CachingDiskBranch::Step::load_metadata(reads) => {
                assert(CachingDiskBranch::State::load_metadata(self, post, lbl, reads)) by {
                    reveal(CachingDiskBranch::State::load_metadata);
                }
                assert(post.sealed_roots == self.sealed_roots);
                assert(post.persisted_root_count == self.persisted_root_count);
                assert(post.active_branch == self.active_branch);
                assert(post.mini_allocator == self.mini_allocator);
                assert(post.disk == self.disk);
                assert(post.seq_end == self.seq_end);
                assert(post.interpreted_branch_summary() == self.interpreted_branch_summary());
                assert(post.sealed_stack_i() == self.sealed_stack_i());
                assert(post.active_branch_i() == self.active_branch_i());
                assert(post.i() == self.i());

                reveal(AllocationBranchStack::State::next);
                reveal(AllocationBranchStack::State::next_by);
                assert(AllocationBranchStack::State::internal_noop(self.i(), post.i(), lbl.i())) by {
                    reveal(AllocationBranchStack::State::internal_noop);
                }
                assert(AllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    lbl.i(),
                    AllocationBranchStack::Step::internal_noop(),
                ));
            },
            CachingDiskBranch::Step::internal_noop() => {
                assert(CachingDiskBranch::State::internal_noop(self, post, lbl)) by {
                    reveal(CachingDiskBranch::State::internal_noop);
                }
                assert(post == self);
                reveal(AllocationBranchStack::State::next);
                reveal(AllocationBranchStack::State::next_by);
                assert(AllocationBranchStack::State::internal_noop(self.i(), post.i(), lbl.i())) by {
                    reveal(AllocationBranchStack::State::internal_noop);
                }
                assert(AllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    lbl.i(),
                    AllocationBranchStack::Step::internal_noop(),
                ));
            },
            CachingDiskBranch::Step::freeze_prepared() => {
                assert(CachingDiskBranch::State::freeze_prepared(self, post, lbl)) by {
                    reveal(CachingDiskBranch::State::freeze_prepared);
                }
                assert(post == self);
                reveal(AllocationBranchStack::State::next);
                reveal(AllocationBranchStack::State::next_by);
                assert(AllocationBranchStack::State::internal_noop(self.i(), post.i(), lbl.i())) by {
                    reveal(AllocationBranchStack::State::internal_noop);
                }
                assert(AllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    lbl.i(),
                    AllocationBranchStack::Step::internal_noop(),
                ));
            },
            CachingDiskBranch::Step::freeze_as() => {
                assert(CachingDiskBranch::State::freeze_as(self, post, lbl)) by {
                    reveal(CachingDiskBranch::State::freeze_as);
                }
                reveal(CachingDiskBranch::State::freeze_as);
                assert(post == self);
                match lbl {
                    CachingDiskBranch::Label::FreezeAsLabel{image} => {
                        assert(image == self.freeze_metadata());
                        assert(self.i().active_branch.branch is None);
                    },
                    _ => { assert(false); }
                }
                reveal(AllocationBranchStack::State::next);
                reveal(AllocationBranchStack::State::next_by);
                assert(AllocationBranchStack::State::internal_noop(self.i(), post.i(), lbl.i())) by {
                    reveal(AllocationBranchStack::State::internal_noop);
                }
                assert(AllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    lbl.i(),
                    AllocationBranchStack::Step::internal_noop(),
                ));
            },
            CachingDiskBranch::Step::internal_fill_au(aus, new_disk) => {
                assert(CachingDiskBranch::State::internal_fill_au(self, post, lbl, aus, new_disk)) by {
                    reveal(CachingDiskBranch::State::internal_fill_au);
                }
                match lbl {
                    CachingDiskBranch::Label::InternalAlloc{allocs, deallocs} => {
                        assert(allocs == aus);
                        assert(deallocs == Set::<AU>::empty());
                    },
                    _ => { assert(false); }
                }
                reveal(CachingDiskBranch::State::internal_fill_au);
                mini_allocator_add_aus_preserves_all_aus(self.mini_allocator, aus);

                assert(post.sealed_roots == self.sealed_roots);
                assert(post.branch_summary == self.branch_summary);
                assert(post.persisted_root_count == self.persisted_root_count);
                assert(post.active_branch == self.active_branch);
                assert(post.seq_end == self.seq_end);
                disk_growth_preserves_loaded_metadata(self, post.disk, aus);
                assert(post.sealed_stack_i() == self.sealed_stack_i());

                disk_growth_preserves_active_loaded_nodes(
                    self.disk,
                    post.disk,
                    self.mini_allocator,
                    post.mini_allocator,
                    aus,
                );
                let filled_active = self.active_branch_i().mini_allocator_fill(aus);
                AllocationBranch::build_next_preserves_inv(
                    self.active_branch_i(),
                    filled_active,
                    crate::allocation_layer::AllocationBranch_v::BuildEvent::AllocFill{},
                    aus,
                    Set::empty(),
                );
                if self.active_branch.root is Some {
                    active_branch_i_visible_candidate(self.active_branch, self.mini_allocator, self.disk);
                    let branch = self.active_branch_i().branch.unwrap();
                    assert(branch.disk_view.entries <= self.visible_branch_nodes());
                    assert(filled_active == AllocationBranch{
                        sealed: false,
                        branch: Some(branch),
                        mini_allocator: post.mini_allocator,
                    });
                    assert(branch.disk_view.entries <= post.visible_branch_nodes()) by {
                        disk_growth_visible_preserves_outside_aus(self.disk, post.disk, aus);
                        assert forall |addr: Address| #[trigger] branch.disk_view.entries.contains_key(addr)
                            implies {
                                &&& post.visible_branch_nodes().contains_key(addr)
                                &&& branch.disk_view.entries[addr] == post.visible_branch_nodes()[addr]
                            } by {
                            assert(self.visible_branch_nodes().contains_key(addr));
                            assert(self.i().active_branch.addrs_closed_under_mini_allocator());
                            assert(self.i().active_branch.mini_allocator.page_is_allocated(addr));
                            assert(self.mini_allocator.page_is_allocated(addr));
                            assert(self.mini_allocator.all_aus().contains(addr.au));
                            assert(!aus.contains(addr.au)) by {
                                if aus.contains(addr.au) {
                                    assert(aus.disjoint(self.mini_allocator.all_aus()));
                                    assert(false);
                                }
                            }
                            assert(!addresses_in_aus(aus).contains(addr));
                            assert(post.disk.visible().contains_key(addr));
                            assert(post.disk.visible()[addr] == self.disk.visible()[addr]);
                        }
                    };
                    branch_candidate_from_allocation_branch_inv(
                        post.active_branch.root.unwrap(),
                        post.visible_branch_nodes(),
                        post.mini_allocator,
                        branch,
                    );
                    active_branch_i_of_equals_candidate(
                        post.active_branch,
                        post.mini_allocator,
                        post.disk,
                        branch,
                    );
                }
                assert(post.active_branch_i() == filled_active);

                reveal(AllocationBranchStack::State::next);
                reveal(AllocationBranchStack::State::next_by);
                assert(AllocationBranchStack::State::internal_fill_au(
                    self.i(),
                    post.i(),
                    lbl.i(),
                    aus,
                )) by {
                    reveal(AllocationBranchStack::State::internal_fill_au);
                }
                assert(AllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    lbl.i(),
                    AllocationBranchStack::Step::internal_fill_au(aus),
                ));
            },
            CachingDiskBranch::Step::append(new_disk, new_active_branch, receipt, init_root, reads, writes) => {
                assert(CachingDiskBranch::State::append(
                    self,
                    post,
                    lbl,
                    new_disk,
                    new_active_branch,
                    receipt,
                    init_root,
                    reads,
                    writes,
                )) by {
                    reveal(CachingDiskBranch::State::append);
                }
                reveal(CachingDiskBranch::State::append);
                match lbl {
                    CachingDiskBranch::Label::AppendLabel{keys, msgs} => {
                        if self.active_branch.root is Some {
                            assert(init_root is None);
                            let read_nodes = to_branch_nodes(reads);
                            let write_nodes = to_branch_nodes(writes);
                            let branch_lbl = CachedBranch::Label::Append{
                                mini_allocator: self.mini_allocator,
                                receipt,
                                keys,
                                msgs,
                                read_nodes,
                                write_nodes,
                            };
                            assert(CachedBranch::State::next(self.active_branch, new_active_branch, branch_lbl));
                            reveal(CachedBranch::State::next);
                            reveal(CachedBranch::State::next_by);
                            let cb_step = choose |step: CachedBranch::Step|
                                CachedBranch::State::next_by(self.active_branch, new_active_branch, branch_lbl, step);
                            match cb_step {
                                CachedBranch::Step::append_step() => {
                                    assert(CachedBranch::State::append_step(self.active_branch, new_active_branch, branch_lbl)) by {
                                        reveal(CachedBranch::State::append_step);
                                    }
                                },
                                _ => { assert(false); },
                            }
	                            assert(new_active_branch == self.active_branch.append(
	                                receipt,
	                                keys,
	                                msgs,
	                                read_nodes,
	                                write_nodes,
	                            ));
                            let branch = self.i().active_branch.branch.unwrap();
                            let path = Path{branch, key: keys[0], depth: receipt.depth()};
                            let target = receipt.target().addr;
                            let appended = branch.append(keys, msgs, path);

                            CachingDisk::State::access_visible_effect(self.disk, post.disk, reads, writes);
                            assert(reads <= self.disk.cache);
                            assert(self.i().active_branch.inv());
                            assert(branch.inv());
                            assert(self.i().active_branch.branch == Some(branch));
                            assert(self.active_branch.root == Some(branch.root));
                            assert(receipt.root == branch.root);
                            active_branch_i_visible_candidate(self.active_branch, self.mini_allocator, self.disk);
                            assert(semantic_active_branch_candidate(
                                self.active_branch.root.unwrap(),
                                self.visible_branch_nodes(),
                                self.mini_allocator,
                                branch,
                            ));

	                            assert(branch.disk_view.entries <= self.visible_branch_nodes());
                            receipt_path_valid_for_append(
                                self.disk,
                                branch,
                                branch.the_ranking(),
                                reads,
                                receipt,
                                keys,
                                msgs,
                            );
                            assert(path.valid());
                            assert(path.target().root == target);
                            assert(path.target().root() == receipt.target().node);
                            assert(path.target().disk_view == branch.disk_view);
                            assert(path.path_equiv(keys.last()));
                            assert(self.i().active_branch.can_append(keys, msgs, path));
                            assert(path.target().has_root());
                            assert(path.target().disk_view.entries.contains_key(path.target().root));
                            assert(branch.disk_view.entries.contains_key(target));
                            linked_append_keys_are_path_equiv(branch, branch.the_ranking(), keys, path);
                            assert forall |key: Key| #[trigger] keys.contains(key)
                                implies is_nop_message(self.i().active_branch.branch_query(key))
                            by {
                                branch_query_nop_for_append_key(branch, keys, path, key);
                                assert(branch.query(key) == Message::Update{delta: nop_delta()});
                                assert(self.i().active_branch.branch_query(key) == branch.query(key));
                            }

                            LinkedBranchRefinement::append_refines(branch, keys, msgs, path);
                            assert(self.i().active_branch.branch_append(keys, msgs, path).branch == Some(appended));
                            assert(self.i().active_branch.branch_append(keys, msgs, path).mini_allocator
                                == self.mini_allocator);

                            assert(write_nodes == loaded_append_write_nodes(receipt, keys, msgs));
                            assert(write_nodes.contains_key(target));
                            assert(writes.contains_key(target));
                            assert(receipt.needed_addrs().contains(target)) by {
                                let i = receipt.lines.len() - 1;
                                assert(0 <= i < receipt.lines.len());
                                assert(receipt.lines[i].addr == target);
                            }
	                            assert(self.visible_branch_nodes().contains_key(target));
                            query_read_node_matches_visible(self.disk, reads, target);
	                            assert(read_nodes[target] == receipt.target().node);
	                            assert(read_nodes[target] == branch.disk_view.entries[target]);

                            assert forall |addr: Address|
                                #[trigger] writes.contains_key(addr)
                                implies addr == target
                            by {
                                assert(write_nodes.contains_key(addr));
                            }
                            assert forall |addr: Address|
                                #[trigger] writes.contains_key(addr)
                                implies !summary_aus(self.branch_summary).contains(addr.au)
                            by {
                                assert(addr == target);
                                assert(branch.disk_view.entries.contains_key(target));
                                assert(self.i().active_branch.addrs_closed_under_mini_allocator());
                                assert(self.i().active_branch.mini_allocator.page_is_allocated(target));
                                assert(self.i().wf());
                            }

                            assert(sealed_nodes_of(post.disk.visible(), post.branch_summary) =~=
                                sealed_nodes_of(self.disk.visible(), self.branch_summary)) by {
                                let sealed_addrs = addresses_in_aus(summary_aus(self.branch_summary));
                                assert_maps_equal!(
                                    sealed_nodes_of(post.disk.visible(), post.branch_summary),
                                    sealed_nodes_of(self.disk.visible(), self.branch_summary),
                                    addr => {
                                        if sealed_nodes_of(post.disk.visible(), post.branch_summary).contains_key(addr) {
                                            assert(sealed_addrs.contains(addr));
                                            if writes.contains_key(addr) {
                                                assert(!summary_aus(self.branch_summary).contains(addr.au));
                                                assert(false);
                                            }
                                        }
                                    }
                                );
                            };
                            assert(writes.dom().disjoint(addresses_in_aus(summary_aus(self.branch_summary)))) by {
                                assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                                    implies !addresses_in_aus(summary_aus(self.branch_summary)).contains(addr)
                                by {
                                    assert(writes.contains_key(addr));
                                    if addresses_in_aus(summary_aus(self.branch_summary)).contains(addr) {
                                        assert(summary_aus(self.branch_summary).contains(addr.au));
                                        assert(false);
                                    }
                                }
                            };
                            access_preserves_sealed_stack_i(self, post, reads, writes);
                            assert(post.sealed_stack_i() == self.sealed_stack_i());

                            let appended_active = self.i().active_branch.branch_append(keys, msgs, path);
                            AllocationBranch::build_next_preserves_inv(
                                self.i().active_branch,
                                appended_active,
                                crate::allocation_layer::AllocationBranch_v::BuildEvent::Append{keys, msgs, path},
                                Set::empty(),
                                Set::empty(),
                            );
                            assert(appended_active == AllocationBranch{
                                sealed: false,
                                branch: Some(appended),
                                mini_allocator: post.mini_allocator,
                            });
                            assert(appended.disk_view.entries <= post.visible_branch_nodes()) by {
                                assert(appended.disk_view.entries.dom() == branch.disk_view.entries.dom());
                                assert forall |addr: Address| #[trigger] appended.disk_view.entries.contains_key(addr)
                                    implies {
                                        &&& post.visible_branch_nodes().contains_key(addr)
                                        &&& appended.disk_view.entries[addr] == post.visible_branch_nodes()[addr]
                                    } by {
                                    assert(branch.disk_view.entries.contains_key(addr));
                                    if addr == target {
                                        assert(write_nodes.contains_key(addr));
                                        assert(writes.contains_key(addr));
                                        assert(appended.disk_view.entries[addr] == write_nodes[addr]);
                                        assert(post.disk.visible().contains_key(addr));
                                        assert(post.disk.visible()[addr] == writes[addr]);
                                    } else {
                                        assert(!writes.contains_key(addr)) by {
                                            if writes.contains_key(addr) {
                                                assert(addr == target);
                                            }
                                        }
                                        assert(appended.disk_view.entries[addr] == branch.disk_view.entries[addr]);
                                        assert(branch.disk_view.entries <= self.visible_branch_nodes());
                                        assert(self.visible_branch_nodes().contains_key(addr));
                                        assert(post.disk.visible()[addr] == self.disk.visible()[addr]);
                                    }
                                }
                            };
                            branch_candidate_from_allocation_branch_inv(
                                post.active_branch.root.unwrap(),
                                post.visible_branch_nodes(),
                                post.mini_allocator,
                                appended,
                            );
                            active_branch_i_of_equals_candidate(
                                post.active_branch,
                                post.mini_allocator,
                                post.disk,
                                appended,
                            );
	                            assert(post.i().active_branch == appended_active);
                            assert(post.i().active_branch == self.i().active_branch.branch_append(keys, msgs, path));
                            assert(post.i().seq_end == self.i().seq_end + keys.len());

                            reveal(AllocationBranchStack::State::next);
                            reveal(AllocationBranchStack::State::next_by);
                            assert(AllocationBranchStack::State::append_to_active(
                                self.i(),
                                post.i(),
                                lbl.i(),
                                path,
                            )) by {
                                reveal(AllocationBranchStack::State::append_to_active);
                            }
                            assert(AllocationBranchStack::State::next_by(
                                self.i(),
                                post.i(),
                                lbl.i(),
                                AllocationBranchStack::Step::append_to_active(path),
                            ));
                        } else {
                            assert(init_root is Some);
                            let init_addr = init_root.unwrap();
                            let write_nodes = to_branch_nodes(writes);
                            let branch_lbl = CachedBranch::Label::Initialize{
                                mini_allocator: self.mini_allocator,
                                init_root: init_addr,
                                keys,
                                msgs,
                                write_nodes,
                            };
                            assert(CachedBranch::State::next(self.active_branch, new_active_branch, branch_lbl));
                            reveal(CachedBranch::State::next);
                            reveal(CachedBranch::State::next_by);
                            let cb_step = choose |step: CachedBranch::Step|
                                CachedBranch::State::next_by(self.active_branch, new_active_branch, branch_lbl, step);
                            match cb_step {
                                CachedBranch::Step::initialize_branch() => {
                                    assert(CachedBranch::State::initialize_branch(self.active_branch, new_active_branch, branch_lbl)) by {
                                        reveal(CachedBranch::State::initialize_branch);
                                    }
                                },
                                _ => { assert(false); },
                            }
                            assert(new_active_branch == self.active_branch.initialize(init_addr, keys, msgs, write_nodes));
                            CachingDisk::State::access_visible_effect(
                                self.disk,
                                post.disk,
                                reads,
                                writes,
                            );
                            mini_allocator_allocate_preserves_all_aus(self.mini_allocator, init_addr);

                            assert(write_nodes == loaded_initialize_write_nodes(init_addr, keys, msgs));
                            assert(writes.dom() =~= set![init_addr]) by {
                                assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                                    implies set![init_addr].contains(addr) by {
                                    assert(write_nodes.contains_key(addr));
                                }
                                assert forall |addr: Address| #[trigger] set![init_addr].contains(addr)
                                    implies writes.dom().contains(addr) by {
                                    assert(write_nodes.contains_key(addr));
                                }
                            };
                            let init_branch = LinkedBranch{
                                root: init_addr,
                                disk_view: DiskView{entries: write_nodes},
                            };
                            let initialized_active =
                                self.active_branch_i().branch_initialize(init_addr, keys, msgs);
                            assert(initialized_active == AllocationBranch{
                                sealed: false,
                                branch: Some(init_branch),
                                mini_allocator: post.mini_allocator,
                            });
                            AllocationBranch::build_next_preserves_inv(
                                self.active_branch_i(),
                                initialized_active,
                                crate::allocation_layer::AllocationBranch_v::BuildEvent::Initialize{
                                    addr: init_addr,
                                    keys,
                                    msgs,
                                },
                                Set::empty(),
                                Set::empty(),
                            );
                            assert(init_branch.disk_view.entries <= post.visible_branch_nodes()) by {
                                assert forall |addr: Address| #[trigger] init_branch.disk_view.entries.contains_key(addr)
                                    implies {
                                        &&& post.visible_branch_nodes().contains_key(addr)
                                        &&& init_branch.disk_view.entries[addr] == post.visible_branch_nodes()[addr]
                                    } by {
                                    assert(write_nodes.contains_key(addr));
                                    assert(addr == init_addr);
                                    assert(writes.contains_key(addr));
                                    assert(post.disk.visible().contains_key(addr));
                                    assert(post.disk.visible()[addr] == writes[addr]);
                                }
                            };
                            branch_candidate_from_allocation_branch_inv(
                                init_addr,
                                post.visible_branch_nodes(),
                                post.mini_allocator,
                                init_branch,
                            );
                            active_branch_i_of_equals_candidate(
                                post.active_branch,
                                post.mini_allocator,
                                post.disk,
                                init_branch,
                            );
	                            assert(sealed_nodes_of(post.disk.visible(), post.branch_summary) =~=
                                sealed_nodes_of(self.disk.visible(), self.branch_summary)) by {
                                let sealed_addrs = addresses_in_aus(summary_aus(self.branch_summary));
                                assert_maps_equal!(
                                    sealed_nodes_of(post.disk.visible(), post.branch_summary),
                                    sealed_nodes_of(self.disk.visible(), self.branch_summary),
                                    addr => {
                                        if sealed_nodes_of(post.disk.visible(), post.branch_summary).contains_key(addr) {
                                            assert(sealed_addrs.contains(addr));
                                            if writes.contains_key(addr) {
                                                assert(addr == init_addr);
                                                assert(self.mini_allocator.all_aus().contains(addr.au));
                                                assert(summary_aus(self.branch_summary).contains(addr.au));
                                                assert(false);
                                            }
                                        }
                                    }
                                );
                            };
                            assert(writes.dom().disjoint(addresses_in_aus(summary_aus(self.branch_summary)))) by {
                                assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                                    implies !addresses_in_aus(summary_aus(self.branch_summary)).contains(addr)
                                by {
                                    assert(writes.contains_key(addr));
                                    assert(addr == init_addr);
                                    if addresses_in_aus(summary_aus(self.branch_summary)).contains(addr) {
                                        assert(summary_aus(self.branch_summary).contains(addr.au));
                                        assert(self.mini_allocator.all_aus().contains(addr.au));
                                        assert(false);
                                    }
                                }
                            };
                            access_preserves_sealed_stack_i(
                                self,
                                post,
                                reads,
                                writes,
                            );
                            assert(post.sealed_stack_i() == self.sealed_stack_i());
                            assert(post.active_branch_i()
                                == self.active_branch_i().branch_initialize(init_addr, keys, msgs));
                            assert(self.active_branch_i() == self.i().active_branch);
                            assert(post.i().active_branch == self.i().active_branch.branch_initialize(init_addr, keys, msgs));

                            reveal(AllocationBranchStack::State::next);
                            reveal(AllocationBranchStack::State::next_by);
                            assert(AllocationBranchStack::State::append_to_empty(
                                self.i(),
                                post.i(),
                                lbl.i(),
                                init_addr,
                            )) by {
                                reveal(AllocationBranchStack::State::append_to_empty);
                            }
                            assert(AllocationBranchStack::State::next_by(
                                self.i(),
                                post.i(),
                                lbl.i(),
                                AllocationBranchStack::Step::append_to_empty(init_addr),
                            ));
                        }
                    },
                    _ => { assert(false); }
                }
            },
            CachingDiskBranch::Step::internal_grow(new_disk, new_root_addr, reads, writes) => {
                assert(CachingDiskBranch::State::internal_grow(self, post, lbl, new_disk, new_root_addr, reads, writes)) by {
                    reveal(CachingDiskBranch::State::internal_grow);
                }
                reveal(CachingDiskBranch::State::internal_grow);
                let write_nodes = to_branch_nodes(writes);
                let old_root = self.active_branch.root.unwrap();
                let branch = self.i().active_branch.branch.unwrap();
                let grown = branch.grow(new_root_addr);

                CachingDisk::State::access_visible_effect(
                    self.disk,
                    post.disk,
                    reads,
                    writes,
                );
                mini_allocator_allocate_preserves_all_aus(self.mini_allocator, new_root_addr);

                assert(write_nodes == loaded_grow_write_nodes(old_root, new_root_addr));
                assert(writes.dom() =~= set![new_root_addr]) by {
                    assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                        implies set![new_root_addr].contains(addr) by {
                        assert(write_nodes.contains_key(addr));
                    }
                    assert forall |addr: Address| #[trigger] set![new_root_addr].contains(addr)
                        implies writes.dom().contains(addr) by {
                        assert(write_nodes.contains_key(addr));
                    }
                };

                assert(!branch.disk_view.entries.contains_key(new_root_addr)) by {
                    if branch.disk_view.entries.contains_key(new_root_addr) {
                        assert(self.i().active_branch.addrs_closed_under_mini_allocator());
                        assert(self.i().active_branch.mini_allocator.page_is_allocated(new_root_addr));
                        assert(false);
                    }
                }
                assert(branch.disk_view.is_fresh(set![new_root_addr])) by {
                    assert forall |addr: Address| #[trigger] set![new_root_addr].contains(addr)
                        implies !branch.disk_view.entries.contains_key(addr) by {
                        assert(addr == new_root_addr);
                    }
                };
                assert(self.i().active_branch.can_grow(new_root_addr));
                active_branch_i_visible_candidate(self.active_branch, self.mini_allocator, self.disk);
                assert(semantic_active_branch_candidate(
                    self.active_branch.root.unwrap(),
                    self.visible_branch_nodes(),
                    self.mini_allocator,
                    branch,
                ));

	                assert(sealed_nodes_of(post.disk.visible(), post.branch_summary) =~=
                    sealed_nodes_of(self.disk.visible(), self.branch_summary)) by {
                    let sealed_addrs = addresses_in_aus(summary_aus(self.branch_summary));
                    assert_maps_equal!(
                        sealed_nodes_of(post.disk.visible(), post.branch_summary),
                        sealed_nodes_of(self.disk.visible(), self.branch_summary),
                        addr => {
                            if sealed_nodes_of(post.disk.visible(), post.branch_summary).contains_key(addr) {
                                assert(sealed_addrs.contains(addr));
                                if writes.contains_key(addr) {
                                    assert(addr == new_root_addr);
                                    assert(self.mini_allocator.all_aus().contains(addr.au));
                                    assert(summary_aus(self.branch_summary).contains(addr.au));
                                    assert(false);
                                }
                            }
                        }
                    );
                };
                assert(writes.dom().disjoint(addresses_in_aus(summary_aus(self.branch_summary)))) by {
                    assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                        implies !addresses_in_aus(summary_aus(self.branch_summary)).contains(addr)
                    by {
                        assert(writes.contains_key(addr));
                        assert(addr == new_root_addr);
                        if addresses_in_aus(summary_aus(self.branch_summary)).contains(addr) {
                            assert(summary_aus(self.branch_summary).contains(addr.au));
                            assert(self.mini_allocator.all_aus().contains(addr.au));
                            assert(false);
                        }
                    }
                };
                access_preserves_sealed_stack_i(
                    self,
                    post,
                    reads,
                    writes,
                );
                assert(post.sealed_stack_i() == self.sealed_stack_i());
                let grown_active = self.i().active_branch.branch_grow(new_root_addr);
                AllocationBranch::build_next_preserves_inv(
                    self.i().active_branch,
                    grown_active,
                    crate::allocation_layer::AllocationBranch_v::BuildEvent::Grow{addr: new_root_addr},
                    Set::empty(),
                    Set::empty(),
                );
                assert(grown_active == AllocationBranch{
                    sealed: false,
                    branch: Some(grown),
                    mini_allocator: post.mini_allocator,
                });
                assert(grown.disk_view.entries <= post.visible_branch_nodes()) by {
                    assert(grown.disk_view.entries == branch.disk_view.entries.insert(
                        new_root_addr,
                        write_nodes[new_root_addr],
                    ));
                    assert forall |addr: Address| #[trigger] grown.disk_view.entries.contains_key(addr)
                        implies {
                            &&& post.visible_branch_nodes().contains_key(addr)
                            &&& grown.disk_view.entries[addr] == post.visible_branch_nodes()[addr]
                        } by {
                        if addr == new_root_addr {
                            assert(writes.contains_key(addr));
                            assert(post.disk.visible().contains_key(addr));
                            assert(post.disk.visible()[addr] == writes[addr]);
                            assert(write_nodes[addr] == to_branch_nodes(post.disk.visible())[addr]);
                        } else {
                            assert(branch.disk_view.entries.contains_key(addr));
                            assert(branch.disk_view.entries <= self.visible_branch_nodes());
                            assert(self.visible_branch_nodes().contains_key(addr));
                            assert(!writes.contains_key(addr)) by {
                                if writes.contains_key(addr) {
                                    assert(writes.dom().contains(addr));
                                    assert(addr == new_root_addr);
                                }
                            }
                            assert(post.disk.visible()[addr] == self.disk.visible()[addr]);
                        }
                    }
                };
                branch_candidate_from_allocation_branch_inv(
                    new_root_addr,
                    post.visible_branch_nodes(),
                    post.mini_allocator,
                    grown,
                );
                active_branch_i_of_equals_candidate(
                    post.active_branch,
                    post.mini_allocator,
                    post.disk,
                    grown,
                );
                assert(post.i().active_branch == grown_active);
                assert(post.i().active_branch == self.i().active_branch.branch_grow(new_root_addr));

                reveal(AllocationBranchStack::State::next);
                reveal(AllocationBranchStack::State::next_by);
                assert(AllocationBranchStack::State::internal_grow(
                    self.i(),
                    post.i(),
                    lbl.i(),
                    new_root_addr,
                )) by {
                    reveal(AllocationBranchStack::State::internal_grow);
                }
                assert(AllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    lbl.i(),
                    AllocationBranchStack::Step::internal_grow(new_root_addr),
                ));
            },
            CachingDiskBranch::Step::query(receipts, reads) => {
                assert(CachingDiskBranch::State::query(self, post, lbl, receipts, reads)) by {
                    reveal(CachingDiskBranch::State::query);
                }
                reveal(CachingDiskBranch::State::query);
                match lbl {
                    CachingDiskBranch::Label::QueryLabel{key, msg} => {
                        CachingDisk::State::access_effect(
                            self.disk,
                            self.disk,
                            reads,
                            Map::<Address, RawPage>::empty(),
                        );
                        let roots = query_roots(self.sealed_roots, self.active_branch);
                        let prefix = (roots.len() - receipts.len()) as nat;
                        self.query_receipts_with_base_matches_roots(
                            reads,
                            receipts,
                            key,
                            receipts.len() as nat,
                        );
                        if receipts.len() == roots.len() {
                            assert(prefix == 0);
                            query_from_receipts_with_nop_base(receipts, receipts.len() as nat);
                        } else {
                            assert(query_from_receipts_up_to(receipts, receipts.len() as nat) is Define);
                            query_from_receipts_with_base_define_absorbs(
                                stack_query_roots_up_to(self, prefix, key),
                                receipts,
                                receipts.len() as nat,
                            );
                        }
                        assert(stack_query_roots_up_to(self, roots.len() as nat, key) == msg);
                        self.stack_query_roots_matches_i_query(key);
                        assert(self.i().query(key) == msg);
                        assert(post == self);

                        reveal(AllocationBranchStack::State::next);
                        reveal(AllocationBranchStack::State::next_by);
                        assert(AllocationBranchStack::State::query_step(self.i(), post.i(), lbl.i())) by {
                            reveal(AllocationBranchStack::State::query_step);
                        }
                        assert(AllocationBranchStack::State::next_by(
                            self.i(),
                            post.i(),
                            lbl.i(),
                            AllocationBranchStack::Step::query_step(),
                        ));
                    },
                    _ => { assert(false); }
                }
            },
            CachingDiskBranch::Step::internal_split(new_disk, new_child_addr, receipt, split_arg, reads, writes) => {
                assert(CachingDiskBranch::State::internal_split(
                    self,
                    post,
                    lbl,
                    new_disk,
                    new_child_addr,
                    receipt,
                    split_arg,
                    reads,
                    writes,
                )) by {
                    reveal(CachingDiskBranch::State::internal_split);
                }
                reveal(CachingDiskBranch::State::internal_split);
                let read_nodes = to_branch_nodes(reads);
                let write_nodes = to_branch_nodes(writes);
                let branch = self.i().active_branch.branch.unwrap();
                let path = Path{branch, key: split_arg.get_pivot(), depth: receipt.depth()};
                let split_branch = branch.split(new_child_addr, path, split_arg);
                let parent_addr = receipt.target().addr;
                let child_addr = receipt.child_addr();

                CachingDisk::State::access_visible_effect(self.disk, post.disk, reads, writes);
                assert(reads <= self.disk.cache);
                mini_allocator_allocate_preserves_all_aus(self.mini_allocator, new_child_addr);
                assert(self.i().active_branch.inv());
                assert(branch.inv());
                assert(self.i().active_branch.branch == Some(branch));
                assert(self.active_branch.root == Some(branch.root));
                assert(receipt.root == branch.root);
                assert(receipt.key == split_arg.get_pivot());
                active_branch_i_visible_candidate(self.active_branch, self.mini_allocator, self.disk);
                assert(semantic_active_branch_candidate(
                    self.active_branch.root.unwrap(),
                    self.visible_branch_nodes(),
                    self.mini_allocator,
                    branch,
                ));

	                assert(branch.disk_view.entries <= self.visible_branch_nodes());

                assert(!branch.disk_view.entries.contains_key(new_child_addr)) by {
                    if branch.disk_view.entries.contains_key(new_child_addr) {
                        assert(self.i().active_branch.addrs_closed_under_mini_allocator());
                        assert(self.i().active_branch.mini_allocator.page_is_allocated(new_child_addr));
                        assert(false);
                    }
                }
                assert(branch.disk_view.is_fresh(set!{new_child_addr})) by {
                    assert forall |addr: Address| #[trigger] set![new_child_addr].contains(addr)
                        implies !branch.disk_view.entries.contains_key(addr) by {
                        assert(addr == new_child_addr);
                    }
                };

	                assert forall |addr: Address|
                    #[trigger] branch.disk_view.entries.contains_key(addr)
                        && reads.contains_key(addr)
                    implies branch.disk_view.entries[addr] == read_nodes[addr]
                by {
                    assert(branch.disk_view.entries <= self.visible_branch_nodes());
                    assert(self.visible_branch_nodes().contains_key(addr));
                    query_read_node_matches_visible(self.disk, reads, addr);
                }
                receipt_path_valid_for_split(
                    self.disk,
                    branch,
                    branch.the_ranking(),
                    reads,
                    receipt,
                    split_arg,
                    new_child_addr,
                );
                assert(path.valid());
                assert(path.target().root == parent_addr);
                assert(path.target().root() == receipt.target().node);
                assert(path.target().disk_view == branch.disk_view);
                assert(path.target().can_split_child_of_index(split_arg, new_child_addr));
                assert(self.i().active_branch.can_split(new_child_addr, path, split_arg));

                LinkedBranchRefinement::split_refines(branch, new_child_addr, path, split_arg);
                assert(split_branch == branch.split(new_child_addr, path, split_arg));
                assert(split_branch.disk_view.entries.dom() =~= branch.disk_view.entries.dom().insert(new_child_addr));

                assert(write_nodes == loaded_split_write_nodes(
                    receipt,
                    read_nodes,
                    split_arg,
                    new_child_addr,
                ));
                assert(write_nodes.contains_key(parent_addr));
                assert(write_nodes.contains_key(child_addr));
                assert(write_nodes.contains_key(new_child_addr));
                assert(writes.contains_key(parent_addr));
                assert(writes.contains_key(child_addr));
                assert(writes.contains_key(new_child_addr));
                assert(split_branch.disk_view.entries[parent_addr] == write_nodes[parent_addr]);
                assert(split_branch.disk_view.entries[child_addr] == write_nodes[child_addr]);
                assert(split_branch.disk_view.entries[new_child_addr] == write_nodes[new_child_addr]);

                assert forall |addr: Address|
                    #[trigger] writes.contains_key(addr)
                    implies addr == parent_addr || addr == child_addr || addr == new_child_addr
                by {
                    assert(write_nodes.contains_key(addr));
                }
                assert forall |addr: Address|
                    #[trigger] writes.contains_key(addr)
                    implies !summary_aus(self.branch_summary).contains(addr.au)
                by {
                    if addr == parent_addr || addr == child_addr {
                        assert(branch.disk_view.entries.contains_key(addr));
                        assert(self.i().active_branch.addrs_closed_under_mini_allocator());
                        assert(self.i().active_branch.mini_allocator.page_is_allocated(addr));
                        assert(self.i().wf());
                    } else {
                        assert(addr == new_child_addr);
                        assert(self.mini_allocator.can_allocate(new_child_addr));
                        assert(self.mini_allocator.all_aus().contains(new_child_addr.au));
                        assert(self.i().wf());
                    }
                }

                assert(sealed_nodes_of(post.disk.visible(), post.branch_summary) =~=
                    sealed_nodes_of(self.disk.visible(), self.branch_summary)) by {
                    let sealed_addrs = addresses_in_aus(summary_aus(self.branch_summary));
                    assert_maps_equal!(
                        sealed_nodes_of(post.disk.visible(), post.branch_summary),
                        sealed_nodes_of(self.disk.visible(), self.branch_summary),
                        addr => {
                            if sealed_nodes_of(post.disk.visible(), post.branch_summary).contains_key(addr) {
                                assert(sealed_addrs.contains(addr));
                                if writes.contains_key(addr) {
                                    assert(!summary_aus(self.branch_summary).contains(addr.au));
                                    assert(false);
                                }
                            }
                        }
                    );
                };
                assert(writes.dom().disjoint(addresses_in_aus(summary_aus(self.branch_summary)))) by {
                    assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                        implies !addresses_in_aus(summary_aus(self.branch_summary)).contains(addr)
                    by {
                        assert(writes.contains_key(addr));
                        if addresses_in_aus(summary_aus(self.branch_summary)).contains(addr) {
                            assert(summary_aus(self.branch_summary).contains(addr.au));
                            assert(false);
                        }
                    }
                };
                access_preserves_sealed_stack_i(self, post, reads, writes);
                assert(post.sealed_stack_i() == self.sealed_stack_i());

                let split_active = self.i().active_branch.branch_split(new_child_addr, path, split_arg);
                AllocationBranch::build_next_preserves_inv(
                    self.i().active_branch,
                    split_active,
                    crate::allocation_layer::AllocationBranch_v::BuildEvent::Split{
                        addr: new_child_addr,
                        path,
                        split_arg,
                    },
                    Set::empty(),
                    Set::empty(),
                );
                assert(split_active == AllocationBranch{
                    sealed: false,
                    branch: Some(split_branch),
                    mini_allocator: post.mini_allocator,
                });
                assert(split_branch.disk_view.entries <= post.visible_branch_nodes()) by {
                    assert forall |addr: Address| #[trigger] split_branch.disk_view.entries.contains_key(addr)
                        implies {
                            &&& post.visible_branch_nodes().contains_key(addr)
                            &&& split_branch.disk_view.entries[addr] == post.visible_branch_nodes()[addr]
                        } by {
                        if addr == parent_addr || addr == child_addr || addr == new_child_addr {
                            assert(write_nodes.contains_key(addr));
                            assert(writes.contains_key(addr));
                            assert(split_branch.disk_view.entries[addr] == write_nodes[addr]);
                            assert(post.disk.visible().contains_key(addr));
                            assert(post.disk.visible()[addr] == writes[addr]);
                        } else {
                            assert(!writes.contains_key(addr)) by {
                                if writes.contains_key(addr) {
                                    assert(addr == parent_addr || addr == child_addr || addr == new_child_addr);
                                }
                            }
                            assert(branch.disk_view.entries.contains_key(addr)) by {
                                assert(split_branch.disk_view.entries.dom()
                                    =~= branch.disk_view.entries.dom().insert(new_child_addr));
                                if !branch.disk_view.entries.contains_key(addr) {
                                    assert(addr == new_child_addr);
                                }
                            }
                            assert(split_branch.disk_view.same_except(
                                branch.disk_view,
                                set![parent_addr, child_addr, new_child_addr],
                            ));
                            assert(split_branch.disk_view.entries[addr] == branch.disk_view.entries[addr]);
                            assert(branch.disk_view.entries <= self.visible_branch_nodes());
                            assert(self.visible_branch_nodes().contains_key(addr));
                            assert(post.disk.visible()[addr] == self.disk.visible()[addr]);
                        }
                    }
                };
                branch_candidate_from_allocation_branch_inv(
                    post.active_branch.root.unwrap(),
                    post.visible_branch_nodes(),
                    post.mini_allocator,
                    split_branch,
                );
                active_branch_i_of_equals_candidate(
                    post.active_branch,
                    post.mini_allocator,
                    post.disk,
                    split_branch,
                );
	                assert(post.i().active_branch == split_active);
                assert(post.i().active_branch == self.i().active_branch.branch_split(new_child_addr, path, split_arg));

                reveal(AllocationBranchStack::State::next);
                reveal(AllocationBranchStack::State::next_by);
                assert(AllocationBranchStack::State::internal_split(
                    self.i(),
                    post.i(),
                    lbl.i(),
                    new_child_addr,
                    path,
                    split_arg,
                )) by {
                    reveal(AllocationBranchStack::State::internal_split);
                }
                assert(AllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    lbl.i(),
                    AllocationBranchStack::Step::internal_split(new_child_addr, path, split_arg),
                ));
            },
            CachingDiskBranch::Step::internal_seal(written_disk, aux_ptr, reads, writes) => {
                assert(CachingDiskBranch::State::internal_seal(
                    self,
                    post,
                    lbl,
                    written_disk,
                    aux_ptr,
                    reads,
                    writes,
                )) by {
                    reveal(CachingDiskBranch::State::internal_seal);
                }
                reveal(CachingDiskBranch::State::internal_seal);

                let read_nodes = to_branch_nodes(reads);
                let write_nodes = to_branch_nodes(writes);
                let root = self.active_branch.root.unwrap();
                let branch = self.i().active_branch.branch.unwrap();
                let dealloc_aus = self.i().active_branch.mini_allocator.removable_aus();
                let sealed_active = self.i().active_branch.branch_seal(aux_ptr, dealloc_aus);
                let sealed_branch = sealed_active.branch.unwrap();
                let sealed_summary = self.mini_allocator.allocated_aus();

                CachingDisk::State::access_visible_effect(
                    self.disk,
                    post.disk,
                    reads,
                    writes,
                );
                assert(reads <= self.disk.cache);

                assert(self.i().active_branch.mini_allocator == self.mini_allocator);
                assert(dealloc_aus == self.mini_allocator.removable_aus());
                assert(self.i().active_branch.branch == Some(branch));
                assert(branch.root == root);
                assert(reads.contains_key(root));
                active_branch_i_visible_candidate(self.active_branch, self.mini_allocator, self.disk);
                assert(semantic_active_branch_candidate(
                    self.active_branch.root.unwrap(),
                    self.visible_branch_nodes(),
                    self.mini_allocator,
                    branch,
                ));
                assert(branch.disk_view.entries <= self.visible_branch_nodes());
	                assert(self.visible_branch_nodes().contains_key(root));
                query_read_node_matches_visible(self.disk, reads, root);
                assert(branch.disk_view.entries.contains_key(root));
                assert(read_nodes[root] == branch.root());
                assert(aux_ptr is Some <==> branch.root() is Index);

                if aux_ptr is Some {
                    let ptr = aux_ptr.unwrap();
                    assert(self.mini_allocator.can_allocate(ptr));
                    assert(self.mini_allocator.allocated_aus().contains(ptr.au));
                    assert(!dealloc_aus.contains(ptr.au)) by {
                        if dealloc_aus.contains(ptr.au) {
                            assert(self.mini_allocator.removable_aus().contains(ptr.au));
                            assert(self.mini_allocator.can_remove(ptr.au));
                            assert(self.mini_allocator.allocs[ptr.au].has_no_allocated_pages());
                            assert(!self.mini_allocator.allocated_aus().contains(ptr.au));
                            assert(false);
                        }
                    }
                }
                assert(self.i().active_branch.can_seal(aux_ptr, dealloc_aus));

                let concrete_sealed_branch = LinkedBranch{
                    root: branch.root,
                    disk_view: DiskView{
                        entries: branch.disk_view.entries.union_prefer_right(write_nodes),
                    },
                };

                if aux_ptr is Some {
                    let ptr = aux_ptr.unwrap();
                    assert(write_nodes == loaded_seal_write_nodes(
                        root,
                        read_nodes,
                        aux_ptr,
                        sealed_summary,
                    ));
                    assert(write_nodes.contains_key(root));
                    assert(write_nodes.contains_key(ptr));
                    assert(write_nodes[root] == BranchNode::Index{
                        pivots: branch.root()->pivots,
                        children: branch.root()->children,
                        aux_ptr,
                    });
                    assert(write_nodes[ptr] == BranchNode::Auxiliary(sealed_summary));
                    assert(concrete_sealed_branch == branch.seal(ptr, sealed_summary)) by {
                        assert_maps_equal!(
                            concrete_sealed_branch.disk_view.entries,
                            branch.seal(ptr, sealed_summary).disk_view.entries,
                            addr => {
                                if concrete_sealed_branch.disk_view.entries.contains_key(addr) {
                                    if write_nodes.contains_key(addr) {
                                        assert(addr == root || addr == ptr);
                                    } else {
                                        assert(branch.disk_view.entries.contains_key(addr));
                                    }
                                }
                                if branch.seal(ptr, sealed_summary).disk_view.entries.contains_key(addr) {
                                    if addr == root || addr == ptr {
                                        assert(write_nodes.contains_key(addr));
                                    } else {
                                        assert(branch.disk_view.entries.contains_key(addr));
                                        assert(!write_nodes.contains_key(addr));
                                    }
                                }
                            }
                        );
                    };
                } else {
                    assert(write_nodes == Map::<Address, BranchNode>::empty());
                    assert(concrete_sealed_branch == branch) by {
                        assert_maps_equal!(
                            concrete_sealed_branch.disk_view.entries,
                            branch.disk_view.entries,
                            addr => {
                                if concrete_sealed_branch.disk_view.entries.contains_key(addr) {
                                    assert(!write_nodes.contains_key(addr));
                                }
                            }
                        );
                    };
                }
                assert(sealed_branch == concrete_sealed_branch);

                self.i().active_branch.branch_seal_preserves_inv(aux_ptr, dealloc_aus);
                assert(sealed_active.inv());
                assert(sealed_branch.valid_sealed_branch());
                assert(sealed_branch.tight_disk_view_with_summary());

                mini_allocator_all_minus_removable_is_allocated(self.mini_allocator);
                if aux_ptr is Some {
                    mini_allocator_allocate_preserves_all_aus(self.mini_allocator, aux_ptr.unwrap());
                    let allocated = self.mini_allocator.allocate(aux_ptr.unwrap());
                    allocated.prune_preserves_wf(dealloc_aus);
                    assert(allocated.all_aus() == self.mini_allocator.all_aus());
                    assert(sealed_active.mini_allocator == allocated.prune(dealloc_aus));
                } else {
                    self.mini_allocator.prune_preserves_wf(dealloc_aus);
                    assert(sealed_active.mini_allocator == self.mini_allocator.prune(dealloc_aus));
                }
                assert(sealed_active.mini_allocator.all_aus() == sealed_summary);
                assert(sealed_branch.get_summary() == sealed_summary);
                let loose_active_summary =
                    Map::<AU, Summary>::empty().insert(sealed_branch.root.au, sealed_branch.get_summary());
                let loose_active_disk = BufferDisk{
                    entries: sealed_nodes_of(post.disk.visible(), loose_active_summary),
                };
                assert(loose_active_summary.dom().finite());
                lemma_values_finite(loose_active_summary);

                assert(summary_aus(self.branch_summary).disjoint(sealed_branch.get_summary())) by {
                    assert forall |au: AU| #[trigger] summary_aus(self.branch_summary).contains(au)
                        implies !sealed_branch.get_summary().contains(au)
                    by {
                        if sealed_branch.get_summary().contains(au) {
                            assert(self.mini_allocator.all_aus().contains(au));
                            assert(false);
                        }
                    }
                };
                assert(!self.branch_summary.contains_key(sealed_branch.root.au)) by {
                    if self.branch_summary.contains_key(sealed_branch.root.au) {
                        assert(self.branch_summary.values().contains(self.branch_summary[sealed_branch.root.au]));
                        lemma_union_set_of_sets_subset(self.branch_summary.values(), self.branch_summary[sealed_branch.root.au]);
                        assert(summary_aus(self.branch_summary).contains(sealed_branch.root.au));
                        assert(sealed_branch.get_summary().contains(sealed_branch.root.au));
                        assert(false);
                    }
                };
                assert(!self.i().branch_summary.contains_key(sealed_branch.root.au));
                assert(tight_branch_in_loose_disk(
                    loose_active_disk,
                    sealed_branch.root,
                    sealed_branch.get_summary(),
                    sealed_branch,
                )) by {
                    assert(sealed_branch.root == root);
                    assert(sealed_branch.valid_sealed_branch());
                    assert(sealed_branch.tight_disk_view_with_summary());
                    assert(sealed_branch.get_summary() == sealed_summary);
                    assert(sealed_branch.disk_view.entries <= loose_active_disk.entries) by {
                        assert forall |addr: Address| #[trigger] sealed_branch.disk_view.entries.contains_key(addr)
                            implies loose_active_disk.entries.contains_key(addr)
                                && loose_active_disk.entries[addr] == sealed_branch.disk_view.entries[addr]
                        by {
                            assert(addrs_closed(sealed_branch.full_repr(), sealed_branch.get_summary()));
                            assert(sealed_branch.full_repr().contains(addr));
                            assert(sealed_branch.get_summary().contains(addr.au));
                            assert(loose_active_summary.contains_key(sealed_branch.root.au));
                            assert(loose_active_summary[sealed_branch.root.au] == sealed_branch.get_summary());
                            assert(summary_aus(loose_active_summary).contains(addr.au)) by {
                                assert(loose_active_summary.values().contains(sealed_branch.get_summary()));
                                lemma_union_set_of_sets_subset(loose_active_summary.values(), sealed_branch.get_summary());
                            }
                            assert(post.disk.visible().contains_key(addr)) by {
                                if writes.contains_key(addr) {
                                    assert(write_nodes.contains_key(addr));
                                    assert(post.disk.visible().contains_key(addr));
                                } else {
                                    assert(branch.disk_view.entries.contains_key(addr));
                                    assert(branch.disk_view.entries <= self.visible_branch_nodes());
                                    assert(self.visible_branch_nodes().contains_key(addr));
                                    assert(post.disk.visible().contains_key(addr));
                                }
                            };
                            assert(to_branch_nodes(post.disk.visible())[addr]
                                == sealed_branch.disk_view.entries[addr]) by {
                                if writes.contains_key(addr) {
                                    assert(write_nodes.contains_key(addr));
                                    assert(post.disk.visible()[addr] == writes[addr]);
                                    assert(to_branch_nodes(post.disk.visible())[addr] == write_nodes[addr]);
                                    assert(sealed_branch.disk_view.entries[addr] == write_nodes[addr]);
                                } else {
                                    assert(branch.disk_view.entries.contains_key(addr));
                                    assert(branch.disk_view.entries <= self.visible_branch_nodes());
                                    assert(self.visible_branch_nodes().contains_key(addr));
                                    assert(post.disk.visible()[addr] == self.disk.visible()[addr]);
                                    assert(to_branch_nodes(post.disk.visible())[addr]
                                        == self.visible_branch_nodes()[addr]);
                                    assert(self.visible_branch_nodes()[addr] == branch.disk_view.entries[addr]);
                                    assert(sealed_branch.disk_view.entries[addr] == branch.disk_view.entries[addr]);
                                }
                            };
                            assert(sealed_nodes_of(post.disk.visible(), loose_active_summary).contains_key(addr));
                            assert(to_branch_nodes(post.disk.visible())[addr] == sealed_branch.disk_view.entries[addr]);
                        }
                    };
                };
                assert(addrs_closed(loose_active_disk.entries.dom(), sealed_branch.get_summary())) by {
                    assert forall |addr: Address| #[trigger] loose_active_disk.entries.dom().contains(addr)
                        implies sealed_branch.get_summary().contains(addr.au)
                    by {
                        assert(loose_active_disk.entries.contains_key(addr));
                        assert(summary_aus(loose_active_summary).contains(addr.au));
                        let summary = lemma_union_set_of_sets_contains(loose_active_summary.values(), addr.au);
                        assert(summary == sealed_branch.get_summary());
                    }
                };
                self.i().sealed_stack.push_branch_preserves_wf(self.i().branch_summary, sealed_branch, loose_active_disk);
                let pushed_stack = self.i().sealed_stack.push_branch(sealed_branch, loose_active_disk);
                let roots = self.i().sealed_stack.sealed_roots.to_set();
                self.i().sealed_stack.sealed_disk.build_branch_summary_finite(roots);
                assert(self.branch_summary.dom().finite());
                assert(sealed_branch.get_summary().contains(sealed_branch.root.au)) by {
                    assert(sealed_branch.full_repr().contains(sealed_branch.root));
                    assert(crate::disk::GenericDisk_v::addrs_closed(
                        sealed_branch.full_repr(),
                        sealed_branch.get_summary(),
                    ));
                }
                assert(!self.branch_summary.contains_key(sealed_branch.root.au));
                branch_summary_insert_ensures(self.branch_summary, sealed_branch);
                assert(summary_aus(post.branch_summary)
                    == summary_aus(self.branch_summary) + sealed_branch.get_summary());
                lemma_values_finite(post.branch_summary);
                assert(post.branch_summary.values().finite());
                assert(writes.dom().disjoint(addresses_in_aus(summary_aus(self.branch_summary)))) by {
                    assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                        implies !addresses_in_aus(summary_aus(self.branch_summary)).contains(addr)
                    by {
                        assert(write_nodes.contains_key(addr));
                        if aux_ptr is Some {
                            assert(addr == root || addr == aux_ptr.unwrap());
                            if addr == root {
                                assert(sealed_branch.get_summary().contains(addr.au)) by {
                                    assert(sealed_branch.full_repr().contains(root));
                                    assert(crate::disk::GenericDisk_v::addrs_closed(
                                        sealed_branch.full_repr(),
                                        sealed_branch.get_summary(),
                                    ));
                                }
                            } else {
                                assert(addr == aux_ptr.unwrap());
                                assert(sealed_branch.get_summary().contains(addr.au)) by {
                                    assert(sealed_branch.full_repr().contains(addr));
                                    assert(crate::disk::GenericDisk_v::addrs_closed(
                                        sealed_branch.full_repr(),
                                        sealed_branch.get_summary(),
                                    ));
                                }
                            }
                        } else {
                            assert(false);
                        }
                        if addresses_in_aus(summary_aus(self.branch_summary)).contains(addr) {
                            assert(summary_aus(self.branch_summary).contains(addr.au));
                            assert(false);
                        }
                    }
                };
                access_preserves_loaded_metadata(self, post.disk, reads, writes);
                assert(branch_summary_reads_valid(post.sealed_roots, post.visible_branch_nodes())) by {
                    assert forall |i: int| #![trigger post.sealed_roots[i]]
                        0 <= i < post.sealed_roots.len()
                        implies root_summary_read_valid(post.sealed_roots[i], post.visible_branch_nodes())
                    by {
                        if i < self.sealed_roots.len() {
                            assert(post.sealed_roots[i] == self.sealed_roots[i]);
                            assert(branch_summary_reads_valid(self.sealed_roots, post.visible_branch_nodes()));
                        } else {
                            assert(i == self.sealed_roots.len());
                            assert(post.sealed_roots[i] == root);
                            assert(post.visible_branch_nodes().contains_key(root));
                            if post.visible_branch_nodes()[root] is Index {
                                assert(aux_ptr is Some);
                                let aux = aux_ptr.unwrap();
                                assert(post.visible_branch_nodes()[root]->aux_ptr == Some(aux));
                                assert(post.visible_branch_nodes().contains_key(aux));
                                assert(post.visible_branch_nodes()[aux] is Auxiliary);
                            } else {
                                assert(post.visible_branch_nodes()[root] is Leaf);
                            }
                        }
                    }
                };
                branch_summary_from_reads_up_to_self_ensures(
                    post.sealed_roots,
                    post.visible_branch_nodes(),
                    post.sealed_roots.len() as nat,
                );
                assert(post.interpreted_branch_summary() == post.branch_summary) by {
                    assert_maps_equal!(
                        post.interpreted_branch_summary(),
                        post.branch_summary,
                        au => {
                            if post.interpreted_branch_summary().contains_key(au) {
                                let idx = root_aus_up_to_member_has_index(
                                    post.sealed_roots,
                                    post.sealed_roots.len() as nat,
                                    au,
                                );
                                if idx < self.sealed_roots.len() {
                                    assert(post.sealed_roots[idx] == self.sealed_roots[idx]);
                                    assert(loaded_branch_summary_agrees(
                                        self.sealed_roots,
                                        post.visible_branch_nodes(),
                                        self.branch_summary,
                                    ));
                                    root_aus_up_to_contains(
                                        self.sealed_roots,
                                        self.sealed_roots.len() as nat,
                                        idx,
                                    );
                                    assert(self.branch_summary.dom().contains(self.sealed_roots[idx].au));
                                    assert(self.branch_summary.contains_key(self.sealed_roots[idx].au));
                                    assert(self.branch_summary[self.sealed_roots[idx].au]
                                        == root_summary_from_read(self.sealed_roots[idx], post.visible_branch_nodes()));
                                    assert(post.interpreted_branch_summary()[au]
                                        == root_summary_from_read(post.sealed_roots[idx], post.visible_branch_nodes()));
                                    assert(self.branch_summary[au]
                                        == root_summary_from_read(self.sealed_roots[idx], post.visible_branch_nodes()));
                                    assert(post.branch_summary[au] == self.branch_summary[au]);
                                } else {
                                    assert(idx == self.sealed_roots.len());
                                    assert(post.sealed_roots[idx] == root);
                                    assert(au == root.au);
                                    assert(post.branch_summary[au] == sealed_summary);
                                    if post.visible_branch_nodes()[root] is Index {
                                        let aux = aux_ptr.unwrap();
                                        assert(post.visible_branch_nodes()[aux] == BranchNode::Auxiliary(sealed_summary));
                                    } else {
                                        assert(root_summary_from_read(root, post.visible_branch_nodes()) == set![root.au]);
                                        assert(sealed_summary == set![root.au]) by {
                                            assert(sealed_branch.get_summary() == sealed_summary);
                                            assert(sealed_branch.root == root);
                                            assert(sealed_branch.root() is Leaf);
                                            assert(sealed_branch.get_summary() == set![root.au]);
                                        }
                                    }
                                }
                            }
                            if post.branch_summary.contains_key(au) {
                                if self.branch_summary.contains_key(au) {
                                    assert(root_aus_up_to(
                                        self.sealed_roots,
                                        self.sealed_roots.len() as nat,
                                    ).contains(au));
                                    let old_idx = root_aus_up_to_member_has_index(
                                        self.sealed_roots,
                                        self.sealed_roots.len() as nat,
                                        au,
                                    );
                                    root_aus_up_to_contains(
                                        post.sealed_roots,
                                        post.sealed_roots.len() as nat,
                                        old_idx,
                                    );
                                    assert(root_aus_up_to(
                                        post.sealed_roots,
                                        post.sealed_roots.len() as nat,
                                    ).contains(au));
                                } else {
                                    assert(au == root.au);
                                    root_aus_up_to_contains(
                                        post.sealed_roots,
                                        post.sealed_roots.len() as nat,
                                        self.sealed_roots.len() as int,
                                    );
                                }
                                assert(post.interpreted_branch_summary().contains_key(au));
                            }
                        }
                    );
                };

                assert(post.i().sealed_stack.sealed_disk.entries =~=
                    pushed_stack.sealed_disk.entries) by {
                    let post_entries = post.i().sealed_stack.sealed_disk.entries;
                    let pushed_entries = pushed_stack.sealed_disk.entries;
                    let pre_sealed_entries = self.i().sealed_stack.sealed_disk.entries;
                    let loose_entries = loose_active_disk.entries;
                    let old_summary = summary_aus(self.branch_summary);
                    let new_summary = sealed_branch.get_summary();
                    assert(summary_aus(loose_active_summary) == new_summary) by {
                        assert_maps_equal!(
                            loose_active_summary,
                            Map::<AU, Summary>::empty().insert(sealed_branch.root.au, new_summary),
                            au => {}
                        );
                        assert(loose_active_summary.dom().finite());
                        lemma_values_finite(loose_active_summary);
                        assert(loose_active_summary.contains_key(sealed_branch.root.au));
                        assert(loose_active_summary[sealed_branch.root.au] == new_summary);
                        assert(loose_active_summary.values().contains(new_summary));
                        assert forall |au: AU| #[trigger] summary_aus(loose_active_summary).contains(au)
                            <==> new_summary.contains(au)
                        by {
                            if summary_aus(loose_active_summary).contains(au) {
                                let summary = lemma_union_set_of_sets_contains(loose_active_summary.values(), au);
                                let root_au = choose |root_au: AU| #![auto]
                                    loose_active_summary.contains_key(root_au)
                                    && loose_active_summary[root_au] == summary;
                                assert(root_au == sealed_branch.root.au);
                                assert(summary == new_summary);
                            } else if new_summary.contains(au) {
                                lemma_union_set_of_sets_subset(loose_active_summary.values(), new_summary);
                            }
                        };
                    };
                    assert_maps_equal!(
                        post_entries,
                            pushed_entries,
                            addr => {
                                if post_entries.contains_key(addr) {
                                    assert(sealed_nodes_of(
                                        post.disk.visible(),
                                        post.interpreted_branch_summary(),
                                    ).contains_key(addr));
                                    assert(post.interpreted_branch_summary() == post.branch_summary);
                                    assert(summary_aus(post.branch_summary).contains(addr.au));
                                    if old_summary.contains(addr.au) {
                                    assert(!new_summary.contains(addr.au));
	                                    assert(!writes.contains_key(addr)) by {
	                                        if writes.contains_key(addr) {
	                                            assert(write_nodes.contains_key(addr));
	                                            if aux_ptr is Some {
	                                                assert(addr == root || addr == aux_ptr.unwrap());
	                                            } else {
	                                                assert(false);
	                                            }
	                                            assert(new_summary.contains(addr.au));
	                                            assert(false);
	                                        }
	                                    }
	                                    assert(self.disk.visible().contains_key(addr));
	                                    assert(to_branch_nodes(post.disk.visible())[addr]
	                                        == to_branch_nodes(self.disk.visible())[addr]);
	                                    assert(pre_sealed_entries.contains_key(addr));
                                        assert(!loose_entries.contains_key(addr)) by {
                                            if loose_entries.contains_key(addr) {
                                                assert(summary_aus(loose_active_summary).contains(addr.au));
                                                assert(new_summary.contains(addr.au));
                                                assert(false);
                                            }
                                        };
	                                } else {
	                                    assert(new_summary.contains(addr.au));
                                        assert(summary_aus(loose_active_summary).contains(addr.au));
                                        assert(loose_entries.contains_key(addr));
	                                }
	                            }
	                            if pushed_entries.contains_key(addr) {
	                                if loose_entries.contains_key(addr) {
                                        assert(summary_aus(loose_active_summary).contains(addr.au));
	                                    assert(new_summary.contains(addr.au));
                                        assert(post.disk.visible().contains_key(addr));
	                                    assert(summary_aus(post.branch_summary).contains(addr.au));
	                                } else {
	                                    assert(pre_sealed_entries.contains_key(addr));
	                                    assert(old_summary.contains(addr.au));
	                                    assert(!new_summary.contains(addr.au));
	                                    assert(self.disk.visible().contains_key(addr));
	                                    assert(post.disk.visible().contains_key(addr));
	                                    assert(summary_aus(post.branch_summary).contains(addr.au));
                                }
                            }
                        }
                    );
                };
                assert(post.i().sealed_stack.sealed_disk == pushed_stack.sealed_disk);
                assert(post.i().sealed_stack.sealed_roots == pushed_stack.sealed_roots);
                assert(post.i().sealed_stack == pushed_stack);

                assert(post.i().active_branch == AllocationBranch{
                    sealed: false,
                    branch: None,
                    mini_allocator: self.i().active_branch.mini_allocator.prune(
                        sealed_branch.get_summary()
                    ),
                });

                reveal(AllocationBranchStack::State::next);
                reveal(AllocationBranchStack::State::next_by);
                assert(AllocationBranchStack::State::internal_seal(
                    self.i(),
                    post.i(),
                    lbl.i(),
                    aux_ptr,
                    loose_active_disk,
                )) by {
                    reveal(AllocationBranchStack::State::internal_seal);
                }
                assert(AllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    lbl.i(),
                    AllocationBranchStack::Step::internal_seal(aux_ptr, loose_active_disk),
                ));
            },
            _ => {
                assert(false);
            },
        }
        assert(AllocationBranchStack::State::next(self.i(), post.i(), lbl.i()));
        AllocationBranchStack::State::inv_next(self.i(), post.i(), lbl.i());
        post.i_inv_implies_semantic_inv();
        assert(post.refinement_inv());
    }

}

impl CachingDiskBranch::Label {
    pub open spec fn i(self) -> AllocationBranchStack::Label {
        match self {
            Self::QueryLabel{key, msg} => AllocationBranchStack::Label::QueryLabel{key, msg},
            Self::AppendLabel{keys, msgs} => AllocationBranchStack::Label::AppendLabel{keys, msgs},
            Self::FreezeAsLabel{image} => AllocationBranchStack::Label::InternalLabel,
            Self::FreezePrepared{image} => AllocationBranchStack::Label::InternalLabel,
            Self::LoadMetadata{root, discovered_aus} => AllocationBranchStack::Label::InternalLabel,
            Self::Internal => AllocationBranchStack::Label::InternalLabel,
            Self::InternalAlloc{allocs, deallocs} => AllocationBranchStack::Label::InternalLabel,
        }
    }
}

}
