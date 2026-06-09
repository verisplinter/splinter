// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]

use vstd::{assert_maps_equal, map::*, prelude::*};
use vstd::map_lib::lemma_values_finite;

use crate::abstract_system::AbstractMap_v::AbstractMap;
use crate::allocation_layer::AllocationBranchBetree_v::summary_aus;
use crate::allocation_layer::AllocationBranch_v::{
    AllocationBranch, BranchNode as AllocationBranchNode, Summary,
};
use crate::betree::LinkedBranch_v::{LinkedBranch, Path, Refinement_v as LinkedBranchRefinement};
use crate::betree::PivotBranchRefinement_v::{self as PivotBranchRefinement, QueryLabel};
use crate::betree::Utils_v::lemma_union_set_of_sets_subset;
use crate::disk::GenericDisk_v::{addrs_closed, AU, Address, Ranking};
use crate::implementation::AllocationBranchStack_v::{
    active_branch_query_or_nop, is_nop_message, AllocationBranchStack,
    SealedAllocationBranchStack,
};
use crate::implementation::CachedBranch_v::{
    receipt_valid_implies_tail_valid, LoadedBranch, LoadedPathReceipt,
};
use crate::implementation::Cache_v::Cache;
use crate::implementation::ConcreteBranch_v::{to_branch_nodes, ConcreteBranch};
use crate::spec::AsyncDisk_t::{AsyncDisk, DiskRequest, DiskResponse, RawPage};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{nop_delta, Message};
use crate::spec::MapSpec_t::ID;

verus! {

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
    key: crate::spec::KeyType_t::Key,
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
    key: crate::spec::KeyType_t::Key,
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

proof fn query_read_node_matches_available(
    state: ConcreteBranch::State,
    new_cache: Cache::State,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    addr: Address,
)
    requires
        state.cache.inv(),
        Cache::State::next(
            state.cache,
            new_cache,
            Cache::Label::Access{reads, writes},
        ),
        reads.contains_key(addr),
    ensures
        state.available_branch_nodes().contains_key(addr),
        to_branch_nodes(reads)[addr] == state.available_branch_nodes()[addr],
{
    let lbl = Cache::Label::Access{reads, writes};
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    assert(Cache::State::next_by(state.cache, new_cache, lbl, Cache::Step::access()));
    assert(lbl->reads.contains_key(addr));
    assert(state.cache.valid_read(addr, reads[addr]));
    assert(state.has_cached_page(addr));
    assert(state.cache_raw_page(addr) == reads[addr]);
    assert(state.available_raw_pages().contains_key(addr));
    assert(state.available_raw_pages()[addr] == reads[addr]);
    assert(state.available_branch_nodes().contains_key(addr));
}

proof fn receipt_query_matches_branch_query_internal(
    state: ConcreteBranch::State,
    new_cache: Cache::State,
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
)
    requires
        state.cache.inv(),
        Cache::State::next(
            state.cache,
            new_cache,
            Cache::Label::Access{reads, writes},
        ),
        branch.inv_internal(ranking),
        receipt.valid_for(branch.root, to_branch_nodes(reads)),
        receipt.target().node is Leaf,
        forall |addr: Address|
            #[trigger] branch.disk_view.entries.contains_key(addr)
            ==> {
                &&& state.available_branch_nodes().contains_key(addr)
                &&& branch.disk_view.entries[addr] == state.available_branch_nodes()[addr]
            },
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
    query_read_node_matches_available(state, new_cache, reads, writes, root);
    assert(branch.disk_view.entries.contains_key(root));
    assert(branch.disk_view.entries[root] == state.available_branch_nodes()[root]);
    assert(read_nodes[root] == branch.disk_view.entries[root]);
    assert(branch.root() == branch.disk_view.entries[root]);
    assert(receipt.lines[0].node == read_nodes[root]);
    assert(receipt.lines[0].node == branch.root());

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
            state,
            new_cache,
            child_branch,
            ranking,
            reads,
            writes,
            child_receipt,
        );
        local_query_internal_descends_to_child(branch, ranking, receipt.key);
        assert(branch.child_at_idx(branch.root().route(receipt.key) + 1) == child_branch);
        assert(child_branch.query_internal(receipt.key, ranking) == child_receipt.result());
        assert(child_receipt.result() == receipt.result());
    }
}

proof fn receipt_query_matches_branch_query(
    state: ConcreteBranch::State,
    new_cache: Cache::State,
    branch: LinkedBranch<Summary>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
)
    requires
        state.cache.inv(),
        Cache::State::next(
            state.cache,
            new_cache,
            Cache::Label::Access{reads, writes},
        ),
        branch.inv(),
        receipt.valid_for(branch.root, to_branch_nodes(reads)),
        receipt.target().node is Leaf,
        forall |addr: Address|
            #[trigger] branch.disk_view.entries.contains_key(addr)
            ==> {
                &&& state.available_branch_nodes().contains_key(addr)
                &&& branch.disk_view.entries[addr] == state.available_branch_nodes()[addr]
            },
    ensures
        branch.query(receipt.key) == receipt.result(),
{
    let ranking = branch.the_ranking();
    receipt_query_matches_branch_query_internal(state, new_cache, branch, ranking, reads, writes, receipt);
    let msg = receipt.result();
    LinkedBranchRefinement::query_internal_refines(branch, ranking, receipt.key, msg);
    LinkedBranchRefinement::query_refines(branch, receipt.key, branch.query(receipt.key));
    assert(branch.i_internal(ranking).query(receipt.key) == msg);
    assert(branch.i().query(receipt.key) == branch.query(receipt.key));
    assert(branch.i() == branch.i_internal(ranking));
    assert(branch.query(receipt.key) == msg);
}

proof fn leaf_append_route_equiv(leaf: AllocationBranchNode, keys: Seq<Key>)
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
    state: ConcreteBranch::State,
    new_cache: Cache::State,
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    keys: Seq<Key>,
    msgs: Seq<Message>,
)
    requires
        state.cache.inv(),
        Cache::State::next(
            state.cache,
            new_cache,
            Cache::Label::Access{reads, writes},
        ),
        branch.inv_internal(ranking),
        receipt.root == branch.root,
        keys.len() > 0,
        crate::implementation::CachedBranch_v::loaded_append_ready(
            receipt,
            to_branch_nodes(reads),
            keys,
            msgs,
        ),
        forall |addr: Address|
            #[trigger] branch.disk_view.entries.contains_key(addr)
            ==> {
                &&& state.available_branch_nodes().contains_key(addr)
                &&& branch.disk_view.entries[addr] == state.available_branch_nodes()[addr]
            },
    ensures
        ({
            let path = Path{branch, key: keys[0], depth: receipt.depth()};
            &&& path.valid()
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
    query_read_node_matches_available(state, new_cache, reads, writes, root);
    assert(branch.disk_view.entries.contains_key(root));
    assert(branch.disk_view.entries[root] == state.available_branch_nodes()[root]);
    assert(read_nodes[root] == branch.disk_view.entries[root]);
    assert(branch.root() == branch.disk_view.entries[root]);
    assert(receipt.lines[0].node == read_nodes[root]);
    assert(receipt.lines[0].node == branch.root());

    if receipt.depth() == 0 {
        assert(receipt.lines.len() == 1);
        assert(receipt.target() == receipt.lines[0]);
        assert(path.valid());
        assert(path.target() == branch);
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
        assert(crate::implementation::CachedBranch_v::loaded_append_ready(
            child_receipt,
            read_nodes,
            keys,
            msgs,
        ));
        child_branch_inv_internal_from_parent(branch, ranking, child_idx);
        receipt_path_valid_for_append(
            state,
            new_cache,
            child_branch,
            ranking,
            reads,
            writes,
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
    state: ConcreteBranch::State,
    new_cache: Cache::State,
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    split_arg: crate::betree::LinkedBranch_v::SplitArg,
    new_child_addr: Address,
)
    requires
        state.cache.inv(),
        Cache::State::next(
            state.cache,
            new_cache,
            Cache::Label::Access{reads, writes},
        ),
        branch.inv_internal(ranking),
        receipt.root == branch.root,
        crate::implementation::CachedBranch_v::loaded_split_ready(
            receipt,
            to_branch_nodes(reads),
            split_arg,
        ),
        branch.disk_view.is_fresh(set!{new_child_addr}),
        to_branch_nodes(reads).contains_key(receipt.child_addr()),
        branch.disk_view.entries.contains_key(receipt.child_addr()),
        to_branch_nodes(reads)[receipt.child_addr()]
            == branch.disk_view.entries[receipt.child_addr()],
        forall |addr: Address|
            #[trigger] branch.disk_view.entries.contains_key(addr)
            ==> {
                &&& state.available_branch_nodes().contains_key(addr)
                &&& branch.disk_view.entries[addr] == state.available_branch_nodes()[addr]
            },
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
    query_read_node_matches_available(state, new_cache, reads, writes, root);
    assert(branch.disk_view.entries.contains_key(root));
    assert(branch.disk_view.entries[root] == state.available_branch_nodes()[root]);
    assert(read_nodes[root] == branch.disk_view.entries[root]);
    assert(branch.root() == branch.disk_view.entries[root]);
    assert(receipt.lines[0].node == read_nodes[root]);
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
        assert(child_branch.disk_view.entries.contains_key(child_branch.root));
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
        assert(crate::implementation::CachedBranch_v::loaded_split_ready(
            child_receipt,
            read_nodes,
            split_arg,
        ));
        child_branch_inv_internal_from_parent(branch, ranking, child_idx);
        receipt_path_valid_for_split(
            state,
            new_cache,
            child_branch,
            ranking,
            reads,
            writes,
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

impl ConcreteBranch::State {
    pub open spec fn active_branch_i(self) -> AllocationBranch
    {
        if self.cached_branches.len() == 0 {
            AllocationBranch::new(Set::empty())
        } else {
            AllocationBranch{
                sealed: false,
                branch: self.overlay_branch(),
                mini_allocator: self.mini_allocator,
            }
        }
    }

    pub open spec fn i(self) -> AllocationBranchStack::State
    {
        AllocationBranchStack::State{
            sealed_stack: SealedAllocationBranchStack{
                sealed_roots: self.sealed_roots_i(),
                sealed_disk: self.sealed_disk_i(),
            },
            branch_summary: self.branch_summary,
            active_branch: self.active_branch_i(),
            seq_end: self.seq_end,
        }
    }

    pub open spec fn abstract_map_i(self) -> AbstractMap::State
    {
        self.i().abstract_map_i()
    }

    pub open spec fn label_to_stack(self, lbl: ConcreteBranch::Label) -> AllocationBranchStack::Label
    {
        match lbl {
            ConcreteBranch::Label::Query{branch_idx, key, msg} =>
                AllocationBranchStack::Label::QueryLabel{ key, msg },
            ConcreteBranch::Label::Append{keys, msgs} =>
                AllocationBranchStack::Label::AppendLabel{ keys, msgs },
            ConcreteBranch::Label::Grow{new_root_addr} =>
                AllocationBranchStack::Label::InternalLabel,
            ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg} =>
                AllocationBranchStack::Label::InternalLabel,
            ConcreteBranch::Label::Seal{aux_ptr} =>
                AllocationBranchStack::Label::InternalLabel,
            ConcreteBranch::Label::FillAU{aus} =>
                AllocationBranchStack::Label::InternalLabel,
            ConcreteBranch::Label::Internal{} =>
                AllocationBranchStack::Label::InternalLabel,
        }
    }

    pub open spec fn label_to_abstract_map(self, lbl: ConcreteBranch::Label) -> AbstractMap::Label
    {
        self.i().label_to_abstract_map(self.label_to_stack(lbl))
    }

    pub open spec fn refinement_wf(self) -> bool
    {
        &&& self.wf()
        &&& self.available_branch_nodes().dom().finite()
        &&& self.i().wf()
    }

    pub proof fn init_refines(
        self,
        cached_branches: Seq<crate::implementation::CachedBranch_v::CachedBranch::State>,
        seq_end: nat,
        init_aus: Set<AU>,
        cache: crate::implementation::Cache_v::Cache::State,
        cache_slots: nat,
        disk: AsyncDisk::State,
    )
        requires
            self.refinement_wf(),
            ConcreteBranch::State::initialize(self, cached_branches, seq_end, init_aus, cache, cache_slots, disk),
        ensures
            AllocationBranchStack::State::initialize(
                self.i(),
                self.sealed_roots_i(),
                self.sealed_disk_i(),
                self.branch_summary,
                init_aus,
                self.seq_end,
            ),
            AbstractMap::State::initialize(self.abstract_map_i(), self.abstract_map_i().stamped_map),
    {
        assert(AllocationBranchStack::State::initialize(
                self.i(),
                self.sealed_roots_i(),
                self.sealed_disk_i(),
                self.branch_summary,
                init_aus,
                self.seq_end,
            ));
        self.i().init_refines(
            self.sealed_roots_i(),
            self.sealed_disk_i(),
            self.branch_summary,
            init_aus,
            self.seq_end,
        );
    }

    proof fn stack_next_implies_abstract_next(
        self,
        post: Self,
        lbl: ConcreteBranch::Label,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
        ensures
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        self.i().next_refines(post.i(), self.label_to_stack(lbl));
    }

    proof fn i_unchanged_when_available_raw_pages_unchanged(self, post: Self)
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            self.cached_branches == post.cached_branches,
            self.branch_summary == post.branch_summary,
            self.seq_end == post.seq_end,
            self.mini_allocator == post.mini_allocator,
            self.available_raw_pages() == post.available_raw_pages(),
        ensures
            self.i() == post.i(),
    {
        Self::available_branch_nodes_equal_if_raw_pages_equal(self, post);
        assert(self.sealed_disk_i() == post.sealed_disk_i());
        assert(self.sealed_roots_i() =~= post.sealed_roots_i()) by {
            assert forall |i: int| 0 <= i < self.sealed_roots_i().len()
                implies self.sealed_roots_i()[i] == post.sealed_roots_i()[i] by {
                Self::overlay_at_same_available_branch_nodes(self, post, i as nat);
            }
        }
        Self::overlay_at_same_available_branch_nodes(self, post, self.active_idx() as nat);
        assert(self.active_branch_i() == post.active_branch_i());
        assert(self.i() == post.i());
    }

    proof fn active_branch_query_matches_stack_active(
        self,
        key: crate::spec::KeyType_t::Key,
        msg: Message,
        receipt: Option<LoadedPathReceipt>,
        reads: Map<Address, RawPage>,
    )
        requires
            self.refinement_wf(),
            Cache::State::next(
                self.cache,
                self.cache,
                Cache::Label::Access{reads, writes: Map::<Address, RawPage>::empty()},
            ),
            self.branch_query_matches(
                self.active_idx() as nat,
                key,
                msg,
                receipt,
                to_branch_nodes(reads),
            ),
        ensures
            active_branch_query_or_nop(self.i().active_branch, key) == msg,
    {
        let idx = self.active_idx() as nat;
        if self.cached_branches[idx as int].root is Some {
            let r = receipt.unwrap();
            let branch = self.overlay_branch().unwrap();
            assert(self.i().active_branch.branch == Some(branch));
            assert(self.i().active_branch.inv());
            assert(branch.inv());
            assert(r.key == key);
            assert(self.cached_branches[idx as int].query_result(r, to_branch_nodes(reads)) == msg);
            assert(r.result() == msg);
            assert forall |addr: Address|
                #[trigger] branch.disk_view.entries.contains_key(addr)
                implies {
                    &&& self.available_branch_nodes().contains_key(addr)
                    &&& branch.disk_view.entries[addr] == self.available_branch_nodes()[addr]
                }
            by {
                assert(branch.disk_view.entries == self.active_branch_entries());
                assert(self.active_branch_entries().contains_key(addr));
                assert(self.active_branch_addrs().contains(addr));
            }
            receipt_query_matches_branch_query(
                self,
                self.cache,
                branch,
                reads,
                Map::<Address, RawPage>::empty(),
                r,
            );
            assert(branch.query(key) == msg);
        } else {
            assert(receipt is None);
            assert(msg == Message::Update{delta: nop_delta()});
            assert(self.i().active_branch.branch is None);
        }
    }

    proof fn sealed_branch_query_matches_stack_sealed(
        self,
        branch_idx: nat,
        key: crate::spec::KeyType_t::Key,
        msg: Message,
        receipt: Option<LoadedPathReceipt>,
        reads: Map<Address, RawPage>,
    )
        requires
            self.refinement_wf(),
            branch_idx < self.historical_len(),
            Cache::State::next(
                self.cache,
                self.cache,
                Cache::Label::Access{reads, writes: Map::<Address, RawPage>::empty()},
            ),
            self.branch_query_matches(branch_idx, key, msg, receipt, to_branch_nodes(reads)),
        ensures
            self.i().sealed_stack.sealed_branch_at(branch_idx).query(key) == msg,
    {
        let r = receipt.unwrap();
        let root = self.sealed_roots_i()[branch_idx as int];
        let branch = self.i().sealed_stack.sealed_branch_at(branch_idx);
        assert(0 <= branch_idx as int);
        assert((branch_idx as int) < self.cached_branches.len() - 1);
        assert(self.cached_branches[branch_idx as int].wf());
        assert(self.cached_branches[branch_idx as int].sealed);
        assert(self.cached_branches[branch_idx as int].root is Some);
        assert(root == self.cached_branches[branch_idx as int].root.unwrap());
        assert(branch.root == root);
        assert(r.key == key);
        assert(self.cached_branches[branch_idx as int].query_result(r, to_branch_nodes(reads)) == msg);
        assert(r.result() == msg);

        assert(self.i().sealed_stack.wf());
        assert(self.i().sealed_stack.sealed_roots.to_set().contains(root));
        assert((#[trigger] self.i().sealed_stack.sealed_disk.get_branch(root)).valid_sealed_branch());
        assert(branch.valid_sealed_branch());
        assert(branch.inv());

        assert forall |addr: Address|
            #[trigger] branch.disk_view.entries.contains_key(addr)
            implies {
                &&& self.available_branch_nodes().contains_key(addr)
                &&& branch.disk_view.entries[addr] == self.available_branch_nodes()[addr]
            }
        by {
            assert(branch.disk_view.entries == self.sealed_disk_i().entries);
            assert(self.sealed_disk_i().entries.contains_key(addr));
        }
        receipt_query_matches_branch_query(
            self,
            self.cache,
            branch,
            reads,
            Map::<Address, RawPage>::empty(),
            r,
        );
        assert(branch.query(key) == msg);
    }

    proof fn sealed_query_up_to_all_nop(
        self,
        end: nat,
        key: crate::spec::KeyType_t::Key,
        query_receipts: Seq<Option<LoadedPathReceipt>>,
        reads: Map<Address, RawPage>,
    )
        requires
            self.refinement_wf(),
            end <= self.historical_len(),
            query_receipts.len() == self.cached_branches.len(),
            Cache::State::next(
                self.cache,
                self.cache,
                Cache::Label::Access{reads, writes: Map::<Address, RawPage>::empty()},
            ),
            forall |j: int|
                0 <= j < end
                ==> self.branch_query_returns_nop(j as nat, key, query_receipts[j], to_branch_nodes(reads)),
        ensures
            self.i().sealed_stack.query_up_to(end, key) == (Message::Update{delta: nop_delta()}),
        decreases end,
    {
        if end == 0 {
        } else {
            let idx = (end - 1) as nat;
            self.sealed_branch_query_matches_stack_sealed(
                idx,
                key,
                Message::Update{delta: nop_delta()},
                query_receipts[idx as int],
                reads,
            );
            self.sealed_query_up_to_all_nop((end - 1) as nat, key, query_receipts, reads);
            assert(is_nop_message(self.i().sealed_stack.sealed_branch_at(idx).query(key)));
        }
    }

    proof fn sealed_query_up_to_hit(
        self,
        end: nat,
        branch_idx: nat,
        key: crate::spec::KeyType_t::Key,
        msg: Message,
        query_receipts: Seq<Option<LoadedPathReceipt>>,
        reads: Map<Address, RawPage>,
    )
        requires
            self.refinement_wf(),
            branch_idx < end <= self.historical_len(),
            query_receipts.len() == self.cached_branches.len(),
            msg != (Message::Update{delta: nop_delta()}),
            Cache::State::next(
                self.cache,
                self.cache,
                Cache::Label::Access{reads, writes: Map::<Address, RawPage>::empty()},
            ),
            self.branch_query_matches(
                branch_idx,
                key,
                msg,
                query_receipts[branch_idx as int],
                to_branch_nodes(reads),
            ),
            forall |j: int|
                branch_idx < j < end
                ==> self.branch_query_returns_nop(j as nat, key, query_receipts[j], to_branch_nodes(reads)),
        ensures
            self.i().sealed_stack.query_up_to(end, key) == msg,
        decreases end - branch_idx,
    {
        let idx = (end - 1) as nat;
        if idx == branch_idx {
            self.sealed_branch_query_matches_stack_sealed(
                branch_idx,
                key,
                msg,
                query_receipts[branch_idx as int],
                reads,
            );
            assert(!is_nop_message(msg));
        } else {
            assert(branch_idx < idx);
            self.sealed_branch_query_matches_stack_sealed(
                idx,
                key,
                Message::Update{delta: nop_delta()},
                query_receipts[idx as int],
                reads,
            );
            self.sealed_query_up_to_hit((end - 1) as nat, branch_idx, key, msg, query_receipts, reads);
            assert(is_nop_message(self.i().sealed_stack.sealed_branch_at(idx).query(key)));
        }
    }

    proof fn query_matches_stack_query(
        self,
        branch_idx: nat,
        key: crate::spec::KeyType_t::Key,
        msg: Message,
        query_receipts: Seq<Option<LoadedPathReceipt>>,
        reads: Map<Address, RawPage>,
    )
        requires
            self.refinement_wf(),
            branch_idx < self.cached_branches.len(),
            query_receipts.len() == self.cached_branches.len(),
            Cache::State::next(
                self.cache,
                self.cache,
                Cache::Label::Access{reads, writes: Map::<Address, RawPage>::empty()},
            ),
            self.query_matches_stack(branch_idx, key, msg, query_receipts, to_branch_nodes(reads)),
        ensures
            self.i().query(key) == msg,
    {
        let active_idx = self.active_idx() as nat;
        let hist_len = self.historical_len();
        assert(active_idx == hist_len);
        if msg == (Message::Update{delta: nop_delta()}) {
            self.active_branch_query_matches_stack_active(
                key,
                msg,
                query_receipts[active_idx as int],
                reads,
            );
            assert(active_branch_query_or_nop(self.i().active_branch, key)
                == Message::Update{delta: nop_delta()});
            self.sealed_query_up_to_all_nop(hist_len, key, query_receipts, reads);
            assert(self.i().query(key) == msg);
        } else if branch_idx == active_idx {
            self.active_branch_query_matches_stack_active(
                key,
                msg,
                query_receipts[active_idx as int],
                reads,
            );
            assert(!is_nop_message(active_branch_query_or_nop(self.i().active_branch, key)));
            assert(self.i().query(key) == msg);
        } else {
            assert(branch_idx < hist_len);
            self.active_branch_query_matches_stack_active(
                key,
                Message::Update{delta: nop_delta()},
                query_receipts[active_idx as int],
                reads,
            );
            assert(active_branch_query_or_nop(self.i().active_branch, key)
                == Message::Update{delta: nop_delta()});
            self.sealed_query_up_to_hit(hist_len, branch_idx, key, msg, query_receipts, reads);
            assert(self.i().query(key) == msg);
        }
    }

    proof fn append_to_empty_active_branch_matches(
        self,
        post: Self,
        keys: Seq<Key>,
        msgs: Seq<Message>,
        writes: Map<Address, RawPage>,
        init_root: Address,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            self.active_cached_branch().can_initialize(
                self.mini_allocator,
                init_root,
                keys,
                msgs,
                to_branch_nodes(writes),
            ),
            Cache::State::next(
                self.cache,
                post.cache,
                Cache::Label::Access{reads: Map::<Address, RawPage>::empty(), writes},
            ),
            post.cached_branches
                == self.cached_branches.update(
                    self.active_idx(),
                    self.active_cached_branch().initialize(init_root, keys, msgs, to_branch_nodes(writes)),
                ),
            post.mini_allocator == self.mini_allocator.allocate(init_root),
            post.disk == self.disk,
        ensures
            post.overlay_branch_entries() == map!{
                init_root => AllocationBranchNode::Leaf{keys, msgs}
            },
            post.i().active_branch == self.i().active_branch.branch_initialize(init_root, keys, msgs),
    {
        let write_nodes = to_branch_nodes(writes);
        assert(write_nodes == crate::implementation::CachedBranch_v::loaded_initialize_write_nodes(
            init_root,
            keys,
            msgs,
        ));
        assert(write_nodes.contains_key(init_root));
        assert(writes.contains_key(init_root));
        ConcreteBranch::State::cache_access_write_visible_as_branch_node(
            self,
            post,
            Map::<Address, RawPage>::empty(),
            writes,
            init_root,
        );
        assert(post.available_branch_nodes()[init_root]
            == AllocationBranchNode::Leaf{keys, msgs});

        let singleton = map!{init_root => AllocationBranchNode::Leaf{keys, msgs}};
        assert(post.active_branch_addrs() == set!{init_root}) by {
            assert forall |addr: Address|
                #[trigger] post.active_branch_addrs().contains(addr)
                <==> set!{init_root}.contains(addr)
            by {
                crate::implementation::ConcreteBranch_v::mini_allocator_allocate_page_is_reserved(
                    self.mini_allocator,
                    init_root,
                    addr,
                );
                if post.active_branch_addrs().contains(addr) {
                    assert(post.mini_allocator.page_is_reserved(addr));
                    if addr != init_root {
                        assert(self.mini_allocator.page_is_reserved(addr));
                        crate::implementation::ConcreteBranch_v::mini_allocator_no_reserved_pages(
                            self.mini_allocator,
                            addr,
                        );
                        assert(false);
                    }
                } else if addr == init_root {
                    assert(post.mini_allocator.page_is_reserved(init_root));
                    assert(post.available_branch_nodes().contains_key(init_root));
                }
            };
        }

        assert(post.overlay_branch_entries() == singleton) by {
            assert forall |addr: Address|
                #[trigger] post.overlay_branch_entries().contains_key(addr)
                <==> singleton.contains_key(addr)
            by {
                if post.overlay_branch_entries().contains_key(addr) {
                    assert(post.active_branch_addrs().contains(addr));
                    assert(addr == init_root);
                } else if singleton.contains_key(addr) {
                    assert(addr == init_root);
                    assert(post.active_branch_addrs().contains(init_root));
                }
            }
            assert forall |addr: Address|
                #[trigger] post.overlay_branch_entries().contains_key(addr)
                implies post.overlay_branch_entries()[addr] == singleton[addr]
            by {
                assert(addr == init_root);
                assert(post.available_branch_nodes()[init_root]
                    == AllocationBranchNode::Leaf{keys, msgs});
            }
            assert_maps_equal!(post.overlay_branch_entries(), singleton);
        }

        assert(self.i().active_branch.branch is None);
        assert(post.active_cached_branch().root == Some(init_root));
        assert(post.overlay_branch() == Some(LinkedBranch{
            root: init_root,
            disk_view: crate::betree::LinkedBranch_v::DiskView{entries: singleton},
        }));
        assert(post.i().active_branch.branch == Some(LinkedBranch{
            root: init_root,
            disk_view: crate::betree::LinkedBranch_v::DiskView{entries: singleton},
        }));
        assert(post.i().active_branch.mini_allocator == self.mini_allocator.allocate(init_root));
        assert(self.i().active_branch.branch_initialize(init_root, keys, msgs).branch
            == post.i().active_branch.branch);
        assert(self.i().active_branch.branch_initialize(init_root, keys, msgs).mini_allocator
            == post.i().active_branch.mini_allocator);
        assert(post.i().active_branch == self.i().active_branch.branch_initialize(init_root, keys, msgs));
    }

    proof fn grow_active_branch_matches(
        self,
        post: Self,
        new_root_addr: Address,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            self.active_cached_branch().can_grow(
                self.mini_allocator,
                new_root_addr,
                to_branch_nodes(reads),
                to_branch_nodes(writes),
            ),
            Cache::State::next(self.cache, post.cache, Cache::Label::Access{reads, writes}),
            post.cached_branches == self.cached_branches.update(
                self.active_idx(),
                self.active_cached_branch().grow(
                    self.mini_allocator,
                    new_root_addr,
                    to_branch_nodes(reads),
                    to_branch_nodes(writes),
                ),
            ),
            post.mini_allocator == self.mini_allocator.allocate(new_root_addr),
            post.disk == self.disk,
        ensures
            self.i().active_branch.can_grow(new_root_addr),
            post.i().active_branch == self.i().active_branch.branch_grow(new_root_addr),
    {
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        let old_root = self.active_cached_branch().root.unwrap();
        let branch = self.overlay_branch().unwrap();
        let grown = branch.grow(new_root_addr);
        let new_root_node = AllocationBranchNode::Index{
            pivots: seq![],
            children: seq![old_root],
            aux_ptr: None,
        };

        assert(self.i().active_branch.branch == Some(branch));
        assert(self.i().active_branch.inv());
        assert(branch.inv());
        assert(self.i().active_branch.mini_allocator.can_allocate(new_root_addr));
        assert(write_nodes == crate::implementation::CachedBranch_v::loaded_grow_write_nodes(
            old_root,
            new_root_addr,
        ));
        assert(write_nodes.contains_key(new_root_addr));
        assert(writes.contains_key(new_root_addr));
        ConcreteBranch::State::cache_access_write_visible_as_branch_node(
            self,
            post,
            reads,
            writes,
            new_root_addr,
        );
        assert(post.available_branch_nodes()[new_root_addr] == new_root_node);
        assert(!self.mini_allocator.page_is_reserved(new_root_addr));
        assert(!branch.disk_view.entries.contains_key(new_root_addr)) by {
            if branch.disk_view.entries.contains_key(new_root_addr) {
                assert(self.overlay_branch_entries().contains_key(new_root_addr));
                assert(self.active_branch_pages_reserved_in_allocator());
                assert(self.mini_allocator.page_is_reserved(new_root_addr));
                assert(false);
            }
        }
        assert(branch.disk_view.is_fresh(set!{new_root_addr}));
        assert(branch.can_grow(new_root_addr));
        assert(self.i().active_branch.can_grow(new_root_addr));

        assert forall |addr: Address|
            #[trigger] writes.contains_key(addr)
            implies addr == new_root_addr
        by {
            assert(write_nodes.contains_key(addr));
        }

        assert forall |addr: Address|
            addr != new_root_addr
            implies (#[trigger] post.available_branch_nodes().contains_key(addr)
                <==> self.available_branch_nodes().contains_key(addr))
        by {
            assert(!writes.contains_key(addr));
            Cache::State::access_unwritten_addr_unchanged(
                self.cache,
                post.cache,
                reads,
                writes,
                addr,
            );
            if self.has_cached_page(addr) {
                assert(post.has_cached_page(addr));
            } else {
                assert(!post.has_cached_page(addr));
                assert(post.disk.content.contains_key(addr) == self.disk.content.contains_key(addr));
            }
        }
        assert forall |addr: Address|
            addr != new_root_addr
            && #[trigger] post.available_branch_nodes().contains_key(addr)
            implies post.available_branch_nodes()[addr] == self.available_branch_nodes()[addr]
        by {
            assert(!writes.contains_key(addr));
            Cache::State::access_unwritten_addr_unchanged(
                self.cache,
                post.cache,
                reads,
                writes,
                addr,
            );
            if self.has_cached_page(addr) {
                assert(post.has_cached_page(addr));
                assert(post.cache_raw_page(addr) == self.cache_raw_page(addr));
            } else {
                assert(!post.has_cached_page(addr));
            }
        }

        assert(post.overlay_branch_entries() == grown.disk_view.entries) by {
            assert forall |addr: Address|
                #[trigger] post.overlay_branch_entries().contains_key(addr)
                <==> grown.disk_view.entries.contains_key(addr)
            by {
                crate::implementation::ConcreteBranch_v::mini_allocator_allocate_page_is_reserved(
                    self.mini_allocator,
                    new_root_addr,
                    addr,
                );
                if post.overlay_branch_entries().contains_key(addr) {
                    assert(post.mini_allocator.page_is_reserved(addr));
                    if addr == new_root_addr {
                        assert(grown.disk_view.entries.contains_key(addr));
                    } else {
                        assert(self.mini_allocator.page_is_reserved(addr));
                        assert(post.available_branch_nodes().contains_key(addr));
                        assert(self.available_branch_nodes().contains_key(addr));
                        assert(self.overlay_branch_entries().contains_key(addr));
                        assert(branch.disk_view.entries.contains_key(addr));
                        assert(grown.disk_view.entries.contains_key(addr));
                    }
                } else if grown.disk_view.entries.contains_key(addr) {
                    if addr == new_root_addr {
                        assert(post.mini_allocator.page_is_reserved(addr));
                        assert(post.available_branch_nodes().contains_key(addr));
                        assert(post.overlay_branch_entries().contains_key(addr));
                    } else {
                        assert(branch.disk_view.entries.contains_key(addr));
                        assert(self.overlay_branch_entries().contains_key(addr));
                        assert(self.mini_allocator.page_is_reserved(addr));
                        assert(post.mini_allocator.page_is_reserved(addr));
                        assert(post.available_branch_nodes().contains_key(addr));
                        assert(post.overlay_branch_entries().contains_key(addr));
                    }
                }
            }
            assert forall |addr: Address|
                #[trigger] post.overlay_branch_entries().contains_key(addr)
                implies post.overlay_branch_entries()[addr] == grown.disk_view.entries[addr]
            by {
                if addr == new_root_addr {
                    assert(post.overlay_branch_entries()[addr] == post.available_branch_nodes()[addr]);
                    assert(grown.disk_view.entries[addr] == new_root_node);
                } else {
                    assert(post.available_branch_nodes()[addr] == self.available_branch_nodes()[addr]);
                    assert(post.overlay_branch_entries()[addr] == post.available_branch_nodes()[addr]);
                    assert(self.overlay_branch_entries()[addr] == self.available_branch_nodes()[addr]);
                    assert(self.overlay_branch_entries()[addr] == branch.disk_view.entries[addr]);
                    assert(grown.disk_view.entries[addr] == branch.disk_view.entries[addr]);
                }
            }
            assert_maps_equal!(post.overlay_branch_entries(), grown.disk_view.entries);
        }

        assert(post.overlay_branch() == Some(grown));
        assert(post.i().active_branch.branch == Some(grown));
        assert(post.i().active_branch.mini_allocator == self.mini_allocator.allocate(new_root_addr));
        assert(post.i().active_branch == self.i().active_branch.branch_grow(new_root_addr));
    }

    proof fn split_active_branch_matches(
        self,
        post: Self,
        new_child_addr: Address,
        split_arg: crate::betree::LinkedBranch_v::SplitArg,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        receipt: LoadedPathReceipt,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            self.active_cached_branch().can_split(
                self.mini_allocator,
                new_child_addr,
                receipt,
                split_arg,
                to_branch_nodes(reads),
                to_branch_nodes(writes),
            ),
            self.active_managed_reads_agree(
                receipt.needed_addrs().insert(receipt.child_addr()),
                to_branch_nodes(reads),
            ),
            Cache::State::next(self.cache, post.cache, Cache::Label::Access{reads, writes}),
            post.cached_branches == self.cached_branches.update(
                self.active_idx(),
                self.active_cached_branch().split(
                    self.mini_allocator,
                    new_child_addr,
                    receipt,
                    split_arg,
                    to_branch_nodes(reads),
                    to_branch_nodes(writes),
                ),
            ),
            post.mini_allocator == self.mini_allocator.allocate(new_child_addr),
            post.disk == self.disk,
        ensures
            ({
                let path = Path{
                    branch: self.overlay_branch().unwrap(),
                    key: split_arg.get_pivot(),
                    depth: receipt.depth(),
                };
                &&& self.i().active_branch.can_split(new_child_addr, path, split_arg)
                &&& post.i().active_branch
                    == self.i().active_branch.branch_split(new_child_addr, path, split_arg)
            }),
    {
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        let branch = self.overlay_branch().unwrap();
        let path = Path{branch, key: split_arg.get_pivot(), depth: receipt.depth()};
        let split_branch = branch.split(new_child_addr, path, split_arg);
        let parent_addr = receipt.target().addr;
        let child_addr = receipt.child_addr();

        assert(self.i().active_branch.branch == Some(branch));
        assert(self.i().active_branch.inv());
        assert(branch.inv());
        assert(self.i().active_branch.mini_allocator.can_allocate(new_child_addr));
        assert(receipt.key == split_arg.get_pivot());
        assert(write_nodes == crate::implementation::CachedBranch_v::loaded_split_write_nodes(
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
        ConcreteBranch::State::cache_access_write_visible_as_branch_node(
            self,
            post,
            reads,
            writes,
            parent_addr,
        );
        ConcreteBranch::State::cache_access_write_visible_as_branch_node(
            self,
            post,
            reads,
            writes,
            child_addr,
        );
        ConcreteBranch::State::cache_access_write_visible_as_branch_node(
            self,
            post,
            reads,
            writes,
            new_child_addr,
        );

        assert(!self.mini_allocator.page_is_reserved(new_child_addr));
        assert(!branch.disk_view.entries.contains_key(new_child_addr)) by {
            if branch.disk_view.entries.contains_key(new_child_addr) {
                assert(self.overlay_branch_entries().contains_key(new_child_addr));
                assert(self.active_branch_pages_reserved_in_allocator());
                assert(self.mini_allocator.page_is_reserved(new_child_addr));
                assert(false);
            }
        }
        assert(branch.disk_view.is_fresh(set!{new_child_addr}));

        assert(receipt.needed_addrs().contains(parent_addr)) by {
            let i = receipt.lines.len() - 1;
            assert(0 <= i < receipt.lines.len());
            assert(receipt.lines[i].addr == parent_addr);
        }
        assert(receipt.needed_addrs().insert(child_addr).contains(parent_addr));
        assert(receipt.needed_addrs().insert(child_addr).contains(child_addr));
        assert(read_nodes[parent_addr] == self.overlay_branch_entries()[parent_addr]);
        assert(read_nodes[child_addr] == self.overlay_branch_entries()[child_addr]);
        assert(branch.disk_view.entries.contains_key(child_addr));
        assert(read_nodes[child_addr] == branch.disk_view.entries[child_addr]);

        assert forall |addr: Address|
            #[trigger] branch.disk_view.entries.contains_key(addr)
            implies {
                &&& self.available_branch_nodes().contains_key(addr)
                &&& branch.disk_view.entries[addr] == self.available_branch_nodes()[addr]
            }
        by {
            assert(self.overlay_branch_entries().contains_key(addr));
            assert(self.active_branch_entries().contains_key(addr));
            assert(self.active_branch_addrs().contains(addr));
        }
        receipt_path_valid_for_split(
            self,
            post.cache,
            branch,
            branch.the_ranking(),
            reads,
            writes,
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

        assert forall |addr: Address|
            #[trigger] writes.contains_key(addr)
            implies addr == parent_addr || addr == child_addr || addr == new_child_addr
        by {
            assert(write_nodes.contains_key(addr));
        }
        assert forall |addr: Address|
            addr != parent_addr
            && addr != child_addr
            && addr != new_child_addr
            implies (#[trigger] post.available_branch_nodes().contains_key(addr)
                <==> self.available_branch_nodes().contains_key(addr))
        by {
            assert(!writes.contains_key(addr));
            Cache::State::access_unwritten_addr_unchanged(
                self.cache,
                post.cache,
                reads,
                writes,
                addr,
            );
            if self.has_cached_page(addr) {
                assert(post.has_cached_page(addr));
            } else {
                assert(!post.has_cached_page(addr));
                assert(post.disk.content.contains_key(addr) == self.disk.content.contains_key(addr));
            }
        }
        assert forall |addr: Address|
            addr != parent_addr
            && addr != child_addr
            && addr != new_child_addr
            && #[trigger] post.available_branch_nodes().contains_key(addr)
            implies post.available_branch_nodes()[addr] == self.available_branch_nodes()[addr]
        by {
            assert(!writes.contains_key(addr));
            Cache::State::access_unwritten_addr_unchanged(
                self.cache,
                post.cache,
                reads,
                writes,
                addr,
            );
            if self.has_cached_page(addr) {
                assert(post.has_cached_page(addr));
                assert(post.cache_raw_page(addr) == self.cache_raw_page(addr));
            } else {
                assert(!post.has_cached_page(addr));
            }
        }

        assert(post.overlay_branch_entries() == split_branch.disk_view.entries) by {
            assert forall |addr: Address|
                #[trigger] post.overlay_branch_entries().contains_key(addr)
                <==> split_branch.disk_view.entries.contains_key(addr)
            by {
                crate::implementation::ConcreteBranch_v::mini_allocator_allocate_page_is_reserved(
                    self.mini_allocator,
                    new_child_addr,
                    addr,
                );
                if post.overlay_branch_entries().contains_key(addr) {
                    assert(post.mini_allocator.page_is_reserved(addr));
                    if addr == new_child_addr {
                        assert(split_branch.disk_view.entries.contains_key(addr));
                    } else {
                        assert(self.mini_allocator.page_is_reserved(addr));
                        if addr == parent_addr || addr == child_addr {
                            assert(self.overlay_branch_entries().contains_key(addr));
                        } else {
                            assert(post.available_branch_nodes().contains_key(addr));
                            assert(self.available_branch_nodes().contains_key(addr));
                            assert(self.overlay_branch_entries().contains_key(addr));
                        }
                        assert(branch.disk_view.entries.contains_key(addr));
                        assert(split_branch.disk_view.entries.contains_key(addr));
                    }
                } else if split_branch.disk_view.entries.contains_key(addr) {
                    if addr == new_child_addr {
                        assert(post.mini_allocator.page_is_reserved(addr));
                        assert(post.available_branch_nodes().contains_key(addr));
                        assert(post.overlay_branch_entries().contains_key(addr));
                    } else {
                        assert(branch.disk_view.entries.contains_key(addr));
                        assert(self.overlay_branch_entries().contains_key(addr));
                        assert(self.mini_allocator.page_is_reserved(addr));
                        assert(post.mini_allocator.page_is_reserved(addr));
                        if addr == parent_addr || addr == child_addr {
                            assert(post.available_branch_nodes().contains_key(addr));
                        } else {
                            assert(post.available_branch_nodes().contains_key(addr));
                        }
                        assert(post.overlay_branch_entries().contains_key(addr));
                    }
                }
            }
            assert forall |addr: Address|
                #[trigger] post.overlay_branch_entries().contains_key(addr)
                implies post.overlay_branch_entries()[addr] == split_branch.disk_view.entries[addr]
            by {
                if addr == parent_addr {
                    assert(post.overlay_branch_entries()[addr] == post.available_branch_nodes()[addr]);
                    assert(post.available_branch_nodes()[addr] == write_nodes[parent_addr]);
                    assert(split_branch.disk_view.entries[addr] == write_nodes[parent_addr]);
                } else if addr == child_addr {
                    assert(post.overlay_branch_entries()[addr] == post.available_branch_nodes()[addr]);
                    assert(post.available_branch_nodes()[addr] == write_nodes[child_addr]);
                    assert(split_branch.disk_view.entries[addr] == write_nodes[child_addr]);
                } else if addr == new_child_addr {
                    assert(post.overlay_branch_entries()[addr] == post.available_branch_nodes()[addr]);
                    assert(post.available_branch_nodes()[addr] == write_nodes[new_child_addr]);
                    assert(split_branch.disk_view.entries[addr] == write_nodes[new_child_addr]);
                } else {
                    assert(post.available_branch_nodes()[addr] == self.available_branch_nodes()[addr]);
                    assert(post.overlay_branch_entries()[addr] == post.available_branch_nodes()[addr]);
                    assert(self.overlay_branch_entries()[addr] == self.available_branch_nodes()[addr]);
                    assert(self.overlay_branch_entries()[addr] == branch.disk_view.entries[addr]);
                    assert(split_branch.disk_view.same_except(
                        branch.disk_view,
                        set!{parent_addr, child_addr, new_child_addr},
                    ));
                    assert(split_branch.disk_view.entries[addr] == branch.disk_view.entries[addr]);
                }
            }
            assert_maps_equal!(post.overlay_branch_entries(), split_branch.disk_view.entries);
        }

        assert(post.overlay_branch() == Some(split_branch));
        assert(post.i().active_branch.branch == Some(split_branch));
        assert(post.i().active_branch.mini_allocator == self.mini_allocator.allocate(new_child_addr));
        assert(post.i().active_branch == self.i().active_branch.branch_split(new_child_addr, path, split_arg));
    }

    pub proof fn query_refines(
        self,
        post: Self,
        lbl: ConcreteBranch::Label,
        reads: Map<Address, RawPage>,
        query_receipts: Seq<Option<LoadedPathReceipt>>,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            ConcreteBranch::State::query(self, post, lbl, reads, query_receipts),
        ensures
            AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(ConcreteBranch::State::query);
        reveal(AllocationBranchStack::State::next);
        reveal(AllocationBranchStack::State::next_by);
        match lbl {
            ConcreteBranch::Label::Query{branch_idx, key, msg} => {
                let cache_lbl = Cache::Label::Access{
                    reads,
                    writes: Map::<Address, RawPage>::empty(),
                };
                assert(Cache::State::next(self.cache, self.cache, cache_lbl));
                self.query_matches_stack_query(branch_idx, key, msg, query_receipts, reads);
                assert(self.i().query(key) == msg);
                assert(self.i() == post.i());
                assert(AllocationBranchStack::State::query_step(
                    self.i(),
                    post.i(),
                    self.label_to_stack(lbl),
                ));
                assert(AllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_stack(lbl),
                    AllocationBranchStack::Step::query_step(),
                ));
            }
            _ => {
                assert(false);
            }
        }
        assert(AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
        self.stack_next_implies_abstract_next(post, lbl);
    }

    pub proof fn append_to_active_refines(
        self,
        post: Self,
        lbl: ConcreteBranch::Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        receipt: LoadedPathReceipt,
        new_cache: crate::implementation::Cache_v::Cache::State,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            ConcreteBranch::State::append(self, post, lbl, reads, writes, receipt, new_cache),
        ensures
            AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(ConcreteBranch::State::append);
        reveal(AllocationBranchStack::State::next);
        reveal(AllocationBranchStack::State::next_by);
        match lbl {
            ConcreteBranch::Label::Append{keys, msgs} => {
                let read_nodes = to_branch_nodes(reads);
                let write_nodes = to_branch_nodes(writes);
                let cache_lbl = Cache::Label::Access{reads, writes};
                let branch = self.overlay_branch().unwrap();
                let path = Path{branch, key: keys[0], depth: receipt.depth()};
                let target = receipt.target().addr;
                let appended = branch.append(keys, msgs, path);

                assert(Cache::State::next(self.cache, new_cache, cache_lbl));
                assert(post.cache == new_cache);
                assert(post.disk == self.disk);
                assert(post.branch_summary == self.branch_summary);
                assert(post.seq_end == self.seq_end + keys.len());
                assert(post.mini_allocator == self.mini_allocator);
                assert(post.cached_branches.len() == self.cached_branches.len());
                assert(post.active_idx() == self.active_idx());
                assert(self.i().active_branch.branch == Some(branch));
                assert(self.i().active_branch.inv());
                assert(branch.inv());

                assert forall |addr: Address|
                    #[trigger] branch.disk_view.entries.contains_key(addr)
                    implies {
                        &&& self.available_branch_nodes().contains_key(addr)
                        &&& branch.disk_view.entries[addr] == self.available_branch_nodes()[addr]
                    }
                by {
                    assert(branch.disk_view.entries == self.active_branch_entries());
                    assert(self.active_branch_entries().contains_key(addr));
                    assert(self.active_branch_addrs().contains(addr));
                }
                receipt_path_valid_for_append(
                    self,
                    new_cache,
                    branch,
                    branch.the_ranking(),
                    reads,
                    writes,
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

                assert(write_nodes == crate::implementation::CachedBranch_v::loaded_append_write_nodes(
                    receipt,
                    keys,
                    msgs,
                ));
                assert(write_nodes.contains_key(target));
                assert(writes.contains_key(target));
                assert(receipt.needed_addrs().contains(target)) by {
                    let i = receipt.lines.len() - 1;
                    assert(0 <= i < receipt.lines.len());
                    assert(receipt.lines[i].addr == target);
                }
                assert(read_nodes[target] == self.available_branch_nodes()[target]);
                assert(read_nodes[target] == receipt.target().node);
                assert(self.available_branch_nodes()[target] == receipt.target().node);
                assert(self.available_branch_nodes()[target] is Leaf);
                ConcreteBranch::State::cache_access_write_visible_as_branch_node(
                    self,
                    post,
                    reads,
                    writes,
                    target,
                );
                assert(post.available_branch_nodes()[target] == write_nodes[target]);
                assert(post.available_branch_nodes()[target] is Leaf);

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
                    assert(self.active_branch_pages_in_allocator());
                    assert(self.mini_allocator.all_aus().contains(target.au));
                }
                ConcreteBranch::State::sealed_disk_i_unchanged_by_cache_access(
                    self,
                    post,
                    reads,
                    writes,
                );
                assert(post.sealed_roots_i() =~= self.sealed_roots_i()) by {
                    assert forall |i: int| 0 <= i < self.sealed_roots_i().len()
                        implies post.sealed_roots_i()[i] == self.sealed_roots_i()[i] by {
                        assert(i < self.cached_branches.len() - 1);
                        assert(i != self.active_idx());
                        assert(post.cached_branches[i] == self.cached_branches[i]);
                    }
                }
                assert(post.i().sealed_stack == self.i().sealed_stack);
                assert(post.i().branch_summary == self.i().branch_summary);

                assert(self.available_branch_nodes().dom() == post.available_branch_nodes().dom()) by {
                    assert forall |addr: Address|
                        #[trigger] self.available_branch_nodes().contains_key(addr)
                        <==> post.available_branch_nodes().contains_key(addr)
                    by {
                        if addr == target {
                            assert(self.available_branch_nodes().contains_key(target));
                            assert(post.available_branch_nodes().contains_key(target));
                        } else {
                            assert(!writes.contains_key(addr));
                            Cache::State::access_unwritten_addr_unchanged(
                                self.cache,
                                post.cache,
                                reads,
                                writes,
                                addr,
                            );
                        }
                    }
                }
                assert forall |addr: Address|
                    addr != target && #[trigger] self.available_branch_nodes().contains_key(addr)
                    implies post.available_branch_nodes()[addr] == self.available_branch_nodes()[addr]
                by {
                    assert(!writes.contains_key(addr));
                    Cache::State::access_unwritten_addr_unchanged(
                        self.cache,
                        post.cache,
                        reads,
                        writes,
                        addr,
                    );
                    if self.has_cached_page(addr) {
                        assert(post.has_cached_page(addr));
                        assert(post.cache_raw_page(addr) == self.cache_raw_page(addr));
                    } else {
                        assert(!post.has_cached_page(addr));
                    }
                }
                assert(post.cached_branches == self.cached_branches) by {
                    assert(post.active_cached_branch() == self.active_cached_branch().append(
                        receipt,
                        keys,
                        msgs,
                        read_nodes,
                        write_nodes,
                    ));
                    assert(post.active_cached_branch() == self.active_cached_branch());
                    assert forall |i: int|
                        0 <= i < self.cached_branches.len()
                        implies post.cached_branches[i] == self.cached_branches[i]
                    by {
                        if i == self.active_idx() {
                            assert(post.cached_branches[i] == post.active_cached_branch());
                        }
                    }
                }
                ConcreteBranch::State::overlay_addrs_same_after_leaf_update(
                    self,
                    post,
                    self.active_idx() as nat,
                    target,
                );

                assert(appended == path.substitute(path.target().append_leaf(keys, msgs)));
                assert(appended.disk_view == path.target().append_leaf(keys, msgs).disk_view);
                assert(path.target().root() == receipt.target().node);
                assert(write_nodes[target] == AllocationBranchNode::Leaf{
                    keys: path.target().root()->keys + keys,
                    msgs: path.target().root()->msgs + msgs,
                });
                assert(appended.disk_view.entries[target] == write_nodes[target]);
                assert(post.overlay_branch_entries() == appended.disk_view.entries) by {
                    assert forall |addr: Address|
                        #[trigger] post.overlay_branch_entries().contains_key(addr)
                        <==> appended.disk_view.entries.contains_key(addr)
                    by {
                        if post.overlay_branch_entries().contains_key(addr) {
                            assert(post.has_overlay_page(addr));
                            assert(self.has_overlay_page(addr));
                            assert(self.overlay_branch_entries().contains_key(addr));
                            assert(branch.disk_view.entries.contains_key(addr));
                            assert(appended.disk_view.entries.dom() == branch.disk_view.entries.dom());
                        }
                        if appended.disk_view.entries.contains_key(addr) {
                            assert(appended.disk_view.entries.dom() == branch.disk_view.entries.dom());
                            assert(branch.disk_view.entries.contains_key(addr));
                            assert(self.overlay_branch_entries().contains_key(addr));
                            assert(self.has_overlay_page(addr));
                            assert(post.has_overlay_page(addr));
                        }
                    }
                    assert forall |addr: Address|
                        #[trigger] post.overlay_branch_entries().contains_key(addr)
                        implies post.overlay_branch_entries()[addr] == appended.disk_view.entries[addr]
                    by {
                        assert(post.has_overlay_page(addr));
                        assert(self.has_overlay_page(addr));
                        assert(self.overlay_branch_entries().contains_key(addr));
                        if addr == target {
                            assert(post.overlay_branch_entries()[addr] == post.available_branch_nodes()[addr]);
                            assert(appended.disk_view.entries[addr] == write_nodes[addr]);
                        } else {
                            assert(post.available_branch_nodes()[addr] == self.available_branch_nodes()[addr]);
                            assert(post.overlay_branch_entries()[addr] == post.available_branch_nodes()[addr]);
                            assert(self.overlay_branch_entries()[addr] == self.available_branch_nodes()[addr]);
                            assert(self.overlay_branch_entries()[addr] == branch.disk_view.entries[addr]);
                            assert(appended.disk_view.entries[addr] == branch.disk_view.entries[addr]);
                        }
                    }
                    assert_maps_equal!(post.overlay_branch_entries(), appended.disk_view.entries);
                }
                assert(post.overlay_branch() == Some(appended));
                assert(post.i().active_branch.branch == Some(appended));
                assert(post.i().active_branch.mini_allocator == self.mini_allocator);
                assert(post.i().active_branch
                    == self.i().active_branch.branch_append(keys, msgs, path));
                assert(post.i().seq_end == self.i().seq_end + keys.len());

                assert(AllocationBranchStack::State::append_to_active(
                    self.i(),
                    post.i(),
                    self.label_to_stack(lbl),
                    path,
                ));
                assert(AllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_stack(lbl),
                    AllocationBranchStack::Step::append_to_active(path),
                ));
            }
            _ => {
                assert(false);
            }
        }
        assert(AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
        self.stack_next_implies_abstract_next(post, lbl);
    }

    pub proof fn append_to_empty_refines(
        self,
        post: Self,
        lbl: ConcreteBranch::Label,
        writes: Map<Address, RawPage>,
        init_root: Address,
        new_cache: crate::implementation::Cache_v::Cache::State,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            ConcreteBranch::State::append_to_empty(self, post, lbl, writes, init_root, new_cache),
        ensures
            AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(ConcreteBranch::State::append_to_empty);
        reveal(AllocationBranchStack::State::next);
        reveal(AllocationBranchStack::State::next_by);
        match lbl {
            ConcreteBranch::Label::Append{keys, msgs} => {
                let write_nodes = to_branch_nodes(writes);
                let cache_lbl = Cache::Label::Access{
                    reads: Map::<Address, RawPage>::empty(),
                    writes,
                };
                assert(Cache::State::next(self.cache, new_cache, cache_lbl));
                assert(post.cache == new_cache);
                assert(post.disk == self.disk);
                assert(post.branch_summary == self.branch_summary);
                assert(post.seq_end == self.seq_end + keys.len());
                assert(post.cached_branches.len() == self.cached_branches.len());
                assert(post.active_idx() == self.active_idx());

                assert forall |addr: Address|
                    #[trigger] writes.contains_key(addr)
                    implies !summary_aus(self.branch_summary).contains(addr.au)
                by {
                    assert(write_nodes.contains_key(addr));
                    assert(write_nodes == crate::implementation::CachedBranch_v::loaded_initialize_write_nodes(
                        init_root,
                        keys,
                        msgs,
                    ));
                    assert(addr == init_root);
                    assert(self.mini_allocator.all_aus().contains(init_root.au));
                }
                ConcreteBranch::State::sealed_disk_i_unchanged_by_cache_access(
                    self,
                    post,
                    Map::<Address, RawPage>::empty(),
                    writes,
                );
                assert(post.sealed_roots_i() =~= self.sealed_roots_i()) by {
                    assert forall |i: int| 0 <= i < self.sealed_roots_i().len()
                        implies post.sealed_roots_i()[i] == self.sealed_roots_i()[i] by {
                        assert(i < self.cached_branches.len() - 1);
                        assert(i != self.active_idx());
                        assert(post.cached_branches[i] == self.cached_branches[i]);
                    }
                }
                assert(post.i().sealed_stack == self.i().sealed_stack);
                assert(post.i().branch_summary == self.i().branch_summary);

                self.append_to_empty_active_branch_matches(post, keys, msgs, writes, init_root);
                assert(self.i().active_branch.branch is None);
                assert(self.i().active_branch.mini_allocator.can_allocate(init_root));
                assert(self.i().active_branch.can_initialize(init_root, keys, msgs));
                assert(post.i().active_branch
                    == self.i().active_branch.branch_initialize(init_root, keys, msgs));
                assert(post.i().seq_end == self.i().seq_end + keys.len());

                assert(AllocationBranchStack::State::append_to_empty(
                    self.i(),
                    post.i(),
                    self.label_to_stack(lbl),
                    init_root,
                ));
                assert(AllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_stack(lbl),
                    AllocationBranchStack::Step::append_to_empty(init_root),
                ));
            }
            _ => {
                assert(false);
            }
        }
        assert(AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
        self.stack_next_implies_abstract_next(post, lbl);
    }

    pub proof fn grow_refines(
        self,
        post: Self,
        lbl: ConcreteBranch::Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        new_cache: crate::implementation::Cache_v::Cache::State,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            ConcreteBranch::State::grow(self, post, lbl, reads, writes, new_cache),
        ensures
            AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(ConcreteBranch::State::grow);
        reveal(AllocationBranchStack::State::next);
        reveal(AllocationBranchStack::State::next_by);
        match lbl {
            ConcreteBranch::Label::Grow{new_root_addr} => {
                let read_nodes = to_branch_nodes(reads);
                let write_nodes = to_branch_nodes(writes);
                let cache_lbl = Cache::Label::Access{reads, writes};
                assert(Cache::State::next(self.cache, new_cache, cache_lbl));
                assert(post.cache == new_cache);
                assert(post.disk == self.disk);
                assert(post.branch_summary == self.branch_summary);
                assert(post.seq_end == self.seq_end);
                assert(post.cached_branches.len() == self.cached_branches.len());
                assert(post.active_idx() == self.active_idx());

                assert forall |addr: Address|
                    #[trigger] writes.contains_key(addr)
                    implies !summary_aus(self.branch_summary).contains(addr.au)
                by {
                    assert(write_nodes.contains_key(addr));
                    assert(write_nodes == crate::implementation::CachedBranch_v::loaded_grow_write_nodes(
                        self.active_cached_branch().root.unwrap(),
                        new_root_addr,
                    ));
                    assert(addr == new_root_addr);
                    assert(self.mini_allocator.all_aus().contains(new_root_addr.au));
                }
                ConcreteBranch::State::sealed_disk_i_unchanged_by_cache_access(
                    self,
                    post,
                    reads,
                    writes,
                );
                assert(post.sealed_roots_i() =~= self.sealed_roots_i()) by {
                    assert forall |i: int| 0 <= i < self.sealed_roots_i().len()
                        implies post.sealed_roots_i()[i] == self.sealed_roots_i()[i] by {
                        assert(i < self.cached_branches.len() - 1);
                        assert(i != self.active_idx());
                        assert(post.cached_branches[i] == self.cached_branches[i]);
                    }
                }
                assert(post.i().sealed_stack == self.i().sealed_stack);
                assert(post.i().branch_summary == self.i().branch_summary);

                self.grow_active_branch_matches(post, new_root_addr, reads, writes);
                assert(post.i().seq_end == self.i().seq_end);
                assert(AllocationBranchStack::State::internal_grow(
                    self.i(),
                    post.i(),
                    self.label_to_stack(lbl),
                    new_root_addr,
                ));
                assert(AllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_stack(lbl),
                    AllocationBranchStack::Step::internal_grow(new_root_addr),
                ));
            }
            _ => {
                assert(false);
            }
        }
        assert(AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
        self.stack_next_implies_abstract_next(post, lbl);
    }

    pub proof fn split_refines(
        self,
        post: Self,
        lbl: ConcreteBranch::Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        receipt: LoadedPathReceipt,
        new_cache: crate::implementation::Cache_v::Cache::State,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            ConcreteBranch::State::split(self, post, lbl, reads, writes, receipt, new_cache),
        ensures
            AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(ConcreteBranch::State::split);
        reveal(AllocationBranchStack::State::next);
        reveal(AllocationBranchStack::State::next_by);
        match lbl {
            ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg} => {
                let read_nodes = to_branch_nodes(reads);
                let write_nodes = to_branch_nodes(writes);
                let cache_lbl = Cache::Label::Access{reads, writes};
                let branch = self.overlay_branch().unwrap();
                let path = Path{branch, key: split_arg.get_pivot(), depth: receipt.depth()};
                let parent_addr = receipt.target().addr;
                let child_addr = receipt.child_addr();

                assert(Cache::State::next(self.cache, new_cache, cache_lbl));
                assert(post.cache == new_cache);
                assert(post.disk == self.disk);
                assert(post.branch_summary == self.branch_summary);
                assert(post.seq_end == self.seq_end);
                assert(post.cached_branches.len() == self.cached_branches.len());
                assert(post.active_idx() == self.active_idx());

                assert(write_nodes == crate::implementation::CachedBranch_v::loaded_split_write_nodes(
                    receipt,
                    read_nodes,
                    split_arg,
                    new_child_addr,
                ));
                assert(receipt.needed_addrs().contains(parent_addr)) by {
                    let i = receipt.lines.len() - 1;
                    assert(0 <= i < receipt.lines.len());
                    assert(receipt.lines[i].addr == parent_addr);
                }
                assert(receipt.needed_addrs().insert(child_addr).contains(parent_addr));
                assert(receipt.needed_addrs().insert(child_addr).contains(child_addr));
                assert(self.mini_allocator.all_aus().contains(parent_addr.au));
                assert(self.mini_allocator.all_aus().contains(child_addr.au));
                assert forall |addr: Address|
                    #[trigger] writes.contains_key(addr)
                    implies !summary_aus(self.branch_summary).contains(addr.au)
                by {
                    assert(write_nodes.contains_key(addr));
                    if addr == parent_addr {
                        assert(self.mini_allocator.all_aus().contains(parent_addr.au));
                    } else if addr == child_addr {
                        assert(self.mini_allocator.all_aus().contains(child_addr.au));
                    } else {
                        assert(addr == new_child_addr);
                        assert(self.mini_allocator.all_aus().contains(new_child_addr.au));
                    }
                }
                ConcreteBranch::State::sealed_disk_i_unchanged_by_cache_access(
                    self,
                    post,
                    reads,
                    writes,
                );
                assert(post.sealed_roots_i() =~= self.sealed_roots_i()) by {
                    assert forall |i: int| 0 <= i < self.sealed_roots_i().len()
                        implies post.sealed_roots_i()[i] == self.sealed_roots_i()[i] by {
                        assert(i < self.cached_branches.len() - 1);
                        assert(i != self.active_idx());
                        assert(post.cached_branches[i] == self.cached_branches[i]);
                    }
                }
                assert(post.i().sealed_stack == self.i().sealed_stack);
                assert(post.i().branch_summary == self.i().branch_summary);

                self.split_active_branch_matches(
                    post,
                    new_child_addr,
                    split_arg,
                    reads,
                    writes,
                    receipt,
                );
                assert(post.i().seq_end == self.i().seq_end);
                assert(AllocationBranchStack::State::internal_split(
                    self.i(),
                    post.i(),
                    self.label_to_stack(lbl),
                    new_child_addr,
                    path,
                    split_arg,
                ));
                assert(AllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_stack(lbl),
                    AllocationBranchStack::Step::internal_split(new_child_addr, path, split_arg),
                ));
            }
            _ => {
                assert(false);
            }
        }
        assert(AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
        self.stack_next_implies_abstract_next(post, lbl);
    }

    pub proof fn seal_refines(
        self,
        post: Self,
        lbl: ConcreteBranch::Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        new_cache: crate::implementation::Cache_v::Cache::State,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            ConcreteBranch::State::seal(self, post, lbl, reads, writes, new_cache),
        ensures
            AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(ConcreteBranch::State::seal);
        reveal(AllocationBranchStack::State::next);
        reveal(AllocationBranchStack::State::next_by);
        match lbl {
            ConcreteBranch::Label::Seal{aux_ptr} => {
                let read_nodes = to_branch_nodes(reads);
                let write_nodes = to_branch_nodes(writes);
                let cache_lbl = Cache::Label::Access{reads, writes};
                let root = self.active_cached_branch().root.unwrap();
                let branch = self.overlay_branch().unwrap();
                let dealloc_aus = self.i().active_branch.mini_allocator.removable_aus();
                let sealed_active = self.i().active_branch.branch_seal(aux_ptr, dealloc_aus);
                let sealed_branch = sealed_active.branch.unwrap();
                let concrete_sealed_branch = LinkedBranch{
                    root: branch.root,
                    disk_view: crate::betree::LinkedBranch_v::DiskView {
                        entries: self.overlay_branch_entries().union_prefer_right(write_nodes),
                    },
                };

                assert(Cache::State::next(self.cache, new_cache, cache_lbl));
                assert(post.cache == new_cache);
                assert(post.disk == self.disk);
                assert(post.seq_end == self.seq_end);
                assert(post.cached_branches.len() == self.cached_branches.len() + 1);
                assert(post.active_cached_branch() == crate::implementation::CachedBranch_v::CachedBranch::State::empty_active());
                let empty_allocator = crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty();
                assert(empty_allocator.wf());
                assert(empty_allocator.add_aus(Set::<AU>::empty()) == empty_allocator) by {
                    assert(empty_allocator.add_aus(Set::<AU>::empty()).allocs =~= empty_allocator.allocs) by {
                        assert forall |au: AU| #[trigger] empty_allocator.add_aus(Set::<AU>::empty()).allocs.contains_key(au)
                            <==> empty_allocator.allocs.contains_key(au) by { }
                    }
                    assert(empty_allocator.add_aus(Set::<AU>::empty()).curr == empty_allocator.curr);
                }
                assert(post.mini_allocator == empty_allocator);
                assert(post.i().active_branch == AllocationBranch::new(Set::empty()));
                assert(self.i().active_branch.branch == Some(branch));
                assert(self.i().active_branch.inv());
                assert(branch.inv());
                assert(branch.root == root);

                assert(Set::<Address>::empty().insert(root).contains(root));
                assert(self.active_managed_reads_agree(Set::<Address>::empty().insert(root), read_nodes));
                assert(read_nodes[root] == self.overlay_branch_entries()[root]);
                assert(branch.disk_view.entries[root] == self.overlay_branch_entries()[root]);
                assert(read_nodes[root] == branch.root());
                assert(aux_ptr is Some <==> branch.root() is Index);
                if aux_ptr is Some {
                    assert(self.mini_allocator.can_allocate(aux_ptr.unwrap()));
                    assert(self.mini_allocator.reserved_aus().contains(aux_ptr.unwrap().au));
                    assert(!self.mini_allocator.removable_aus().contains(aux_ptr.unwrap().au)) by {
                        if self.mini_allocator.removable_aus().contains(aux_ptr.unwrap().au) {
                            assert(self.mini_allocator.can_remove(aux_ptr.unwrap().au));
                            assert(self.mini_allocator.allocs[aux_ptr.unwrap().au].has_no_outstanding_refs());
                            assert(!self.mini_allocator.reserved_aus().contains(aux_ptr.unwrap().au));
                            assert(false);
                        }
                    }
                }
                assert(self.i().active_branch.can_seal(aux_ptr, dealloc_aus));
                assert(post.branch_summary == self.branch_summary.insert(
                    concrete_sealed_branch.root.au,
                    concrete_sealed_branch.get_summary(),
                ));

                if aux_ptr is Some {
                    let ptr = aux_ptr.unwrap();
                    assert(write_nodes == crate::implementation::CachedBranch_v::loaded_seal_write_nodes(
                        root,
                        read_nodes,
                        aux_ptr,
                        self.mini_allocator.reserved_aus(),
                    ));
                    assert(write_nodes.contains_key(root));
                    assert(write_nodes.contains_key(ptr));
                    assert(write_nodes[root] == AllocationBranchNode::Index{
                        pivots: branch.root()->pivots,
                        children: branch.root()->children,
                        aux_ptr,
                    });
                    assert(write_nodes[ptr] == AllocationBranchNode::Auxiliary(
                        self.mini_allocator.reserved_aus(),
                    ));
                    assert(concrete_sealed_branch == branch.seal(ptr, self.mini_allocator.reserved_aus())) by {
                        assert forall |addr: Address|
                            #[trigger] concrete_sealed_branch.disk_view.entries.contains_key(addr)
                            <==> branch.seal(ptr, self.mini_allocator.reserved_aus()).disk_view.entries.contains_key(addr)
                        by {
                            if concrete_sealed_branch.disk_view.entries.contains_key(addr) {
                                if write_nodes.contains_key(addr) {
                                    assert(addr == root || addr == ptr);
                                } else {
                                    assert(self.overlay_branch_entries().contains_key(addr));
                                    assert(branch.disk_view.entries.contains_key(addr));
                                }
                            } else if branch.seal(ptr, self.mini_allocator.reserved_aus()).disk_view.entries.contains_key(addr) {
                                if addr == root || addr == ptr {
                                    assert(write_nodes.contains_key(addr));
                                } else {
                                    assert(branch.disk_view.entries.contains_key(addr));
                                    assert(self.overlay_branch_entries().contains_key(addr));
                                }
                            }
                        }
                        assert forall |addr: Address|
                            #[trigger] concrete_sealed_branch.disk_view.entries.contains_key(addr)
                            implies concrete_sealed_branch.disk_view.entries[addr]
                                == branch.seal(ptr, self.mini_allocator.reserved_aus()).disk_view.entries[addr]
                        by {
                            if addr == root {
                                assert(concrete_sealed_branch.disk_view.entries[addr] == write_nodes[root]);
                            } else if addr == ptr {
                                assert(concrete_sealed_branch.disk_view.entries[addr] == write_nodes[ptr]);
                            } else {
                                assert(!write_nodes.contains_key(addr));
                                assert(concrete_sealed_branch.disk_view.entries[addr]
                                    == self.overlay_branch_entries()[addr]);
                                assert(self.overlay_branch_entries()[addr] == branch.disk_view.entries[addr]);
                            }
                        }
                        assert_maps_equal!(
                            concrete_sealed_branch.disk_view.entries,
                            branch.seal(ptr, self.mini_allocator.reserved_aus()).disk_view.entries
                        );
                    }
                } else {
                    assert(write_nodes == Map::<Address, AllocationBranchNode>::empty());
                    assert(concrete_sealed_branch == branch);
                }
                assert(sealed_branch == concrete_sealed_branch);
                assert(post.branch_summary == self.branch_summary.insert(
                    sealed_branch.root.au,
                    sealed_branch.get_summary(),
                ));
                assert(sealed_branch.disk_view.entries
                    == self.overlay_branch_entries().union_prefer_right(write_nodes));

                self.i().active_branch.branch_seal_preserves_inv(aux_ptr, dealloc_aus);
                assert(sealed_active.inv());
                assert(sealed_active.sealed);
                assert(sealed_branch.valid_sealed_branch());
                assert(sealed_branch.tight_disk_view_with_summary());

                let sealed_allocator =
                    if aux_ptr is Some {
                        self.mini_allocator.allocate(aux_ptr.unwrap())
                    } else {
                        self.mini_allocator
                    };
                if aux_ptr is Some {
                    crate::implementation::ConcreteBranch_v::mini_allocator_allocate_preserves_all_aus(
                        self.mini_allocator,
                        aux_ptr.unwrap(),
                    );
                    assert(sealed_allocator.all_aus() == self.mini_allocator.all_aus());
                }
                crate::implementation::ConcreteBranch_v::mini_allocator_prune_all_aus_subset(
                    sealed_allocator,
                    dealloc_aus,
                );
                assert(sealed_branch.get_summary() <= self.mini_allocator.all_aus()) by {
                    assert(sealed_branch.get_summary() == sealed_active.mini_allocator.all_aus());
                    assert(sealed_active.mini_allocator == sealed_allocator.prune(dealloc_aus));
                    assert(sealed_active.mini_allocator.all_aus() <= sealed_allocator.all_aus());
                    if aux_ptr is Some {
                        assert(sealed_allocator.all_aus() == self.mini_allocator.all_aus());
                    } else {
                        assert(sealed_allocator == self.mini_allocator);
                    }
                }
                assert(summary_aus(self.branch_summary).disjoint(sealed_branch.get_summary())) by {
                    assert forall |au: AU| #[trigger] summary_aus(self.branch_summary).contains(au)
                        implies !sealed_branch.get_summary().contains(au) by {
                        if sealed_branch.get_summary().contains(au) {
                            assert(self.mini_allocator.all_aus().contains(au));
                            assert(false);
                        }
                    }
                }
                assert(!self.branch_summary.contains_key(sealed_branch.root.au)) by {
                    if self.branch_summary.contains_key(sealed_branch.root.au) {
                        assert(self.branch_summary[sealed_branch.root.au].contains(sealed_branch.root.au));
                        assert(self.branch_summary.values().contains(self.branch_summary[sealed_branch.root.au]));
                        lemma_values_finite(self.branch_summary);
                        lemma_union_set_of_sets_subset(
                            self.branch_summary.values(),
                            self.branch_summary[sealed_branch.root.au],
                        );
                        assert(summary_aus(self.branch_summary).contains(sealed_branch.root.au));
                        assert(sealed_branch.get_summary().contains(sealed_branch.root.au));
                        assert(false);
                    }
                }
                crate::implementation::ConcreteBranch_v::branch_summary_insert_fresh_ensures(
                    self.branch_summary,
                    sealed_branch.root.au,
                    sealed_branch.get_summary(),
                );
                assert(summary_aus(post.branch_summary)
                    == summary_aus(self.branch_summary) + sealed_branch.get_summary());

                let pushed_stack = self.i().sealed_stack.push_branch(sealed_branch);
                assert(post.i().sealed_stack.sealed_disk.entries =~= pushed_stack.sealed_disk.entries) by {
                    let post_entries = post.i().sealed_stack.sealed_disk.entries;
                    let pushed_entries = pushed_stack.sealed_disk.entries;
                    let pre_sealed_entries = self.i().sealed_stack.sealed_disk.entries;
                    let branch_entries = sealed_branch.disk_view.entries;
                    let old_summary = summary_aus(self.branch_summary);
                    let new_summary = sealed_branch.get_summary();
                    assert forall |addr: Address| #[trigger] post_entries.contains_key(addr)
                        <==> pushed_entries.contains_key(addr) by {
                        if post_entries.contains_key(addr) {
                            assert(post.available_branch_nodes().contains_key(addr));
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
                                        assert(branch_entries.contains_key(addr));
                                        assert(new_summary.contains(addr.au));
                                        assert(false);
                                    }
                                }
                                Cache::State::access_unwritten_addr_unchanged(
                                    self.cache,
                                    post.cache,
                                    reads,
                                    writes,
                                    addr,
                                );
                                if post.has_cached_page(addr) {
                                    assert(self.has_cached_page(addr));
                                    assert(post.cache_raw_page(addr) == self.cache_raw_page(addr));
                                    assert(post.available_raw_pages()[addr] == self.available_raw_pages()[addr]);
                                } else {
                                    assert(!self.has_cached_page(addr));
                                    assert(post.disk.content.contains_key(addr));
                                    assert(self.disk.content.contains_key(addr));
                                    assert(post.available_raw_pages()[addr] == self.available_raw_pages()[addr]);
                                }
                                assert(self.available_branch_nodes().contains_key(addr));
                                assert(pre_sealed_entries.contains_key(addr));
                            } else {
                                assert(new_summary.contains(addr.au));
                                if writes.contains_key(addr) {
                                    ConcreteBranch::State::cache_access_write_visible_as_branch_node(
                                        self,
                                        post,
                                        reads,
                                        writes,
                                        addr,
                                    );
                                    assert(write_nodes.contains_key(addr));
                                    assert(branch_entries.contains_key(addr));
                                } else {
                                    Cache::State::access_unwritten_addr_unchanged(
                                        self.cache,
                                        post.cache,
                                        reads,
                                        writes,
                                        addr,
                                    );
                                    if post.has_cached_page(addr) {
                                        assert(self.has_cached_page(addr));
                                        assert(post.cache_raw_page(addr) == self.cache_raw_page(addr));
                                        assert(post.available_raw_pages()[addr] == self.available_raw_pages()[addr]);
                                    } else {
                                        assert(!self.has_cached_page(addr));
                                        assert(post.disk.content.contains_key(addr));
                                        assert(self.disk.content.contains_key(addr));
                                        assert(post.available_raw_pages()[addr] == self.available_raw_pages()[addr]);
                                    }
                                    assert(self.available_branch_nodes().contains_key(addr));
                                    assert(self.mini_allocator.all_aus().contains(addr.au));
                                    assert(self.mini_allocator.page_is_reserved(addr));
                                    assert(self.active_branch_addrs().contains(addr));
                                    assert(self.overlay_branch_entries().contains_key(addr));
                                    assert(branch_entries.contains_key(addr));
                                }
                            }
                        } else if pushed_entries.contains_key(addr) {
                            if branch_entries.contains_key(addr) {
                                assert(new_summary.contains(addr.au)) by {
                                    assert(branch_entries.dom().contains(addr));
                                    assert(branch_entries.dom() =~= sealed_branch.full_repr());
                                    assert(addrs_closed(sealed_branch.full_repr(), new_summary));
                                }
                                if writes.contains_key(addr) {
                                    ConcreteBranch::State::cache_access_write_visible_as_branch_node(
                                        self,
                                        post,
                                        reads,
                                        writes,
                                        addr,
                                    );
                                } else {
                                    assert(self.overlay_branch_entries().contains_key(addr));
                                    Cache::State::access_unwritten_addr_unchanged(
                                        self.cache,
                                        post.cache,
                                        reads,
                                        writes,
                                        addr,
                                    );
                                    if self.has_cached_page(addr) {
                                        assert(post.has_cached_page(addr));
                                        assert(post.cache_raw_page(addr) == self.cache_raw_page(addr));
                                        assert(post.available_raw_pages()[addr] == self.available_raw_pages()[addr]);
                                    } else {
                                        assert(!post.has_cached_page(addr));
                                        assert(self.disk.content.contains_key(addr));
                                        assert(post.disk.content.contains_key(addr));
                                        assert(post.available_raw_pages()[addr] == self.available_raw_pages()[addr]);
                                    }
                                    assert(post.available_branch_nodes().contains_key(addr));
                                }
                                assert(summary_aus(post.branch_summary).contains(addr.au));
                            } else {
                                assert(pre_sealed_entries.contains_key(addr));
                                assert(old_summary.contains(addr.au));
                                assert(!new_summary.contains(addr.au));
                                assert(!writes.contains_key(addr)) by {
                                    if writes.contains_key(addr) {
                                        assert(write_nodes.contains_key(addr));
                                        if aux_ptr is Some {
                                            assert(addr == root || addr == aux_ptr.unwrap());
                                        } else {
                                            assert(false);
                                        }
                                        assert(branch_entries.contains_key(addr));
                                        assert(new_summary.contains(addr.au));
                                        assert(false);
                                    }
                                }
                                Cache::State::access_unwritten_addr_unchanged(
                                    self.cache,
                                    post.cache,
                                    reads,
                                    writes,
                                    addr,
                                );
                                assert(self.available_branch_nodes().contains_key(addr));
                                if self.has_cached_page(addr) {
                                    assert(post.has_cached_page(addr));
                                    assert(post.cache_raw_page(addr) == self.cache_raw_page(addr));
                                    assert(post.available_raw_pages()[addr] == self.available_raw_pages()[addr]);
                                } else {
                                    assert(!post.has_cached_page(addr));
                                    assert(self.disk.content.contains_key(addr));
                                    assert(post.disk.content.contains_key(addr));
                                    assert(post.available_raw_pages()[addr] == self.available_raw_pages()[addr]);
                                }
                                assert(post.available_branch_nodes().contains_key(addr));
                                assert(summary_aus(post.branch_summary).contains(addr.au));
                            }
                        }
                    }
                    assert forall |addr: Address| #[trigger] post_entries.contains_key(addr)
                        implies post_entries[addr] == pushed_entries[addr] by {
                        assert(post.available_branch_nodes().contains_key(addr));
                        assert(summary_aus(post.branch_summary).contains(addr.au));
                        if branch_entries.contains_key(addr) {
                            if writes.contains_key(addr) {
                                ConcreteBranch::State::cache_access_write_visible_as_branch_node(
                                    self,
                                    post,
                                    reads,
                                    writes,
                                    addr,
                                );
                                assert(post.available_branch_nodes()[addr] == write_nodes[addr]);
                                assert(branch_entries[addr] == write_nodes[addr]);
                            } else {
                                assert(self.overlay_branch_entries().contains_key(addr));
                                Cache::State::access_unwritten_addr_unchanged(
                                    self.cache,
                                    post.cache,
                                    reads,
                                    writes,
                                    addr,
                                );
                                if post.has_cached_page(addr) {
                                    assert(self.has_cached_page(addr));
                                    assert(post.cache_raw_page(addr) == self.cache_raw_page(addr));
                                    assert(post.available_raw_pages()[addr] == self.available_raw_pages()[addr]);
                                } else {
                                    assert(!self.has_cached_page(addr));
                                    assert(post.disk.content.contains_key(addr));
                                    assert(self.disk.content.contains_key(addr));
                                    assert(post.available_raw_pages()[addr] == self.available_raw_pages()[addr]);
                                }
                                assert(post.available_branch_nodes()[addr] == self.available_branch_nodes()[addr]);
                                assert(branch_entries[addr] == self.overlay_branch_entries()[addr]);
                                assert(self.overlay_branch_entries()[addr] == self.available_branch_nodes()[addr]);
                            }
                        } else {
                            assert(pre_sealed_entries.contains_key(addr));
                            assert(!writes.contains_key(addr)) by {
                                if writes.contains_key(addr) {
                                    assert(write_nodes.contains_key(addr));
                                    if aux_ptr is Some {
                                        assert(addr == root || addr == aux_ptr.unwrap());
                                    } else {
                                        assert(false);
                                    }
                                    assert(branch_entries.contains_key(addr));
                                    assert(false);
                                }
                            }
                            Cache::State::access_unwritten_addr_unchanged(
                                self.cache,
                                post.cache,
                                reads,
                                writes,
                                addr,
                            );
                            if post.has_cached_page(addr) {
                                assert(self.has_cached_page(addr));
                                assert(post.cache_raw_page(addr) == self.cache_raw_page(addr));
                                assert(post.available_raw_pages()[addr] == self.available_raw_pages()[addr]);
                            } else {
                                assert(!self.has_cached_page(addr));
                                assert(post.disk.content.contains_key(addr));
                                assert(self.disk.content.contains_key(addr));
                                assert(post.available_raw_pages()[addr] == self.available_raw_pages()[addr]);
                            }
                            assert(post.available_branch_nodes()[addr] == self.available_branch_nodes()[addr]);
                            assert(pre_sealed_entries[addr] == self.available_branch_nodes()[addr]);
                        }
                    }
                }
                assert(post.i().sealed_stack.sealed_disk == pushed_stack.sealed_disk);

                assert(post.sealed_roots_i() =~= self.sealed_roots_i().push(sealed_branch.root)) by {
                    assert forall |i: int| #![auto] 0 <= i < post.sealed_roots_i().len()
                        implies post.sealed_roots_i()[i] == self.sealed_roots_i().push(sealed_branch.root)[i]
                    by {
                        if i < self.sealed_roots_i().len() {
                            assert(i < self.cached_branches.len() - 1);
                            assert(post.cached_branches[i] == self.cached_branches[i]);
                        } else {
                            assert(i == self.sealed_roots_i().len());
                            assert(i == self.cached_branches.len() - 1);
                            assert(post.cached_branches[i].root == Some(sealed_branch.root));
                        }
                    }
                }

                assert(post.i().sealed_stack.sealed_roots
                    == self.i().sealed_stack.push_branch(sealed_branch).sealed_roots);

                assert(post.i().sealed_stack == self.i().sealed_stack.push_branch(sealed_branch));
                assert(AllocationBranchStack::State::internal_seal(
                    self.i(),
                    post.i(),
                    self.label_to_stack(lbl),
                    aux_ptr,
                ));
                assert(AllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_stack(lbl),
                    AllocationBranchStack::Step::internal_seal(aux_ptr),
                ));
            }
            _ => {
                assert(false);
            }
        }
        assert(AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
        self.stack_next_implies_abstract_next(post, lbl);
    }

    pub proof fn fill_au_refines(
        self,
        post: Self,
        lbl: ConcreteBranch::Label,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            ConcreteBranch::State::fill_au(self, post, lbl),
        ensures
            AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(AllocationBranchStack::State::next);
        reveal(AllocationBranchStack::State::next_by);
        match lbl {
            ConcreteBranch::Label::FillAU{aus} => {
                Self::available_branch_nodes_ignore_mini_allocator(self, post);
                Self::overlay_at_ignores_mini_allocator(self, post, self.active_idx() as nat);
                assert(self.sealed_disk_i() == post.sealed_disk_i());
                assert(self.sealed_roots_i() =~= post.sealed_roots_i()) by {
                    assert forall |i: int| 0 <= i < self.sealed_roots_i().len()
                        implies self.sealed_roots_i()[i] == post.sealed_roots_i()[i] by {
                        Self::overlay_at_ignores_mini_allocator(self, post, i as nat);
                    }
                }
                assert(self.i().sealed_stack == post.i().sealed_stack);
                assert(self.overlay_branch_entries() == post.overlay_branch_entries()) by {
                    assert forall |addr: Address|
                        #[trigger] self.overlay_branch_entries().contains_key(addr)
                            <==> post.overlay_branch_entries().contains_key(addr)
                    by {
                        crate::implementation::ConcreteBranch_v::mini_allocator_add_aus_page_is_reserved(
                            self.mini_allocator,
                            aus,
                            addr,
                        );
                        assert(self.available_branch_nodes().contains_key(addr)
                            <==> post.available_branch_nodes().contains_key(addr));
                    }
                    assert forall |addr: Address|
                        #[trigger] self.overlay_branch_entries().contains_key(addr)
                        implies self.overlay_branch_entries()[addr] == post.overlay_branch_entries()[addr]
                    by {
                        assert(self.available_branch_nodes()[addr] == post.available_branch_nodes()[addr]);
                    }
                    assert_maps_equal!(self.overlay_branch_entries(), post.overlay_branch_entries());
                }
                assert(self.overlay_branch() == post.overlay_branch());
                assert(post.i().active_branch == self.i().active_branch.mini_allocator_fill(aus));
                assert(AllocationBranchStack::State::internal_fill_au(
                    self.i(),
                    post.i(),
                    self.label_to_stack(lbl),
                    aus,
                ));
                assert(AllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_stack(lbl),
                    AllocationBranchStack::Step::internal_fill_au(aus),
                ));
            }
            _ => { }
        }
        assert(AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
        self.stack_next_implies_abstract_next(post, lbl);
    }

    pub proof fn internal_cache_refines(
        self,
        post: Self,
        lbl: ConcreteBranch::Label,
        new_cache: crate::implementation::Cache_v::Cache::State,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            ConcreteBranch::State::internal_cache(self, post, lbl, new_cache),
        ensures
            AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        self.i_unchanged_when_available_raw_pages_unchanged(post);
        reveal(AllocationBranchStack::State::next);
        reveal(AllocationBranchStack::State::next_by);
        assert(AllocationBranchStack::State::internal_noop(
            self.i(),
            post.i(),
            self.label_to_stack(lbl),
        ));
        assert(AllocationBranchStack::State::next_by(
            self.i(),
            post.i(),
            self.label_to_stack(lbl),
            AllocationBranchStack::Step::internal_noop(),
        ));
        assert(AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
        self.stack_next_implies_abstract_next(post, lbl);
    }

    pub proof fn internal_disk_refines(
        self,
        post: Self,
        lbl: ConcreteBranch::Label,
        new_disk: AsyncDisk::State,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            ConcreteBranch::State::internal_disk(self, post, lbl, new_disk),
        ensures
            AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        self.i_unchanged_when_available_raw_pages_unchanged(post);
        reveal(AllocationBranchStack::State::next);
        reveal(AllocationBranchStack::State::next_by);
        assert(AllocationBranchStack::State::internal_noop(
            self.i(),
            post.i(),
            self.label_to_stack(lbl),
        ));
        assert(AllocationBranchStack::State::next_by(
            self.i(),
            post.i(),
            self.label_to_stack(lbl),
            AllocationBranchStack::Step::internal_noop(),
        ));
        assert(AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
        self.stack_next_implies_abstract_next(post, lbl);
    }

    pub proof fn cache_disk_ops_refines(
        self,
        post: Self,
        lbl: ConcreteBranch::Label,
        new_cache: crate::implementation::Cache_v::Cache::State,
        new_disk: AsyncDisk::State,
        cache_requests: Set<DiskRequest>,
        cache_responses: Map<Address, DiskResponse>,
        disk_requests: Map<ID, DiskRequest>,
        disk_responses: Map<ID, DiskResponse>,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            ConcreteBranch::State::cache_disk_ops(
                self,
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
            AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        self.i_unchanged_when_available_raw_pages_unchanged(post);
        reveal(AllocationBranchStack::State::next);
        reveal(AllocationBranchStack::State::next_by);
        assert(AllocationBranchStack::State::internal_noop(
            self.i(),
            post.i(),
            self.label_to_stack(lbl),
        ));
        assert(AllocationBranchStack::State::next_by(
            self.i(),
            post.i(),
            self.label_to_stack(lbl),
            AllocationBranchStack::Step::internal_noop(),
        ));
        assert(AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
        self.stack_next_implies_abstract_next(post, lbl);
    }

    pub proof fn next_refines(
        self,
        post: Self,
        lbl: ConcreteBranch::Label,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            ConcreteBranch::State::next(self, post, lbl),
        ensures
            AllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
            AbstractMap::State::next(self.abstract_map_i(), post.abstract_map_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(ConcreteBranch::State::next);
        reveal(ConcreteBranch::State::next_by);

        let step = choose |step| ConcreteBranch::State::next_by(self, post, lbl, step);
        match step {
            ConcreteBranch::Step::query(reads, query_receipts) => {
                self.query_refines(post, lbl, reads, query_receipts);
            }
            ConcreteBranch::Step::append(reads, writes, receipt, new_cache) => {
                self.append_to_active_refines(post, lbl, reads, writes, receipt, new_cache);
            }
            ConcreteBranch::Step::append_to_empty(writes, init_root, new_cache) => {
                self.append_to_empty_refines(post, lbl, writes, init_root, new_cache);
            }
            ConcreteBranch::Step::grow(reads, writes, new_cache) => {
                self.grow_refines(post, lbl, reads, writes, new_cache);
            }
            ConcreteBranch::Step::split(reads, writes, receipt, new_cache) => {
                self.split_refines(post, lbl, reads, writes, receipt, new_cache);
            }
            ConcreteBranch::Step::seal(reads, writes, new_cache) => {
                self.seal_refines(post, lbl, reads, writes, new_cache);
            }
            ConcreteBranch::Step::fill_au() => {
                self.fill_au_refines(post, lbl);
            }
            ConcreteBranch::Step::internal_cache(new_cache) => {
                self.internal_cache_refines(post, lbl, new_cache);
            }
            ConcreteBranch::Step::internal_disk(new_disk) => {
                self.internal_disk_refines(post, lbl, new_disk);
            }
            ConcreteBranch::Step::cache_disk_ops(
                new_cache,
                new_disk,
                cache_requests,
                cache_responses,
                disk_requests,
                disk_responses,
            ) => {
                self.cache_disk_ops_refines(
                    post,
                    lbl,
                    new_cache,
                    new_disk,
                    cache_requests,
                    cache_responses,
                    disk_requests,
                    disk_responses,
                );
            }
            _ => { }
        }
    }
}

}
