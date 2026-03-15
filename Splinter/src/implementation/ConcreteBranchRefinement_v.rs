// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::map::*;
use vstd::assert_maps_equal;

use crate::allocation_layer::AllocationBranch_v::{AllocationBranch, BranchNode as AllocationBranchNode, Summary};
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::Buffer_v::SimpleBuffer;
use crate::betree::LinkedBranch_v::{LinkedBranch, Node, Path as BranchPath, SplitArg};
use crate::betree::PivotBranch_v;
use crate::betree::PivotBranch_v::Node as PivotNode;
use crate::betree::PivotBranchRefinement_v::QueryLabel;
use crate::betree::Utils_v::{lemma_set_subset_of_union_seq_of_sets, lemma_union_seq_of_sets_contains, union_seq_of_sets};
use crate::disk::GenericDisk_v::{Address, Pointer, Ranking};
use crate::implementation::Cache_v::{Cache, Entry, Slot};
use crate::implementation::ConcreteBranch_v::{
    invert_contains_pair, union_prefer_right_uses_left, union_prefer_right_uses_right,
    ConcreteBranch, decode_branch_page, to_branch_nodes,
};
use crate::spec::AsyncDisk_t::{DiskRequest, DiskResponse, RawPage};
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::ID;
use crate::spec::Messages_t::Message;

verus! {

proof fn cache_has_cached_page_gets_addr(cache: Cache::State, addr: Address)
    requires
        cache.inv(),
        cache.lookup_map.contains_key(addr),
        cache.entries[cache.lookup_map[addr]] is Filled,
    ensures
        cache.entries.contains_key(cache.lookup_map[addr]),
        cache.entries[cache.lookup_map[addr]] is Filled,
        cache.entries[cache.lookup_map[addr]].get_addr() == addr,
{
    cache.build_lookup_map_ensures();
}

proof fn cache_filled_entry_in_lookup(cache: Cache::State, slot: Slot)
    requires
        cache.inv(),
        cache.entries.contains_key(slot),
        cache.entries[slot] is Filled,
    ensures
        cache.lookup_map.contains_key(cache.entries[slot].get_addr()),
        cache.lookup_map[cache.entries[slot].get_addr()] == slot,
{
    cache.build_lookup_map_ensures();
}

proof fn branch_read_agrees_with_overlay(
    pre: ConcreteBranch::State,
    new_cache: Cache::State,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    addr: Address,
)
    requires
        pre.wf(),
        Cache::State::next(pre.cache, new_cache, Cache::Label::Access{reads, writes}),
        pre.overlay_branch_entries().contains_key(addr),
        to_branch_nodes(reads).contains_key(addr),
        reads.contains_key(addr),
        pre.cache.valid_read(addr, reads[addr]),
    ensures
        to_branch_nodes(reads)[addr] == pre.overlay_branch_entries()[addr],
{
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step| Cache::State::next_by(pre.cache, new_cache, Cache::Label::Access{reads, writes}, step);
    match step {
        Cache::Step::access() => {
            assert(reads.contains_key(addr));
            assert(pre.cache.valid_read(addr, reads[addr]));
            cache_has_cached_page_gets_addr(pre.cache, addr);
            let slot = pre.cache.lookup_map[addr];
            assert(pre.cache.entries.contains_key(slot));
            assert(pre.cache.entries[slot] is Filled);
            assert(pre.cache.entries[slot].get_addr() == addr);
            assert(pre.has_cached_page(addr));
            assert(pre.cache_raw_page(addr) == reads[addr]);
            assert(pre.overlay_raw_page(addr) == reads[addr]);
            assert(pre.overlay_branch_entries().contains_key(addr));
            assert(to_branch_nodes(reads)[addr] == decode_branch_page(reads[addr]));
            assert(pre.overlay_branch_entries()[addr] == decode_branch_page(pre.overlay_raw_page(addr)));
        }
        _ => { assert(false); }
    }
}

proof fn union_seq_of_sets_equal<A>(left: Seq<Set<A>>, right: Seq<Set<A>>)
    requires
        left.len() == right.len(),
        forall |i: int| 0 <= i < left.len() ==> #[trigger] left[i] == right[i],
    ensures
        union_seq_of_sets(left) == union_seq_of_sets(right),
{
    assert forall |a: A| #[trigger] union_seq_of_sets(left).contains(a) implies union_seq_of_sets(right).contains(a) by {
        lemma_union_seq_of_sets_contains(left, a);
        let i = choose |i: int| #![trigger left[i].contains(a)] 0 <= i < left.len() && left[i].contains(a);
        assert(right[i].contains(a));
        assert(exists |j: int| #![trigger right[j].contains(a)] 0 <= j < right.len() && right[j].contains(a));
        lemma_set_subset_of_union_seq_of_sets(right, a);
    };
    assert forall |a: A| #[trigger] union_seq_of_sets(right).contains(a) implies union_seq_of_sets(left).contains(a) by {
        lemma_union_seq_of_sets_contains(right, a);
        let i = choose |i: int| #![trigger right[i].contains(a)] 0 <= i < right.len() && right[i].contains(a);
        assert(left[i].contains(a));
        assert(exists |j: int| #![trigger left[j].contains(a)] 0 <= j < left.len() && left[j].contains(a));
        lemma_set_subset_of_union_seq_of_sets(left, a);
    };
}

proof fn union_seq_of_sets_singleton<A>(s: Set<A>)
    ensures
        union_seq_of_sets(seq![s]) == s,
{
    assert forall |a: A| #[trigger] union_seq_of_sets(seq![s]).contains(a) <==> s.contains(a) by {
        if union_seq_of_sets(seq![s]).contains(a) {
            lemma_union_seq_of_sets_contains(seq![s], a);
            assert(s.contains(a));
        }
        if s.contains(a) {
            assert(exists |i: int| #![trigger seq![s][i].contains(a)] 0 <= i < 1 && seq![s][i].contains(a));
            lemma_set_subset_of_union_seq_of_sets(seq![s], a);
        }
    };
}

proof fn loaded_path_contains_root(root: Address, loaded: Map<Address, AllocationBranchNode>, key: Key, depth: nat)
    requires
        crate::implementation::CachedBranch_v::loaded_has_route_at_depth(root, loaded, key, depth),
    ensures
        crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(root, loaded, key, depth).contains(root),
    decreases depth,
{
    if depth == 0 {
    } else {
        assert(crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(root, loaded, key, depth)
            == crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(
                crate::implementation::CachedBranch_v::loaded_child_addr(root, loaded, key),
                loaded,
                key,
                (depth - 1) as nat,
            ).insert(root));
    }
}

proof fn loaded_child_path_subset(root: Address, loaded: Map<Address, AllocationBranchNode>, key: Key, depth: nat)
    requires
        depth > 0,
        crate::implementation::CachedBranch_v::loaded_has_route_at_depth(root, loaded, key, depth),
    ensures
        crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(
            crate::implementation::CachedBranch_v::loaded_child_addr(root, loaded, key),
            loaded,
            key,
            (depth - 1) as nat,
        ) <= crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(root, loaded, key, depth),
{
    let child_addr = crate::implementation::CachedBranch_v::loaded_child_addr(root, loaded, key);
    assert(crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(root, loaded, key, depth)
        == crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(
            child_addr,
            loaded,
            key,
            (depth - 1) as nat,
        ).insert(root));
    assert forall |addr: Address|
        #[trigger] crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(child_addr, loaded, key, (depth - 1) as nat).contains(addr)
        implies crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(root, loaded, key, depth).contains(addr)
    by {
    };
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
    crate::betree::LinkedBranch_v::Refinement_v::i_internal_wf(branch, ranking);
    crate::betree::LinkedBranch_v::Refinement_v::lemma_route_ensures(node, key);
    assert(node.valid_child_index(r + 1));
    assert(branch_i is Index);
    assert(branch_i->pivots == node->pivots);
    assert(branch_i.route(key) == node.route(key));
    assert(branch_i->children[r + 1] == child_i);
    crate::betree::PivotBranchRefinement_v::query_refines(
        branch_i,
        QueryLabel{key, msg: branch_i.query(key)},
    );
    crate::betree::PivotBranchRefinement_v::query_refines_to_routed_child(
        branch_i,
        QueryLabel{key, msg: branch_i.query(key)},
    );
    crate::betree::PivotBranchRefinement_v::query_refines(
        child_i,
        QueryLabel{key, msg: child_i.query(key)},
    );
    assert(branch_i.i().query(key) == branch_i.query(key));
    assert(child_i.i().query(key) == branch_i.query(key));
    assert(child_i.i().query(key) == child_i.query(key));
    assert(branch_i.query(key) == child_i.query(key));
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
    crate::betree::LinkedBranch_v::Refinement_v::lemma_route_ensures(node, key);
    assert(node.valid_child_index(r + 1));
    assert(node is Index);
    child_branch_inv_internal_from_parent(branch, ranking, r + 1);
    crate::betree::LinkedBranch_v::Refinement_v::query_internal_refines(
        branch,
        ranking,
        key,
        branch.query_internal(key, ranking),
    );
    crate::betree::LinkedBranch_v::Refinement_v::query_internal_refines(
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


proof fn loaded_target_is_leaf_at_depth(root: Address, loaded: Map<Address, AllocationBranchNode>, key: Key, depth: nat)
    requires
        crate::implementation::CachedBranch_v::loaded_has_route_at_depth(root, loaded, key, depth),
    ensures
        crate::implementation::CachedBranch_v::loaded_target_at_depth(root, loaded, key, depth) is Leaf,
    decreases depth,
{
    if depth == 0 {
    } else {
        loaded_target_is_leaf_at_depth(
            crate::implementation::CachedBranch_v::loaded_child_addr(root, loaded, key),
            loaded,
            key,
            (depth - 1) as nat,
        );
    }
}

proof fn child_branch_inv_internal_from_parent(branch: LinkedBranch<Summary>, ranking: Ranking, child_idx: int)
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

proof fn path_target_inv_internal(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    key: Key,
    depth: nat,
)
    requires
        branch.inv_internal(ranking),
        (BranchPath{branch, key, depth}).valid(),
    ensures
        (BranchPath{branch, key, depth}).target().inv_internal(ranking),
    decreases depth,
{
    let path = BranchPath{branch, key, depth};
    if depth == 0 {
    } else {
        let child_idx = branch.root().route(key) + 1;
        crate::betree::LinkedBranch_v::Refinement_v::lemma_route_ensures(branch.root(), key);
        child_branch_inv_internal_from_parent(branch, ranking, child_idx);
        path_target_inv_internal(branch.child_at_idx(child_idx), ranking, key, (depth - 1) as nat);
        assert(path.subpath() == BranchPath{branch: branch.child_at_idx(child_idx), key, depth: (depth - 1) as nat});
        assert(path.target() == path.subpath().target());
    }
}

proof fn loaded_path_reads_agree_with_branch_disk_at_depth(
    pre: ConcreteBranch::State,
    new_cache: Cache::State,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    branch: LinkedBranch<Summary>,
    key: Key,
    depth: nat,
)
    requires
        pre.wf(),
        Cache::State::next(pre.cache, new_cache, Cache::Label::Access{reads, writes}),
        branch.wf(),
        branch.disk_view.entries == pre.overlay_branch_entries(),
        crate::implementation::CachedBranch_v::loaded_has_route_at_depth(branch.root, to_branch_nodes(reads), key, depth),
        crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(branch.root, to_branch_nodes(reads), key, depth) <= reads.dom(),
    ensures
        crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(branch.root, to_branch_nodes(reads), key, depth)
            <= branch.disk_view.entries.dom(),
        forall |addr: Address|
            #[trigger] crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(branch.root, to_branch_nodes(reads), key, depth).contains(addr)
            ==> to_branch_nodes(reads)[addr] == branch.disk_view.entries[addr],
    decreases depth,
{
    let read_nodes = to_branch_nodes(reads);
    loaded_path_contains_root(branch.root, read_nodes, key, depth);
    assert(reads.contains_key(branch.root));
    assert(pre.overlay_branch_entries().contains_key(branch.root));
    let lbl = Cache::Label::Access{reads, writes};
    reveal(Cache::State::next_by);
    reveal(Cache::State::next);
    assert(Cache::State::next_by(pre.cache, new_cache, lbl, Cache::Step::access()));
    assert(pre.cache.valid_read(branch.root, lbl->reads[branch.root])) by {};
    branch_read_agrees_with_overlay(pre, new_cache, reads, writes, branch.root);
    assert(read_nodes[branch.root] == pre.overlay_branch_entries()[branch.root]);
    assert(branch.disk_view.entries[branch.root] == pre.overlay_branch_entries()[branch.root]);
    if depth == 0 {
        assert(crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(branch.root, read_nodes, key, depth)
            == set!{branch.root});
        assert forall |addr: Address|
            #[trigger] crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(branch.root, read_nodes, key, depth).contains(addr)
            implies read_nodes[addr] == branch.disk_view.entries[addr]
        by {
            assert(addr == branch.root);
        };
    } else {
        let node = read_nodes[branch.root];
        assert(node == branch.root());
        assert(node is Index);
        Key::strictly_sorted_implies_sorted(node->pivots);
        Key::largest_lte_ensures(node->pivots, key, node.route(key));
        let child_idx = node.route(key) + 1;
        assert(branch.root().valid_child_index(child_idx));
        let child_branch = branch.child_at_idx(child_idx);
        let child_addr = crate::implementation::CachedBranch_v::loaded_child_addr(branch.root, read_nodes, key);
        assert(child_addr == branch.root()->children[child_idx]);
        assert(child_branch.disk_view.entries == pre.overlay_branch_entries());
        loaded_child_path_subset(branch.root, read_nodes, key, depth);
        assert(crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(child_addr, read_nodes, key, (depth - 1) as nat) <= reads.dom()) by {
            assert forall |addr: Address|
                #[trigger] crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(child_addr, read_nodes, key, (depth - 1) as nat).contains(addr)
                implies reads.dom().contains(addr)
            by {
                assert(crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(branch.root, read_nodes, key, depth).contains(addr));
            };
        };
        loaded_path_reads_agree_with_branch_disk_at_depth(
            pre,
            new_cache,
            reads,
            writes,
            child_branch,
            key,
            (depth - 1) as nat,
        );
        assert forall |addr: Address|
            #[trigger] crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(branch.root, read_nodes, key, depth).contains(addr)
            implies read_nodes[addr] == branch.disk_view.entries[addr]
        by {
            if addr == branch.root {
            } else {
                assert(crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(child_addr, read_nodes, key, (depth - 1) as nat).contains(addr));
            }
        };
    }
}

proof fn loaded_path_matches_branch_target_at_depth(
    branch: LinkedBranch<Summary>,
    loaded: Map<Address, AllocationBranchNode>,
    key: Key,
    depth: nat,
)
    requires
        branch.wf(),
        crate::implementation::CachedBranch_v::loaded_has_route_at_depth(branch.root, loaded, key, depth),
        crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(branch.root, loaded, key, depth)
            <= branch.disk_view.entries.dom(),
        forall |addr: Address|
            #[trigger] crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(branch.root, loaded, key, depth).contains(addr)
            ==> loaded[addr] == branch.disk_view.entries[addr],
    ensures
        (BranchPath{branch, key, depth}).valid(),
        (BranchPath{branch, key, depth}).target().disk_view == branch.disk_view,
        (BranchPath{branch, key, depth}).target().root
            == crate::implementation::CachedBranch_v::loaded_target_addr_at_depth(branch.root, loaded, key, depth),
        (BranchPath{branch, key, depth}).target().root()
            == crate::implementation::CachedBranch_v::loaded_target_at_depth(branch.root, loaded, key, depth),
    decreases depth,
{
    let path = BranchPath{branch, key, depth};
    loaded_path_contains_root(branch.root, loaded, key, depth);
    assert(loaded[branch.root] == branch.disk_view.entries[branch.root]);
    assert(branch.disk_view.entries[branch.root] == branch.root());
    if depth == 0 {
        assert(path.valid());
        assert(path.target() == branch);
    } else {
        let node = loaded[branch.root];
        assert(node == branch.root());
        assert(node is Index);
        Key::strictly_sorted_implies_sorted(node->pivots);
        Key::largest_lte_ensures(node->pivots, key, node.route(key));
        let child_idx = node.route(key) + 1;
        assert(branch.root().valid_child_index(child_idx));
        let child_branch = branch.child_at_idx(child_idx);
        let child_addr = crate::implementation::CachedBranch_v::loaded_child_addr(branch.root, loaded, key);
        assert(child_addr == branch.root()->children[child_idx]);
        loaded_child_path_subset(branch.root, loaded, key, depth);
        assert forall |addr: Address|
            #[trigger] crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(child_addr, loaded, key, (depth - 1) as nat).contains(addr)
            implies loaded[addr] == child_branch.disk_view.entries[addr]
        by {
            assert(crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(branch.root, loaded, key, depth).contains(addr));
            assert(loaded[addr] == branch.disk_view.entries[addr]);
            assert(child_branch.disk_view.entries[addr] == branch.disk_view.entries[addr]);
        };
        loaded_path_matches_branch_target_at_depth(child_branch, loaded, key, (depth - 1) as nat);
        assert(path.subpath() == BranchPath{branch: child_branch, key, depth: (depth - 1) as nat});
        assert(path.valid());
        assert(path.target() == path.subpath().target());
        assert(path.target().disk_view == child_branch.disk_view);
        assert(child_branch.disk_view == branch.disk_view);
    }
}

proof fn loaded_query_matches_branch_query_internal_at_depth(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    loaded: Map<Address, AllocationBranchNode>,
    key: Key,
    depth: nat,
)
    requires
        branch.inv_internal(ranking),
        crate::implementation::CachedBranch_v::loaded_query_ready_at_depth(branch.root, loaded, key, depth),
        crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(branch.root, loaded, key, depth)
            <= branch.disk_view.entries.dom(),
        forall |addr: Address|
            #[trigger] crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(branch.root, loaded, key, depth).contains(addr)
            ==> loaded[addr] == branch.disk_view.entries[addr],
    ensures
        (BranchPath{branch, key, depth}).valid(),
        branch.query_internal(key, ranking)
            == crate::implementation::CachedBranch_v::loaded_query_result_at_depth(branch.root, loaded, key, depth),
    decreases depth,
{
    loaded_path_matches_branch_target_at_depth(branch, loaded, key, depth);
    if depth == 0 {
        loaded_path_contains_root(branch.root, loaded, key, depth);
        assert(loaded[branch.root] == branch.disk_view.entries[branch.root]);
        assert(branch.disk_view.entries[branch.root] == branch.root());
        let node = loaded[branch.root];
        assert(node == branch.root());
        assert(node is Leaf);
        reveal(LinkedBranch::query_internal);
    } else {
        loaded_path_contains_root(branch.root, loaded, key, depth);
        assert(loaded[branch.root] == branch.disk_view.entries[branch.root]);
        assert(branch.disk_view.entries[branch.root] == branch.root());
        let node = loaded[branch.root];
        assert(node == branch.root());
        assert(node is Index);
        Key::strictly_sorted_implies_sorted(node->pivots);
        Key::largest_lte_ensures(node->pivots, key, node.route(key));
        let child_idx = node.route(key) + 1;
        assert(branch.root().valid_child_index(child_idx));
        let child_branch = branch.child_at_idx(child_idx);
        let child_addr = crate::implementation::CachedBranch_v::loaded_child_addr(branch.root, loaded, key);
        assert(child_addr == branch.root()->children[child_idx]);
        child_branch_inv_internal_from_parent(branch, ranking, child_idx);
        loaded_child_path_subset(branch.root, loaded, key, depth);
        assert forall |addr: Address|
            #[trigger] crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(child_addr, loaded, key, (depth - 1) as nat).contains(addr)
            implies loaded[addr] == child_branch.disk_view.entries[addr]
        by {
            assert(crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(branch.root, loaded, key, depth).contains(addr));
            assert(loaded[addr] == branch.disk_view.entries[addr]);
            assert(child_branch.disk_view.entries[addr] == branch.disk_view.entries[addr]);
        };
        loaded_query_matches_branch_query_internal_at_depth(child_branch, ranking, loaded, key, (depth - 1) as nat);
        assert(branch.root().route(key) == node.route(key));
        assert(child_branch == branch.child_at_idx(branch.root().route(key) + 1));
        local_query_internal_descends_to_child(branch, ranking, key);
        assert(branch.query_internal(key, ranking)
            == branch.child_at_idx(branch.root().route(key) + 1).query_internal(key, ranking));
        assert(branch.child_at_idx(branch.root().route(key) + 1).query_internal(key, ranking)
            == child_branch.query_internal(key, ranking));
        assert(branch.query_internal(key, ranking)
            == crate::implementation::CachedBranch_v::loaded_query_result_at_depth(child_addr, loaded, key, (depth - 1) as nat));
        assert(crate::implementation::CachedBranch_v::loaded_query_result_at_depth(branch.root, loaded, key, depth)
            == crate::implementation::CachedBranch_v::loaded_query_result_at_depth(child_addr, loaded, key, (depth - 1) as nat));
    }
}

proof fn loaded_query_matches_branch_query_at_depth(
    branch: LinkedBranch<Summary>,
    loaded: Map<Address, AllocationBranchNode>,
    key: Key,
    depth: nat,
)
    requires
        branch.inv(),
        crate::implementation::CachedBranch_v::loaded_query_ready_at_depth(branch.root, loaded, key, depth),
        crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(branch.root, loaded, key, depth)
            <= branch.disk_view.entries.dom(),
        forall |addr: Address|
            #[trigger] crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(branch.root, loaded, key, depth).contains(addr)
            ==> loaded[addr] == branch.disk_view.entries[addr],
    ensures
        (BranchPath{branch, key, depth}).valid(),
        branch.query(key)
            == crate::implementation::CachedBranch_v::loaded_query_result_at_depth(branch.root, loaded, key, depth),
{
    loaded_query_matches_branch_query_internal_at_depth(branch, branch.the_ranking(), loaded, key, depth);
    let msg = crate::implementation::CachedBranch_v::loaded_query_result_at_depth(branch.root, loaded, key, depth);
    crate::betree::LinkedBranch_v::Refinement_v::query_internal_refines(branch, branch.the_ranking(), key, msg);
    crate::betree::LinkedBranch_v::Refinement_v::query_refines(branch, key, branch.query(key));
    assert(branch.i_internal(branch.the_ranking()).query(key) == msg);
    assert(branch.i().query(key) == branch.query(key));
    assert(branch.i() == branch.i_internal(branch.the_ranking()));
    assert(branch.query(key) == msg);
}

proof fn leaf_append_route_equiv(leaf: AllocationBranchNode, keys: Seq<Key>)
    requires
        leaf is Leaf,
        leaf.wf(),
        leaf.keys_strictly_sorted(),
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

proof fn loaded_append_implies_branch_can_append_at_depth(
    branch: LinkedBranch<Summary>,
    loaded: Map<Address, AllocationBranchNode>,
    keys: Seq<Key>,
    msgs: Seq<Message>,
    depth: nat,
)
    requires
        branch.wf(),
        keys.len() > 0,
        crate::implementation::CachedBranch_v::loaded_append_ready_at_depth(branch.root, loaded, keys, msgs, depth),
        crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(branch.root, loaded, keys[0], depth)
            <= branch.disk_view.entries.dom(),
        forall |addr: Address|
            #[trigger] crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(branch.root, loaded, keys[0], depth).contains(addr)
            ==> loaded[addr] == branch.disk_view.entries[addr],
    ensures
        branch.can_append(keys, msgs, BranchPath{branch, key: keys[0], depth}),
    decreases depth,
{
    let key = keys[0];
    let path = BranchPath{branch, key, depth};
    loaded_path_matches_branch_target_at_depth(branch, loaded, key, depth);
    let leaf = crate::implementation::CachedBranch_v::loaded_target_at_depth(branch.root, loaded, key, depth);
    assert(crate::implementation::CachedBranch_v::loaded_query_ready_at_depth(branch.root, loaded, key, depth));
    loaded_target_is_leaf_at_depth(branch.root, loaded, key, depth);
    assert(leaf == crate::implementation::CachedBranch_v::loaded_target_at_depth(branch.root, loaded, key, depth));
    assert(leaf is Leaf);
    assert(path.target().root() == leaf);
    assert(Key::lt(path.target().root()->keys.last(), key));
    if depth == 0 {
        leaf_append_route_equiv(leaf, keys);
        assert(path.path_equiv(keys.last()));
    } else {
        let root = branch.root;
        loaded_path_contains_root(root, loaded, key, depth);
        assert(loaded[root] == branch.disk_view.entries[root]);
        assert(branch.disk_view.entries[root] == branch.root());
        let node = loaded[root];
        assert(node == branch.root());
        assert(node is Index);
        Key::strictly_sorted_implies_sorted(node->pivots);
        Key::largest_lte_ensures(node->pivots, key, node.route(key));
        let child_idx = node.route(key) + 1;
        assert(branch.root().valid_child_index(child_idx));
        let child_branch = branch.child_at_idx(child_idx);
        let child_addr = crate::implementation::CachedBranch_v::loaded_child_addr(root, loaded, key);
        assert(child_addr == branch.root()->children[child_idx]);
        loaded_child_path_subset(root, loaded, key, depth);
        assert forall |addr: Address|
            #[trigger] crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(child_addr, loaded, key, (depth - 1) as nat).contains(addr)
            implies loaded[addr] == child_branch.disk_view.entries[addr]
        by {
            assert(crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(root, loaded, key, depth).contains(addr));
            assert(loaded[addr] == branch.disk_view.entries[addr]);
            assert(child_branch.disk_view.entries[addr] == branch.disk_view.entries[addr]);
        };
        loaded_append_implies_branch_can_append_at_depth(child_branch, loaded, keys, msgs, (depth - 1) as nat);
        assert(node.route(key) == node.route(keys.last()));
        assert(path.subpath() == BranchPath{branch: child_branch, key, depth: (depth - 1) as nat});
        assert(path.subpath().path_equiv(keys.last()));
        assert(path.path_equiv(keys.last()));
    }
    assert(branch.can_append(keys, msgs, path));
}

proof fn reachable_branch_addrs_empty_unfold(
    s: ConcreteBranch::State,
    addr: Address,
    fuel: nat,
)
    requires
        fuel == 0 || !s.available_branch_nodes().contains_key(addr),
    ensures
        s.reachable_branch_addrs_from_with_fuel(addr, fuel) =~= Set::<Address>::empty(),
{
    reveal(ConcreteBranch::State::reachable_branch_addrs_from_with_fuel);
    reveal(ConcreteBranch::State::reachable_branch_addrs_from_with_fuel_contains);
    assert forall |a: Address|
        #[trigger] s.reachable_branch_addrs_from_with_fuel(addr, fuel).contains(a)
        <==> #[trigger] Set::<Address>::empty().contains(a) by {
    };
}

proof fn reachable_branch_addrs_leaf_unfold(
    s: ConcreteBranch::State,
    addr: Address,
    fuel: nat,
)
    requires
        fuel > 0,
        s.available_branch_nodes().contains_key(addr),
        s.available_branch_nodes()[addr] is Leaf || s.available_branch_nodes()[addr] is Auxiliary,
    ensures
        s.reachable_branch_addrs_from_with_fuel(addr, fuel) =~= set!{addr},
{
    reveal(ConcreteBranch::State::reachable_branch_addrs_from_with_fuel);
    reveal(ConcreteBranch::State::reachable_branch_addrs_from_with_fuel_contains);
    assert forall |a: Address|
        #[trigger] s.reachable_branch_addrs_from_with_fuel(addr, fuel).contains(a)
        <==> #[trigger] set!{addr}.contains(a) by {
    };
}

proof fn reachable_branch_addrs_index_contains(
    s: ConcreteBranch::State,
    addr: Address,
    fuel: nat,
    a: Address,
)
    requires
        fuel > 0,
        s.available_branch_nodes().contains_key(addr),
        !(s.available_branch_nodes()[addr] is Leaf),
        !(s.available_branch_nodes()[addr] is Auxiliary),
    ensures
        s.reachable_branch_addrs_from_with_fuel(addr, fuel).contains(a)
            <==> (
                union_seq_of_sets(Seq::new(
                    s.available_branch_nodes()[addr]->children.len(),
                    |i: int| s.reachable_branch_addrs_from_with_fuel(
                        s.available_branch_nodes()[addr]->children[i],
                        (fuel - 1) as nat,
                    ),
                ))
                + (if s.follow_aux_ptr_at(addr, s.available_branch_nodes()[addr]) {
                    s.reachable_branch_addrs_from_with_fuel(
                        s.available_branch_nodes()[addr]->aux_ptr.unwrap(),
                        (fuel - 1) as nat,
                    )
                } else {
                    Set::<Address>::empty()
                })
                + set!{addr}
            ).contains(a),
{
    let node = s.available_branch_nodes()[addr];
    let child_sets = Seq::new(
        node->children.len(),
        |i: int| s.reachable_branch_addrs_from_with_fuel(
            node->children[i],
            (fuel - 1) as nat,
        ),
    );
    let aux_set =
        if s.follow_aux_ptr_at(addr, node) {
            s.reachable_branch_addrs_from_with_fuel(
                node->aux_ptr.unwrap(),
                (fuel - 1) as nat,
            )
        } else {
            Set::<Address>::empty()
        };
    s.reachable_branch_addrs_index_contains(addr, fuel, a);
    assert(({
            ||| a == addr
            ||| s.follow_aux_ptr_at(addr, node)
                && s.reachable_branch_addrs_from_with_fuel_contains(node->aux_ptr.unwrap(), (fuel - 1) as nat, a)
            ||| exists |i: int|
                0 <= i < node->children.len()
                && s.reachable_branch_addrs_from_with_fuel_contains(node->children[i], (fuel - 1) as nat, a)
        })
        <==> (union_seq_of_sets(child_sets) + aux_set + set!{addr}).contains(a)) by {
        if a == addr
            || (s.follow_aux_ptr_at(addr, node)
                && s.reachable_branch_addrs_from_with_fuel_contains(node->aux_ptr.unwrap(), (fuel - 1) as nat, a))
            || exists |i: int|
                0 <= i < node->children.len()
                && s.reachable_branch_addrs_from_with_fuel_contains(node->children[i], (fuel - 1) as nat, a) {
            if a == addr {
                assert((union_seq_of_sets(child_sets) + aux_set + set!{addr}).contains(a));
            } else if s.follow_aux_ptr_at(addr, node)
                && s.reachable_branch_addrs_from_with_fuel_contains(node->aux_ptr.unwrap(), (fuel - 1) as nat, a) {
                assert(aux_set.contains(a));
                assert((union_seq_of_sets(child_sets) + aux_set + set!{addr}).contains(a));
            } else {
                let i = choose |i: int|
                    0 <= i < node->children.len()
                    && s.reachable_branch_addrs_from_with_fuel_contains(node->children[i], (fuel - 1) as nat, a);
                assert(0 <= i < child_sets.len());
                assert(child_sets[i].contains(a));
                lemma_set_subset_of_union_seq_of_sets(child_sets, a);
                assert((union_seq_of_sets(child_sets) + aux_set + set!{addr}).contains(a));
            }
        } else if (union_seq_of_sets(child_sets) + aux_set + set!{addr}).contains(a) {
            if a == addr {
                assert(a == addr);
            } else if aux_set.contains(a) {
                assert(s.follow_aux_ptr_at(addr, node));
                assert(s.reachable_branch_addrs_from_with_fuel_contains(node->aux_ptr.unwrap(), (fuel - 1) as nat, a));
            } else {
                assert(union_seq_of_sets(child_sets).contains(a));
                lemma_union_seq_of_sets_contains(child_sets, a);
                let i = choose |i: int| #![trigger child_sets[i].contains(a)] 0 <= i < child_sets.len() && child_sets[i].contains(a);
                assert(s.reachable_branch_addrs_from_with_fuel_contains(node->children[i], (fuel - 1) as nat, a));
            }
        }
    };
}

proof fn reachable_branch_addrs_more_fuel(
    s: ConcreteBranch::State,
    addr: Address,
    fuel: nat,
    a: Address,
)
    requires
        s.reachable_branch_addrs_from_with_fuel(addr, fuel).contains(a),
    ensures
        s.reachable_branch_addrs_from_with_fuel(addr, fuel + 1).contains(a),
    decreases fuel,
{
    if fuel == 0 {
        reachable_branch_addrs_empty_unfold(s, addr, fuel);
        assert(false);
    } else if !s.available_branch_nodes().contains_key(addr) {
        reachable_branch_addrs_empty_unfold(s, addr, fuel);
        assert(false);
    } else {
        let node = s.available_branch_nodes()[addr];
        if node is Leaf || node is Auxiliary {
            reachable_branch_addrs_leaf_unfold(s, addr, fuel);
            reachable_branch_addrs_leaf_unfold(s, addr, fuel + 1);
        } else {
            reachable_branch_addrs_index_contains(s, addr, fuel, a);
            if a == addr {
                reachable_branch_addrs_index_contains(s, addr, fuel + 1, a);
            } else if s.follow_aux_ptr_at(addr, node)
                && s.reachable_branch_addrs_from_with_fuel_contains(node->aux_ptr.unwrap(), (fuel - 1) as nat, a) {
                reachable_branch_addrs_more_fuel(s, node->aux_ptr.unwrap(), (fuel - 1) as nat, a);
                reachable_branch_addrs_index_contains(s, addr, fuel + 1, a);
                assert(s.reachable_branch_addrs_from_with_fuel_contains(node->aux_ptr.unwrap(), fuel, a));
            } else {
                let i = choose |i: int|
                    0 <= i < node->children.len()
                    && s.reachable_branch_addrs_from_with_fuel_contains(node->children[i], (fuel - 1) as nat, a);
                reachable_branch_addrs_more_fuel(s, node->children[i], (fuel - 1) as nat, a);
                reachable_branch_addrs_index_contains(s, addr, fuel + 1, a);
                assert(s.reachable_branch_addrs_from_with_fuel_contains(node->children[i], fuel, a));
            }
        }
    }
}

proof fn reachable_branch_addrs_equal_when_available_nodes_equal(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    addr: Address,
    fuel: nat,
)
    requires
        pre.cached_branch.root == post.cached_branch.root,
        pre.cached_branch.sealed == post.cached_branch.sealed,
        pre.available_branch_nodes() =~= post.available_branch_nodes(),
    ensures
        pre.reachable_branch_addrs_from_with_fuel(addr, fuel)
            == post.reachable_branch_addrs_from_with_fuel(addr, fuel),
    decreases fuel,
{
    if fuel == 0 {
        reachable_branch_addrs_empty_unfold(pre, addr, fuel);
        reachable_branch_addrs_empty_unfold(post, addr, fuel);
    } else {
        assert(pre.available_branch_nodes().contains_key(addr) <==> post.available_branch_nodes().contains_key(addr));
        if !pre.available_branch_nodes().contains_key(addr) {
            reachable_branch_addrs_empty_unfold(pre, addr, fuel);
            reachable_branch_addrs_empty_unfold(post, addr, fuel);
        } else {
            let pre_node = pre.available_branch_nodes()[addr];
            let post_node = post.available_branch_nodes()[addr];
            assert(pre_node == post_node);
            if pre_node is Leaf || pre_node is Auxiliary {
                reachable_branch_addrs_leaf_unfold(pre, addr, fuel);
                reachable_branch_addrs_leaf_unfold(post, addr, fuel);
            } else {
                let pre_child_sets = Seq::new(
                    pre_node->children.len(),
                    |i: int| pre.reachable_branch_addrs_from_with_fuel(pre_node->children[i], (fuel - 1) as nat),
                );
                let post_child_sets = Seq::new(
                    post_node->children.len(),
                    |i: int| post.reachable_branch_addrs_from_with_fuel(post_node->children[i], (fuel - 1) as nat),
                );
                assert(pre_child_sets.len() == post_child_sets.len());
                assert forall |i: int| 0 <= i < pre_child_sets.len() implies #[trigger] pre_child_sets[i] == post_child_sets[i] by {
                    assert(pre_node->children[i] == post_node->children[i]);
                    reachable_branch_addrs_equal_when_available_nodes_equal(
                        pre,
                        post,
                        pre_node->children[i],
                        (fuel - 1) as nat,
                    );
                };
                union_seq_of_sets_equal(pre_child_sets, post_child_sets);
                let pre_aux_set =
                    if pre.follow_aux_ptr_at(addr, pre_node) {
                        pre.reachable_branch_addrs_from_with_fuel(pre_node->aux_ptr.unwrap(), (fuel - 1) as nat)
                    } else {
                        Set::<Address>::empty()
                    };
                let post_aux_set =
                    if post.follow_aux_ptr_at(addr, post_node) {
                        post.reachable_branch_addrs_from_with_fuel(post_node->aux_ptr.unwrap(), (fuel - 1) as nat)
                    } else {
                        Set::<Address>::empty()
                    };
                if pre.follow_aux_ptr_at(addr, pre_node) {
                    assert(post.follow_aux_ptr_at(addr, post_node));
                    assert(pre_node->aux_ptr.unwrap() == post_node->aux_ptr.unwrap());
                    reachable_branch_addrs_equal_when_available_nodes_equal(
                        pre,
                        post,
                        pre_node->aux_ptr.unwrap(),
                        (fuel - 1) as nat,
                    );
                    assert(pre_aux_set == post_aux_set);
                } else {
                    assert(!post.follow_aux_ptr_at(addr, post_node));
                    assert(pre_aux_set == post_aux_set);
                }
                assert forall |a: Address|
                    #[trigger] pre.reachable_branch_addrs_from_with_fuel(addr, fuel).contains(a)
                    <==> post.reachable_branch_addrs_from_with_fuel(addr, fuel).contains(a) by {
                    reachable_branch_addrs_index_contains(pre, addr, fuel, a);
                    reachable_branch_addrs_index_contains(post, addr, fuel, a);
                    assert((union_seq_of_sets(pre_child_sets) + pre_aux_set + set!{addr}).contains(a)
                        <==> (union_seq_of_sets(post_child_sets) + post_aux_set + set!{addr}).contains(a));
                };
            }
        }
    }
}

proof fn reachable_branch_addrs_are_available(
    s: ConcreteBranch::State,
    addr: Address,
    fuel: nat,
)
    ensures
        s.reachable_branch_addrs_from_with_fuel(addr, fuel) <= s.available_branch_nodes().dom(),
    decreases fuel,
{
    if fuel == 0 {
        reachable_branch_addrs_empty_unfold(s, addr, fuel);
    } else if !s.available_branch_nodes().contains_key(addr) {
        reachable_branch_addrs_empty_unfold(s, addr, fuel);
    } else {
        let node = s.available_branch_nodes()[addr];
        if node is Leaf || node is Auxiliary {
            reachable_branch_addrs_leaf_unfold(s, addr, fuel);
            assert(set!{addr} <= s.available_branch_nodes().dom());
        } else {
            let child_sets = Seq::new(
                node->children.len(),
                |i: int| s.reachable_branch_addrs_from_with_fuel(node->children[i], (fuel - 1) as nat),
            );
            assert forall |i: int| 0 <= i < child_sets.len()
                implies #[trigger] child_sets[i] <= s.available_branch_nodes().dom() by {
                reachable_branch_addrs_are_available(s, node->children[i], (fuel - 1) as nat);
            };
            assert(union_seq_of_sets(child_sets) <= s.available_branch_nodes().dom()) by {
                assert forall |a: Address| #[trigger] union_seq_of_sets(child_sets).contains(a)
                    implies s.available_branch_nodes().dom().contains(a) by {
                    lemma_union_seq_of_sets_contains(child_sets, a);
                    let i = choose |i: int| #![trigger child_sets[i].contains(a)] 0 <= i < child_sets.len() && child_sets[i].contains(a);
                    assert(child_sets[i] <= s.available_branch_nodes().dom());
                };
            };
            let aux_set =
                if s.follow_aux_ptr_at(addr, node) {
                    s.reachable_branch_addrs_from_with_fuel(node->aux_ptr.unwrap(), (fuel - 1) as nat)
                } else {
                    Set::<Address>::empty()
                };
            if s.follow_aux_ptr_at(addr, node) {
                reachable_branch_addrs_are_available(s, node->aux_ptr.unwrap(), (fuel - 1) as nat);
            }
            assert(aux_set <= s.available_branch_nodes().dom());
            assert(union_seq_of_sets(child_sets) + aux_set + set!{addr} <= s.available_branch_nodes().dom()) by {
                assert forall |a: Address|
                    #[trigger] (union_seq_of_sets(child_sets) + aux_set + set!{addr}).contains(a)
                    implies s.available_branch_nodes().dom().contains(a) by {
                    if union_seq_of_sets(child_sets).contains(a) {
                    } else if aux_set.contains(a) {
                    } else {
                        assert(a == addr);
                        assert(s.available_branch_nodes().contains_key(addr));
                    }
                };
            };
            assert forall |a: Address|
                #[trigger] s.reachable_branch_addrs_from_with_fuel(addr, fuel).contains(a)
                implies s.available_branch_nodes().dom().contains(a) by {
                reachable_branch_addrs_index_contains(s, addr, fuel, a);
                assert((union_seq_of_sets(child_sets) + aux_set + set!{addr}).contains(a));
            };
        }
    }
}

proof fn overlay_branch_equal_when_available_nodes_equal(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
)
    requires
        pre.cached_branch.root == post.cached_branch.root,
        pre.cached_branch.sealed == post.cached_branch.sealed,
        pre.available_branch_nodes() =~= post.available_branch_nodes(),
    ensures
        pre.overlay_branch_entries() =~= post.overlay_branch_entries(),
        pre.overlay_branch() =~= post.overlay_branch(),
{
    assert(pre.available_branch_nodes().dom() =~= post.available_branch_nodes().dom());
    assert(pre.available_branch_nodes().dom().len() == post.available_branch_nodes().dom().len());
    match pre.cached_branch.root {
        Some(root) => {
            assert(post.cached_branch.root is Some);
            reachable_branch_addrs_equal_when_available_nodes_equal(
                pre,
                post,
                root,
                pre.available_branch_nodes().dom().len(),
            );
            assert(pre.overlay_branch_addrs() == post.overlay_branch_addrs());
        }
        None => {
            assert(post.cached_branch.root is None);
        }
    }

    assert forall |addr: Address| #[trigger] pre.overlay_branch_entries().contains_key(addr)
        <==> post.overlay_branch_entries().contains_key(addr) by {
        if pre.overlay_branch_entries().contains_key(addr) {
            assert(pre.overlay_branch_addrs().contains(addr));
            assert(post.overlay_branch_addrs().contains(addr));
        }
        if post.overlay_branch_entries().contains_key(addr) {
            assert(post.overlay_branch_addrs().contains(addr));
            assert(pre.overlay_branch_addrs().contains(addr));
        }
    };

    assert forall |addr: Address| #[trigger] pre.overlay_branch_entries().contains_key(addr)
        implies pre.overlay_branch_entries()[addr] == post.overlay_branch_entries()[addr] by {
        assert(pre.overlay_branch_addrs().contains(addr));
        assert(post.overlay_branch_addrs().contains(addr));
        match pre.cached_branch.root {
            Some(root) => {
                reachable_branch_addrs_are_available(pre, root, pre.available_branch_nodes().dom().len());
                reachable_branch_addrs_are_available(post, root, post.available_branch_nodes().dom().len());
                assert(pre.available_branch_nodes().contains_key(addr));
                assert(post.available_branch_nodes().contains_key(addr));
            }
            None => { assert(false); }
        }
        assert(pre.overlay_branch_entries()[addr] == pre.available_branch_nodes()[addr]);
        assert(post.overlay_branch_entries()[addr] == post.available_branch_nodes()[addr]);
        assert(pre.available_branch_nodes()[addr] == post.available_branch_nodes()[addr]);
    };
}

proof fn access_preserves_available_branch_nodes_dom(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre.wf(),
        post.wf(),
        Cache::State::next(pre.cache, post.cache, Cache::Label::Access{reads, writes}),
        post.disk == pre.disk,
        forall |addr: Address| #[trigger] writes.contains_key(addr) ==> pre.available_branch_nodes().contains_key(addr),
    ensures
        pre.available_branch_nodes().dom() =~= post.available_branch_nodes().dom(),
{
    assert forall |addr: Address| #[trigger] pre.available_branch_nodes().contains_key(addr)
        <==> post.available_branch_nodes().contains_key(addr) by {
        if pre.available_branch_nodes().contains_key(addr) {
            if pre.has_cached_page(addr) {
                if !writes.contains_key(addr) {
                    ConcreteBranch::State::access_unwritten_pre_cached_page_stays_cached(pre, post, reads, writes, addr);
                } else {
                    ConcreteBranch::State::access_preserves_cached_page(pre, post, reads, writes, addr);
                }
                assert(post.available_branch_nodes().contains_key(addr));
            } else {
                assert(pre.disk.content.contains_key(addr));
                assert(post.disk.content.contains_key(addr));
                assert(post.available_branch_nodes().contains_key(addr));
            }
        }
        if post.available_branch_nodes().contains_key(addr) {
            if post.has_cached_page(addr) {
                if !writes.contains_key(addr) {
                    ConcreteBranch::State::access_unwritten_post_cached_page_is_pre_cached(pre, post, reads, writes, addr);
                } else {
                    assert(pre.available_branch_nodes().contains_key(addr));
                }
                assert(pre.available_branch_nodes().contains_key(addr));
            } else {
                assert(post.disk.content.contains_key(addr));
                assert(pre.disk.content.contains_key(addr));
                assert(pre.available_branch_nodes().contains_key(addr));
            }
        }
    };
}

proof fn access_unwritten_available_branch_node_unchanged(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    addr: Address,
)
    requires
        pre.wf(),
        post.wf(),
        Cache::State::next(pre.cache, post.cache, Cache::Label::Access{reads, writes}),
        post.disk == pre.disk,
        pre.available_branch_nodes().contains_key(addr),
        !writes.contains_key(addr),
    ensures
        post.available_branch_nodes().contains_key(addr),
        post.available_branch_nodes()[addr] == pre.available_branch_nodes()[addr],
{
    if pre.has_cached_page(addr) {
        ConcreteBranch::State::access_unwritten_pre_cached_page_stays_cached(pre, post, reads, writes, addr);
        assert(post.available_branch_nodes()[addr] == decode_branch_page(post.cache_raw_page(addr)));
        assert(pre.available_branch_nodes()[addr] == decode_branch_page(pre.cache_raw_page(addr)));
    } else {
        if post.has_cached_page(addr) {
            ConcreteBranch::State::access_unwritten_post_cached_page_is_pre_cached(pre, post, reads, writes, addr);
            assert(false);
        }
        assert(pre.disk.content.contains_key(addr));
        assert(post.disk.content.contains_key(addr));
        assert(post.available_branch_nodes()[addr] == decode_branch_page(post.disk.content[addr]));
        assert(pre.available_branch_nodes()[addr] == decode_branch_page(pre.disk.content[addr]));
    }
}

proof fn access_preserves_available_branch_nodes_when_writes_empty(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    reads: Map<Address, RawPage>,
)
    requires
        pre.wf(),
        post.wf(),
        Cache::State::next(pre.cache, post.cache, Cache::Label::Access{reads, writes: Map::empty()}),
        post.disk == pre.disk,
    ensures
        pre.available_branch_nodes() =~= post.available_branch_nodes(),
{
    access_preserves_available_branch_nodes_dom(pre, post, reads, Map::empty());
    assert forall |addr: Address| #[trigger] pre.available_branch_nodes().contains_key(addr)
        implies pre.available_branch_nodes()[addr] == post.available_branch_nodes()[addr] by {
        access_unwritten_available_branch_node_unchanged(pre, post, reads, Map::empty(), addr);
    };
}

proof fn access_updates_available_branch_nodes_with_single_fresh_write(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    fresh_addr: Address,
)
    requires
        pre.wf(),
        post.wf(),
        Cache::State::next(pre.cache, post.cache, Cache::Label::Access{reads, writes}),
        post.disk == pre.disk,
        writes.dom() == set!{fresh_addr},
        !pre.available_branch_nodes().contains_key(fresh_addr),
    ensures
        post.available_branch_nodes() =~= pre.available_branch_nodes().insert(fresh_addr, to_branch_nodes(writes)[fresh_addr]),
{
    ConcreteBranch::State::access_preserves_cached_page(pre, post, reads, writes, fresh_addr);
    assert(post.available_branch_nodes().contains_key(fresh_addr));
    assert(post.available_branch_nodes()[fresh_addr] == decode_branch_page(post.cache_raw_page(fresh_addr)));
    assert(post.available_branch_nodes()[fresh_addr] == to_branch_nodes(writes)[fresh_addr]);

    assert forall |addr: Address| #[trigger] post.available_branch_nodes().contains_key(addr)
        <==> pre.available_branch_nodes().insert(fresh_addr, to_branch_nodes(writes)[fresh_addr]).contains_key(addr) by {
        if post.available_branch_nodes().contains_key(addr) {
            if addr == fresh_addr {
            } else {
                assert(!writes.contains_key(addr));
                if post.has_cached_page(addr) {
                    ConcreteBranch::State::access_unwritten_post_cached_page_is_pre_cached(pre, post, reads, writes, addr);
                    assert(pre.available_branch_nodes().contains_key(addr));
                } else {
                    assert(post.disk.content.contains_key(addr));
                    assert(pre.disk.content.contains_key(addr));
                    assert(pre.available_branch_nodes().contains_key(addr));
                }
            }
        }
        if pre.available_branch_nodes().insert(fresh_addr, to_branch_nodes(writes)[fresh_addr]).contains_key(addr) {
            if addr == fresh_addr {
                assert(post.available_branch_nodes().contains_key(addr));
            } else {
                assert(pre.available_branch_nodes().contains_key(addr));
                assert(!writes.contains_key(addr));
                if pre.has_cached_page(addr) {
                    ConcreteBranch::State::access_unwritten_pre_cached_page_stays_cached(pre, post, reads, writes, addr);
                    assert(post.available_branch_nodes().contains_key(addr));
                } else {
                    assert(pre.disk.content.contains_key(addr));
                    assert(post.disk.content.contains_key(addr));
                    assert(post.available_branch_nodes().contains_key(addr));
                }
            }
        }
    };

    assert forall |addr: Address| #[trigger] post.available_branch_nodes().contains_key(addr)
        implies post.available_branch_nodes()[addr] == pre.available_branch_nodes().insert(fresh_addr, to_branch_nodes(writes)[fresh_addr])[addr] by {
        if addr == fresh_addr {
            assert(post.available_branch_nodes()[addr] == to_branch_nodes(writes)[addr]);
        } else {
            assert(!writes.contains_key(addr));
            assert(pre.available_branch_nodes().contains_key(addr));
            access_unwritten_available_branch_node_unchanged(pre, post, reads, writes, addr);
        }
    };
}

proof fn access_updates_available_branch_nodes_with_one_fresh_write_set(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    fresh_addr: Address,
)
    requires
        pre.wf(),
        post.wf(),
        Cache::State::next(pre.cache, post.cache, Cache::Label::Access{reads, writes}),
        post.disk == pre.disk,
        writes.contains_key(fresh_addr),
        !pre.available_branch_nodes().contains_key(fresh_addr),
        forall |addr: Address| #[trigger] writes.contains_key(addr) && addr != fresh_addr
            ==> pre.available_branch_nodes().contains_key(addr),
    ensures
        post.available_branch_nodes().dom() =~= pre.available_branch_nodes().dom().insert(fresh_addr),
        forall |addr: Address| #[trigger] post.available_branch_nodes().contains_key(addr)
            ==> post.available_branch_nodes()[addr] == if writes.contains_key(addr) {
                to_branch_nodes(writes)[addr]
            } else {
                pre.available_branch_nodes()[addr]
            },
{
    assert forall |addr: Address| #[trigger] post.available_branch_nodes().contains_key(addr)
        <==> pre.available_branch_nodes().dom().insert(fresh_addr).contains(addr) by {
        if post.available_branch_nodes().contains_key(addr) {
            if writes.contains_key(addr) {
                if addr == fresh_addr {
                } else {
                    assert(pre.available_branch_nodes().contains_key(addr));
                }
            } else if post.has_cached_page(addr) {
                ConcreteBranch::State::access_unwritten_post_cached_page_is_pre_cached(pre, post, reads, writes, addr);
                assert(pre.available_branch_nodes().contains_key(addr));
            } else {
                assert(post.disk.content.contains_key(addr));
                assert(pre.disk.content.contains_key(addr));
                assert(pre.available_branch_nodes().contains_key(addr));
            }
        }
        if pre.available_branch_nodes().dom().insert(fresh_addr).contains(addr) {
            if addr == fresh_addr {
                ConcreteBranch::State::access_preserves_cached_page(pre, post, reads, writes, addr);
                assert(post.available_branch_nodes().contains_key(addr));
            } else {
                assert(pre.available_branch_nodes().contains_key(addr));
                if writes.contains_key(addr) {
                    ConcreteBranch::State::access_preserves_cached_page(pre, post, reads, writes, addr);
                    assert(post.available_branch_nodes().contains_key(addr));
                } else if pre.has_cached_page(addr) {
                    ConcreteBranch::State::access_unwritten_pre_cached_page_stays_cached(pre, post, reads, writes, addr);
                    assert(post.available_branch_nodes().contains_key(addr));
                } else {
                    assert(pre.disk.content.contains_key(addr));
                    assert(post.disk.content.contains_key(addr));
                    assert(post.available_branch_nodes().contains_key(addr));
                }
            }
        }
    };

    assert forall |addr: Address| #[trigger] post.available_branch_nodes().contains_key(addr)
        implies post.available_branch_nodes()[addr] == if writes.contains_key(addr) {
            to_branch_nodes(writes)[addr]
        } else {
            pre.available_branch_nodes()[addr]
        } by {
        if writes.contains_key(addr) {
            ConcreteBranch::State::access_preserves_cached_page(pre, post, reads, writes, addr);
            assert(post.available_branch_nodes()[addr] == decode_branch_page(post.cache_raw_page(addr)));
            assert(post.available_branch_nodes()[addr] == to_branch_nodes(writes)[addr]);
        } else {
            access_unwritten_available_branch_node_unchanged(pre, post, reads, writes, addr);
        }
    };
}

proof fn reachable_branch_addrs_equal_under_leaf_rewrite(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    leaf_addr: Address,
    addr: Address,
    fuel: nat,
)
    requires
        pre.cached_branch.root == post.cached_branch.root,
        pre.cached_branch.sealed == post.cached_branch.sealed,
        pre.available_branch_nodes().dom() =~= post.available_branch_nodes().dom(),
        forall |a: Address|
            #[trigger] pre.available_branch_nodes().contains_key(a)
            && a != leaf_addr
            ==> pre.available_branch_nodes()[a] == post.available_branch_nodes()[a],
        pre.available_branch_nodes().contains_key(leaf_addr) ==> pre.available_branch_nodes()[leaf_addr] is Leaf,
        post.available_branch_nodes().contains_key(leaf_addr) ==> post.available_branch_nodes()[leaf_addr] is Leaf,
    ensures
        pre.reachable_branch_addrs_from_with_fuel(addr, fuel)
            == post.reachable_branch_addrs_from_with_fuel(addr, fuel),
    decreases fuel,
{
    if fuel == 0 {
        reachable_branch_addrs_empty_unfold(pre, addr, fuel);
        reachable_branch_addrs_empty_unfold(post, addr, fuel);
    } else {
        assert(pre.available_branch_nodes().contains_key(addr) <==> post.available_branch_nodes().contains_key(addr));
        if !pre.available_branch_nodes().contains_key(addr) {
            reachable_branch_addrs_empty_unfold(pre, addr, fuel);
            reachable_branch_addrs_empty_unfold(post, addr, fuel);
        } else if addr == leaf_addr {
            assert(post.available_branch_nodes().contains_key(addr));
            assert(pre.available_branch_nodes()[addr] is Leaf);
            assert(post.available_branch_nodes()[addr] is Leaf);
            reachable_branch_addrs_leaf_unfold(pre, addr, fuel);
            reachable_branch_addrs_leaf_unfold(post, addr, fuel);
        } else {
            let pre_node = pre.available_branch_nodes()[addr];
            let post_node = post.available_branch_nodes()[addr];
            assert(pre_node == post_node);
            if pre_node is Leaf || pre_node is Auxiliary {
                reachable_branch_addrs_leaf_unfold(pre, addr, fuel);
                reachable_branch_addrs_leaf_unfold(post, addr, fuel);
            } else {
                let pre_child_sets = Seq::new(
                    pre_node->children.len(),
                    |i: int| pre.reachable_branch_addrs_from_with_fuel(pre_node->children[i], (fuel - 1) as nat),
                );
                let post_child_sets = Seq::new(
                    post_node->children.len(),
                    |i: int| post.reachable_branch_addrs_from_with_fuel(post_node->children[i], (fuel - 1) as nat),
                );
                assert(pre_child_sets.len() == post_child_sets.len());
                assert forall |i: int| 0 <= i < pre_child_sets.len() implies #[trigger] pre_child_sets[i] == post_child_sets[i] by {
                    reachable_branch_addrs_equal_under_leaf_rewrite(pre, post, leaf_addr, pre_node->children[i], (fuel - 1) as nat);
                };
                union_seq_of_sets_equal(pre_child_sets, post_child_sets);
                let pre_aux_set =
                    if pre.follow_aux_ptr_at(addr, pre_node) {
                        pre.reachable_branch_addrs_from_with_fuel(pre_node->aux_ptr.unwrap(), (fuel - 1) as nat)
                    } else {
                        Set::<Address>::empty()
                    };
                let post_aux_set =
                    if post.follow_aux_ptr_at(addr, post_node) {
                        post.reachable_branch_addrs_from_with_fuel(post_node->aux_ptr.unwrap(), (fuel - 1) as nat)
                    } else {
                        Set::<Address>::empty()
                    };
                if pre.follow_aux_ptr_at(addr, pre_node) {
                    reachable_branch_addrs_equal_under_leaf_rewrite(pre, post, leaf_addr, pre_node->aux_ptr.unwrap(), (fuel - 1) as nat);
                }
                assert(pre_aux_set == post_aux_set);
                assert forall |a: Address|
                    #[trigger] pre.reachable_branch_addrs_from_with_fuel(addr, fuel).contains(a)
                    <==> post.reachable_branch_addrs_from_with_fuel(addr, fuel).contains(a) by {
                    reachable_branch_addrs_index_contains(pre, addr, fuel, a);
                    reachable_branch_addrs_index_contains(post, addr, fuel, a);
                };
            }
        }
    }
}

proof fn unsealed_reachable_branch_addrs_equal_for_branch_under_fresh_write(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    branch: LinkedBranch<Summary>,
    fresh_addr: Address,
    addr: Address,
    fuel: nat,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        pre.overlay_branch() == Some(branch),
        branch.inv(),
        !pre.cached_branch.sealed,
        !post.cached_branch.sealed,
        branch.disk_view.entries.contains_key(addr),
        !branch.disk_view.entries.contains_key(fresh_addr),
        forall |a: Address| #[trigger] branch.disk_view.entries.contains_key(a) ==> {
            &&& post.available_branch_nodes().contains_key(a)
            &&& post.available_branch_nodes()[a] == branch.disk_view.entries[a]
        },
    ensures
        pre.reachable_branch_addrs_from_with_fuel(addr, fuel)
            == post.reachable_branch_addrs_from_with_fuel(addr, fuel),
    decreases fuel,
{
    if fuel == 0 {
        reachable_branch_addrs_empty_unfold(pre, addr, fuel);
        reachable_branch_addrs_empty_unfold(post, addr, fuel);
    } else {
        pre.branch_disk_entry_matches_available(branch, addr);
        assert(post.available_branch_nodes().contains_key(addr));
        let node = branch.disk_view.entries[addr];
        assert(post.available_branch_nodes()[addr] == node);
        if node is Leaf || node is Auxiliary {
            reachable_branch_addrs_leaf_unfold(pre, addr, fuel);
            reachable_branch_addrs_leaf_unfold(post, addr, fuel);
        } else {
            assert(!pre.follow_aux_ptr_at(addr, node));
            assert(!post.follow_aux_ptr_at(addr, node));
            let pre_child_sets = Seq::new(
                node->children.len(),
                |i: int| pre.reachable_branch_addrs_from_with_fuel(node->children[i], (fuel - 1) as nat),
            );
            let post_child_sets = Seq::new(
                node->children.len(),
                |i: int| post.reachable_branch_addrs_from_with_fuel(node->children[i], (fuel - 1) as nat),
            );
            assert forall |i: int| 0 <= i < pre_child_sets.len() implies #[trigger] pre_child_sets[i] == post_child_sets[i] by {
                assert(branch.disk_view.valid_address(node->children[i]));
                assert(branch.disk_view.entries.contains_key(node->children[i]));
                unsealed_reachable_branch_addrs_equal_for_branch_under_fresh_write(
                    pre,
                    post,
                    branch,
                    fresh_addr,
                    node->children[i],
                    (fuel - 1) as nat,
                );
            };
            union_seq_of_sets_equal(pre_child_sets, post_child_sets);
            assert forall |a: Address|
                #[trigger] pre.reachable_branch_addrs_from_with_fuel(addr, fuel).contains(a)
                <==> post.reachable_branch_addrs_from_with_fuel(addr, fuel).contains(a) by {
                reachable_branch_addrs_index_contains(pre, addr, fuel, a);
                reachable_branch_addrs_index_contains(post, addr, fuel, a);
                assert((union_seq_of_sets(pre_child_sets) + set!{addr}).contains(a)
                    <==> (union_seq_of_sets(post_child_sets) + set!{addr}).contains(a));
            };
        }
    }
}

proof fn reachable_branch_addrs_equal_for_unchanged_subbranch_under_except(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    branch: LinkedBranch<Summary>,
    subbranch: LinkedBranch<Summary>,
    except: Set<Address>,
    fuel: nat,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        pre.overlay_branch() == Some(branch),
        branch.inv(),
        pre.cached_branch.root == Some(branch.root),
        post.cached_branch.root == Some(branch.root),
        subbranch.disk_view == branch.disk_view,
        subbranch.inv_internal(branch.the_ranking()),
        except.contains(branch.root),
        subbranch.reachable_addrs_using_ranking(branch.the_ranking()).disjoint(except),
        forall |a: Address| #[trigger] branch.disk_view.entries.contains_key(a) && !except.contains(a) ==> {
            &&& post.available_branch_nodes().contains_key(a)
            &&& post.available_branch_nodes()[a] == branch.disk_view.entries[a]
        },
    ensures
        pre.reachable_branch_addrs_from_with_fuel(subbranch.root, fuel)
            == post.reachable_branch_addrs_from_with_fuel(subbranch.root, fuel),
    decreases fuel,
{
    if fuel == 0 {
        reachable_branch_addrs_empty_unfold(pre, subbranch.root, fuel);
        reachable_branch_addrs_empty_unfold(post, subbranch.root, fuel);
    } else {
        pre.branch_disk_entry_matches_available(branch, subbranch.root);
        assert(!except.contains(subbranch.root)) by {
            if except.contains(subbranch.root) {
                assert(subbranch.reachable_addrs_using_ranking(branch.the_ranking()).contains(subbranch.root));
            }
        };
        assert(post.available_branch_nodes().contains_key(subbranch.root));
        let node = branch.disk_view.entries[subbranch.root];
        assert(post.available_branch_nodes()[subbranch.root] == node);
        if node is Leaf || node is Auxiliary {
            reachable_branch_addrs_leaf_unfold(pre, subbranch.root, fuel);
            reachable_branch_addrs_leaf_unfold(post, subbranch.root, fuel);
        } else {
            assert(!pre.follow_aux_ptr_at(subbranch.root, node)) by {
                if pre.follow_aux_ptr_at(subbranch.root, node) {
                    assert(subbranch.root == branch.root);
                    assert(except.contains(branch.root));
                    assert(subbranch.reachable_addrs_using_ranking(branch.the_ranking()).contains(branch.root));
                }
            };
            assert(!post.follow_aux_ptr_at(subbranch.root, node)) by {
                if post.follow_aux_ptr_at(subbranch.root, node) {
                    assert(subbranch.root == branch.root);
                    assert(except.contains(branch.root));
                    assert(subbranch.reachable_addrs_using_ranking(branch.the_ranking()).contains(branch.root));
                }
            };
            let pre_child_sets = Seq::new(
                node->children.len(),
                |i: int| pre.reachable_branch_addrs_from_with_fuel(node->children[i], (fuel - 1) as nat),
            );
            let post_child_sets = Seq::new(
                node->children.len(),
                |i: int| post.reachable_branch_addrs_from_with_fuel(node->children[i], (fuel - 1) as nat),
            );
            assert forall |i: int| 0 <= i < pre_child_sets.len() implies #[trigger] pre_child_sets[i] == post_child_sets[i] by {
                assert(subbranch.root().valid_child_index(i));
                child_branch_inv_internal_from_parent(subbranch, branch.the_ranking(), i);
                crate::betree::LinkedBranch_v::Refinement_v::lemma_reachable_disjoint_implies_child_reachable_disjoint(
                    subbranch,
                    branch.the_ranking(),
                    except,
                    i,
                );
                reachable_branch_addrs_equal_for_unchanged_subbranch_under_except(
                    pre,
                    post,
                    branch,
                    subbranch.child_at_idx(i),
                    except,
                    (fuel - 1) as nat,
                );
            };
            union_seq_of_sets_equal(pre_child_sets, post_child_sets);
            assert forall |a: Address|
                #[trigger] pre.reachable_branch_addrs_from_with_fuel(subbranch.root, fuel).contains(a)
                <==> post.reachable_branch_addrs_from_with_fuel(subbranch.root, fuel).contains(a) by {
                reachable_branch_addrs_index_contains(pre, subbranch.root, fuel, a);
                reachable_branch_addrs_index_contains(post, subbranch.root, fuel, a);
                assert((union_seq_of_sets(pre_child_sets) + set!{subbranch.root}).contains(a)
                    <==> (union_seq_of_sets(post_child_sets) + set!{subbranch.root}).contains(a));
            };
        }
    }
}

proof fn sealed_root_reachable_branch_addrs_equal_under_aux_write(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    branch: LinkedBranch<Summary>,
    aux_addr: Address,
    fuel: nat,
)
    requires
        fuel > 1,
        pre.refinement_wf(),
        post.wf(),
        pre.overlay_branch() == Some(branch),
        branch.inv(),
        !pre.cached_branch.sealed,
        post.cached_branch.sealed,
        pre.cached_branch.root == Some(branch.root),
        post.cached_branch.root == Some(branch.root),
        branch.root() is Index,
        !branch.disk_view.entries.contains_key(aux_addr),
        forall |a: Address| #[trigger] branch.disk_view.entries.contains_key(a) && a != branch.root ==> {
            &&& post.available_branch_nodes().contains_key(a)
            &&& post.available_branch_nodes()[a] == branch.disk_view.entries[a]
        },
        post.available_branch_nodes().contains_key(branch.root),
        post.available_branch_nodes()[branch.root] == branch.seal(aux_addr, pre.mini_allocator.reserved_aus()).disk_view.entries[branch.root],
        post.available_branch_nodes().contains_key(aux_addr),
        post.available_branch_nodes()[aux_addr] == branch.seal(aux_addr, pre.mini_allocator.reserved_aus()).disk_view.entries[aux_addr],
    ensures
        post.reachable_branch_addrs_from_with_fuel(branch.root, fuel)
            == pre.reachable_branch_addrs_from_with_fuel(branch.root, fuel).insert(aux_addr),
{
    let ranking = branch.the_ranking();
    let root = branch.root;
    let node = branch.root();
    let except = set!{root, aux_addr};
    let pre_child_sets = Seq::new(
        node->children.len(),
        |i: int| pre.reachable_branch_addrs_from_with_fuel(node->children[i], (fuel - 1) as nat),
    );
    let post_child_sets = Seq::new(
        node->children.len(),
        |i: int| post.reachable_branch_addrs_from_with_fuel(node->children[i], (fuel - 1) as nat),
    );
    assert forall |i: int| 0 <= i < pre_child_sets.len() implies #[trigger] pre_child_sets[i] == post_child_sets[i] by {
        assert(branch.root().valid_child_index(i));
        child_branch_inv_internal_from_parent(branch, ranking, i);
        let child = branch.child_at_idx(i);
        assert(child.reachable_addrs_using_ranking(ranking).disjoint(except)) by {
            if child.reachable_addrs_using_ranking(ranking).contains(root) {
                crate::betree::LinkedBranch_v::Refinement_v::lemma_reachable_child_has_smaller_rank(child, ranking, root);
                assert(branch.children_reachable_addrs_using_ranking(ranking)[i].contains(child.root));
                crate::betree::LinkedBranch_v::Refinement_v::lemma_reachable_child_has_smaller_rank(branch, ranking, child.root);
            } else if child.reachable_addrs_using_ranking(ranking).contains(aux_addr) {
                crate::betree::LinkedBranch_v::Refinement_v::lemma_reachable_implies_valid_address(child, ranking, aux_addr);
            }
        };
        reachable_branch_addrs_equal_for_unchanged_subbranch_under_except(
            pre,
            post,
            branch,
            child,
            except,
            (fuel - 1) as nat,
        );
    };
    union_seq_of_sets_equal(pre_child_sets, post_child_sets);
    assert(!pre.follow_aux_ptr_at(root, node));
    assert(post.follow_aux_ptr_at(root, post.available_branch_nodes()[root]));
    reachable_branch_addrs_leaf_unfold(post, aux_addr, (fuel - 1) as nat);
    assert(post.reachable_branch_addrs_from_with_fuel(aux_addr, (fuel - 1) as nat) == set!{aux_addr});
    assert forall |a: Address|
        #[trigger] post.reachable_branch_addrs_from_with_fuel(root, fuel).contains(a)
        <==> pre.reachable_branch_addrs_from_with_fuel(root, fuel).insert(aux_addr).contains(a) by {
        reachable_branch_addrs_index_contains(pre, root, fuel, a);
        reachable_branch_addrs_index_contains(post, root, fuel, a);
        assert((union_seq_of_sets(post_child_sets)
            + post.reachable_branch_addrs_from_with_fuel(aux_addr, (fuel - 1) as nat)
            + set!{root}).contains(a)
            <==> (union_seq_of_sets(pre_child_sets) + set!{root}).insert(aux_addr).contains(a));
    };
}

proof fn unsealed_reachable_branch_addrs_equal_for_unchanged_subbranch_under_except(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    branch: LinkedBranch<Summary>,
    subbranch: LinkedBranch<Summary>,
    except: Set<Address>,
    fuel: nat,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        pre.overlay_branch() == Some(branch),
        branch.inv(),
        !pre.cached_branch.sealed,
        !post.cached_branch.sealed,
        subbranch.disk_view == branch.disk_view,
        subbranch.inv_internal(branch.the_ranking()),
        subbranch.reachable_addrs_using_ranking(branch.the_ranking()).disjoint(except),
        forall |a: Address| #[trigger] branch.disk_view.entries.contains_key(a) && !except.contains(a) ==> {
            &&& post.available_branch_nodes().contains_key(a)
            &&& post.available_branch_nodes()[a] == branch.disk_view.entries[a]
        },
    ensures
        pre.reachable_branch_addrs_from_with_fuel(subbranch.root, fuel)
            == post.reachable_branch_addrs_from_with_fuel(subbranch.root, fuel),
    decreases fuel,
{
    if fuel == 0 {
        reachable_branch_addrs_empty_unfold(pre, subbranch.root, fuel);
        reachable_branch_addrs_empty_unfold(post, subbranch.root, fuel);
    } else {
        pre.branch_disk_entry_matches_available(branch, subbranch.root);
        assert(post.available_branch_nodes().contains_key(subbranch.root));
        let node = branch.disk_view.entries[subbranch.root];
        assert(post.available_branch_nodes()[subbranch.root] == node);
        if node is Leaf || node is Auxiliary {
            reachable_branch_addrs_leaf_unfold(pre, subbranch.root, fuel);
            reachable_branch_addrs_leaf_unfold(post, subbranch.root, fuel);
        } else {
            assert(!pre.follow_aux_ptr_at(subbranch.root, node));
            assert(!post.follow_aux_ptr_at(subbranch.root, node));
            let pre_child_sets = Seq::new(
                node->children.len(),
                |i: int| pre.reachable_branch_addrs_from_with_fuel(node->children[i], (fuel - 1) as nat),
            );
            let post_child_sets = Seq::new(
                node->children.len(),
                |i: int| post.reachable_branch_addrs_from_with_fuel(node->children[i], (fuel - 1) as nat),
            );
            assert forall |i: int| 0 <= i < pre_child_sets.len() implies #[trigger] pre_child_sets[i] == post_child_sets[i] by {
                assert(subbranch.root().valid_child_index(i));
                child_branch_inv_internal_from_parent(subbranch, branch.the_ranking(), i);
                crate::betree::LinkedBranch_v::Refinement_v::lemma_reachable_disjoint_implies_child_reachable_disjoint(
                    subbranch,
                    branch.the_ranking(),
                    except,
                    i,
                );
                unsealed_reachable_branch_addrs_equal_for_unchanged_subbranch_under_except(
                    pre,
                    post,
                    branch,
                    subbranch.child_at_idx(i),
                    except,
                    (fuel - 1) as nat,
                );
            };
            union_seq_of_sets_equal(pre_child_sets, post_child_sets);
            assert forall |a: Address|
                #[trigger] pre.reachable_branch_addrs_from_with_fuel(subbranch.root, fuel).contains(a)
                <==> post.reachable_branch_addrs_from_with_fuel(subbranch.root, fuel).contains(a) by {
                reachable_branch_addrs_index_contains(pre, subbranch.root, fuel, a);
                reachable_branch_addrs_index_contains(post, subbranch.root, fuel, a);
                assert((union_seq_of_sets(pre_child_sets) + set!{subbranch.root}).contains(a)
                    <==> (union_seq_of_sets(post_child_sets) + set!{subbranch.root}).contains(a));
            };
        }
    }
}

proof fn concrete_reachable_from_overlay_branch_implies_in_disk_view(
    pre: ConcreteBranch::State,
    branch: LinkedBranch<Summary>,
    addr: Address,
    fuel: nat,
    a: Address,
)
    requires
        pre.refinement_wf(),
        pre.overlay_branch() == Some(branch),
        branch.inv(),
        branch.disk_view.entries.contains_key(addr),
        pre.reachable_branch_addrs_from_with_fuel(addr, fuel).contains(a),
    ensures
        branch.disk_view.entries.contains_key(a),
    decreases fuel,
{
    if fuel == 0 {
        assert(false);
    } else {
        pre.branch_disk_entry_matches_available(branch, addr);
        let node = branch.disk_view.entries[addr];
        if node is Leaf || node is Auxiliary {
            reachable_branch_addrs_leaf_unfold(pre, addr, fuel);
            assert(a == addr);
        } else {
            reachable_branch_addrs_index_contains(pre, addr, fuel, a);
            if a == addr {
            } else if pre.follow_aux_ptr_at(addr, node)
                && pre.reachable_branch_addrs_from_with_fuel(node->aux_ptr.unwrap(), (fuel - 1) as nat).contains(a) {
                assert(branch.disk_view.entries.contains_key(node->aux_ptr.unwrap()));
                concrete_reachable_from_overlay_branch_implies_in_disk_view(
                    pre,
                    branch,
                    node->aux_ptr.unwrap(),
                    (fuel - 1) as nat,
                    a,
                );
            } else {
                let i = choose |i: int|
                    0 <= i < node->children.len()
                    && pre.reachable_branch_addrs_from_with_fuel_contains(node->children[i], (fuel - 1) as nat, a);
                assert(branch.disk_view.valid_address(node->children[i]));
                concrete_reachable_from_overlay_branch_implies_in_disk_view(
                    pre,
                    branch,
                    node->children[i],
                    (fuel - 1) as nat,
                    a,
                );
            }
        }
    }
}

pub open spec fn allocation_branch_can_grow(branch: AllocationBranch, addr: Address) -> bool
{
    &&& !branch.sealed
    &&& branch.branch is Some
    &&& branch.mini_allocator.can_allocate(addr)
    &&& branch.branch.unwrap().can_grow(addr)
}

pub open spec fn allocation_branch_grow(branch: AllocationBranch, addr: Address) -> AllocationBranch
    recommends allocation_branch_can_grow(branch, addr)
{
    AllocationBranch {
        branch: Some(branch.branch.unwrap().grow(addr)),
        mini_allocator: branch.mini_allocator.allocate(addr),
        ..branch
    }
}

pub open spec fn allocation_branch_can_seal(branch: AllocationBranch, ptr: Pointer) -> bool
{
    &&& !branch.sealed
    &&& branch.branch is Some
    &&& (ptr is Some <==> branch.branch.unwrap().root() is Index)
    &&& (ptr is Some ==> branch.mini_allocator.can_allocate(ptr.unwrap()))
}

pub open spec fn allocation_branch_seal(branch: AllocationBranch, ptr: Pointer) -> AllocationBranch
    recommends allocation_branch_can_seal(branch, ptr)
{
    let post_allocator =
        if ptr is Some {
            branch.mini_allocator.allocate(ptr.unwrap()).prune(Set::empty())
        } else {
            branch.mini_allocator.prune(Set::empty())
        };
    let sealed_branch =
        if ptr is Some {
            branch.branch.unwrap().seal(ptr.unwrap(), branch.mini_allocator.reserved_aus())
        } else {
            branch.branch.unwrap()
        };
    AllocationBranch {
        sealed: true,
        branch: Some(sealed_branch),
        mini_allocator: MiniAllocator::empty().add_aus(post_allocator.all_aus()),
    }
}

impl ConcreteBranch::State {
    proof fn internal_disk_preserves_available_branch_nodes(
        pre: Self,
        post: Self,
        new_disk: crate::spec::AsyncDisk_t::AsyncDisk::State,
    )
        requires
            pre.wf(),
            post.wf(),
            crate::spec::AsyncDisk_t::AsyncDisk::State::next(pre.disk, new_disk, crate::spec::AsyncDisk_t::AsyncDisk::Label::Internal{}),
            post.cached_branch == pre.cached_branch,
            post.mini_allocator == pre.mini_allocator,
            post.cache == pre.cache,
            post.disk == new_disk,
            post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
        ensures
            pre.available_branch_nodes() =~= post.available_branch_nodes(),
    {
        reveal(crate::spec::AsyncDisk_t::AsyncDisk::State::next);
        reveal(crate::spec::AsyncDisk_t::AsyncDisk::State::next_by);
        let disk_step = choose |dstep|
            crate::spec::AsyncDisk_t::AsyncDisk::State::next_by(
                pre.disk,
                post.disk,
                crate::spec::AsyncDisk_t::AsyncDisk::Label::Internal{},
                dstep,
            );
        assert forall |addr: Address| #[trigger] pre.available_branch_nodes().contains_key(addr)
            <==> post.available_branch_nodes().contains_key(addr) by {
            if pre.available_branch_nodes().contains_key(addr) {
                if pre.has_cached_page(addr) {
                    assert(post.has_cached_page(addr));
                } else {
                    assert(pre.disk.content.contains_key(addr));
                    if disk_step is process_write {
                        let id = disk_step.get_process_write_0();
                        let req = pre.disk.requests[id];
                        let write_addr = req->to;
                        if addr == write_addr {
                            let slot = pre.cache.lookup_map[addr];
                            assert(pre.cache.entries[slot] == Entry::Filled{addr, data: req->data});
                            assert(pre.has_cached_page(addr));
                            assert(false);
                        }
                    }
                    assert(post.disk.content.contains_key(addr));
                }
            }
            if post.available_branch_nodes().contains_key(addr) {
                if post.has_cached_page(addr) {
                    assert(pre.has_cached_page(addr));
                } else {
                    assert(post.disk.content.contains_key(addr));
                    if disk_step is process_write {
                        let id = disk_step.get_process_write_0();
                        let req = pre.disk.requests[id];
                        let write_addr = req->to;
                        if addr == write_addr {
                            let slot = pre.cache.lookup_map[addr];
                            assert(pre.cache.entries[slot] == Entry::Filled{addr, data: req->data});
                            assert(pre.has_cached_page(addr));
                            assert(false);
                        }
                    }
                    assert(pre.disk.content.contains_key(addr));
                }
            }
        };
        assert forall |addr: Address| #[trigger] pre.available_branch_nodes().contains_key(addr)
            implies pre.available_branch_nodes()[addr] == post.available_branch_nodes()[addr] by {
            if pre.has_cached_page(addr) {
                assert(post.has_cached_page(addr));
                assert(pre.cache_raw_page(addr) == post.cache_raw_page(addr));
            } else {
                assert(pre.disk.content.contains_key(addr));
                if disk_step is process_write {
                    let id = disk_step.get_process_write_0();
                    let req = pre.disk.requests[id];
                    let write_addr = req->to;
                    if addr == write_addr {
                        let slot = pre.cache.lookup_map[addr];
                        assert(pre.cache.entries[slot] == Entry::Filled{addr, data: req->data});
                        assert(pre.has_cached_page(addr));
                        assert(false);
                    }
                } else {
                    assert(post.disk.content == pre.disk.content);
                }
                assert(post.disk.content.contains_key(addr));
                assert(pre.disk.content[addr] == post.disk.content[addr]);
            }
            assert(pre.available_raw_pages()[addr] == post.available_raw_pages()[addr]);
            assert(pre.available_branch_nodes()[addr] == decode_branch_page(pre.available_raw_pages()[addr]));
            assert(post.available_branch_nodes()[addr] == decode_branch_page(post.available_raw_pages()[addr]));
        };
    }

    proof fn internal_cache_preserves_available_branch_nodes(
        pre: Self,
        post: Self,
        new_cache: Cache::State,
    )
        requires
            pre.wf(),
            post.wf(),
            Cache::State::next(pre.cache, new_cache, Cache::Label::Internal{}),
            post.cached_branch == pre.cached_branch,
            post.mini_allocator == pre.mini_allocator,
            post.cache == new_cache,
            post.disk == pre.disk,
        ensures
            pre.available_branch_nodes() =~= post.available_branch_nodes(),
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let step = choose |step| Cache::State::next_by(pre.cache, post.cache, Cache::Label::Internal{}, step);
        assert forall |addr: Address| #[trigger] pre.available_branch_nodes().contains_key(addr)
            <==> post.available_branch_nodes().contains_key(addr) by {
            if pre.available_branch_nodes().contains_key(addr) {
                if pre.has_cached_page(addr) {
                    cache_has_cached_page_gets_addr(pre.cache, addr);
                    let slot = pre.cache.lookup_map[addr];
                    if step is reserve {
                        let new_slots_mapping = step.get_reserve_0();
                        assert(!new_slots_mapping.contains_key(slot));
                        assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                        assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                        cache_filled_entry_in_lookup(post.cache, slot);
                        assert(post.has_cached_page(addr));
                    } else if step is evict {
                        let evicted_slots = step.get_evict_0();
                        if evicted_slots.contains(slot) {
                            assert(pre.cache.status_map[slot] is Clean);
                            assert(pre.cache_raw_page(addr) == pre.disk.content[addr]);
                            assert(post.disk.content.contains_key(addr));
                        } else {
                            assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                            assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                            cache_filled_entry_in_lookup(post.cache, slot);
                            assert(post.has_cached_page(addr));
                        }
                    } else {
                        assert(post.cache == pre.cache);
                        assert(post.has_cached_page(addr));
                    }
                } else {
                    assert(pre.disk.content.contains_key(addr));
                    assert(post.disk.content.contains_key(addr));
                }
            }
            if post.available_branch_nodes().contains_key(addr) {
                if post.has_cached_page(addr) {
                    cache_has_cached_page_gets_addr(post.cache, addr);
                    let slot = post.cache.lookup_map[addr];
                    if step is reserve {
                        let new_slots_mapping = step.get_reserve_0();
                        assert(!new_slots_mapping.contains_key(slot)) by {
                            if new_slots_mapping.contains_key(slot) {
                                assert(post.cache.entries[slot] is Reserved);
                                assert(post.cache.entries[slot] is Filled);
                                assert(false);
                            }
                        };
                        assert(pre.cache.entries[slot] == post.cache.entries[slot]);
                        cache_filled_entry_in_lookup(pre.cache, slot);
                        assert(pre.has_cached_page(addr));
                    } else if step is evict {
                        let evicted_slots = step.get_evict_0();
                        assert(!evicted_slots.contains(slot)) by {
                            if evicted_slots.contains(slot) {
                                assert(post.cache.entries[slot] is Empty);
                                assert(post.cache.entries[slot] is Filled);
                                assert(false);
                            }
                        };
                        assert(pre.cache.entries[slot] == post.cache.entries[slot]);
                        cache_filled_entry_in_lookup(pre.cache, slot);
                        assert(pre.has_cached_page(addr));
                    } else {
                        assert(post.cache == pre.cache);
                        assert(pre.has_cached_page(addr));
                    }
                } else {
                    assert(post.disk.content.contains_key(addr));
                    assert(pre.disk.content.contains_key(addr));
                }
            }
        };
        assert forall |addr: Address| #[trigger] pre.available_branch_nodes().contains_key(addr)
            implies pre.available_branch_nodes()[addr] == post.available_branch_nodes()[addr] by {
            if pre.has_cached_page(addr) {
                cache_has_cached_page_gets_addr(pre.cache, addr);
                    let slot = pre.cache.lookup_map[addr];
                    if step is reserve {
                        let new_slots_mapping = step.get_reserve_0();
                        assert(!new_slots_mapping.contains_key(slot));
                        assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                        assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                        cache_filled_entry_in_lookup(post.cache, slot);
                        assert(post.has_cached_page(addr));
                    } else if step is evict {
                        let evicted_slots = step.get_evict_0();
                        if evicted_slots.contains(slot) {
                            assert(pre.cache.status_map[slot] is Clean);
                            assert(pre.cache_raw_page(addr) == pre.disk.content[addr]);
                            assert(post.available_raw_pages()[addr] == post.disk.content[addr]);
                        } else {
                            assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                            assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                            cache_filled_entry_in_lookup(post.cache, slot);
                            assert(post.has_cached_page(addr));
                        }
                    } else {
                        assert(post.cache == pre.cache);
                        assert(post.has_cached_page(addr));
                    }
                } else {
                    assert(pre.disk.content.contains_key(addr));
                    if step is reserve {
                        let new_slots_mapping = step.get_reserve_0();
                        assert(!post.has_cached_page(addr)) by {
                            if post.has_cached_page(addr) {
                                cache_has_cached_page_gets_addr(post.cache, addr);
                                let slot = post.cache.lookup_map[addr];
                                if new_slots_mapping.contains_key(slot) {
                                    assert(post.cache.entries[slot] is Reserved);
                                    assert(post.cache.entries[slot] is Filled);
                                    assert(false);
                                }
                                assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                                assert(pre.cache.entries[slot] is Filled);
                                cache_filled_entry_in_lookup(pre.cache, slot);
                                assert(pre.has_cached_page(addr));
                                assert(false);
                            }
                        };
                    } else if step is evict {
                        let evicted_slots = step.get_evict_0();
                        assert(!post.has_cached_page(addr)) by {
                            if post.has_cached_page(addr) {
                                cache_has_cached_page_gets_addr(post.cache, addr);
                                let slot = post.cache.lookup_map[addr];
                                assert(!evicted_slots.contains(slot)) by {
                                    if evicted_slots.contains(slot) {
                                        assert(post.cache.entries[slot] is Empty);
                                        assert(post.cache.entries[slot] is Filled);
                                        assert(false);
                                    }
                                };
                                assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                                assert(pre.cache.entries[slot] is Filled);
                                cache_filled_entry_in_lookup(pre.cache, slot);
                                assert(pre.has_cached_page(addr));
                                assert(false);
                            }
                        };
                    } else {
                        assert(!post.has_cached_page(addr));
                    }
                    assert(post.available_raw_pages()[addr] == post.disk.content[addr]);
                }
            assert(pre.available_branch_nodes()[addr] == decode_branch_page(pre.available_raw_pages()[addr]));
            assert(post.available_branch_nodes()[addr] == decode_branch_page(post.available_raw_pages()[addr]));
            assert(pre.available_raw_pages()[addr] == post.available_raw_pages()[addr]);
        };
    }

    proof fn cache_disk_ops_preserves_available_branch_nodes(
        pre: Self,
        post: Self,
        new_cache: Cache::State,
        new_disk: crate::spec::AsyncDisk_t::AsyncDisk::State,
        cache_requests: Set<DiskRequest>,
        cache_responses: Map<Address, DiskResponse>,
        disk_requests: Map<ID, DiskRequest>,
        disk_responses: Map<ID, DiskResponse>,
    )
        requires
            pre.wf(),
            post.wf(),
            pre.disk_requests_match_cache_requests(cache_requests, disk_requests),
            pre.disk_responses_match_cache_responses(cache_responses, disk_responses),
            Cache::State::next(pre.cache, new_cache, Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses}),
            crate::spec::AsyncDisk_t::AsyncDisk::State::next(
                pre.disk,
                new_disk,
                crate::spec::AsyncDisk_t::AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses},
            ),
            post.cached_branch == pre.cached_branch,
            post.mini_allocator == pre.mini_allocator,
            post.cache == new_cache,
            post.disk == new_disk,
        ensures
            pre.available_branch_nodes() =~= post.available_branch_nodes(),
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let cache_lbl = Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses};
        let cache_step = choose |step| Cache::State::next_by(pre.cache, post.cache, cache_lbl, step);
        reveal(crate::spec::AsyncDisk_t::AsyncDisk::State::next);
        reveal(crate::spec::AsyncDisk_t::AsyncDisk::State::next_by);
        let disk_lbl = crate::spec::AsyncDisk_t::AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses};
        let disk_step = choose |step| crate::spec::AsyncDisk_t::AsyncDisk::State::next_by(pre.disk, post.disk, disk_lbl, step);
        match disk_step {
            crate::spec::AsyncDisk_t::AsyncDisk::Step::disk_ops() => {
                assert(post.disk.content == pre.disk.content);
            }
            _ => { assert(false); }
        }
        assert forall |addr: Address| #[trigger] pre.available_branch_nodes().contains_key(addr)
            <==> post.available_branch_nodes().contains_key(addr) by {
            if pre.available_branch_nodes().contains_key(addr) {
                if pre.has_cached_page(addr) {
                    cache_has_cached_page_gets_addr(pre.cache, addr);
                    if cache_step is load_initiate {
                        assert(post.has_cached_page(addr) == pre.has_cached_page(addr));
                    } else if cache_step is load_complete {
                        if pre.has_cached_page(addr) {
                            assert(!cache_responses.contains_key(addr)) by {
                                if cache_responses.contains_key(addr) {
                                    assert(pre.cache.lookup_map.contains_key(addr));
                                    assert(pre.cache.entries[pre.cache.lookup_map[addr]] is Loading);
                                    assert(pre.cache.entries[pre.cache.lookup_map[addr]] is Filled);
                                    assert(false);
                                }
                            };
                            assert(post.cache.lookup_map == pre.cache.lookup_map);
                            assert(post.cache.entries[pre.cache.lookup_map[addr]] == pre.cache.entries[pre.cache.lookup_map[addr]]);
                            assert(post.cache.status_map[pre.cache.lookup_map[addr]] == pre.cache.status_map[pre.cache.lookup_map[addr]]);
                            assert(post.has_cached_page(addr));
                        } else {
                            assert(pre.disk.content.contains_key(addr));
                            assert(post.disk.content.contains_key(addr));
                        }
                    } else {
                        assert(post.has_cached_page(addr) == pre.has_cached_page(addr));
                    }
                } else {
                    assert(pre.disk.content.contains_key(addr));
                    assert(post.disk.content.contains_key(addr));
                }
            }
            if post.available_branch_nodes().contains_key(addr) {
                if post.has_cached_page(addr) {
                    cache_has_cached_page_gets_addr(post.cache, addr);
                    if cache_step is load_complete {
                        if !pre.has_cached_page(addr) {
                            assert(cache_responses.contains_key(addr)) by {
                                let slot = post.cache.lookup_map[addr];
                                if !cache_responses.contains_key(addr) {
                                    assert(pre.cache.lookup_map == post.cache.lookup_map);
                                    assert(pre.cache.lookup_map.contains_key(addr));
                                    assert(pre.cache.lookup_map[addr] == slot);
                                    let restricted_lookup = pre.cache.lookup_map.restrict(cache_responses.dom());
                                    let slot_addr_map = restricted_lookup.invert();
                                    if slot_addr_map.contains_key(slot) {
                                        let resp_addr = slot_addr_map[slot];
                                        invert_contains_pair(restricted_lookup, slot);
                                        assert(restricted_lookup.contains_pair(resp_addr, slot));
                                        assert(pre.cache.lookup_map.contains_key(resp_addr));
                                        assert(pre.cache.lookup_map[resp_addr] == slot);
                                        pre.cache.build_lookup_map_ensures();
                                        assert(pre.cache.lookup_map.is_injective());
                                        assert(resp_addr == addr);
                                        assert(cache_responses.contains_key(addr));
                                        assert(false);
                                    }
                                    assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                                    assert(post.cache.entries[slot] is Filled);
                                    assert(pre.cache.entries[slot] is Filled);
                                    cache_filled_entry_in_lookup(pre.cache, slot);
                                    assert(pre.has_cached_page(addr));
                                    assert(false);
                                }
                            };
                            assert(post.cache_raw_page(addr) == cache_responses[addr]->data);
                            assert(pre.disk.content.contains_key(addr));
                            assert(cache_responses[addr]->data == pre.disk.content[addr]);
                        }
                    } else if cache_step is load_initiate {
                        assert(pre.has_cached_page(addr)) by {
                            if !pre.has_cached_page(addr) {
                                let slot = post.cache.lookup_map[addr];
                                let new_slots_mapping = cache_step.get_load_initiate_0();
                                if new_slots_mapping.contains_key(slot) {
                                    assert(post.cache.entries[slot] is Loading);
                                    assert(post.cache.entries[slot] is Filled);
                                    assert(false);
                                }
                                assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                                assert(post.cache.entries[slot] is Filled);
                                assert(pre.cache.entries[slot] is Filled);
                                cache_filled_entry_in_lookup(pre.cache, slot);
                                assert(pre.has_cached_page(addr));
                                assert(false);
                            }
                        };
                    } else {
                        assert(pre.has_cached_page(addr));
                    }
                } else {
                    assert(post.disk.content.contains_key(addr));
                    assert(pre.disk.content.contains_key(addr));
                }
            }
        };
        assert forall |addr: Address| #[trigger] pre.available_branch_nodes().contains_key(addr)
            implies pre.available_branch_nodes()[addr] == post.available_branch_nodes()[addr] by {
            if pre.has_cached_page(addr) {
                cache_has_cached_page_gets_addr(pre.cache, addr);
            }
            assert(post.disk.content == pre.disk.content);
            if !pre.has_cached_page(addr) {
                assert(pre.available_raw_pages()[addr] == pre.disk.content[addr]);
                if post.has_cached_page(addr) {
                    Self::cache_disk_ops_new_cached_page_matches_disk(
                        pre,
                        post,
                        cache_requests,
                        cache_responses,
                        disk_requests,
                        disk_responses,
                        addr,
                    );
                    assert(post.available_raw_pages()[addr] == post.cache_raw_page(addr));
                } else {
                    assert(post.available_raw_pages()[addr] == post.disk.content[addr]);
                }
            }
            assert(pre.available_branch_nodes()[addr] == decode_branch_page(pre.available_raw_pages()[addr]));
            assert(post.available_branch_nodes()[addr] == decode_branch_page(post.available_raw_pages()[addr]));
            assert(pre.available_raw_pages()[addr] == post.available_raw_pages()[addr]);
        };
    }

    proof fn cache_disk_ops_new_cached_page_matches_disk(
        pre: Self,
        post: Self,
        cache_requests: Set<DiskRequest>,
        cache_responses: Map<Address, DiskResponse>,
        disk_requests: Map<ID, DiskRequest>,
        disk_responses: Map<ID, DiskResponse>,
        addr: Address,
    )
        requires
            pre.wf(),
            post.wf(),
            pre.disk_responses_match_cache_responses(cache_responses, disk_responses),
            Cache::State::next(pre.cache, post.cache, Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses}),
            crate::spec::AsyncDisk_t::AsyncDisk::State::next(
                pre.disk,
                post.disk,
                crate::spec::AsyncDisk_t::AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses},
            ),
            !pre.has_cached_page(addr),
            post.has_cached_page(addr),
        ensures
            cache_responses.contains_key(addr),
            post.cache_raw_page(addr) == cache_responses[addr]->data,
            cache_responses[addr]->data == pre.disk.content[addr],
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let cache_lbl = Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses};
        let cache_step = choose |step| Cache::State::next_by(pre.cache, post.cache, cache_lbl, step);
        reveal(crate::spec::AsyncDisk_t::AsyncDisk::State::next);
        reveal(crate::spec::AsyncDisk_t::AsyncDisk::State::next_by);
        let disk_lbl = crate::spec::AsyncDisk_t::AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses};
        let disk_step = choose |step| crate::spec::AsyncDisk_t::AsyncDisk::State::next_by(pre.disk, post.disk, disk_lbl, step);
        match disk_step {
            crate::spec::AsyncDisk_t::AsyncDisk::Step::disk_ops() => {
                assert(post.disk.content == pre.disk.content);
            }
            _ => { assert(false); }
        }
        cache_has_cached_page_gets_addr(post.cache, addr);
        match cache_step {
            Cache::Step::load_complete() => {
                let slot = post.cache.lookup_map[addr];
                let restricted_lookup = pre.cache.lookup_map.restrict(cache_responses.dom());
                let slot_addr_map = restricted_lookup.invert();
                let updated_entries = Map::new(
                    |slt| slot_addr_map.contains_key(slt),
                    |slt| Entry::Filled{
                        addr: slot_addr_map[slt],
                        data: cache_responses[slot_addr_map[slt]]->data
                    }
                );
                assert(pre.cache.lookup_map == post.cache.lookup_map);
                assert(post.cache.entries == pre.cache.entries.union_prefer_right(updated_entries));
                assert(pre.cache.lookup_map.contains_key(addr));
                assert(pre.cache.lookup_map[addr] == slot);
                if slot_addr_map.contains_key(slot) {
                    let resp_addr = slot_addr_map[slot];
                    invert_contains_pair(restricted_lookup, slot);
                    assert(restricted_lookup.contains_pair(resp_addr, slot));
                    assert(pre.cache.lookup_map.contains_key(resp_addr));
                    assert(pre.cache.lookup_map[resp_addr] == slot);
                    pre.cache.build_lookup_map_ensures();
                    assert(pre.cache.lookup_map.is_injective());
                    assert(resp_addr == addr);
                    union_prefer_right_uses_right(pre.cache.entries, updated_entries, slot);
                    assert(post.cache.entries[slot] == updated_entries[slot]);
                    assert(post.cache.entries[slot] == Entry::Filled{addr, data: cache_responses[addr]->data});
                } else {
                    assert(pre.cache.entries.contains_key(slot)) by {
                        if !pre.cache.entries.contains_key(slot) {
                            assert(!updated_entries.contains_key(slot));
                            assert(!pre.cache.entries.union_prefer_right(updated_entries).contains_key(slot));
                            assert(post.cache.entries == pre.cache.entries.union_prefer_right(updated_entries));
                            assert(post.cache.entries.contains_key(slot));
                            assert(false);
                        }
                    };
                    union_prefer_right_uses_left(pre.cache.entries, updated_entries, slot);
                    assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                    assert(post.cache.entries[slot] is Filled);
                    assert(pre.cache.entries[slot] is Filled);
                    cache_filled_entry_in_lookup(pre.cache, slot);
                    assert(pre.has_cached_page(addr));
                    assert(false);
                }
                assert(cache_responses.contains_key(addr));
                assert(post.cache_raw_page(addr) == cache_responses[addr]->data);
                let id = choose |id: ID| #[trigger] disk_responses.contains_key(id) && pre.outstanding_cache_reqs[id] == addr;
                assert(pre.outstanding_cache_reqs.restrict(disk_responses.dom()).values().contains(addr));
                assert(disk_responses.contains_key(id));
                assert(pre.outstanding_cache_reqs[id] == addr);
                assert(cache_responses[addr] == disk_responses[id]);
                assert(pre.disk.responses.contains_key(id));
                assert(pre.outstanding_reqs_responses_ok());
                assert(pre.disk.responses[id] is ReadResp);
                assert(pre.disk.responses[id]->data == pre.disk.content[addr]);
                assert(cache_responses[addr]->data == pre.disk.content[addr]);
            }
            Cache::Step::load_initiate(new_slots_mapping) => {
                let slot = post.cache.lookup_map[addr];
                let updated_entries = Map::new(
                    |slt| new_slots_mapping.contains_key(slt),
                    |slt| Entry::Loading{addr: new_slots_mapping[slt]}
                );
                assert(post.cache.entries == pre.cache.entries.union_prefer_right(updated_entries));
                if new_slots_mapping.contains_key(slot) {
                    assert(post.cache.entries[slot] is Loading);
                    assert(post.cache.entries[slot] is Filled);
                    assert(false);
                }
                assert(pre.cache.entries.contains_key(slot)) by {
                    if !pre.cache.entries.contains_key(slot) {
                        assert(!updated_entries.contains_key(slot));
                        assert(!pre.cache.entries.union_prefer_right(updated_entries).contains_key(slot));
                        assert(post.cache.entries == pre.cache.entries.union_prefer_right(updated_entries));
                        assert(post.cache.entries.contains_key(slot));
                        assert(false);
                    }
                };
                union_prefer_right_uses_left(pre.cache.entries, updated_entries, slot);
                assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                assert(post.cache.entries[slot] is Filled);
                assert(pre.cache.entries[slot] is Filled);
                cache_filled_entry_in_lookup(pre.cache, slot);
                assert(pre.has_cached_page(addr));
                assert(false);
            }
            Cache::Step::writeback_initiate() | Cache::Step::writeback_complete() => {
                assert(post.cache.lookup_map == pre.cache.lookup_map);
                assert(post.cache.entries == pre.cache.entries);
                assert(pre.has_cached_page(addr));
                assert(false);
            }
            _ => { assert(false); }
        }
    }

    pub open spec fn abstract_mini_allocator(self) -> MiniAllocator
    {
        if self.cached_branch.sealed {
            MiniAllocator::empty().add_aus(self.mini_allocator.all_aus())
        } else {
            self.mini_allocator
        }
    }

    pub open spec fn overlay_entries_match_available(self) -> bool
    {
        match self.overlay_branch() {
            Some(branch) => {
                &&& self.cached_branch.root is Some
                &&& branch.root == self.cached_branch.root.unwrap()
                &&& branch.disk_view.entries.dom() <= self.available_branch_nodes().dom()
                &&& forall |addr: Address|
                    #[trigger] branch.disk_view.entries.contains_key(addr)
                    ==> branch.disk_view.entries[addr] == self.available_branch_nodes()[addr]
            }
            None => {
                self.cached_branch.root is None
            }
        }
    }

    pub open spec fn i(self) -> AllocationBranch
    {
        AllocationBranch {
            sealed: self.cached_branch.sealed,
            branch: self.overlay_branch(),
            mini_allocator: self.abstract_mini_allocator(),
        }
    }

    pub open spec fn refinement_wf(self) -> bool
    {
        &&& self.wf()
        &&& self.available_branch_nodes().dom().finite()
        &&& self.overlay_entries_match_available()
        &&& self.i().inv()
    }

    proof fn overlay_entry_matches_available(self, addr: Address)
        requires
            self.overlay_entries_match_available(),
            self.overlay_branch_entries().contains_key(addr),
        ensures
            self.available_branch_nodes().contains_key(addr),
            self.overlay_branch_entries()[addr] == self.available_branch_nodes()[addr],
    {
        match self.overlay_branch() {
            Some(branch) => {
                assert(branch.disk_view.entries == self.overlay_branch_entries());
                assert(branch.disk_view.entries.contains_key(addr));
                assert(branch.disk_view.entries.dom().contains(addr));
                assert(self.available_branch_nodes().dom().contains(addr));
                assert(self.available_branch_nodes().contains_key(addr));
                assert(branch.disk_view.entries[addr] == self.available_branch_nodes()[addr]);
                assert(self.overlay_branch_entries()[addr] == self.available_branch_nodes()[addr]);
            }
            None => {
                assert(false);
            }
        }
    }

    proof fn branch_disk_entry_matches_available(self, branch: LinkedBranch<Summary>, addr: Address)
        requires
            self.overlay_entries_match_available(),
            self.overlay_branch() == Some(branch),
            branch.disk_view.entries.contains_key(addr),
        ensures
            self.overlay_branch_entries().contains_key(addr),
            self.available_branch_nodes().contains_key(addr),
            branch.disk_view.entries[addr] == self.available_branch_nodes()[addr],
    {
        assert(self.overlay_branch_entries() == branch.disk_view.entries);
        assert(self.overlay_branch_entries().contains_key(addr));
        self.overlay_entry_matches_available(addr);
        assert(branch.disk_view.entries[addr] == self.available_branch_nodes()[addr]);
    }

    proof fn overlay_branch_matches_entries(self, branch: LinkedBranch<Summary>)
        requires
            self.cached_branch.root == Some(branch.root),
            self.overlay_branch_entries() =~= branch.disk_view.entries,
        ensures
            self.overlay_branch() == Some(branch),
    {
        assert(self.overlay_branch_entries() == branch.disk_view.entries);
        assert(self.overlay_branch() == Some(branch));
    }

    proof fn internal_cache_preserves_i(
        pre: Self,
        post: Self,
        new_cache: Cache::State,
    )
        requires
            pre.wf(),
            post.wf(),
            Cache::State::next(pre.cache, new_cache, Cache::Label::Internal{}),
            post.cached_branch == pre.cached_branch,
            post.mini_allocator == pre.mini_allocator,
            post.cache == new_cache,
            post.disk == pre.disk,
        ensures
            post.i() == pre.i(),
    {
        Self::internal_cache_preserves_available_branch_nodes(pre, post, new_cache);
        overlay_branch_equal_when_available_nodes_equal(pre, post);
        assert(pre.abstract_mini_allocator() == post.abstract_mini_allocator());
        assert(post.i() == pre.i());
    }

    proof fn cache_disk_ops_preserves_i(
        pre: Self,
        post: Self,
        new_cache: Cache::State,
        new_disk: crate::spec::AsyncDisk_t::AsyncDisk::State,
        cache_requests: Set<DiskRequest>,
        cache_responses: Map<Address, DiskResponse>,
        disk_requests: Map<ID, DiskRequest>,
        disk_responses: Map<ID, DiskResponse>,
    )
        requires
            pre.wf(),
            post.wf(),
            pre.disk_requests_match_cache_requests(cache_requests, disk_requests),
            pre.disk_responses_match_cache_responses(cache_responses, disk_responses),
            Cache::State::next(pre.cache, new_cache, Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses}),
            crate::spec::AsyncDisk_t::AsyncDisk::State::next(
                pre.disk,
                new_disk,
                crate::spec::AsyncDisk_t::AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses},
            ),
            post.cached_branch == pre.cached_branch,
            post.mini_allocator == pre.mini_allocator,
            post.cache == new_cache,
            post.disk == new_disk,
        ensures
            post.i() == pre.i(),
    {
        Self::cache_disk_ops_preserves_available_branch_nodes(
            pre,
            post,
            new_cache,
            new_disk,
            cache_requests,
            cache_responses,
            disk_requests,
            disk_responses,
        );
        overlay_branch_equal_when_available_nodes_equal(pre, post);
        assert(pre.abstract_mini_allocator() == post.abstract_mini_allocator());
        assert(post.i() == pre.i());
    }

    pub open spec fn label_refines(pre: Self, post: Self, lbl: ConcreteBranch::Label) -> bool
    {
        match lbl {
            ConcreteBranch::Label::Query{key, msg, depth} => {
                let path = BranchPath{branch: pre.i().branch.unwrap(), key, depth};
                &&& pre.i().branch is Some
                &&& path.valid()
                &&& msg == pre.i().branch_query(key)
                &&& post.i() == pre.i()
            }
            ConcreteBranch::Label::Append{keys, msgs, depth} => {
                if pre.i().branch is Some && keys.len() > 0 {
                    let path = BranchPath{branch: pre.i().branch.unwrap(), key: keys[0], depth};
                    &&& path.valid()
                    &&& pre.i().can_append(keys, msgs, path)
                    &&& post.i() == pre.i().branch_append(keys, msgs, path)
                } else {
                    false
                }
            }
            ConcreteBranch::Label::Grow{new_root_addr} => {
                &&& allocation_branch_can_grow(pre.i(), new_root_addr)
                &&& post.i() == allocation_branch_grow(pre.i(), new_root_addr)
            }
            ConcreteBranch::Label::Split{new_child_addr, pivot, depth, split_arg} => {
                let path = BranchPath{branch: pre.i().branch.unwrap(), key: pivot, depth};
                &&& pre.i().branch is Some
                &&& path.valid()
                &&& pre.i().can_split(new_child_addr, path, split_arg)
                &&& post.i() == pre.i().branch_split(new_child_addr, path, split_arg)
            }
            ConcreteBranch::Label::Seal{aux_ptr} => {
                &&& allocation_branch_can_seal(pre.i(), aux_ptr)
                &&& post.i() == allocation_branch_seal(pre.i(), aux_ptr)
            }
            ConcreteBranch::Label::Internal{} => {
                post.i() == pre.i()
            }
        }
    }

    proof fn query_refines(
        pre: Self,
        post: Self,
        lbl: ConcreteBranch::Label,
        reads: Map<Address, RawPage>,
        needed: Set<Address>,
    )
        requires
            pre.wf(),
            post.wf(),
            pre.refinement_wf(),
            post.refinement_wf(),
            ConcreteBranch::State::query(pre, post, lbl, reads, needed),
        ensures
            Self::label_refines(pre, post, lbl),
    {
        reveal(ConcreteBranch::State::query);
        let read_nodes = to_branch_nodes(reads);
        match lbl {
            ConcreteBranch::Label::Query{key, msg, depth} => {
                let branch = pre.overlay_branch().unwrap();
                let path = BranchPath{branch, key, depth};
                assert(pre.cached_branch.can_query(pre.mini_allocator, key, depth, read_nodes, needed));
                loaded_path_reads_agree_with_branch_disk_at_depth(
                    pre,
                    pre.cache,
                    reads,
                    Map::<Address, RawPage>::empty(),
                    branch,
                    key,
                    depth,
                );
                loaded_query_matches_branch_query_at_depth(branch, read_nodes, key, depth);
                assert(path.valid());
                assert(branch.query(key) == pre.cached_branch.query_result(key, depth, read_nodes));
                assert(msg == pre.cached_branch.query_result(key, depth, read_nodes));
                assert(post.cached_branch == pre.cached_branch);
                assert(post.cache == pre.cache);
                assert(post.disk == pre.disk);
                assert(post.overlay_branch() == pre.overlay_branch());
                assert(post.i() == pre.i());
            }
            _ => { assert(false); }
        }
    }

    proof fn append_refines(
        pre: Self,
        post: Self,
        lbl: ConcreteBranch::Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
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
            Self::label_refines(pre, post, lbl),
    {
        reveal(ConcreteBranch::State::append);
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        let cache_lbl = Cache::Label::Access{reads, writes};
        let cache_step = choose |step| Cache::State::next_by(pre.cache, new_cache, cache_lbl, step);
        match lbl {
            ConcreteBranch::Label::Append{keys, msgs, depth} => {
                assert(keys.len() > 0);
                let first_key = keys[0];
                let branch = pre.overlay_branch().unwrap();
                let path = BranchPath{branch, key: first_key, depth};
                let root = branch.root;
                let leaf_addr = crate::implementation::CachedBranch_v::loaded_target_addr_at_depth(root, read_nodes, first_key, depth);
                let expected_write_nodes =
                    crate::implementation::CachedBranch_v::loaded_append_write_nodes_at_depth(root, read_nodes, keys, msgs, depth);
                let appended = branch.append(keys, msgs, path);
                assert(pre.cached_branch.can_append(pre.mini_allocator, keys, msgs, depth, read_nodes, write_nodes, needed));
                loaded_path_reads_agree_with_branch_disk_at_depth(pre, new_cache, reads, writes, branch, first_key, depth);
                assert(needed.contains(root));
                assert(reads.contains_key(root));
                match cache_step {
                    Cache::Step::access() => {
                        let cache_lbl = Cache::Label::Access{reads, writes};
                        reveal(Cache::State::next_by);
                        reveal(Cache::State::next);
                        assert(Cache::State::next_by(pre.cache, new_cache, cache_lbl, Cache::Step::access()));
                        assert(pre.cache.valid_read(root, cache_lbl->reads[root])) by {};
                    }
                    _ => { assert(false); }
                }
                assert(read_nodes.contains_key(root));
                branch_read_agrees_with_overlay(pre, new_cache, reads, writes, root);
                assert(branch.root() == read_nodes[root]);
                loaded_append_implies_branch_can_append_at_depth(branch, read_nodes, keys, msgs, depth);
                loaded_path_matches_branch_target_at_depth(branch, read_nodes, first_key, depth);
                assert(path.valid());
                assert(write_nodes == expected_write_nodes);
                assert(writes.dom() == set!{leaf_addr});
                crate::betree::LinkedBranch_v::Refinement_v::append_refines(branch, keys, msgs, path);
                crate::betree::LinkedBranch_v::Refinement_v::lemma_path_target(path, branch.the_ranking());
                assert(post.cached_branch == pre.cached_branch.append(
                    keys,
                    msgs,
                    depth,
                    read_nodes,
                    write_nodes,
                    needed,
                ));
                assert(post.mini_allocator == pre.mini_allocator);
                assert(post.cache == new_cache);
                assert(post.disk == pre.disk);
                assert(path.target().root == leaf_addr);
                assert(path.target().disk_view == branch.disk_view);
                assert(path.target().disk_view.entries.contains_key(path.target().root));
                assert(branch.disk_view.entries.contains_key(leaf_addr));
                pre.branch_disk_entry_matches_available(branch, leaf_addr);
                assert forall |addr: Address| #[trigger] writes.contains_key(addr) implies pre.available_branch_nodes().contains_key(addr) by {
                    assert(addr == leaf_addr);
                };
                access_preserves_available_branch_nodes_dom(pre, post, reads, writes);
                ConcreteBranch::State::access_preserves_cached_page(pre, post, reads, writes, leaf_addr);
                assert(post.available_branch_nodes()[leaf_addr] == decode_branch_page(post.cache_raw_page(leaf_addr)));
                assert(post.available_branch_nodes()[leaf_addr] == write_nodes[leaf_addr]);
                assert(pre.available_branch_nodes()[leaf_addr] is Leaf);
                assert(post.available_branch_nodes()[leaf_addr] is Leaf);
                assert(path.target().root() == read_nodes[leaf_addr]);
                assert(write_nodes[leaf_addr] == AllocationBranchNode::Leaf{
                    keys: path.target().root()->keys + keys,
                    msgs: path.target().root()->msgs + msgs,
                });
                assert(appended == path.substitute(path.target().append_leaf(keys, msgs)));
                assert(appended.disk_view == path.target().append_leaf(keys, msgs).disk_view);
                assert(appended.disk_view.entries[leaf_addr] == path.target().append_leaf(keys, msgs).disk_view.entries[leaf_addr]);
                assert(appended.disk_view.entries[leaf_addr] == AllocationBranchNode::Leaf{
                    keys: path.target().root()->keys + keys,
                    msgs: path.target().root()->msgs + msgs,
                });
                assert(appended.disk_view.entries[leaf_addr] == write_nodes[leaf_addr]);
                assert forall |addr: Address|
                    #[trigger] pre.available_branch_nodes().contains_key(addr)
                    && addr != leaf_addr
                    implies pre.available_branch_nodes()[addr] == post.available_branch_nodes()[addr]
                by {
                    access_unwritten_available_branch_node_unchanged(pre, post, reads, writes, addr);
                };
                reachable_branch_addrs_equal_under_leaf_rewrite(
                    pre,
                    post,
                    leaf_addr,
                    root,
                    pre.available_branch_nodes().dom().len(),
                );
                assert(pre.overlay_branch_addrs() == post.overlay_branch_addrs());
                assert(branch.disk_view.entries.dom() == appended.disk_view.entries.dom());
                assert forall |addr: Address| #[trigger] post.overlay_branch_entries().contains_key(addr)
                    <==> appended.disk_view.entries.contains_key(addr) by {
                    if post.overlay_branch_entries().contains_key(addr) {
                        assert(post.overlay_branch_addrs().contains(addr));
                        assert(pre.overlay_branch_addrs().contains(addr));
                        assert(branch.disk_view.entries.contains_key(addr));
                        assert(appended.disk_view.entries.contains_key(addr));
                    }
                    if appended.disk_view.entries.contains_key(addr) {
                        assert(branch.disk_view.entries.contains_key(addr));
                        assert(pre.overlay_branch_addrs().contains(addr));
                        assert(post.overlay_branch_addrs().contains(addr));
                    }
                };
                assert forall |addr: Address| #[trigger] post.overlay_branch_entries().contains_key(addr)
                    implies post.overlay_branch_entries()[addr] == appended.disk_view.entries[addr] by {
                    assert(post.overlay_branch_addrs().contains(addr));
                    assert(pre.overlay_branch_addrs().contains(addr));
                    assert(pre.available_branch_nodes().contains_key(addr));
                    assert(post.available_branch_nodes().contains_key(addr));
                    if addr == leaf_addr {
                        assert(post.overlay_branch_entries()[addr] == post.available_branch_nodes()[addr]);
                        assert(appended.disk_view.entries[addr] == write_nodes[addr]);
                    } else {
                        assert(post.overlay_branch_entries()[addr] == post.available_branch_nodes()[addr]);
                        assert(pre.overlay_branch_entries()[addr] == pre.available_branch_nodes()[addr]);
                        assert(pre.available_branch_nodes()[addr] == post.available_branch_nodes()[addr]);
                        assert(pre.overlay_branch_entries()[addr] == branch.disk_view.entries[addr]);
                        assert(appended.disk_view.entries[addr] == branch.disk_view.entries[addr]);
                    }
                };
                assert(post.overlay_branch_entries() =~= appended.disk_view.entries);
                post.overlay_branch_matches_entries(appended);
                assert(post.i().branch == Some(appended));
                assert(post.i().mini_allocator == pre.i().mini_allocator);
                assert(post.i() == pre.i().branch_append(keys, msgs, path));
            }
            _ => { assert(false); }
        }
    }

    proof fn grow_refines(
        pre: Self,
        post: Self,
        lbl: ConcreteBranch::Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        new_cache: crate::implementation::Cache_v::Cache::State,
    )
        requires
            pre.wf(),
            post.wf(),
            pre.refinement_wf(),
            post.refinement_wf(),
            ConcreteBranch::State::grow(pre, post, lbl, reads, writes, new_cache),
        ensures
            Self::label_refines(pre, post, lbl),
    {
        reveal(ConcreteBranch::State::grow);
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        match lbl {
            ConcreteBranch::Label::Grow{new_root_addr} => {
                let branch = pre.overlay_branch().unwrap();
                let grown = branch.grow(new_root_addr);
                assert(branch.can_grow(new_root_addr));
                assert(post.cached_branch == pre.cached_branch.grow(
                    pre.mini_allocator,
                    new_root_addr,
                    read_nodes,
                    write_nodes,
                ));
                assert(post.mini_allocator == pre.mini_allocator.allocate(new_root_addr));
                assert(post.cache == new_cache);
                assert(post.disk == pre.disk);
                assert(write_nodes == crate::implementation::CachedBranch_v::loaded_grow_write_nodes(branch.root, new_root_addr));
                assert(writes.dom() == set!{new_root_addr});
                access_updates_available_branch_nodes_with_single_fresh_write(pre, post, reads, writes, new_root_addr);
                assert(post.available_branch_nodes().dom() =~= pre.available_branch_nodes().dom().insert(new_root_addr));
                assert(!pre.available_branch_nodes().contains_key(new_root_addr));
                assert(!branch.disk_view.entries.contains_key(new_root_addr));
                assert(write_nodes[new_root_addr] == AllocationBranchNode::Index{
                    pivots: seq![],
                    children: seq![branch.root],
                    aux_ptr: None,
                });
                assert(pre.overlay_branch_entries() == branch.disk_view.entries);
                assert(pre.cached_branch.root is Some);
                assert(pre.cached_branch.root.unwrap() == branch.root);
                assert(!pre.cached_branch.sealed);
                assert(!post.cached_branch.sealed);
                assert forall |addr: Address| #[trigger] branch.disk_view.entries.contains_key(addr) implies {
                    &&& post.available_branch_nodes().contains_key(addr)
                    &&& post.available_branch_nodes()[addr] == branch.disk_view.entries[addr]
                } by {
                    pre.branch_disk_entry_matches_available(branch, addr);
                    assert(addr != new_root_addr);
                    assert(post.available_branch_nodes().contains_key(addr));
                    assert(post.available_branch_nodes()[addr] == pre.available_branch_nodes().insert(new_root_addr, to_branch_nodes(writes)[new_root_addr])[addr]);
                    assert(pre.available_branch_nodes()[addr] == pre.overlay_branch_entries()[addr]);
                };
                unsealed_reachable_branch_addrs_equal_for_branch_under_fresh_write(
                    pre,
                    post,
                    branch,
                    new_root_addr,
                    branch.root,
                    pre.available_branch_nodes().dom().len(),
                );
                let pre_len = pre.available_branch_nodes().dom().len();
                assert(!pre.available_branch_nodes().dom().contains(new_root_addr));
                vstd::set::axiom_set_insert_len(pre.available_branch_nodes().dom(), new_root_addr);
                assert(pre.available_branch_nodes().dom().insert(new_root_addr).len() == pre_len + 1);
                assert(post.available_branch_nodes().dom().len() - 1 == pre_len);
                let old_reach = pre.reachable_branch_addrs_from_with_fuel(branch.root, pre_len);
                let post_old_reach = post.reachable_branch_addrs_from_with_fuel(branch.root, pre_len);
                assert(old_reach == post_old_reach);
                let post_new_reach = post.reachable_branch_addrs_from_with_fuel(new_root_addr, post.available_branch_nodes().dom().len());
                union_seq_of_sets_singleton(post_old_reach);
                assert(!post.follow_aux_ptr_at(new_root_addr, write_nodes[new_root_addr]));
                assert forall |addr: Address| #[trigger] post_new_reach.contains(addr)
                    <==> grown.disk_view.entries.contains_key(addr) by {
                    reachable_branch_addrs_index_contains(post, new_root_addr, post.available_branch_nodes().dom().len(), addr);
                    assert(union_seq_of_sets(seq![post_old_reach]) == post_old_reach);
                    if post_new_reach.contains(addr) {
                        if addr == new_root_addr {
                            assert(grown.disk_view.entries.contains_key(addr));
                        } else {
                            assert(post_old_reach.contains(addr));
                            assert(old_reach.contains(addr));
                            assert(pre.overlay_branch_addrs().contains(addr));
                            assert(branch.disk_view.entries.contains_key(addr));
                            assert(grown.disk_view.entries.contains_key(addr));
                        }
                    }
                    if grown.disk_view.entries.contains_key(addr) {
                        if addr == new_root_addr {
                            assert(post_new_reach.contains(addr));
                        } else {
                            assert(branch.disk_view.entries.contains_key(addr));
                            assert(pre.overlay_branch_addrs().contains(addr));
                            assert(old_reach.contains(addr));
                            assert(post_old_reach.contains(addr));
                            assert(post_new_reach.contains(addr));
                        }
                    }
                };
                assert(post.overlay_branch_addrs() == post_new_reach);
                assert(grown.disk_view.entries.dom() == branch.disk_view.entries.dom().insert(new_root_addr));
                assert forall |addr: Address| #[trigger] post.overlay_branch_entries().contains_key(addr)
                    <==> grown.disk_view.entries.contains_key(addr) by {
                    assert(post.overlay_branch_addrs().contains(addr) <==> post_new_reach.contains(addr));
                };
                assert forall |addr: Address| #[trigger] post.overlay_branch_entries().contains_key(addr)
                    implies post.overlay_branch_entries()[addr] == grown.disk_view.entries[addr] by {
                    assert(post.overlay_branch_addrs().contains(addr));
                    assert(post.available_branch_nodes().contains_key(addr));
                    if addr == new_root_addr {
                        assert(post.overlay_branch_entries()[addr] == post.available_branch_nodes()[addr]);
                        assert(grown.disk_view.entries[addr] == write_nodes[addr]);
                    } else {
                        assert(post_old_reach.contains(addr));
                        assert(old_reach.contains(addr));
                        assert(pre.overlay_branch_addrs().contains(addr));
                        assert(pre.available_branch_nodes().contains_key(addr));
                        assert(post.overlay_branch_entries()[addr] == post.available_branch_nodes()[addr]);
                        assert(pre.overlay_branch_entries()[addr] == pre.available_branch_nodes()[addr]);
                        assert(pre.overlay_branch_entries()[addr] == branch.disk_view.entries[addr]);
                        assert(grown.disk_view.entries[addr] == branch.disk_view.entries[addr]);
                    }
                };
                assert(post.overlay_branch_entries() =~= grown.disk_view.entries);
                post.overlay_branch_matches_entries(grown);
                assert(post.i() == allocation_branch_grow(pre.i(), new_root_addr));
            }
            _ => { assert(false); }
        }
    }

    proof fn split_refines(
        pre: Self,
        post: Self,
        lbl: ConcreteBranch::Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
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
            Self::label_refines(pre, post, lbl),
    {
        reveal(ConcreteBranch::State::split);
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        match lbl {
            ConcreteBranch::Label::Split{new_child_addr, pivot, depth, split_arg} => {
                let branch = pre.overlay_branch().unwrap();
                let path = BranchPath{branch, key: pivot, depth};
                let root = branch.root;
                let child_addr =
                    crate::implementation::CachedBranch_v::loaded_split_child_addr_at_depth(root, read_nodes, pivot, depth);
                let path_addrs =
                    crate::implementation::CachedBranch_v::loaded_path_addrs_at_depth(root, read_nodes, pivot, depth);
                assert(pre.cached_branch.can_split(pre.mini_allocator, new_child_addr, pivot, depth, split_arg, read_nodes, write_nodes, needed));
                assert(needed == path_addrs.insert(child_addr));
                assert(path_addrs <= reads.dom()) by {
                    assert forall |addr: Address| #[trigger] path_addrs.contains(addr) implies reads.dom().contains(addr) by {
                        assert(needed.contains(addr));
                    };
                };
                loaded_path_reads_agree_with_branch_disk_at_depth(pre, new_cache, reads, writes, branch, pivot, depth);
                loaded_path_matches_branch_target_at_depth(branch, read_nodes, pivot, depth);
                assert(path.valid());
                path_target_inv_internal(branch, branch.the_ranking(), pivot, depth);
                let child_idx = path.target().root().route(pivot) + 1;
                crate::betree::LinkedBranch_v::Refinement_v::lemma_route_ensures(path.target().root(), pivot);
                child_branch_inv_internal_from_parent(path.target(), branch.the_ranking(), child_idx);
                crate::betree::LinkedBranch_v::Refinement_v::lemma_path_target(path, branch.the_ranking());
                assert(path.target().child_at_idx(child_idx).root == child_addr);
                assert(path.target().child_at_idx(child_idx).disk_view == branch.disk_view);
                assert(branch.disk_view.entries.contains_key(child_addr));
                let lbl = Cache::Label::Access{reads, writes};
                reveal(Cache::State::next_by);
                reveal(Cache::State::next);
                assert(Cache::State::next_by(pre.cache, new_cache, lbl, Cache::Step::access()));
                assert(pre.cache.valid_read(child_addr, lbl->reads[child_addr])) by {};
                assert(pre.overlay_branch_entries().contains_key(child_addr));
                branch_read_agrees_with_overlay(pre, new_cache, reads, writes, child_addr);
                assert(read_nodes[child_addr] == branch.disk_view.entries[child_addr]);
                assert(!pre.i().sealed);
                assert(pre.i().branch is Some);
                assert(pre.i().branch.unwrap() == branch);
                assert(pre.i().mini_allocator == pre.mini_allocator);
                assert(pre.mini_allocator.can_allocate(new_child_addr));
                assert(!pre.i().mini_allocator.page_is_reserved(new_child_addr));
                assert(!branch.disk_view.entries.contains_key(new_child_addr)) by {
                    if branch.disk_view.entries.contains_key(new_child_addr) {
                        assert(pre.i().addrs_closed_under_mini_allocator());
                        assert(pre.i().mini_allocator.page_is_reserved(new_child_addr));
                    }
                };
                assert(split_arg.wf(path.target().child_at_idx(child_idx)));
                assert(path.target().child_at_idx(path.target().root().route(pivot) + 1).disk_view.is_fresh(set!{new_child_addr}));
                assert(branch.can_split(new_child_addr, path, split_arg));
                crate::betree::LinkedBranch_v::Refinement_v::split_refines(
                    branch,
                    new_child_addr,
                    path,
                    split_arg,
                );
                let split_branch = branch.split(new_child_addr, path, split_arg);
                let except = set!{path.target().root, child_addr, new_child_addr};
                assert(split_branch.disk_view.same_except(branch.disk_view, except));
                assert(split_branch.disk_view.entries.dom() =~= branch.disk_view.entries.dom().insert(new_child_addr));
                assert(write_nodes == crate::implementation::CachedBranch_v::loaded_split_write_nodes_at_depth(
                    root,
                    read_nodes,
                    pivot,
                    depth,
                    split_arg,
                    new_child_addr,
                ));
                assert(write_nodes.dom() == except);
                assert(write_nodes.contains_key(path.target().root));
                assert(write_nodes.contains_key(child_addr));
                assert(write_nodes.contains_key(new_child_addr));
                assert(write_nodes.contains_key(path.target().root) <==> writes.contains_key(path.target().root));
                assert(write_nodes.contains_key(child_addr) <==> writes.contains_key(child_addr));
                assert(write_nodes.contains_key(new_child_addr) <==> writes.contains_key(new_child_addr));
                assert(writes.contains_key(path.target().root));
                assert(writes.contains_key(child_addr));
                assert(writes.contains_key(new_child_addr));
                assert(!pre.available_branch_nodes().contains_key(new_child_addr));
                assert forall |addr: Address| #[trigger] writes.contains_key(addr) && addr != new_child_addr
                    implies pre.available_branch_nodes().contains_key(addr) by {
                    assert(write_nodes.contains_key(addr));
                    assert(write_nodes.dom().contains(addr));
                    assert(addr == path.target().root || addr == child_addr);
                    pre.branch_disk_entry_matches_available(branch, addr);
                };
                access_updates_available_branch_nodes_with_one_fresh_write_set(pre, post, reads, writes, new_child_addr);
                assert forall |addr: Address| #[trigger] branch.disk_view.entries.contains_key(addr) && !except.contains(addr) implies {
                    &&& post.available_branch_nodes().contains_key(addr)
                    &&& post.available_branch_nodes()[addr] == branch.disk_view.entries[addr]
                } by {
                    pre.branch_disk_entry_matches_available(branch, addr);
                    assert(!write_nodes.contains_key(addr));
                    assert(!writes.contains_key(addr));
                    access_unwritten_available_branch_node_unchanged(pre, post, reads, writes, addr);
                };
                assert(post.cached_branch == pre.cached_branch.split(
                    pre.mini_allocator,
                    new_child_addr,
                    pivot,
                    depth,
                    split_arg,
                    read_nodes,
                    write_nodes,
                    needed,
                ));
                assert(post.mini_allocator == pre.mini_allocator.allocate(new_child_addr));
                assert(post.cache == new_cache);
                assert(post.disk == pre.disk);
                assert(split_branch.disk_view.entries[path.target().root] == write_nodes[path.target().root]);
                assert(split_branch.disk_view.entries[child_addr] == write_nodes[child_addr]);
                assert(split_branch.disk_view.entries[new_child_addr] == write_nodes[new_child_addr]);
                assert(post.overlay_branch_entries() =~= split_branch.disk_view.entries);
                post.overlay_branch_matches_entries(split_branch);
                assert(post.i().branch == Some(split_branch));
                assert(post.i().mini_allocator == pre.i().mini_allocator.allocate(new_child_addr));
                assert(post.i() == pre.i().branch_split(new_child_addr, path, split_arg));
            }
            _ => { assert(false); }
        }
    }

    proof fn seal_refines(
        pre: Self,
        post: Self,
        lbl: ConcreteBranch::Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        new_cache: crate::implementation::Cache_v::Cache::State,
    )
        requires
            pre.wf(),
            post.wf(),
            pre.refinement_wf(),
            post.refinement_wf(),
            ConcreteBranch::State::seal(pre, post, lbl, reads, writes, new_cache),
        ensures
            Self::label_refines(pre, post, lbl),
    {
        reveal(ConcreteBranch::State::seal);
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        match lbl {
            ConcreteBranch::Label::Seal{aux_ptr} => {
                let branch = pre.overlay_branch().unwrap();
                let summary = pre.mini_allocator.reserved_aus();
                assert(post.cached_branch == pre.cached_branch.seal(
                    pre.mini_allocator,
                    aux_ptr,
                    read_nodes,
                    write_nodes,
                ));
                if aux_ptr is Some {
                    assert(post.mini_allocator == pre.mini_allocator.allocate(aux_ptr.unwrap()).prune(Set::empty()));
                } else {
                    assert(post.mini_allocator == pre.mini_allocator.prune(Set::empty()));
                }
                assert(post.cache == new_cache);
                assert(post.disk == pre.disk);
                assert(pre.cached_branch.can_seal(pre.mini_allocator, aux_ptr, read_nodes, write_nodes));
                assert(read_nodes.contains_key(branch.root));
                assert(branch.disk_view.entries.contains_key(branch.root));
                let lbl = Cache::Label::Access{reads, writes};
                reveal(Cache::State::next_by);
                reveal(Cache::State::next);
                assert(Cache::State::next_by(pre.cache, new_cache, lbl, Cache::Step::access()));
                assert(pre.cache.valid_read(branch.root, lbl->reads[branch.root])) by {};
                branch_read_agrees_with_overlay(pre, new_cache, reads, writes, branch.root);
                assert(branch.root() == read_nodes[branch.root]);
                if aux_ptr is Some {
                    let aux = aux_ptr.unwrap();
                    assert(branch.root() is Index);
                    assert(write_nodes == crate::implementation::CachedBranch_v::loaded_seal_write_nodes(branch.root, read_nodes, aux_ptr, summary));
                    assert(write_nodes.dom() == set!{branch.root, aux});
                    assert(write_nodes.contains_key(branch.root));
                    assert(write_nodes.contains_key(aux));
                    assert(write_nodes.contains_key(branch.root) <==> writes.contains_key(branch.root));
                    assert(write_nodes.contains_key(aux) <==> writes.contains_key(aux));
                    assert(writes.contains_key(branch.root));
                    assert(writes.contains_key(aux));
                    assert(!pre.available_branch_nodes().contains_key(aux));
                    assert forall |addr: Address| #[trigger] writes.contains_key(addr) && addr != aux
                        implies pre.available_branch_nodes().contains_key(addr) by {
                        assert(write_nodes.contains_key(addr));
                        assert(write_nodes.dom().contains(addr));
                        assert(addr == branch.root);
                        pre.branch_disk_entry_matches_available(branch, branch.root);
                    };
                    access_updates_available_branch_nodes_with_one_fresh_write_set(pre, post, reads, writes, aux);
                    let sealed = branch.seal(aux, summary);
                    let pre_len = pre.available_branch_nodes().dom().len();
                    vstd::set::axiom_set_insert_len(pre.available_branch_nodes().dom(), aux);
                    assert(post.available_branch_nodes().dom().len() == pre_len + 1);
                    assert(pre.overlay_branch_entries() == branch.disk_view.entries);
                    assert(!branch.disk_view.entries.contains_key(aux));
                    assert(post.available_branch_nodes()[branch.root] == write_nodes[branch.root]);
                    assert(post.available_branch_nodes()[branch.root] == sealed.disk_view.entries[branch.root]);
                    assert(post.available_branch_nodes().contains_key(aux));
                    assert(post.available_branch_nodes()[aux] == if writes.contains_key(aux) {
                        to_branch_nodes(writes)[aux]
                    } else {
                        arbitrary()
                    });
                    assert(post.available_branch_nodes()[aux] == write_nodes[aux]);
                    assert(write_nodes[aux] == AllocationBranchNode::Auxiliary(summary));
                    assert(sealed.disk_view.entries[aux] == AllocationBranchNode::Auxiliary(summary));
                    assert forall |addr: Address| #[trigger] branch.disk_view.entries.contains_key(addr) && addr != branch.root implies {
                        &&& post.available_branch_nodes().contains_key(addr)
                        &&& post.available_branch_nodes()[addr] == branch.disk_view.entries[addr]
                    } by {
                        pre.branch_disk_entry_matches_available(branch, addr);
                        assert(!write_nodes.contains_key(addr));
                        assert(!writes.contains_key(addr));
                        access_unwritten_available_branch_node_unchanged(pre, post, reads, writes, addr);
                    };
                    sealed_root_reachable_branch_addrs_equal_under_aux_write(
                        pre,
                        post,
                        branch,
                        aux,
                        post.available_branch_nodes().dom().len(),
                    );
                    assert(post.overlay_branch_addrs()
                        == pre.reachable_branch_addrs_from_with_fuel(branch.root, post.available_branch_nodes().dom().len()).insert(aux));
                    assert forall |addr: Address| #[trigger] post.overlay_branch_entries().contains_key(addr)
                        <==> sealed.disk_view.entries.contains_key(addr) by {
                        if post.overlay_branch_entries().contains_key(addr) {
                            assert(post.overlay_branch_addrs().contains(addr));
                            if addr != aux {
                                concrete_reachable_from_overlay_branch_implies_in_disk_view(
                                    pre,
                                    branch,
                                    branch.root,
                                    post.available_branch_nodes().dom().len(),
                                    addr,
                                );
                            }
                            assert(sealed.disk_view.entries.contains_key(addr));
                        }
                        if sealed.disk_view.entries.contains_key(addr) {
                            if addr == aux {
                                assert(post.overlay_branch_addrs().contains(addr));
                            } else {
                                assert(branch.disk_view.entries.contains_key(addr));
                                assert(pre.overlay_branch_addrs().contains(addr));
                                reachable_branch_addrs_more_fuel(pre, branch.root, pre_len, addr);
                                assert(pre.reachable_branch_addrs_from_with_fuel(branch.root, post.available_branch_nodes().dom().len()).contains(addr));
                                assert(post.overlay_branch_addrs().contains(addr));
                            }
                        }
                    };
                    assert forall |addr: Address| #[trigger] post.overlay_branch_entries().contains_key(addr)
                        implies post.overlay_branch_entries()[addr] == sealed.disk_view.entries[addr] by {
                        assert(post.overlay_branch_addrs().contains(addr));
                        assert(post.available_branch_nodes().contains_key(addr));
                        if addr == aux || addr == branch.root {
                            assert(post.overlay_branch_entries()[addr] == post.available_branch_nodes()[addr]);
                        } else {
                            assert(pre.overlay_branch_entries().contains_key(addr));
                            assert(pre.available_branch_nodes().contains_key(addr));
                            assert(post.overlay_branch_entries()[addr] == post.available_branch_nodes()[addr]);
                            assert(pre.overlay_branch_entries()[addr] == pre.available_branch_nodes()[addr]);
                            assert(pre.overlay_branch_entries()[addr] == branch.disk_view.entries[addr]);
                            assert(sealed.disk_view.entries[addr] == branch.disk_view.entries[addr]);
                        }
                    };
                    assert(post.overlay_branch_entries() =~= sealed.disk_view.entries);
                    post.overlay_branch_matches_entries(sealed);
                } else {
                    assert(branch.root() is Leaf);
                    assert(write_nodes == Map::<Address, AllocationBranchNode>::empty());
                    assert(writes.dom() == Set::<Address>::empty()) by {
                        assert forall |addr: Address| #[trigger] writes.dom().contains(addr) implies false by {
                            assert(write_nodes.contains_key(addr));
                        };
                    };
                    assert(writes == Map::<Address, RawPage>::empty());
                    access_preserves_available_branch_nodes_when_writes_empty(pre, post, reads);
                    let root = branch.root;
                    assert(pre.cached_branch.root == Some(root));
                    assert(post.cached_branch.root == Some(root));
                    assert(pre.available_branch_nodes().contains_key(root));
                    assert(post.available_branch_nodes().contains_key(root));
                    assert(pre.available_branch_nodes()[root] is Leaf);
                    assert(post.available_branch_nodes()[root] == pre.available_branch_nodes()[root]);
                    reachable_branch_addrs_leaf_unfold(pre, root, pre.available_branch_nodes().dom().len());
                    reachable_branch_addrs_leaf_unfold(post, root, post.available_branch_nodes().dom().len());
                    assert(pre.overlay_branch_addrs() == set!{root});
                    assert(post.overlay_branch_addrs() == set!{root});
                    assert(pre.overlay_branch_entries().dom() =~= set!{root});
                    assert(post.overlay_branch_entries().dom() =~= set!{root});
                    assert(pre.overlay_branch_entries()[root] == pre.available_branch_nodes()[root]);
                    assert(post.overlay_branch_entries()[root] == post.available_branch_nodes()[root]);
                    assert(post.overlay_branch_entries()[root] == branch.disk_view.entries[root]);
                    assert(post.overlay_branch_entries() =~= branch.disk_view.entries);
                    post.overlay_branch_matches_entries(branch);
                }
                assert(post.i() == allocation_branch_seal(pre.i(), aux_ptr));
            }
            _ => { assert(false); }
        }
    }

    proof fn internal_cache_refines(pre: Self, post: Self, lbl: ConcreteBranch::Label, new_cache: crate::implementation::Cache_v::Cache::State)
        requires
            pre.wf(),
            post.wf(),
            pre.refinement_wf(),
            post.refinement_wf(),
            ConcreteBranch::State::internal_cache(pre, post, lbl, new_cache),
        ensures
            Self::label_refines(pre, post, lbl),
    {
        reveal(ConcreteBranch::State::internal_cache);
        assert(lbl is Internal);
        Self::internal_cache_preserves_i(pre, post, new_cache);
    }

    proof fn internal_disk_refines(pre: Self, post: Self, lbl: ConcreteBranch::Label, new_disk: crate::spec::AsyncDisk_t::AsyncDisk::State)
        requires
            pre.wf(),
            post.wf(),
            pre.refinement_wf(),
            post.refinement_wf(),
            ConcreteBranch::State::internal_disk(pre, post, lbl, new_disk),
        ensures
            Self::label_refines(pre, post, lbl),
    {
        reveal(ConcreteBranch::State::internal_disk);
        assert(lbl is Internal);
        assert(post.cached_branch == pre.cached_branch);
        assert(post.mini_allocator == pre.mini_allocator);
        assert(post.cache == pre.cache);
        Self::internal_disk_preserves_available_branch_nodes(pre, post, new_disk);
        overlay_branch_equal_when_available_nodes_equal(pre, post);
        assert(post.abstract_mini_allocator() == pre.abstract_mini_allocator());
        assert(post.i() == pre.i());
    }

    proof fn cache_disk_ops_refines(
        pre: Self,
        post: Self,
        lbl: ConcreteBranch::Label,
        new_cache: crate::implementation::Cache_v::Cache::State,
        new_disk: crate::spec::AsyncDisk_t::AsyncDisk::State,
        cache_requests: Set<DiskRequest>,
        cache_responses: Map<Address, DiskResponse>,
        disk_requests: Map<ID, DiskRequest>,
        disk_responses: Map<ID, DiskResponse>,
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
            Self::label_refines(pre, post, lbl),
    {
        reveal(ConcreteBranch::State::cache_disk_ops);
        assert(lbl is Internal);
        Self::cache_disk_ops_preserves_i(
            pre,
            post,
            new_cache,
            new_disk,
            cache_requests,
            cache_responses,
            disk_requests,
            disk_responses,
        );
    }

    pub proof fn next_refines(pre: Self, post: Self, lbl: ConcreteBranch::Label)
        requires
            pre.wf(),
            post.wf(),
            pre.refinement_wf(),
            post.refinement_wf(),
            ConcreteBranch::State::next(pre, post, lbl),
        ensures
            Self::label_refines(pre, post, lbl),
    {
        reveal(ConcreteBranch::State::next);
        reveal(ConcreteBranch::State::next_by);

        let step = choose |step| ConcreteBranch::State::next_by(pre, post, lbl, step);
        match step {
            ConcreteBranch::Step::query(reads, needed) =>
                Self::query_refines(pre, post, lbl, reads, needed),
            ConcreteBranch::Step::append(reads, writes, needed, new_cache) =>
                Self::append_refines(pre, post, lbl, reads, writes, needed, new_cache),
            ConcreteBranch::Step::grow(reads, writes, new_cache) =>
                Self::grow_refines(pre, post, lbl, reads, writes, new_cache),
            ConcreteBranch::Step::split(reads, writes, needed, new_cache) =>
                Self::split_refines(pre, post, lbl, reads, writes, needed, new_cache),
            ConcreteBranch::Step::seal(reads, writes, new_cache) =>
                Self::seal_refines(pre, post, lbl, reads, writes, new_cache),
            ConcreteBranch::Step::internal_cache(new_cache) =>
                Self::internal_cache_refines(pre, post, lbl, new_cache),
            ConcreteBranch::Step::internal_disk(new_disk) =>
                Self::internal_disk_refines(pre, post, lbl, new_disk),
            ConcreteBranch::Step::cache_disk_ops(
                new_cache,
                new_disk,
                cache_requests,
                cache_responses,
                disk_requests,
                disk_responses,
            ) =>
                Self::cache_disk_ops_refines(
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
}

} // verus!
