// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::map::*;

use crate::abstract_system::AbstractMap_v::AbstractMap;
use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::allocation_layer::AllocationBranch_v::{AllocationBranch, BranchNode as AllocationBranchNode, Summary};
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::LinkedBranch_v::{LinkedBranch, Path as BranchPath, SplitArg};
use crate::betree::LinkedBranch_v::Refinement_v as LinkedBranchRefinement_v;
use crate::betree::PivotBranchRefinement_v;
use crate::betree::PivotBranchRefinement_v::{InternalLabel as PivotInternalLabel, QueryLabel};
use crate::disk::GenericDisk_v::{Address, Ranking};
use crate::implementation::AllocationBranchStackRefinement_v::{append_puts, append_puts_wf};
use crate::implementation::AllocationBranchStack_v::{AllocationBranchStack, normalize_value};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedBranch_v::LoadedPathReceipt;
use crate::implementation::ConcreteBranch_v::ConcreteBranch;
use crate::implementation::ConcreteBranch_v::to_branch_nodes;
use crate::spec::AsyncDisk_t::RawPage;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{nop_delta, Message};

verus! {

impl ConcreteBranch::State {
    pub open spec fn branch_stack_i_at(self, idx: nat) -> AllocationBranch
        recommends idx < self.cached_branches.len()
    {
        if idx == self.active_idx() as nat {
            AllocationBranch{
                sealed: false,
                branch: self.overlay_branch_at(idx),
                mini_allocator: self.mini_allocator,
            }
        } else {
            let branch = self.overlay_branch_at(idx);
            if branch is Some {
                AllocationBranch{
                    sealed: true,
                    branch,
                    mini_allocator: MiniAllocator::empty().add_aus(branch.unwrap().get_summary()),
                }
            } else {
                AllocationBranch{
                    sealed: true,
                    branch: None,
                    mini_allocator: MiniAllocator::empty(),
                }
            }
        }
    }

    pub open spec fn i(self) -> AllocationBranchStack
    {
        AllocationBranchStack{
            branches: Seq::new(self.cached_branches.len(), |i: int| self.branch_stack_i_at(i as nat)),
            seq_end: self.seq_end,
        }
    }

    pub open spec fn abstract_map_i(self) -> AbstractMap::State
    {
        self.i().abstract_map_i()
    }

    pub open spec fn label_to_abstract_map(self, lbl: ConcreteBranch::Label) -> AbstractMap::Label
    {
        match lbl {
            ConcreteBranch::Label::Query{branch_idx, key, msg} =>
                AbstractMap::Label::QueryLabel{
                    end_lsn: self.seq_end,
                    key,
                    value: normalize_value(msg),
                },
            ConcreteBranch::Label::Append{keys, msgs} =>
                AbstractMap::Label::PutLabel{ puts: append_puts(self.seq_end, keys, msgs) },
            ConcreteBranch::Label::Grow{new_root_addr} =>
                AbstractMap::Label::InternalLabel{},
            ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg} =>
                AbstractMap::Label::InternalLabel{},
            ConcreteBranch::Label::Seal{aux_ptr} =>
                AbstractMap::Label::InternalLabel{},
            ConcreteBranch::Label::FillAU{aus} =>
                AbstractMap::Label::InternalLabel{},
            ConcreteBranch::Label::Internal{} =>
                AbstractMap::Label::InternalLabel{},
        }
    }

    pub open spec fn refinement_wf(self) -> bool
    {
        &&& self.wf()
        &&& self.available_branch_nodes().dom().finite()
        &&& self.i().wf()
    }
}

proof fn branch_stack_entry_matches_overlay(pre: ConcreteBranch::State, idx: nat)
    requires
        pre.refinement_wf(),
        idx < pre.cached_branches.len(),
    ensures
        pre.i().branches[idx as int] == pre.branch_stack_i_at(idx),
        pre.branch_stack_i_at(idx).branch == pre.overlay_branch_at(idx),
{
    assert(pre.i().branches[idx as int] == pre.branch_stack_i_at(idx));
    if idx == pre.active_idx() {
        assert(pre.branch_stack_i_at(idx).branch == pre.overlay_branch_at(idx));
    } else if pre.overlay_branch_at(idx) is Some {
        assert(pre.branch_stack_i_at(idx).branch == pre.overlay_branch_at(idx));
    } else {
        assert(pre.branch_stack_i_at(idx).branch is None);
        assert(pre.branch_stack_i_at(idx).branch == pre.overlay_branch_at(idx));
    }
}

proof fn overlay_entries_match_branch_disk(
    pre: ConcreteBranch::State,
    idx: nat,
    branch: LinkedBranch<Summary>,
    addr: Address,
)
    requires
        pre.wf(),
        idx < pre.cached_branches.len(),
        pre.overlay_branch_at(idx) == Some(branch),
        branch.disk_view.entries.contains_key(addr),
    ensures
        pre.overlay_branch_entries_at(idx).contains_key(addr),
        pre.overlay_branch_entries_at(idx)[addr] == branch.disk_view.entries[addr],
{
    let overlay = pre.overlay_branch_at(idx).unwrap();
    assert(overlay == branch);
    assert(overlay.disk_view.entries == pre.overlay_branch_entries_at(idx));
    assert(overlay.disk_view.entries.contains_key(addr));
}

proof fn union_seq_of_sets_equal<A>(left: Seq<Set<A>>, right: Seq<Set<A>>)
    requires
        left.len() == right.len(),
        forall |i: int| 0 <= i < left.len() ==> #[trigger] left[i] == right[i],
    ensures
        crate::betree::Utils_v::union_seq_of_sets(left) == crate::betree::Utils_v::union_seq_of_sets(right),
{
    assert forall |a: A|
        #[trigger] crate::betree::Utils_v::union_seq_of_sets(left).contains(a)
            implies crate::betree::Utils_v::union_seq_of_sets(right).contains(a)
    by {
        crate::betree::Utils_v::lemma_union_seq_of_sets_contains(left, a);
        let i = choose |i: int| #![trigger left[i].contains(a)] 0 <= i < left.len() && left[i].contains(a);
        assert(right[i].contains(a));
        assert(exists |j: int| #![trigger right[j].contains(a)] 0 <= j < right.len() && right[j].contains(a));
        crate::betree::Utils_v::lemma_set_subset_of_union_seq_of_sets(right, a);
    };
    assert forall |a: A|
        #[trigger] crate::betree::Utils_v::union_seq_of_sets(right).contains(a)
            implies crate::betree::Utils_v::union_seq_of_sets(left).contains(a)
    by {
        crate::betree::Utils_v::lemma_union_seq_of_sets_contains(right, a);
        let i = choose |i: int| #![trigger right[i].contains(a)] 0 <= i < right.len() && right[i].contains(a);
        assert(left[i].contains(a));
        assert(exists |j: int| #![trigger left[j].contains(a)] 0 <= j < left.len() && left[j].contains(a));
        crate::betree::Utils_v::lemma_set_subset_of_union_seq_of_sets(left, a);
    };
}

pub proof fn query_step_refines_from_stack_query(pre: ConcreteBranch::State, lbl: ConcreteBranch::Label)
    requires
        pre.refinement_wf(),
        lbl is Query,
        pre.i().query(lbl->key) == lbl->msg,
    ensures
        AbstractMap::State::next(pre.abstract_map_i(), pre.abstract_map_i(), pre.label_to_abstract_map(lbl)),
{
    match lbl {
        ConcreteBranch::Label::Query{branch_idx, key, msg} => {
            crate::implementation::AllocationBranchStackRefinement_v::query_refines_to_abstract_map(pre.i(), key);
        }
        _ => { assert(false); }
    }
}

pub proof fn internal_step_refines_from_same_abstract_map(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
)
    requires
        pre.refinement_wf(),
        post.refinement_wf(),
        post.abstract_map_i() == pre.abstract_map_i(),
        !(lbl is Query),
        !(lbl is Append),
    ensures
        AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
{
    reveal(AbstractMap::State::next);
    reveal(AbstractMap::State::next_by);
    assert(AbstractMap::State::next_by(
        pre.abstract_map_i(),
        post.abstract_map_i(),
        pre.label_to_abstract_map(lbl),
        AbstractMap::Step::internal(),
    ));
}

proof fn loaded_index_path_contains_root(root: Address, loaded: Map<Address, AllocationBranchNode>, key: Key, depth: nat)
    requires
        crate::implementation::CachedBranch_v::loaded_has_index_route_at_depth(root, loaded, key, depth),
    ensures
        crate::implementation::CachedBranch_v::loaded_index_path_addrs_at_depth(root, loaded, key, depth).contains(root),
    decreases depth,
{
    if depth > 0 {
        assert(crate::implementation::CachedBranch_v::loaded_index_path_addrs_at_depth(root, loaded, key, depth)
            == crate::implementation::CachedBranch_v::loaded_index_path_addrs_at_depth(
                crate::implementation::CachedBranch_v::loaded_child_addr(root, loaded, key),
                loaded,
                key,
                (depth - 1) as nat,
            ).insert(root));
    }
}

proof fn loaded_index_child_path_subset(root: Address, loaded: Map<Address, AllocationBranchNode>, key: Key, depth: nat)
    requires
        depth > 0,
        crate::implementation::CachedBranch_v::loaded_has_index_route_at_depth(root, loaded, key, depth),
    ensures
        crate::implementation::CachedBranch_v::loaded_index_path_addrs_at_depth(
            crate::implementation::CachedBranch_v::loaded_child_addr(root, loaded, key),
            loaded,
            key,
            (depth - 1) as nat,
        ) <= crate::implementation::CachedBranch_v::loaded_index_path_addrs_at_depth(root, loaded, key, depth),
{
    let child_addr = crate::implementation::CachedBranch_v::loaded_child_addr(root, loaded, key);
    assert(crate::implementation::CachedBranch_v::loaded_index_path_addrs_at_depth(root, loaded, key, depth)
        == crate::implementation::CachedBranch_v::loaded_index_path_addrs_at_depth(
            child_addr,
            loaded,
            key,
            (depth - 1) as nat,
        ).insert(root));
    assert forall |addr: Address|
        #[trigger] crate::implementation::CachedBranch_v::loaded_index_path_addrs_at_depth(child_addr, loaded, key, (depth - 1) as nat).contains(addr)
        implies crate::implementation::CachedBranch_v::loaded_index_path_addrs_at_depth(root, loaded, key, depth).contains(addr)
    by { };
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

proof fn loaded_index_path_matches_branch_target_at_depth(
    branch: LinkedBranch<Summary>,
    loaded: Map<Address, AllocationBranchNode>,
    key: Key,
    depth: nat,
)
    requires
        branch.wf(),
        crate::implementation::CachedBranch_v::loaded_has_index_route_at_depth(branch.root, loaded, key, depth),
        crate::implementation::CachedBranch_v::loaded_index_path_addrs_at_depth(branch.root, loaded, key, depth)
            <= branch.disk_view.entries.dom(),
        forall |addr: Address|
            #[trigger] crate::implementation::CachedBranch_v::loaded_index_path_addrs_at_depth(branch.root, loaded, key, depth).contains(addr)
            ==> loaded[addr] == branch.disk_view.entries[addr],
    ensures
        (BranchPath{branch, key, depth}).valid(),
        (BranchPath{branch, key, depth}).target().disk_view == branch.disk_view,
        (BranchPath{branch, key, depth}).target().root
            == crate::implementation::CachedBranch_v::loaded_index_target_addr_at_depth(branch.root, loaded, key, depth),
        (BranchPath{branch, key, depth}).target().root()
            == crate::implementation::CachedBranch_v::loaded_index_target_at_depth(branch.root, loaded, key, depth),
    decreases depth,
{
    let path = BranchPath{branch, key, depth};
    loaded_index_path_contains_root(branch.root, loaded, key, depth);
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
        assert(child_branch.disk_view.entries == branch.disk_view.entries);
        loaded_index_child_path_subset(branch.root, loaded, key, depth);
        assert forall |addr: Address|
            #[trigger] crate::implementation::CachedBranch_v::loaded_index_path_addrs_at_depth(child_addr, loaded, key, (depth - 1) as nat).contains(addr)
            implies loaded[addr] == child_branch.disk_view.entries[addr]
        by {
            assert(crate::implementation::CachedBranch_v::loaded_index_path_addrs_at_depth(branch.root, loaded, key, depth).contains(addr));
            assert(loaded[addr] == branch.disk_view.entries[addr]);
            assert(child_branch.disk_view.entries[addr] == branch.disk_view.entries[addr]);
        };
        loaded_index_path_matches_branch_target_at_depth(child_branch, loaded, key, (depth - 1) as nat);
        assert(path.subpath() == BranchPath{branch: child_branch, key, depth: (depth - 1) as nat});
        assert(path.valid());
        assert(path.target() == path.subpath().target());
        assert(path.target().disk_view == child_branch.disk_view);
        assert(child_branch.disk_view == branch.disk_view);
    }
}

proof fn receipt_query_matches_branch_query_internal(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    loaded: Map<Address, AllocationBranchNode>,
    receipt: LoadedPathReceipt,
)
    requires
        branch.inv_internal(ranking),
        receipt.valid_for(branch.root, loaded),
        receipt.target_is_leaf(),
        receipt.needed_addrs() <= branch.disk_view.entries.dom(),
        forall |addr: Address|
            #[trigger] receipt.needed_addrs().contains(addr)
            ==> loaded[addr] == branch.disk_view.entries[addr],
    ensures
        branch.query_internal(receipt.key, ranking) == receipt.result(),
    decreases receipt.depth(),
{
    let key = receipt.key;
    assert(receipt.needed_addrs().contains(branch.root)) by {
        assert(receipt.lines[0].addr == branch.root);
    };
    if receipt.depth() == 0 {
        assert(receipt.lines.len() == 1);
        assert(loaded[branch.root] == branch.disk_view.entries[branch.root]) by {
            assert(receipt.needed_addrs().contains(branch.root));
        };
        assert(branch.disk_view.entries[branch.root] == branch.root());
        let node = loaded[branch.root];
        assert(node == branch.root());
        assert(node is Leaf);
        reveal(LinkedBranch::query_internal);
    } else {
        let child_receipt = receipt.tail();
        crate::implementation::CachedBranch_v::receipt_valid_implies_tail_valid(receipt, loaded);
        assert(child_receipt.target_is_leaf());
        assert(loaded[branch.root] == branch.disk_view.entries[branch.root]) by {
            assert(receipt.needed_addrs().contains(branch.root));
        };
        assert(branch.disk_view.entries[branch.root] == branch.root());
        let node = loaded[branch.root];
        assert(node == branch.root());
        assert(node is Index);
        assert(receipt.lines[0].wf());
        assert(node.keys_strictly_sorted());
        Key::strictly_sorted_implies_sorted(node->pivots);
        Key::largest_lte_ensures(node->pivots, key, node.route(key));
        let child_idx = node.route(key) + 1;
        assert(branch.root().valid_child_index(child_idx));
        let child_branch = branch.child_at_idx(child_idx);
        let child_addr = crate::implementation::CachedBranch_v::loaded_child_addr(branch.root, loaded, key);
        assert(child_addr == child_receipt.root);
        child_branch_inv_internal_from_parent(branch, ranking, child_idx);
        assert forall |addr: Address|
            #[trigger] child_receipt.needed_addrs().contains(addr)
            implies loaded[addr] == child_branch.disk_view.entries[addr]
        by {
            assert(receipt.needed_addrs().contains(addr)) by {
                let i = choose |i: int| 0 <= i < child_receipt.lines.len() && #[trigger] child_receipt.lines[i].addr == addr;
                assert(receipt.lines[i + 1] == child_receipt.lines[i]);
            };
            assert(loaded[addr] == branch.disk_view.entries[addr]);
            assert(child_branch.disk_view.entries[addr] == branch.disk_view.entries[addr]);
        };
        assert(child_receipt.needed_addrs() <= child_branch.disk_view.entries.dom()) by {
            assert forall |addr: Address|
                #[trigger] child_receipt.needed_addrs().contains(addr)
                implies child_branch.disk_view.entries.dom().contains(addr)
            by {
                assert(receipt.needed_addrs().contains(addr)) by {
                    let i = choose |i: int| 0 <= i < child_receipt.lines.len() && #[trigger] child_receipt.lines[i].addr == addr;
                    assert(receipt.lines[i + 1] == child_receipt.lines[i]);
                };
                assert(branch.disk_view.entries.dom().contains(addr));
                assert(child_branch.disk_view.entries == branch.disk_view.entries);
            };
        };
        receipt_query_matches_branch_query_internal(child_branch, ranking, loaded, child_receipt);
        assert(receipt.result() == child_receipt.result());
        local_query_internal_descends_to_child(branch, ranking, key);
        assert(branch.query_internal(key, ranking)
            == branch.child_at_idx(branch.root().route(key) + 1).query_internal(key, ranking));
        assert(branch.child_at_idx(branch.root().route(key) + 1).query_internal(key, ranking)
            == child_branch.query_internal(key, ranking));
    }
}

proof fn receipt_query_matches_branch_query(
    branch: LinkedBranch<Summary>,
    loaded: Map<Address, AllocationBranchNode>,
    receipt: LoadedPathReceipt,
)
    requires
        branch.inv(),
        receipt.valid_for(branch.root, loaded),
        receipt.target_is_leaf(),
        receipt.needed_addrs() <= branch.disk_view.entries.dom(),
        forall |addr: Address|
            #[trigger] receipt.needed_addrs().contains(addr)
            ==> loaded[addr] == branch.disk_view.entries[addr],
    ensures
        branch.query(receipt.key) == receipt.result(),
{
    let key = receipt.key;
    let msg = receipt.result();
    receipt_query_matches_branch_query_internal(branch, branch.the_ranking(), loaded, receipt);
    crate::betree::LinkedBranch_v::Refinement_v::query_internal_refines(
        branch,
        branch.the_ranking(),
        key,
        branch.query_internal(key, branch.the_ranking()),
    );
    crate::betree::LinkedBranch_v::Refinement_v::query_refines(branch, key, branch.query(key));
    assert(branch.query_internal(key, branch.the_ranking()) == msg);
    assert(branch.i_internal(branch.the_ranking()).query(key) == msg);
    assert(branch.i().query(key) == branch.query(key));
    assert(branch.i() == branch.i_internal(branch.the_ranking()));
    assert(branch.query(key) == msg);
}

proof fn branch_read_agrees_with_overlay_at(
    pre: ConcreteBranch::State,
    new_cache: Cache::State,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    branch_idx: nat,
    addr: Address,
)
    requires
        pre.wf(),
        branch_idx < pre.cached_branches.len(),
        Cache::State::next(pre.cache, new_cache, Cache::Label::Access{reads, writes}),
        pre.overlay_branch_entries_at(branch_idx).contains_key(addr),
        reads.contains_key(addr),
        to_branch_nodes(reads).contains_key(addr),
    ensures
        to_branch_nodes(reads)[addr] == pre.overlay_branch_entries_at(branch_idx)[addr],
{
    let lbl = Cache::Label::Access{reads, writes};
    reveal(Cache::State::next_by);
    reveal(Cache::State::next);
    assert(Cache::State::next_by(pre.cache, new_cache, lbl, Cache::Step::access()));
    assert(pre.cache.valid_read(addr, lbl->reads[addr])) by {};
    assert(pre.cache.lookup_map.contains_key(addr));
    assert(pre.cache.entries[pre.cache.lookup_map[addr]] is Filled);
    assert(pre.has_cached_page(addr));
    assert(pre.cache_raw_page(addr) == reads[addr]);
    assert(pre.overlay_raw_page_at(branch_idx, addr) == reads[addr]);
}

proof fn available_branch_node_unchanged_at_unwritten_addr(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    addr: Address,
)
    requires
        pre.wf(),
        post.wf(),
        post.disk == pre.disk,
        Cache::State::next(pre.cache, post.cache, Cache::Label::Access{reads, writes}),
        pre.available_branch_nodes().contains_key(addr),
        !writes.contains_key(addr),
    ensures
        post.available_branch_nodes().contains_key(addr),
        post.available_branch_nodes()[addr] == pre.available_branch_nodes()[addr],
{
    Cache::State::access_unwritten_addr_unchanged(pre.cache, post.cache, reads, writes, addr);
    if pre.has_cached_page(addr) {
        assert(post.has_cached_page(addr));
        assert(post.cache_raw_page(addr) == pre.cache_raw_page(addr));
        assert(post.available_branch_nodes()[addr]
            == crate::implementation::ConcreteBranch_v::decode_branch_page(post.cache_raw_page(addr)));
        assert(pre.available_branch_nodes()[addr]
            == crate::implementation::ConcreteBranch_v::decode_branch_page(pre.cache_raw_page(addr)));
    } else {
        if pre.cache.lookup_map.contains_key(addr) {
            let slot = pre.cache.lookup_map[addr];
            assert(!(pre.cache.entries[slot] is Filled));
            assert(post.cache.lookup_map.contains_key(addr));
            assert(post.cache.lookup_map[addr] == slot);
            assert(post.cache.entries[slot] == pre.cache.entries[slot]);
            assert(!(post.cache.entries[slot] is Filled));
            assert(!post.has_cached_page(addr));
        } else {
            assert(!post.cache.lookup_map.contains_key(addr));
            assert(!post.has_cached_page(addr));
        }
        assert(pre.disk.content.contains_key(addr));
        assert(post.disk.content.contains_key(addr));
        assert(post.available_branch_nodes()[addr]
            == crate::implementation::ConcreteBranch_v::decode_branch_page(post.disk.content[addr]));
        assert(pre.available_branch_nodes()[addr]
            == crate::implementation::ConcreteBranch_v::decode_branch_page(pre.disk.content[addr]));
    }
}

proof fn unavailable_branch_node_stays_unavailable_at_unwritten_addr(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    addr: Address,
)
    requires
        pre.wf(),
        post.wf(),
        post.disk == pre.disk,
        Cache::State::next(pre.cache, post.cache, Cache::Label::Access{reads, writes}),
        !pre.available_branch_nodes().contains_key(addr),
        !writes.contains_key(addr),
    ensures
        !post.available_branch_nodes().contains_key(addr),
{
    Cache::State::access_unwritten_addr_unchanged(pre.cache, post.cache, reads, writes, addr);
    assert(!pre.has_cached_page(addr));
    assert(!pre.disk.content.contains_key(addr));
    if pre.cache.lookup_map.contains_key(addr) {
        let slot = pre.cache.lookup_map[addr];
        assert(post.cache.lookup_map.contains_key(addr));
        assert(post.cache.lookup_map[addr] == slot);
        assert(post.cache.entries[slot] == pre.cache.entries[slot]);
        assert(!(pre.cache.entries[slot] is Filled));
        assert(!(post.cache.entries[slot] is Filled));
        assert(!post.has_cached_page(addr));
    } else {
        assert(!post.cache.lookup_map.contains_key(addr));
        assert(!post.has_cached_page(addr));
    }
    assert(!post.disk.content.contains_key(addr));
}

proof fn available_branch_nodes_unchanged_when_writes_empty(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    reads: Map<Address, RawPage>,
)
    requires
        pre.wf(),
        post.wf(),
        post.disk == pre.disk,
        Cache::State::next(pre.cache, post.cache, Cache::Label::Access{reads, writes: Map::<Address, RawPage>::empty()}),
    ensures
        post.available_branch_nodes() == pre.available_branch_nodes(),
{
    let writes = Map::<Address, RawPage>::empty();
    let pre_nodes = pre.available_branch_nodes();
    let post_nodes = post.available_branch_nodes();
    assert forall |addr: Address|
        #[trigger] post_nodes.contains_key(addr) <==> pre_nodes.contains_key(addr)
    by {
        if pre_nodes.contains_key(addr) {
            available_branch_node_unchanged_at_unwritten_addr(pre, post, reads, writes, addr);
        } else {
            unavailable_branch_node_stays_unavailable_at_unwritten_addr(pre, post, reads, writes, addr);
        }
    };
    assert forall |addr: Address|
        #[trigger] post_nodes.contains_key(addr) implies post_nodes[addr] == pre_nodes[addr]
    by {
        available_branch_node_unchanged_at_unwritten_addr(pre, post, reads, writes, addr);
    };
    assert_maps_equal!(post_nodes, pre_nodes);
}

proof fn written_addr_is_available_branch_node_after_access(
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
        writes.contains_key(addr),
    ensures
        post.available_branch_nodes().contains_key(addr),
        post.has_cached_page(addr),
        post.cache_raw_page(addr) == writes[addr],
        post.available_branch_nodes()[addr] == to_branch_nodes(writes)[addr],
{
    let lbl = Cache::Label::Access{reads, writes};
    reveal(Cache::State::next_by);
    reveal(Cache::State::next);
    assert(Cache::State::next_by(pre.cache, post.cache, lbl, Cache::Step::access()));
    assert(pre.cache.valid_write(addr)) by {};
    assert(pre.cache.lookup_map.contains_key(addr));
    let slot = pre.cache.lookup_map[addr];
    assert(post.cache.lookup_map == pre.cache.lookup_map);
    assert(post.cache.lookup_map.contains_key(addr));
    let updated_entries = pre.cache.write_updated_entries(writes);
    assert(pre.cache.lookup_map.restrict(writes.dom()).contains_key(addr));
    assert(pre.cache.lookup_map.restrict(writes.dom())[addr] == slot);
    assert(updated_entries.contains_key(slot));
    assert(updated_entries[slot] == crate::implementation::Cache_v::Entry::Filled{
        addr: pre.cache.entries[slot].get_addr(),
        data: writes[pre.cache.entries[slot].get_addr()],
    });
    assert(pre.cache.entries[slot].get_addr() == addr);
    assert(post.cache.entries[slot] == updated_entries[slot]);
    assert(post.cache.entries[slot] is Filled);
    assert(post.cache.entries[slot].get_addr() == addr);
    assert(post.has_cached_page(addr));
    assert(post.cache_raw_page(addr) == writes[addr]);
    assert(post.available_branch_nodes()[addr]
        == crate::implementation::ConcreteBranch_v::decode_branch_page(post.cache_raw_page(addr)));
    assert(post.available_branch_nodes()[addr] == to_branch_nodes(writes)[addr]);
}

proof fn reachable_terminal_contains_only_self(
    s: ConcreteBranch::State,
    branch_idx: nat,
    addr: Address,
    fuel: nat,
    a: Address,
)
    requires
        branch_idx < s.cached_branches.len(),
        fuel > 0,
        s.available_branch_nodes().contains_key(addr),
        s.available_branch_nodes()[addr] is Leaf || s.available_branch_nodes()[addr] is Auxiliary,
    ensures
        s.reachable_branch_addrs_from_with_fuel_contains(branch_idx, addr, fuel, a) <==> a == addr,
{
    assert(s.reachable_branch_addrs_from_with_fuel_contains(branch_idx, addr, fuel, a) <==> a == addr);
}

proof fn seal_write_addr_in_active_allocator(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Seal,
        ConcreteBranch::State::seal(pre, post, lbl, reads, writes, new_cache),
        writes.contains_key(addr),
    ensures
        pre.mini_allocator.all_aus().contains(addr.au),
{
    reveal(ConcreteBranch::State::seal);
    let read_nodes = to_branch_nodes(reads);
    let write_nodes = to_branch_nodes(writes);
    let aux_ptr = lbl->aux_ptr;
    assert(pre.active_cached_branch().can_seal(pre.mini_allocator, aux_ptr, read_nodes, write_nodes));
    assert(write_nodes.contains_key(addr));
    assert(write_nodes == crate::implementation::CachedBranch_v::loaded_seal_write_nodes(
        pre.active_cached_branch().root.unwrap(),
        read_nodes,
        aux_ptr,
        pre.mini_allocator.reserved_aus(),
    ));
    if addr == pre.active_cached_branch().root.unwrap() {
        assert(pre.active_cached_branch().valid_allocator(pre.mini_allocator));
        assert(pre.mini_allocator.all_aus().contains(addr.au));
    } else {
        assert(aux_ptr is Some);
        assert(addr == aux_ptr.unwrap());
        assert(pre.mini_allocator.can_allocate(addr));
        assert(pre.mini_allocator.allocs.contains_key(addr.au));
        assert(pre.mini_allocator.all_aus().contains(addr.au));
    }
}

proof fn historical_seal_writes_skip_branch_entry(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    j: nat,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Seal,
        ConcreteBranch::State::seal(pre, post, lbl, reads, writes, new_cache),
        j < pre.active_idx(),
        pre.i().branches[j as int].branch is Some,
        pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(addr),
    ensures
        !writes.contains_key(addr),
{
    let hist = pre.i().branches[j as int];
    let branch = hist.branch.unwrap();
    assert(hist.inv());
    assert(hist.sealed);
    assert(branch.tight_disk_view_with_summary());
    assert(branch.disk_view.representation() == branch.full_repr());
    assert(branch.full_repr().contains(addr));
    assert(branch.valid_sealed_branch());
    assert(branch.get_summary() == hist.mini_allocator.all_aus());
    assert(branch.get_summary().contains(addr.au));
    assert(pre.sealed_branch_disjoint_from_active_allocator_at(j));
    assert(branch.get_summary().disjoint(pre.mini_allocator.all_aus()));
    if writes.contains_key(addr) {
        seal_write_addr_in_active_allocator(pre, post, lbl, reads, writes, new_cache, addr);
        assert(pre.mini_allocator.all_aus().contains(addr.au));
        assert(false);
    }
}

proof fn historical_sealed_entry_unchanged_under_seal(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    j: nat,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Seal,
        ConcreteBranch::State::seal(pre, post, lbl, reads, writes, new_cache),
        post.disk == pre.disk,
        j < pre.active_idx(),
        pre.i().branches[j as int].branch is Some,
        pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(addr),
    ensures
        post.available_branch_nodes().contains_key(addr),
        post.available_branch_nodes()[addr] == pre.i().branches[j as int].branch.unwrap().disk_view.entries[addr],
{
    let branch = pre.i().branches[j as int].branch.unwrap();
    historical_seal_writes_skip_branch_entry(pre, post, lbl, reads, writes, new_cache, j, addr);
    branch_stack_entry_matches_overlay(pre, j);
    assert(pre.branch_stack_i_at(j).branch == Some(branch));
    assert(pre.overlay_branch_at(j) == Some(branch));
    assert(pre.overlay_branch_entries_at(j) == branch.disk_view.entries);
    ConcreteBranch::State::overlay_entry_matches_available(pre, j, addr);
    available_branch_node_unchanged_at_unwritten_addr(pre, post, reads, writes, addr);
}

proof fn historical_reachable_contains_unchanged_under_seal(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    j: nat,
    current_addr: Address,
    fuel: nat,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Seal,
        ConcreteBranch::State::seal(pre, post, lbl, reads, writes, new_cache),
        post.disk == pre.disk,
        j < pre.active_idx(),
        pre.i().branches[j as int].branch is Some,
        pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(current_addr),
    ensures
        pre.reachable_branch_addrs_from_with_fuel_contains(j, current_addr, fuel, addr)
            == post.reachable_branch_addrs_from_with_fuel_contains(j, current_addr, fuel, addr),
        pre.reachable_branch_addrs_from_with_fuel_contains(j, current_addr, fuel, addr)
            ==> pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(addr),
        post.reachable_branch_addrs_from_with_fuel_contains(j, current_addr, fuel, addr)
            ==> pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(addr),
    decreases fuel,
{
    let branch = pre.i().branches[j as int].branch.unwrap();
    let hist = pre.i().branches[j as int];
    branch_stack_entry_matches_overlay(pre, j);
    assert(pre.overlay_branch_at(j) == Some(branch));
    assert(pre.overlay_branch_entries_at(j) == branch.disk_view.entries);

    if fuel == 0 {
    } else {
        historical_sealed_entry_unchanged_under_seal(pre, post, lbl, reads, writes, new_cache, j, current_addr);
        ConcreteBranch::State::overlay_entry_matches_available(pre, j, current_addr);
        assert(pre.available_branch_nodes()[current_addr] == branch.disk_view.entries[current_addr]);
        assert(post.available_branch_nodes()[current_addr] == branch.disk_view.entries[current_addr]);
        let node = branch.disk_view.entries[current_addr];

        assert(post.cached_branches[j as int] == pre.cached_branches[j as int]);
        assert(pre.follow_aux_ptr_at(j, current_addr, node) == post.follow_aux_ptr_at(j, current_addr, node));

        if node is Leaf || node is Auxiliary {
            assert(pre.reachable_branch_addrs_from_with_fuel_contains(j, current_addr, fuel, addr) == (addr == current_addr));
            assert(post.reachable_branch_addrs_from_with_fuel_contains(j, current_addr, fuel, addr) == (addr == current_addr));
        } else {
            assert(hist.inv());
            assert(hist.sealed);
            assert(branch.valid_sealed_branch());
            assert(branch.inv());
            assert(branch.disk_view.no_dangling_address());
            assert(branch.disk_view.node_has_valid_child_address(node));

            if pre.follow_aux_ptr_at(j, current_addr, node) {
                assert(current_addr == branch.root);
                assert(node->aux_ptr is Some);
                assert(branch.disk_view.valid_address(node->aux_ptr.unwrap()));
                historical_reachable_contains_unchanged_under_seal(
                    pre,
                    post,
                    lbl,
                    reads,
                    writes,
                    new_cache,
                    j,
                    node->aux_ptr.unwrap(),
                    (fuel - 1) as nat,
                    addr,
                );
            }

            assert forall |i: int|
                0 <= i < node->children.len()
                implies pre.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, addr)
                    == post.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, addr)
                && (pre.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, addr)
                    ==> branch.disk_view.entries.contains_key(addr))
                && (post.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, addr)
                    ==> branch.disk_view.entries.contains_key(addr))
            by {
                assert(branch.disk_view.valid_address(node->children[i]));
                historical_reachable_contains_unchanged_under_seal(
                    pre,
                    post,
                    lbl,
                    reads,
                    writes,
                    new_cache,
                    j,
                    node->children[i],
                    (fuel - 1) as nat,
                    addr,
                );
            };
        }
    }
}

proof fn historical_post_overlay_entry_in_pre_branch_under_seal(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    j: nat,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Seal,
        ConcreteBranch::State::seal(pre, post, lbl, reads, writes, new_cache),
        post.disk == pre.disk,
        j < pre.active_idx(),
        pre.i().branches[j as int].branch is Some,
        post.overlay_branch_entries_at(j).contains_key(addr),
    ensures
        pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(addr),
{
    let branch = pre.i().branches[j as int].branch.unwrap();
    let hist = pre.i().branches[j as int];
    branch_stack_entry_matches_overlay(pre, j);
    assert(pre.overlay_branch_at(j) == Some(branch));
    assert(hist.inv());
    assert(hist.sealed);
    assert(branch.valid_sealed_branch());
    assert(branch.inv());
    assert(branch.disk_view.entries.contains_key(branch.root));
    historical_reachable_contains_unchanged_under_seal(
        pre,
        post,
        lbl,
        reads,
        writes,
        new_cache,
        j,
        branch.root,
        post.available_branch_nodes().dom().len(),
        addr,
    );
}

proof fn seal_available_branch_nodes_domain(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Seal,
        ConcreteBranch::State::seal(pre, post, lbl, reads, writes, new_cache),
        post.disk == pre.disk,
    ensures
        lbl->aux_ptr is Some ==> post.available_branch_nodes().dom()
            == pre.available_branch_nodes().dom().insert(lbl->aux_ptr.unwrap()),
        lbl->aux_ptr is None ==> post.available_branch_nodes().dom()
            == pre.available_branch_nodes().dom(),
{
    let aux_ptr = lbl->aux_ptr;
    let write_nodes = to_branch_nodes(writes);
    if aux_ptr is None {
        assert(write_nodes == crate::implementation::CachedBranch_v::loaded_seal_write_nodes(
            pre.active_cached_branch().root.unwrap(),
            to_branch_nodes(reads),
            aux_ptr,
            pre.mini_allocator.reserved_aus(),
        ));
        assert forall |addr: Address| #[trigger] writes.contains_key(addr) <==> false by {
            assert(write_nodes.contains_key(addr) == writes.contains_key(addr));
        };
        assert_maps_equal!(writes, Map::<Address, RawPage>::empty());
        assert forall |addr: Address|
            #[trigger] post.available_branch_nodes().contains_key(addr)
                <==> pre.available_branch_nodes().contains_key(addr)
        by {
            if pre.available_branch_nodes().contains_key(addr) {
                available_branch_node_unchanged_at_unwritten_addr(pre, post, reads, writes, addr);
            } else {
                unavailable_branch_node_stays_unavailable_at_unwritten_addr(pre, post, reads, writes, addr);
            }
        };
    } else {
        let aux = aux_ptr.unwrap();
        assert(!pre.available_branch_nodes().contains_key(aux));
        assert(write_nodes == crate::implementation::CachedBranch_v::loaded_seal_write_nodes(
            pre.active_cached_branch().root.unwrap(),
            to_branch_nodes(reads),
            aux_ptr,
            pre.mini_allocator.reserved_aus(),
        ));
        assert(write_nodes.contains_key(aux));
        assert(writes.contains_key(aux));
        written_addr_is_available_branch_node_after_access(pre, post, reads, writes, aux);
        assert forall |addr: Address|
            addr != aux
            implies #[trigger] post.available_branch_nodes().contains_key(addr)
                <==> pre.available_branch_nodes().contains_key(addr)
        by {
            if pre.available_branch_nodes().contains_key(addr) {
                if writes.contains_key(addr) {
                    written_addr_is_available_branch_node_after_access(pre, post, reads, writes, addr);
                } else {
                    available_branch_node_unchanged_at_unwritten_addr(pre, post, reads, writes, addr);
                }
            } else {
                if writes.contains_key(addr) {
                    assert(write_nodes.contains_key(addr));
                    assert(addr == pre.active_cached_branch().root.unwrap());
                    reveal(Cache::State::next_by);
                    reveal(Cache::State::next);
                    let cache_lbl = Cache::Label::Access{reads, writes};
                    assert(Cache::State::next_by(pre.cache, post.cache, cache_lbl, Cache::Step::access()));
                    assert(pre.cache.valid_read(addr, reads[addr])) by {};
                    assert(pre.has_cached_page(addr));
                    assert(pre.available_branch_nodes().contains_key(addr));
                } else {
                    unavailable_branch_node_stays_unavailable_at_unwritten_addr(pre, post, reads, writes, addr);
                }
            }
        };
        assert forall |addr: Address|
            #[trigger] post.available_branch_nodes().dom().contains(addr)
                <==> pre.available_branch_nodes().dom().insert(aux).contains(addr)
        by {
            if addr == aux {
            } else {
                assert(post.available_branch_nodes().contains_key(addr)
                    <==> pre.available_branch_nodes().contains_key(addr));
            }
        };
        assert(post.available_branch_nodes().dom() == pre.available_branch_nodes().dom().insert(aux));
    }
}

proof fn historical_pre_branch_entry_in_post_overlay_under_seal(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    j: nat,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Seal,
        ConcreteBranch::State::seal(pre, post, lbl, reads, writes, new_cache),
        post.disk == pre.disk,
        j < pre.active_idx(),
        pre.i().branches[j as int].branch is Some,
        pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(addr),
    ensures
        post.overlay_branch_entries_at(j).contains_key(addr),
        post.overlay_branch_entries_at(j)[addr] == pre.i().branches[j as int].branch.unwrap().disk_view.entries[addr],
{
    let branch = pre.i().branches[j as int].branch.unwrap();
    branch_stack_entry_matches_overlay(pre, j);
    assert(pre.i().branches[j as int] == pre.branch_stack_i_at(j));
    assert(pre.i().branches[j as int].branch is Some);
    assert(pre.i().branches[j as int].branch.unwrap() == branch);
    assert(pre.branch_stack_i_at(j).branch is Some);
    assert(pre.branch_stack_i_at(j).branch.unwrap() == branch);
    assert(pre.overlay_branch_at(j) is Some);
    assert(pre.overlay_branch_at(j).unwrap() == branch);
    assert(pre.overlay_branch_entries_at(j) == branch.disk_view.entries);
    let root = branch.root;
    let pre_len = pre.available_branch_nodes().dom().len();
    assert(pre.overlay_branch_entries_at(j).contains_key(addr));
    assert(pre.has_overlay_page_at(j, addr));
    assert(pre.reachable_branch_addrs_from_with_fuel_contains(j, root, pre_len, addr));

    seal_available_branch_nodes_domain(pre, post, lbl, reads, writes, new_cache);
    if lbl->aux_ptr is Some {
        let aux = lbl->aux_ptr.unwrap();
        assert(post.available_branch_nodes().dom() == pre.available_branch_nodes().dom().insert(aux));
        vstd::set::axiom_set_insert_len(pre.available_branch_nodes().dom(), aux);
        ConcreteBranch::State::reachable_branch_addrs_more_fuel(pre, j, root, pre_len, addr);
        historical_reachable_contains_unchanged_under_seal(
            pre,
            post,
            lbl,
            reads,
            writes,
            new_cache,
            j,
            root,
            pre_len + 1,
            addr,
        );
        assert(post.available_branch_nodes().dom().len() == pre_len + 1);
        assert(post.has_overlay_page_at(j, addr));
    } else {
        assert(post.available_branch_nodes().dom() == pre.available_branch_nodes().dom());
        historical_reachable_contains_unchanged_under_seal(
            pre,
            post,
            lbl,
            reads,
            writes,
            new_cache,
            j,
            root,
            pre_len,
            addr,
        );
        assert(post.available_branch_nodes().dom().len() == pre_len);
        assert(post.has_overlay_page_at(j, addr));
    }
    ConcreteBranch::State::overlay_entry_matches_available(post, j, addr);
    historical_sealed_entry_unchanged_under_seal(pre, post, lbl, reads, writes, new_cache, j, addr);
}

proof fn historical_overlay_unchanged_under_seal(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    j: nat,
)
    requires
        pre.refinement_wf(),
        post.refinement_wf(),
        lbl is Seal,
        ConcreteBranch::State::seal(pre, post, lbl, reads, writes, new_cache),
        post.disk == pre.disk,
        j < pre.active_idx(),
        pre.i().branches[j as int].branch is Some,
    ensures
        post.overlay_branch_entries_at(j) == pre.overlay_branch_entries_at(j),
        post.overlay_branch_at(j) == pre.overlay_branch_at(j),
        post.branch_stack_i_at(j) == pre.branch_stack_i_at(j),
{
    let branch = pre.i().branches[j as int].branch.unwrap();
    branch_stack_entry_matches_overlay(pre, j);
    assert(pre.i().branches[j as int] == pre.branch_stack_i_at(j));
    assert(pre.i().branches[j as int].branch is Some);
    assert(pre.i().branches[j as int].branch.unwrap() == branch);
    assert(pre.branch_stack_i_at(j).branch is Some);
    assert(pre.branch_stack_i_at(j).branch.unwrap() == branch);
    assert(pre.overlay_branch_at(j) is Some);
    assert(pre.overlay_branch_at(j).unwrap() == branch);
    assert(pre.overlay_branch_entries_at(j) == branch.disk_view.entries);

    let pre_entries = pre.overlay_branch_entries_at(j);
    let post_entries = post.overlay_branch_entries_at(j);
    assert forall |addr: Address| #[trigger] post_entries.contains_key(addr) <==> pre_entries.contains_key(addr) by {
        if post_entries.contains_key(addr) {
            historical_post_overlay_entry_in_pre_branch_under_seal(pre, post, lbl, reads, writes, new_cache, j, addr);
        } else if pre_entries.contains_key(addr) {
            historical_pre_branch_entry_in_post_overlay_under_seal(pre, post, lbl, reads, writes, new_cache, j, addr);
        }
    };
    assert forall |addr: Address| #[trigger] pre_entries.contains_key(addr) implies post_entries[addr] == pre_entries[addr] by {
        historical_pre_branch_entry_in_post_overlay_under_seal(pre, post, lbl, reads, writes, new_cache, j, addr);
        ConcreteBranch::State::overlay_entry_matches_available(post, j, addr);
        historical_sealed_entry_unchanged_under_seal(pre, post, lbl, reads, writes, new_cache, j, addr);
    };
    assert_maps_equal!(post_entries, pre_entries);

    assert(post.cached_branches[j as int] == pre.cached_branches[j as int]);
    assert(post.overlay_branch_at(j) == pre.overlay_branch_at(j));
    assert(post.branch_stack_i_at(j).branch == post.overlay_branch_at(j));
    assert(pre.branch_stack_i_at(j).branch == pre.overlay_branch_at(j));
    assert(post.branch_stack_i_at(j) == pre.branch_stack_i_at(j));
}

proof fn active_reachable_contains_unchanged_under_seal_except(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    branch: LinkedBranch<Summary>,
    subbranch: LinkedBranch<Summary>,
    except: Set<Address>,
    fuel: nat,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Seal,
        lbl->aux_ptr is Some,
        ConcreteBranch::State::seal(pre, post, lbl, reads, writes, new_cache),
        post.disk == pre.disk,
        pre.overlay_branch() == Some(branch),
        branch.inv(),
        subbranch.disk_view == branch.disk_view,
        subbranch.inv_internal(branch.the_ranking()),
        except.contains(branch.root),
        subbranch.reachable_addrs_using_ranking(branch.the_ranking()).disjoint(except),
        forall |a: Address| #[trigger] branch.disk_view.entries.contains_key(a) && !except.contains(a) ==> {
            &&& post.available_branch_nodes().contains_key(a)
            &&& post.available_branch_nodes()[a] == branch.disk_view.entries[a]
        },
    ensures
        pre.reachable_branch_addrs_from_with_fuel(pre.active_idx() as nat, subbranch.root, fuel)
            == post.reachable_branch_addrs_from_with_fuel(pre.active_idx() as nat, subbranch.root, fuel),
    decreases fuel,
{
    let j = pre.active_idx() as nat;
    if fuel == 0 {
        assert(pre.reachable_branch_addrs_from_with_fuel(j, subbranch.root, fuel)
            == post.reachable_branch_addrs_from_with_fuel(j, subbranch.root, fuel));
    } else {
        ConcreteBranch::State::overlay_entry_matches_available(pre, j, subbranch.root);
        assert(!except.contains(subbranch.root)) by {
            assert(subbranch.reachable_addrs_using_ranking(branch.the_ranking()).contains(subbranch.root));
        };
        assert(post.available_branch_nodes().contains_key(subbranch.root));
        let node = branch.disk_view.entries[subbranch.root];
        assert(pre.available_branch_nodes()[subbranch.root] == node);
        assert(post.available_branch_nodes()[subbranch.root] == node);
        if node is Leaf || node is Auxiliary {
            assert forall |a: Address|
                #[trigger] pre.reachable_branch_addrs_from_with_fuel_contains(j, subbranch.root, fuel, a)
                    <==> post.reachable_branch_addrs_from_with_fuel_contains(j, subbranch.root, fuel, a)
            by {
                reachable_terminal_contains_only_self(pre, j, subbranch.root, fuel, a);
                reachable_terminal_contains_only_self(post, j, subbranch.root, fuel, a);
            };
            assert forall |a: Address|
                #[trigger] pre.reachable_branch_addrs_from_with_fuel(j, subbranch.root, fuel).contains(a)
                    <==> post.reachable_branch_addrs_from_with_fuel(j, subbranch.root, fuel).contains(a)
            by {
                assert(pre.reachable_branch_addrs_from_with_fuel(j, subbranch.root, fuel).contains(a)
                    == pre.reachable_branch_addrs_from_with_fuel_contains(j, subbranch.root, fuel, a));
                assert(post.reachable_branch_addrs_from_with_fuel(j, subbranch.root, fuel).contains(a)
                    == post.reachable_branch_addrs_from_with_fuel_contains(j, subbranch.root, fuel, a));
            };
            assert(pre.reachable_branch_addrs_from_with_fuel(j, subbranch.root, fuel)
                == post.reachable_branch_addrs_from_with_fuel(j, subbranch.root, fuel));
        } else {
            assert(!pre.follow_aux_ptr_at(j, subbranch.root, node));
            assert(!post.follow_aux_ptr_at(j, subbranch.root, node)) by {
                if post.follow_aux_ptr_at(j, subbranch.root, node) {
                    assert(subbranch.root == branch.root);
                }
            };
            let pre_child_sets = Seq::new(
                node->children.len(),
                |i: int| pre.reachable_branch_addrs_from_with_fuel(
                    j,
                    node->children[i],
                    (fuel - 1) as nat,
                ),
            );
            let post_child_sets = Seq::new(
                node->children.len(),
                |i: int| post.reachable_branch_addrs_from_with_fuel(
                    j,
                    node->children[i],
                    (fuel - 1) as nat,
                ),
            );
            assert forall |i: int|
                0 <= i < pre_child_sets.len()
                implies #[trigger] pre_child_sets[i] == post_child_sets[i]
            by {
                assert(subbranch.root().valid_child_index(i));
                child_branch_inv_internal_from_parent(subbranch, branch.the_ranking(), i);
                crate::betree::LinkedBranch_v::Refinement_v::lemma_reachable_disjoint_implies_child_reachable_disjoint(
                    subbranch,
                    branch.the_ranking(),
                    except,
                    i,
                );
                active_reachable_contains_unchanged_under_seal_except(
                    pre,
                    post,
                    lbl,
                    reads,
                    writes,
                    new_cache,
                    branch,
                    subbranch.child_at_idx(i),
                    except,
                    (fuel - 1) as nat,
                );
            };
            union_seq_of_sets_equal(pre_child_sets, post_child_sets);
            assert forall |a: Address|
                #[trigger] pre.reachable_branch_addrs_from_with_fuel_contains(j, subbranch.root, fuel, a)
                    <==> post.reachable_branch_addrs_from_with_fuel_contains(j, subbranch.root, fuel, a)
            by {
                if pre.reachable_branch_addrs_from_with_fuel_contains(j, subbranch.root, fuel, a) {
                    if a != subbranch.root {
                        let i = choose |i: int|
                            0 <= i < node->children.len() &&
                            pre.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, a);
                        assert(pre_child_sets[i].contains(a));
                        assert(post_child_sets[i].contains(a));
                        crate::betree::Utils_v::lemma_set_subset_of_union_seq_of_sets(pre_child_sets, a);
                        assert(crate::betree::Utils_v::union_seq_of_sets(post_child_sets).contains(a));
                        assert(post.reachable_branch_addrs_from_with_fuel_contains(
                            j,
                            node->children[i],
                            (fuel - 1) as nat,
                            a,
                        ));
                        assert(post.reachable_branch_addrs_from_with_fuel_contains(j, subbranch.root, fuel, a));
                    }
                }
                if post.reachable_branch_addrs_from_with_fuel_contains(j, subbranch.root, fuel, a) {
                    if a != subbranch.root {
                        let i = choose |i: int|
                            0 <= i < node->children.len() &&
                            post.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, a);
                        assert(post_child_sets[i].contains(a));
                        assert(pre_child_sets[i].contains(a));
                        crate::betree::Utils_v::lemma_set_subset_of_union_seq_of_sets(post_child_sets, a);
                        assert(crate::betree::Utils_v::union_seq_of_sets(pre_child_sets).contains(a));
                        assert(pre.reachable_branch_addrs_from_with_fuel_contains(
                            j,
                            node->children[i],
                            (fuel - 1) as nat,
                            a,
                        ));
                        assert(pre.reachable_branch_addrs_from_with_fuel_contains(j, subbranch.root, fuel, a));
                    }
                }
            };
            assert forall |a: Address|
                #[trigger] pre.reachable_branch_addrs_from_with_fuel(j, subbranch.root, fuel).contains(a)
                    <==> post.reachable_branch_addrs_from_with_fuel(j, subbranch.root, fuel).contains(a)
            by {
                assert(pre.reachable_branch_addrs_from_with_fuel(j, subbranch.root, fuel).contains(a)
                    == pre.reachable_branch_addrs_from_with_fuel_contains(j, subbranch.root, fuel, a));
                assert(post.reachable_branch_addrs_from_with_fuel(j, subbranch.root, fuel).contains(a)
                    == post.reachable_branch_addrs_from_with_fuel_contains(j, subbranch.root, fuel, a));
            };
            assert(pre.reachable_branch_addrs_from_with_fuel(j, subbranch.root, fuel)
                == post.reachable_branch_addrs_from_with_fuel(j, subbranch.root, fuel));
        }
    }
}

proof fn active_sealed_root_reachable_branch_addrs_equal_under_aux_write(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    branch: LinkedBranch<Summary>,
    aux_addr: Address,
    fuel: nat,
)
    requires
        fuel > 1,
        pre.refinement_wf(),
        post.wf(),
        lbl is Seal,
        lbl->aux_ptr == Some(aux_addr),
        ConcreteBranch::State::seal(pre, post, lbl, reads, writes, new_cache),
        post.disk == pre.disk,
        pre.overlay_branch() == Some(branch),
        branch.inv(),
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
        post.reachable_branch_addrs_from_with_fuel(pre.active_idx() as nat, branch.root, fuel)
            == pre.reachable_branch_addrs_from_with_fuel(pre.active_idx() as nat, branch.root, fuel).insert(aux_addr),
{
    let j = pre.active_idx() as nat;
    let ranking = branch.the_ranking();
    let root = branch.root;
    let node = branch.root();
    let except = set!{root, aux_addr};
    let pre_child_sets = Seq::new(
        node->children.len(),
        |i: int| pre.reachable_branch_addrs_from_with_fuel(j, node->children[i], (fuel - 1) as nat),
    );
    let post_child_sets = Seq::new(
        node->children.len(),
        |i: int| post.reachable_branch_addrs_from_with_fuel(j, node->children[i], (fuel - 1) as nat),
    );
    assert forall |i: int|
        0 <= i < pre_child_sets.len()
        implies #[trigger] pre_child_sets[i] == post_child_sets[i]
    by {
        assert(branch.root().valid_child_index(i));
        child_branch_inv_internal_from_parent(branch, ranking, i);
        let child = branch.child_at_idx(i);
        assert(child.reachable_addrs_using_ranking(ranking).disjoint(except)) by {
            if child.reachable_addrs_using_ranking(ranking).contains(root) {
                crate::betree::LinkedBranch_v::Refinement_v::lemma_reachable_child_has_smaller_rank(child, ranking, root);
            }
            if child.reachable_addrs_using_ranking(ranking).contains(aux_addr) {
                crate::betree::LinkedBranch_v::Refinement_v::lemma_reachable_implies_valid_address(child, ranking, aux_addr);
            }
        };
        active_reachable_contains_unchanged_under_seal_except(
            pre,
            post,
            lbl,
            reads,
            writes,
            new_cache,
            branch,
            child,
            except,
            (fuel - 1) as nat,
        );
    };
    union_seq_of_sets_equal(pre_child_sets, post_child_sets);
    assert(!pre.follow_aux_ptr_at(j, root, node));
    assert(post.follow_aux_ptr_at(j, root, post.available_branch_nodes()[root]));
    assert(post.available_branch_nodes()[aux_addr] is Auxiliary);
    assert forall |a: Address|
        #[trigger] post.reachable_branch_addrs_from_with_fuel_contains(j, aux_addr, (fuel - 1) as nat, a)
            <==> a == aux_addr
    by {
        reachable_terminal_contains_only_self(post, j, aux_addr, (fuel - 1) as nat, a);
    };
    assert forall |a: Address|
        #[trigger] post.reachable_branch_addrs_from_with_fuel(j, branch.root, fuel).contains(a)
            <==> pre.reachable_branch_addrs_from_with_fuel(j, branch.root, fuel).insert(aux_addr).contains(a)
    by {
        assert(post.reachable_branch_addrs_from_with_fuel(j, aux_addr, (fuel - 1) as nat).contains(a)
            == post.reachable_branch_addrs_from_with_fuel_contains(j, aux_addr, (fuel - 1) as nat, a));
        if post.reachable_branch_addrs_from_with_fuel(j, branch.root, fuel).contains(a) {
            if a == aux_addr {
            } else if a == root {
            } else {
                let i = choose |i: int|
                    0 <= i < node->children.len()
                    && post.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, a);
                assert(post_child_sets[i].contains(a));
                assert(pre_child_sets[i].contains(a));
                assert(pre.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, a));
                assert(exists |k: int|
                    0 <= k < node->children.len()
                    && pre.reachable_branch_addrs_from_with_fuel_contains(j, node->children[k], (fuel - 1) as nat, a));
                assert(pre.reachable_branch_addrs_from_with_fuel_contains(j, root, fuel, a));
            }
        }
        if pre.reachable_branch_addrs_from_with_fuel(j, branch.root, fuel).insert(aux_addr).contains(a) {
            if a == aux_addr {
                assert(post.reachable_branch_addrs_from_with_fuel_contains(j, aux_addr, (fuel - 1) as nat, a));
                assert(post.reachable_branch_addrs_from_with_fuel_contains(j, root, fuel, a));
            } else if a == root {
            } else {
                let post_root_node = post.available_branch_nodes()[root];
                assert(post_root_node == AllocationBranchNode::Index{
                    pivots: node->pivots,
                    children: node->children,
                    aux_ptr: Some(aux_addr),
                });
                let i = choose |i: int|
                    0 <= i < node->children.len()
                    && pre.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, a);
                assert(pre_child_sets[i].contains(a));
                assert(post_child_sets[i].contains(a));
                assert(post.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, a));
                assert(post.reachable_branch_addrs_from_with_fuel_contains(j, root, fuel, a)
                    == (
                        a == root
                        || post.follow_aux_ptr_at(j, root, post_root_node)
                            && post.reachable_branch_addrs_from_with_fuel_contains(j, post_root_node->aux_ptr.unwrap(), (fuel - 1) as nat, a)
                        || exists |k: int|
                            0 <= k < post_root_node->children.len()
                            && post.reachable_branch_addrs_from_with_fuel_contains(j, post_root_node->children[k], (fuel - 1) as nat, a)
                    ));
                assert(exists |k: int|
                    0 <= k < node->children.len()
                    && post.reachable_branch_addrs_from_with_fuel_contains(j, node->children[k], (fuel - 1) as nat, a));
                assert(post.reachable_branch_addrs_from_with_fuel_contains(j, root, fuel, a));
            }
        }
    };
    assert(post.reachable_branch_addrs_from_with_fuel(j, branch.root, fuel)
        == pre.reachable_branch_addrs_from_with_fuel(j, branch.root, fuel).insert(aux_addr));
}

proof fn active_concrete_reachable_implies_in_branch_disk_view(
    pre: ConcreteBranch::State,
    branch: LinkedBranch<Summary>,
    current_addr: Address,
    fuel: nat,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        pre.overlay_branch() == Some(branch),
        branch.inv(),
        branch.disk_view.entries.contains_key(current_addr),
        pre.reachable_branch_addrs_from_with_fuel_contains(pre.active_idx() as nat, current_addr, fuel, addr),
    ensures
        branch.disk_view.entries.contains_key(addr),
    decreases fuel,
{
    let j = pre.active_idx() as nat;
    if fuel == 0 {
        assert(false);
    } else {
        overlay_entries_match_branch_disk(pre, j, branch, current_addr);
        let node = branch.disk_view.entries[current_addr];
        if node is Leaf || node is Auxiliary {
            reachable_terminal_contains_only_self(pre, j, current_addr, fuel, addr);
            assert(addr == current_addr);
        } else if addr == current_addr {
        } else if pre.follow_aux_ptr_at(j, current_addr, node)
            && pre.reachable_branch_addrs_from_with_fuel_contains(j, node->aux_ptr.unwrap(), (fuel - 1) as nat, addr) {
            assert(branch.disk_view.entries.contains_key(node->aux_ptr.unwrap()));
            active_concrete_reachable_implies_in_branch_disk_view(
                pre,
                branch,
                node->aux_ptr.unwrap(),
                (fuel - 1) as nat,
                addr,
            );
        } else {
            let i = choose |i: int|
                0 <= i < node->children.len()
                && pre.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, addr);
            assert(branch.disk_view.valid_address(node->children[i]));
            active_concrete_reachable_implies_in_branch_disk_view(
                pre,
                branch,
                node->children[i],
                (fuel - 1) as nat,
                addr,
            );
        }
    }
}

proof fn concrete_reachable_implies_in_agreeing_branch_disk_view(
    s: ConcreteBranch::State,
    branch_idx: nat,
    branch: LinkedBranch<Summary>,
    current_addr: Address,
    fuel: nat,
    addr: Address,
)
    requires
        s.wf(),
        branch_idx < s.cached_branches.len(),
        s.cached_branches[branch_idx as int].root == Some(branch.root),
        branch.inv(),
        s.cached_branches[branch_idx as int].sealed ==> branch.valid_sealed_branch(),
        branch.disk_view.entries.contains_key(current_addr),
        forall |a: Address| #[trigger] branch.disk_view.entries.contains_key(a) ==> {
            &&& s.available_branch_nodes().contains_key(a)
            &&& s.available_branch_nodes()[a] == branch.disk_view.entries[a]
        },
        s.reachable_branch_addrs_from_with_fuel_contains(branch_idx, current_addr, fuel, addr),
    ensures
        branch.disk_view.entries.contains_key(addr),
    decreases fuel,
{
    if fuel == 0 {
        assert(false);
    } else {
        let node = branch.disk_view.entries[current_addr];
        assert(s.available_branch_nodes().contains_key(current_addr));
        assert(s.available_branch_nodes()[current_addr] == node);
        if node is Leaf || node is Auxiliary {
            reachable_terminal_contains_only_self(s, branch_idx, current_addr, fuel, addr);
            assert(addr == current_addr);
        } else if addr == current_addr {
        } else if s.follow_aux_ptr_at(branch_idx, current_addr, node)
            && s.reachable_branch_addrs_from_with_fuel_contains(
                branch_idx,
                node->aux_ptr.unwrap(),
                (fuel - 1) as nat,
                addr,
            ) {
            assert(current_addr == s.cached_branches[branch_idx as int].root.unwrap());
            assert(current_addr == branch.root);
            assert(s.cached_branches[branch_idx as int].sealed);
            assert(branch.valid_sealed_branch());
            assert(branch.sealed_root());
            assert(branch.disk_view.valid_address(node->aux_ptr.unwrap()));
            concrete_reachable_implies_in_agreeing_branch_disk_view(
                s,
                branch_idx,
                branch,
                node->aux_ptr.unwrap(),
                (fuel - 1) as nat,
                addr,
            );
        } else {
            let i = choose |i: int|
                0 <= i < node->children.len()
                && s.reachable_branch_addrs_from_with_fuel_contains(branch_idx, node->children[i], (fuel - 1) as nat, addr);
            assert(branch.disk_view.valid_address(node->children[i]));
            concrete_reachable_implies_in_agreeing_branch_disk_view(
                s,
                branch_idx,
                branch,
                node->children[i],
                (fuel - 1) as nat,
                addr,
            );
        }
    }
}

proof fn active_sparse_map_preserved_under_aux_seal(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
)
    requires
        pre.refinement_wf(),
        post.refinement_wf(),
        lbl is Seal,
        lbl->aux_ptr is Some,
        ConcreteBranch::State::seal(pre, post, lbl, reads, writes, new_cache),
        post.disk == pre.disk,
    ensures
        AllocationBranchStack::branch_sparse_map(post.branch_stack_i_at(pre.active_idx() as nat))
            == AllocationBranchStack::branch_sparse_map(pre.i().active_branch()),
{
    reveal(ConcreteBranch::State::seal);
    let j = pre.active_idx() as nat;
    let branch = pre.overlay_branch().unwrap();
    let root = branch.root;
    let aux = lbl->aux_ptr.unwrap();
    let summary = pre.mini_allocator.reserved_aus();
    let sealed = branch.seal(aux, summary);
    let read_nodes = to_branch_nodes(reads);
    let write_nodes = to_branch_nodes(writes);
    let cache_lbl = Cache::Label::Access{reads, writes};

    branch_stack_entry_matches_overlay(pre, j);
    assert(pre.i().branches[j as int] == pre.branch_stack_i_at(j));
    assert(pre.i().active_branch() == pre.branch_stack_i_at(j));
    assert(pre.branch_stack_i_at(j).branch == Some(branch));
    assert(pre.overlay_branch_at(j) == Some(branch));
    assert(pre.overlay_branch_entries_at(j) == branch.disk_view.entries);
    assert(pre.active_cached_branch().can_seal(pre.mini_allocator, lbl->aux_ptr, read_nodes, write_nodes));
    reveal(Cache::State::next_by);
    reveal(Cache::State::next);
    assert(Cache::State::next_by(pre.cache, new_cache, cache_lbl, Cache::Step::access()));
    assert(cache_lbl->reads.contains_key(root));
    assert(pre.cache.valid_read(root, cache_lbl->reads[root])) by {};
    ConcreteBranch::State::overlay_entry_matches_available(pre, j, root);
    assert(read_nodes[root] == crate::implementation::ConcreteBranch_v::decode_branch_page(reads[root]));
    assert(pre.has_cached_page(root));
    assert(pre.available_branch_nodes()[root] == branch.disk_view.entries[root]);
    assert(read_nodes[root] == pre.available_branch_nodes()[root]);
    assert(branch.inv());
    assert(read_nodes[root] is Index);
    assert(branch.root() == read_nodes[root]);
    assert(branch.root() is Index);
    assert(write_nodes == crate::implementation::CachedBranch_v::loaded_seal_write_nodes(
        root,
        read_nodes,
        lbl->aux_ptr,
        summary,
    ));
    assert(write_nodes.dom() == set!{root, aux});
    assert(write_nodes.contains_key(root));
    assert(write_nodes.contains_key(aux));
    assert(writes.contains_key(root));
    assert(writes.contains_key(aux));
    assert(!pre.available_branch_nodes().contains_key(aux));

    assert forall |addr: Address| #[trigger] branch.disk_view.entries.contains_key(addr) && addr != root implies {
        &&& post.available_branch_nodes().contains_key(addr)
        &&& post.available_branch_nodes()[addr] == branch.disk_view.entries[addr]
    } by {
        overlay_entries_match_branch_disk(pre, j, branch, addr);
        ConcreteBranch::State::overlay_entry_matches_available(pre, j, addr);
        assert(!write_nodes.contains_key(addr));
        assert(!writes.contains_key(addr));
        available_branch_node_unchanged_at_unwritten_addr(pre, post, reads, writes, addr);
    };

    written_addr_is_available_branch_node_after_access(pre, post, reads, writes, root);
    written_addr_is_available_branch_node_after_access(pre, post, reads, writes, aux);
    assert(post.available_branch_nodes()[root] == write_nodes[root]);
    assert(post.available_branch_nodes()[root] == sealed.disk_view.entries[root]);
    assert(post.available_branch_nodes()[aux] == write_nodes[aux]);
    assert(post.available_branch_nodes()[aux] == sealed.disk_view.entries[aux]);

    seal_available_branch_nodes_domain(pre, post, lbl, reads, writes, new_cache);
    let pre_len = pre.available_branch_nodes().dom().len();
    assert(post.available_branch_nodes().dom() == pre.available_branch_nodes().dom().insert(aux));
    vstd::set::axiom_set_insert_len(pre.available_branch_nodes().dom(), aux);
    assert(post.available_branch_nodes().dom().len() == pre_len + 1);

    active_sealed_root_reachable_branch_addrs_equal_under_aux_write(
        pre,
        post,
        lbl,
        reads,
        writes,
        new_cache,
        branch,
        aux,
        post.available_branch_nodes().dom().len(),
    );

    assert forall |addr: Address|
        #[trigger] post.overlay_branch_entries_at(j).contains_key(addr) <==> sealed.disk_view.entries.contains_key(addr)
    by {
        if post.overlay_branch_entries_at(j).contains_key(addr) {
            assert(post.reachable_branch_addrs_from_with_fuel(j, root, post.available_branch_nodes().dom().len()).contains(addr));
            if addr != aux {
                assert(pre.reachable_branch_addrs_from_with_fuel(j, root, post.available_branch_nodes().dom().len()).contains(addr));
                active_concrete_reachable_implies_in_branch_disk_view(
                    pre,
                    branch,
                    root,
                    post.available_branch_nodes().dom().len(),
                    addr,
                );
            }
            assert(sealed.disk_view.entries.contains_key(addr));
        }
        if sealed.disk_view.entries.contains_key(addr) {
            if addr == aux {
                assert(post.reachable_branch_addrs_from_with_fuel_contains(j, aux, (post.available_branch_nodes().dom().len() - 1) as nat, addr));
                assert(post.reachable_branch_addrs_from_with_fuel_contains(j, root, post.available_branch_nodes().dom().len(), addr));
                assert(post.overlay_branch_entries_at(j).contains_key(addr));
            } else {
                assert(branch.disk_view.entries.contains_key(addr));
                overlay_entries_match_branch_disk(pre, j, branch, addr);
                ConcreteBranch::State::reachable_branch_addrs_more_fuel(pre, j, root, pre_len, addr);
                assert(pre.reachable_branch_addrs_from_with_fuel(j, root, post.available_branch_nodes().dom().len()).contains(addr));
                assert(post.reachable_branch_addrs_from_with_fuel(j, root, post.available_branch_nodes().dom().len()).contains(addr));
                assert(post.overlay_branch_entries_at(j).contains_key(addr));
            }
        }
    };
    assert forall |addr: Address|
        #[trigger] post.overlay_branch_entries_at(j).contains_key(addr)
            implies post.overlay_branch_entries_at(j)[addr] == sealed.disk_view.entries[addr]
    by {
        if addr == aux || addr == root {
            ConcreteBranch::State::overlay_entry_matches_available(post, j, addr);
        } else {
            ConcreteBranch::State::overlay_entry_matches_available(post, j, addr);
            assert(pre.overlay_branch_entries_at(j).contains_key(addr));
            ConcreteBranch::State::overlay_entry_matches_available(pre, j, addr);
            assert(post.overlay_branch_entries_at(j)[addr] == post.available_branch_nodes()[addr]);
            assert(pre.overlay_branch_entries_at(j)[addr] == pre.available_branch_nodes()[addr]);
            assert(pre.overlay_branch_entries_at(j)[addr] == branch.disk_view.entries[addr]);
            assert(sealed.disk_view.entries[addr] == branch.disk_view.entries[addr]);
        }
    };
    assert_maps_equal!(post.overlay_branch_entries_at(j), sealed.disk_view.entries);
    assert(post.cached_branches[j as int].root == Some(root));
    assert(post.overlay_branch_at(j) == Some(sealed));
    assert(post.branch_stack_i_at(j).branch == Some(sealed));
    linked_seal_preserves_buffer(branch, aux, summary);
    assert(AllocationBranchStack::branch_sparse_map(post.branch_stack_i_at(j))
        == AllocationBranchStack::branch_sparse_map(pre.branch_stack_i_at(j)));
    assert(AllocationBranchStack::branch_sparse_map(pre.branch_stack_i_at(j))
        == AllocationBranchStack::branch_sparse_map(pre.i().active_branch()));
}

proof fn receipt_reads_agree_with_branch_disk_at(
    pre: ConcreteBranch::State,
    new_cache: Cache::State,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    branch_idx: nat,
    branch: LinkedBranch<Summary>,
    receipt: LoadedPathReceipt,
)
    requires
        pre.wf(),
        branch_idx < pre.cached_branches.len(),
        Cache::State::next(pre.cache, new_cache, Cache::Label::Access{reads, writes}),
        branch.wf(),
        branch.disk_view.entries == pre.overlay_branch_entries_at(branch_idx),
        receipt.valid_for(branch.root, to_branch_nodes(reads)),
    ensures
        receipt.needed_addrs() <= branch.disk_view.entries.dom(),
        forall |addr: Address|
            #[trigger] receipt.needed_addrs().contains(addr)
            ==> to_branch_nodes(reads)[addr] == branch.disk_view.entries[addr],
    decreases receipt.depth(),
{
    let read_nodes = to_branch_nodes(reads);
    assert(receipt.needed_addrs().contains(branch.root)) by {
        assert(receipt.lines[0].addr == branch.root);
    };
    branch_read_agrees_with_overlay_at(pre, new_cache, reads, writes, branch_idx, branch.root);
    assert(read_nodes[branch.root] == branch.disk_view.entries[branch.root]);
    if receipt.depth() == 0 {
        assert(receipt.lines.len() == 1);
        assert(receipt.needed_addrs() == set!{branch.root}) by {
            assert forall |addr: Address| #[trigger] receipt.needed_addrs().contains(addr) implies set!{branch.root}.contains(addr) by {
                let i = choose |i: int| 0 <= i < receipt.lines.len() && #[trigger] receipt.lines[i].addr == addr;
                assert(i == 0);
            };
            assert forall |addr: Address| #[trigger] set!{branch.root}.contains(addr) implies receipt.needed_addrs().contains(addr) by {
                assert(receipt.lines[0].addr == branch.root);
            };
        };
        assert forall |addr: Address|
            #[trigger] receipt.needed_addrs().contains(addr)
            implies read_nodes[addr] == branch.disk_view.entries[addr]
        by {
                assert(addr == branch.root);
        };
        assert(receipt.needed_addrs() <= branch.disk_view.entries.dom()) by {
            assert(branch.disk_view.entries.contains_key(branch.root));
            assert forall |addr: Address|
                #[trigger] receipt.needed_addrs().contains(addr)
                implies branch.disk_view.entries.dom().contains(addr)
            by {
                assert(addr == branch.root);
            };
        };
    } else {
        let child_receipt = receipt.tail();
        crate::implementation::CachedBranch_v::receipt_valid_implies_tail_valid(receipt, read_nodes);
        let node = read_nodes[branch.root];
        assert(node == branch.root());
        assert(node is Index);
        assert(receipt.lines[0].wf());
        assert(node.keys_strictly_sorted());
        let child_idx = node.route(receipt.key) + 1;
        Key::strictly_sorted_implies_sorted(node->pivots);
        Key::largest_lte_ensures(node->pivots, receipt.key, node.route(receipt.key));
        assert(branch.root().valid_child_index(child_idx));
        let child_branch = branch.child_at_idx(child_idx);
        let child_addr = crate::implementation::CachedBranch_v::loaded_child_addr(branch.root, read_nodes, receipt.key);
        assert(child_addr == child_receipt.root);
        assert(child_branch.disk_view.entries == pre.overlay_branch_entries_at(branch_idx));
        receipt_reads_agree_with_branch_disk_at(
            pre,
            new_cache,
            reads,
            writes,
            branch_idx,
            child_branch,
            child_receipt,
        );
        assert forall |addr: Address|
            #[trigger] receipt.needed_addrs().contains(addr)
            implies read_nodes[addr] == branch.disk_view.entries[addr]
        by {
            if addr != branch.root {
                assert(child_receipt.needed_addrs().contains(addr)) by {
                    let i = choose |i: int| 0 <= i < receipt.lines.len() && #[trigger] receipt.lines[i].addr == addr;
                    assert(i > 0);
                    assert(child_receipt.lines[i - 1] == receipt.lines[i]);
                };
                assert(read_nodes[addr] == child_branch.disk_view.entries[addr]);
                assert(child_branch.disk_view.entries[addr] == branch.disk_view.entries[addr]);
            }
        };
        assert(receipt.needed_addrs() <= branch.disk_view.entries.dom()) by {
            assert(branch.disk_view.entries.contains_key(branch.root));
            assert forall |addr: Address|
                #[trigger] receipt.needed_addrs().contains(addr)
                implies branch.disk_view.entries.dom().contains(addr)
            by {
                if addr != branch.root {
                    assert(child_receipt.needed_addrs().contains(addr)) by {
                        let i = choose |i: int| 0 <= i < receipt.lines.len() && #[trigger] receipt.lines[i].addr == addr;
                        assert(i > 0);
                        assert(child_receipt.lines[i - 1] == receipt.lines[i]);
                    };
                    assert(child_branch.disk_view.entries.dom().contains(addr));
                    assert(child_branch.disk_view.entries == branch.disk_view.entries);
                }
            };
        };
    }
}

proof fn receipt_query_matches_branch_sparse_buffer_at(
    pre: ConcreteBranch::State,
    reads: Map<Address, RawPage>,
    branch_idx: nat,
    branch: LinkedBranch<Summary>,
    receipt: LoadedPathReceipt,
)
    requires
        pre.refinement_wf(),
        branch_idx < pre.cached_branches.len(),
        pre.overlay_branch_at(branch_idx) is Some,
        branch == pre.overlay_branch_at(branch_idx).unwrap(),
        Cache::State::next(pre.cache, pre.cache, Cache::Label::Access{reads, writes: Map::<Address, RawPage>::empty()}),
        receipt.valid_for(branch.root, to_branch_nodes(reads)),
        receipt.target_is_leaf(),
        receipt.needed_addrs() <= reads.dom(),
    ensures
        AllocationBranchStack::branch_sparse_buffer(pre.i().branches[branch_idx as int]).query(receipt.key) == receipt.result(),
{
    let read_nodes = to_branch_nodes(reads);
    let depth = receipt.depth();
    branch_stack_entry_matches_overlay(pre, branch_idx);
    assert(pre.i().branches[branch_idx as int] == pre.branch_stack_i_at(branch_idx));
    assert(pre.i().branches[branch_idx as int].branch == Some(branch));
    assert(pre.i().branches[branch_idx as int].inv());
    if pre.i().branches[branch_idx as int].sealed {
        assert(branch.valid_sealed_branch());
        assert(branch.inv());
    } else {
        assert(branch.inv());
    }
    assert(branch.wf()) by {
        assert(branch.inv());
    };
    crate::implementation::CachedBranch_v::receipt_valid_implies_loaded_path_at_depth(receipt, read_nodes);
    crate::implementation::CachedBranch_v::receipt_query_matches_loaded_query_result_at_depth(receipt, read_nodes);
    receipt_reads_agree_with_branch_disk_at(
        pre,
        pre.cache,
        reads,
        Map::<Address, RawPage>::empty(),
        branch_idx,
        branch,
        receipt,
    );
    receipt_query_matches_branch_query(branch, read_nodes, receipt);
    crate::implementation::AllocationBranchStackRefinement_v::branch_sparse_query_refines(pre.i().branches[branch_idx as int], receipt.key);
}

proof fn receipt_index_matches_branch_target_at(
    pre: ConcreteBranch::State,
    new_cache: Cache::State,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    branch_idx: nat,
    branch: LinkedBranch<Summary>,
    receipt: LoadedPathReceipt,
)
    requires
        pre.refinement_wf(),
        branch_idx < pre.cached_branches.len(),
        pre.overlay_branch_at(branch_idx) is Some,
        branch == pre.overlay_branch_at(branch_idx).unwrap(),
        Cache::State::next(pre.cache, new_cache, Cache::Label::Access{reads, writes}),
        receipt.valid_for(branch.root, to_branch_nodes(reads)),
        receipt.target_is_index(),
        receipt.needed_addrs() <= reads.dom(),
    ensures
        (BranchPath{branch, key: receipt.key, depth: receipt.depth()}).valid(),
        (BranchPath{branch, key: receipt.key, depth: receipt.depth()}).target().disk_view == branch.disk_view,
        (BranchPath{branch, key: receipt.key, depth: receipt.depth()}).target().root == receipt.target_addr(),
        (BranchPath{branch, key: receipt.key, depth: receipt.depth()}).target().root() == receipt.target_node(),
{
    let read_nodes = to_branch_nodes(reads);
    let depth = receipt.depth();
    branch_stack_entry_matches_overlay(pre, branch_idx);
    assert(pre.i().branches[branch_idx as int] == pre.branch_stack_i_at(branch_idx));
    assert(pre.i().branches[branch_idx as int].branch == Some(branch));
    assert(pre.i().branches[branch_idx as int].inv());
    if pre.i().branches[branch_idx as int].sealed {
        assert(branch.valid_sealed_branch());
        assert(branch.inv());
    } else {
        assert(branch.inv());
    }
    assert(branch.wf()) by {
        assert(branch.inv());
    };
    crate::implementation::CachedBranch_v::receipt_valid_implies_loaded_index_path_at_depth(receipt, read_nodes);
    receipt_reads_agree_with_branch_disk_at(
        pre,
        new_cache,
        reads,
        writes,
        branch_idx,
        branch,
        receipt,
    );
    loaded_index_path_matches_branch_target_at_depth(branch, read_nodes, receipt.key, depth);
}

proof fn concrete_query_matches_stack_to_stack_query(
    pre: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    query_receipts: Seq<Option<crate::implementation::CachedBranch_v::LoadedPathReceipt>>,
)
    requires
        pre.refinement_wf(),
        lbl is Query,
        ConcreteBranch::State::query(pre, pre, lbl, reads, query_receipts),
    ensures
        pre.i().query(lbl->key) == lbl->msg,
{
    reveal(ConcreteBranch::State::query);
    let branch_idx = lbl->branch_idx;
    let key = lbl->key;
    let msg = lbl->msg;
    let read_nodes = crate::implementation::ConcreteBranch_v::to_branch_nodes(reads);

    if msg == (Message::Update{delta: nop_delta()}) {
        assert forall |j: int|
            0 <= j < pre.i().branches.len()
            implies #[trigger] AllocationBranchStack::branch_sparse_buffer(pre.i().branches[j]).query(key)
                == (Message::Update{delta: nop_delta()})
        by {
            if pre.cached_branches[j].root is Some {
                let branch = pre.overlay_branch_at(j as nat).unwrap();
                let receipt = query_receipts[j].unwrap();
                assert(pre.branch_query_returns_nop(j as nat, key, query_receipts[j], read_nodes));
                receipt_query_matches_branch_sparse_buffer_at(
                    pre,
                    reads,
                    j as nat,
                    branch,
                    receipt,
                );
            } else {
                assert(j == pre.active_idx()) by {
                    if j != pre.active_idx() {
                        assert(0 <= j < pre.cached_branches.len() - 1);
                        assert(pre.cached_branches[j].sealed) by {
                            assert(pre.refinement_wf());
                            assert(pre.wf());
                            assert forall |i: int|
                                0 <= i < pre.cached_branches.len() - 1
                                implies #[trigger] pre.cached_branches[i].sealed
                            by {
                                assert(pre.cached_branches[i].wf());
                                assert(pre.cached_branches[i].sealed);
                            };
                            assert(0 <= j < pre.cached_branches.len() - 1);
                        };
                        assert(pre.cached_branches[j].wf()) by {
                            assert(pre.refinement_wf());
                            assert(pre.wf());
                            assert forall |i: int|
                                0 <= i < pre.cached_branches.len() - 1
                                implies #[trigger] pre.cached_branches[i].wf()
                            by {
                                assert(pre.cached_branches[i].wf());
                            };
                            assert(0 <= j < pre.cached_branches.len() - 1);
                        };
                        assert(pre.cached_branches[j].root is Some);
                    }
                };
                assert(pre.i().branches[j] == pre.branch_stack_i_at(j as nat));
                assert(pre.i().branches[j].branch is None);
                assert(AllocationBranchStack::branch_sparse_buffer(pre.i().branches[j]).query(key)
                    == (Message::Update{delta: nop_delta()}));
            }
        };
        crate::implementation::AllocationBranchStackRefinement_v::query_up_to_all_nop(
            pre.i().branches,
            pre.i().branches.len() as nat,
            key,
        );
    } else {
        assert(pre.branch_query_matches(
            branch_idx,
            key,
            msg,
            query_receipts[branch_idx as int],
            read_nodes,
        ));
        if pre.cached_branches[branch_idx as int].root is Some {
            let branch = pre.overlay_branch_at(branch_idx).unwrap();
            let receipt = query_receipts[branch_idx as int].unwrap();
            receipt_query_matches_branch_sparse_buffer_at(
                pre,
                reads,
                branch_idx,
                branch,
                receipt,
            );
        } else {
            assert(false);
        }
        assert forall |j: int|
            branch_idx < j < pre.i().branches.len()
            implies #[trigger] AllocationBranchStack::branch_sparse_buffer(pre.i().branches[j]).query(key)
                == (Message::Update{delta: nop_delta()})
        by {
            if pre.cached_branches[j].root is Some {
                let branch = pre.overlay_branch_at(j as nat).unwrap();
                let receipt = query_receipts[j].unwrap();
                assert(pre.branch_query_returns_nop(j as nat, key, query_receipts[j], read_nodes));
                receipt_query_matches_branch_sparse_buffer_at(
                    pre,
                    reads,
                    j as nat,
                    branch,
                    receipt,
                );
            } else {
                assert(j == pre.active_idx()) by {
                    if j != pre.active_idx() {
                        assert(0 <= j < pre.cached_branches.len() - 1);
                        assert(pre.cached_branches[j].sealed) by {
                            assert(pre.wf());
                        };
                        assert(pre.cached_branches[j].wf()) by {
                            assert(pre.wf());
                        };
                        assert(pre.cached_branches[j].root is Some);
                    }
                };
                assert(pre.i().branches[j] == pre.branch_stack_i_at(j as nat));
                assert(pre.i().branches[j].branch is None);
                assert(AllocationBranchStack::branch_sparse_buffer(pre.i().branches[j]).query(key)
                    == (Message::Update{delta: nop_delta()}));
            }
        };
        crate::implementation::AllocationBranchStackRefinement_v::query_up_to_from_latest_hit(
            pre.i().branches,
            pre.i().branches.len() as nat,
            branch_idx,
            key,
            msg,
        );
    }
}

pub proof fn concrete_query_step_refines_to_abstract_map(
    pre: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    query_receipts: Seq<Option<crate::implementation::CachedBranch_v::LoadedPathReceipt>>,
)
    requires
        pre.refinement_wf(),
        lbl is Query,
        ConcreteBranch::State::query(pre, pre, lbl, reads, query_receipts),
    ensures
        AbstractMap::State::next(pre.abstract_map_i(), pre.abstract_map_i(), pre.label_to_abstract_map(lbl)),
{
    concrete_query_matches_stack_to_stack_query(pre, lbl, reads, query_receipts);
    query_step_refines_from_stack_query(pre, lbl);
}

pub proof fn concrete_fill_au_step_refines_to_abstract_map(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
)
    requires
        pre.refinement_wf(),
        post.refinement_wf(),
        lbl is FillAU,
        ConcreteBranch::State::fill_au(pre, post, lbl),
    ensures
        AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
{
    let pre_stack = pre.i();
    let post_stack = post.i();

    assert(post.seq_end == pre.seq_end);
    assert(post.cached_branches == pre.cached_branches);
    assert(post.cache == pre.cache);
    assert(post.disk == pre.disk);
    assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
    assert(post.active_idx() == pre.active_idx());
    assert forall |j: int|
        0 <= j < post_stack.branches.len()
        implies #[trigger] AllocationBranchStack::branch_sparse_map(post_stack.branches[j])
            == AllocationBranchStack::branch_sparse_map(pre_stack.branches[j])
    by {
        assert(post_stack.branches[j] == post.branch_stack_i_at(j as nat));
        assert(pre_stack.branches[j] == pre.branch_stack_i_at(j as nat));
        if j != pre.active_idx() {
            assert(j < pre.cached_branches.len() - 1) by {
                if !(j < pre.cached_branches.len() - 1) {
                    assert(j == pre.cached_branches.len() - 1);
                    assert(j == pre.active_idx());
                }
            };
            ConcreteBranch::State::overlay_at_ignores_mini_allocator(pre, post, j as nat);
            assert(post.overlay_branch_at(j as nat) == pre.overlay_branch_at(j as nat));
            assert(post.branch_stack_i_at(j as nat).branch == pre.branch_stack_i_at(j as nat).branch);
        } else if pre.cached_branches[j].root is Some {
            ConcreteBranch::State::overlay_at_ignores_mini_allocator(pre, post, j as nat);
            assert(post.overlay_branch_at(j as nat) == pre.overlay_branch_at(j as nat));
            assert(post.branch_stack_i_at(j as nat).branch == pre.branch_stack_i_at(j as nat).branch);
        } else {
            assert(j == pre.active_idx());
            assert(post.cached_branches[j].root is None);
            assert(post.branch_stack_i_at(j as nat).branch is None);
            assert(pre.branch_stack_i_at(j as nat).branch is None);
        }
    };
    crate::implementation::AllocationBranchStackRefinement_v::sparse_map_equal_from_pointwise_branch_sparse_map_equal(
        post_stack,
        pre_stack,
    );
    crate::implementation::AllocationBranchStackRefinement_v::kmmap_equal_from_sparse_map_equal(post_stack, pre_stack);
    assert(post_stack.kmmap_i() == pre_stack.kmmap_i());
    assert(post.abstract_map_i() == pre.abstract_map_i());
    internal_step_refines_from_same_abstract_map(pre, post, lbl);
}

proof fn branch_sparse_map_equal_from_equal_buffer(left: AllocationBranch, right: AllocationBranch)
    requires
        left.branch is Some,
        right.branch is Some,
        left.branch.unwrap().i().i().map == right.branch.unwrap().i().i().map,
    ensures
        AllocationBranchStack::branch_sparse_map(left) == AllocationBranchStack::branch_sparse_map(right),
{
    let left_raw = left.branch.unwrap().i().i().map;
    let right_raw = right.branch.unwrap().i().i().map;
    let left_sparse = AllocationBranchStack::branch_sparse_map(left);
    let right_sparse = AllocationBranchStack::branch_sparse_map(right);
    assert forall |k: Key| #[trigger] left_sparse.contains_key(k) <==> right_sparse.contains_key(k) by {
        assert(left_raw == right_raw);
        assert(left_sparse.contains_key(k) == (left_raw.contains_key(k) && !AllocationBranchStack::is_nop_message(left_raw[k])));
        assert(right_sparse.contains_key(k) == (right_raw.contains_key(k) && !AllocationBranchStack::is_nop_message(right_raw[k])));
    };
    assert forall |k: Key| #[trigger] left_sparse.contains_key(k) implies left_sparse[k] == right_sparse[k] by {
        assert(left_raw == right_raw);
        assert(left_sparse[k] == left_raw[k]);
        assert(right_sparse[k] == right_raw[k]);
    };
    assert_maps_equal!(left_sparse, right_sparse);
}

proof fn allocation_split_preserves_sparse_map(
    pre: AllocationBranch,
    new_child_addr: Address,
    path: BranchPath<Summary>,
    split_arg: SplitArg,
)
    requires
        pre.inv(),
        pre.can_split(new_child_addr, path, split_arg),
    ensures
        AllocationBranchStack::branch_sparse_map(pre.branch_split(new_child_addr, path, split_arg))
            == AllocationBranchStack::branch_sparse_map(pre),
{
    let pre_branch = pre.branch.unwrap();
    let post = pre.branch_split(new_child_addr, path, split_arg);
    let post_branch = post.branch.unwrap();
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
        pre_branch,
        ranking,
        post_ranking,
        new_child_addr,
        path,
        split_arg,
    );
    PivotBranchRefinement_v::lemma_path_target_is_wf(path_i);
    broadcast use crate::betree::LinkedBranch_v::Refinement_v::lemma_route_ensures;
    assert(path.target().root().valid_child_index(split_child_idx));
    assert(split_child_idx == path_i.target().route(pivot) + 1);
    assert(path_i.target()->children[split_child_idx] == split_child.i_internal(ranking));
    assert(split_arg.wf(split_child));
    assert(split_arg.i().wf(split_child.i_internal(ranking))) by {};
    assert(path_i.target().can_split_child_of_index(split_arg.i())) by {};
    PivotBranchRefinement_v::split_refines(pre_i, path_i, split_arg.i());
    assert(post_i == pre_i.split(path_i, split_arg.i()));
    assert(post_i.i() == pre_i.split(path_i, split_arg.i()).i());
    assert(pre_i.split(path_i, split_arg.i()).i() == pre_i.i());
    assert(pre_branch.i() == pre_i);
    assert(post_branch.i() == post_i);
    assert(post_branch.i().i() == pre_branch.i().i());
    branch_sparse_map_equal_from_equal_buffer(post, pre);
}

proof fn active_allocation_branch_can_split(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    new_cache: Cache::State,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Split,
        ConcreteBranch::State::split(pre, post, lbl, reads, writes, receipt, new_cache),
    ensures
        match lbl {
            ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg} => {
                let depth = receipt.depth();
                pre.i().active_branch().can_split(
                    new_child_addr,
                    BranchPath{branch: pre.overlay_branch().unwrap(), key: pivot, depth},
                    split_arg,
                )
            }
            _ => true,
        },
{
    reveal(ConcreteBranch::State::split);
    match lbl {
        ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg} => {
            let j = pre.active_idx() as nat;
            let branch = pre.overlay_branch().unwrap();
            let depth = receipt.depth();
            let needed = receipt.needed_addrs().insert(receipt.child_addr());
            let path = BranchPath{branch, key: pivot, depth};
            let read_nodes = to_branch_nodes(reads);
            let write_nodes = to_branch_nodes(writes);
            branch_stack_entry_matches_overlay(pre, j);
            assert(pre.i().active_branch() == pre.branch_stack_i_at(j));
            assert(pre.branch_stack_i_at(j).branch == Some(branch));
            assert(!pre.i().active_branch().sealed);
            assert(pre.i().active_branch().mini_allocator == pre.mini_allocator);
            assert(pre.active_cached_branch().root == Some(branch.root));

            assert(pre.active_cached_branch().can_split(
                pre.mini_allocator,
                new_child_addr,
                receipt,
                split_arg,
                read_nodes,
                write_nodes,
            ));
            assert(receipt.key == pivot);
            let child_addr = receipt.child_addr();
            let path_addrs = receipt.needed_addrs();
            assert(needed == path_addrs.insert(child_addr));
            assert(path_addrs <= reads.dom()) by {
                assert forall |addr: Address| #[trigger] path_addrs.contains(addr) implies reads.dom().contains(addr) by {
                    assert(needed.contains(addr));
                };
            };
            receipt_index_matches_branch_target_at(pre, new_cache, reads, writes, j, branch, receipt);
            crate::betree::LinkedBranch_v::Refinement_v::lemma_path_target(path, branch.the_ranking());
            assert(path.valid());
            assert(path.target().root() is Index);

            let child_idx = path.target().root().route(pivot) + 1;
            crate::betree::LinkedBranch_v::Refinement_v::lemma_route_ensures(path.target().root(), pivot);
            assert(path.target().root().valid_child_index(child_idx));
            assert(path.target().disk_view.wf()) by {
                assert(path.target().wf());
            };
            assert(path.target().disk_view.node_has_valid_child_address(path.target().root()));
            assert(path.target().child_at_idx(child_idx).root == child_addr);
            assert(path.target().child_at_idx(child_idx).disk_view == branch.disk_view);
            assert(path.target().child_at_idx(child_idx).has_root());

            assert(pre.overlay_branch_entries().contains_key(child_addr)) by {
                overlay_entries_match_branch_disk(pre, j, branch, child_addr);
            };
            branch_read_agrees_with_overlay_at(pre, new_cache, reads, writes, j, child_addr);
            assert(read_nodes[child_addr] == branch.disk_view.entries[child_addr]);
            assert(crate::implementation::CachedBranch_v::split_arg_matches_child(read_nodes[child_addr], split_arg));
            assert(path.target().child_at_idx(child_idx).root() == read_nodes[child_addr]);
            match split_arg {
                SplitArg::SplitLeaf{pivot} => {
                    assert(path.target().child_at_idx(child_idx).root() is Leaf);
                    assert(split_arg.wf(path.target().child_at_idx(child_idx)));
                }
                SplitArg::SplitIndex{pivot, pivot_index} => {
                    assert(path.target().child_at_idx(child_idx).root() is Index);
                    assert(split_arg.wf(path.target().child_at_idx(child_idx)));
                }
            }

            assert(!branch.disk_view.entries.contains_key(new_child_addr)) by {
                if branch.disk_view.entries.contains_key(new_child_addr) {
                    overlay_entries_match_branch_disk(pre, j, branch, new_child_addr);
                    ConcreteBranch::State::overlay_entry_matches_available(pre, j, new_child_addr);
                    assert(false);
                }
            };
            assert(path.target().child_at_idx(child_idx).disk_view.is_fresh(set!{new_child_addr}));

            assert(branch.can_split(new_child_addr, path, split_arg));
            assert(pre.i().active_branch().can_split(new_child_addr, path, split_arg));
        }
        _ => { assert(false); }
    }
}

proof fn active_allocation_split_post_inv(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    new_cache: Cache::State,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Split,
        ConcreteBranch::State::split(pre, post, lbl, reads, writes, receipt, new_cache),
    ensures
        match lbl {
            ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg} => {
                let depth = receipt.depth();
                let branch = pre.overlay_branch().unwrap();
                let path = BranchPath{branch, key: pivot, depth};
                let modeled_post = pre.i().active_branch().branch_split(new_child_addr, path, split_arg);
                &&& modeled_post.inv()
                &&& modeled_post.branch is Some
                &&& modeled_post.branch.unwrap().tight_disk_view()
            }
            _ => false,
        },
{
    match lbl {
        ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg} => {
            let branch = pre.overlay_branch().unwrap();
            let depth = receipt.depth();
            let path = BranchPath{branch, key: pivot, depth};
            let alloc_pre = pre.i().active_branch();
            let modeled_post = alloc_pre.branch_split(new_child_addr, path, split_arg);
            active_allocation_branch_can_split(pre, post, lbl, reads, writes, receipt, new_cache);
            assert(AllocationBranch::build_next(
                alloc_pre,
                modeled_post,
                crate::allocation_layer::AllocationBranch_v::BuildEvent::Split{
                    addr: new_child_addr,
                    path,
                    split_arg,
                },
                Set::<crate::disk::GenericDisk_v::AU>::empty(),
                Set::<crate::disk::GenericDisk_v::AU>::empty(),
            ));
            AllocationBranch::build_next_preserves_inv(
                alloc_pre,
                modeled_post,
                crate::allocation_layer::AllocationBranch_v::BuildEvent::Split{
                    addr: new_child_addr,
                    path,
                    split_arg,
                },
                Set::<crate::disk::GenericDisk_v::AU>::empty(),
                Set::<crate::disk::GenericDisk_v::AU>::empty(),
            );
        }
        _ => { assert(false); }
    }
}

proof fn grow_write_addr_in_active_allocator(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Grow,
        ConcreteBranch::State::grow(pre, post, lbl, reads, writes, new_cache),
        writes.contains_key(addr),
    ensures
        pre.mini_allocator.all_aus().contains(addr.au),
{
    reveal(ConcreteBranch::State::grow);
    let read_nodes = to_branch_nodes(reads);
    let write_nodes = to_branch_nodes(writes);
    let new_root_addr = lbl->new_root_addr;
    assert(pre.active_cached_branch().can_grow(pre.mini_allocator, new_root_addr, read_nodes, write_nodes));
    assert(write_nodes == crate::implementation::CachedBranch_v::loaded_grow_write_nodes(
        pre.active_cached_branch().root.unwrap(),
        new_root_addr,
    ));
    assert(write_nodes.contains_key(addr));
    assert(addr == new_root_addr);
    assert(pre.mini_allocator.can_allocate(addr));
    assert(pre.mini_allocator.all_aus().contains(addr.au));
}

proof fn grow_available_branch_nodes_domain(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Grow,
        ConcreteBranch::State::grow(pre, post, lbl, reads, writes, new_cache),
        post.disk == pre.disk,
    ensures
        post.available_branch_nodes().dom() == pre.available_branch_nodes().dom().insert(lbl->new_root_addr),
        post.available_branch_nodes().dom().len() == pre.available_branch_nodes().dom().len() + 1,
{
    reveal(ConcreteBranch::State::grow);
    let new_root = lbl->new_root_addr;
    let write_nodes = to_branch_nodes(writes);
    assert(write_nodes == crate::implementation::CachedBranch_v::loaded_grow_write_nodes(
        pre.active_cached_branch().root.unwrap(),
        new_root,
    ));
    assert(writes.dom() == set!{new_root});
    assert(!pre.available_branch_nodes().contains_key(new_root));
    written_addr_is_available_branch_node_after_access(pre, post, reads, writes, new_root);
    assert forall |addr: Address|
        #[trigger] post.available_branch_nodes().contains_key(addr)
            <==> pre.available_branch_nodes().dom().insert(new_root).contains(addr)
    by {
        if post.available_branch_nodes().contains_key(addr) {
            if addr == new_root {
            } else if writes.contains_key(addr) {
                assert(writes.dom().contains(addr));
                assert(addr == new_root);
            } else if pre.available_branch_nodes().contains_key(addr) {
            } else {
                unavailable_branch_node_stays_unavailable_at_unwritten_addr(pre, post, reads, writes, addr);
                assert(false);
            }
        }
        if pre.available_branch_nodes().dom().insert(new_root).contains(addr) {
            if addr == new_root {
                assert(post.available_branch_nodes().contains_key(addr));
            } else {
                assert(!writes.contains_key(addr));
                available_branch_node_unchanged_at_unwritten_addr(pre, post, reads, writes, addr);
            }
        }
    };
    assert(post.available_branch_nodes().dom() == pre.available_branch_nodes().dom().insert(new_root));
    vstd::set::axiom_set_insert_len(pre.available_branch_nodes().dom(), new_root);
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
        post.disk == pre.disk,
        Cache::State::next(pre.cache, post.cache, Cache::Label::Access{reads, writes}),
        writes.contains_key(fresh_addr),
        !pre.available_branch_nodes().contains_key(fresh_addr),
        forall |addr: Address|
            #[trigger] writes.contains_key(addr) && addr != fresh_addr
            ==> pre.available_branch_nodes().contains_key(addr),
    ensures
        post.available_branch_nodes().dom() == pre.available_branch_nodes().dom().insert(fresh_addr),
        forall |addr: Address| #[trigger] post.available_branch_nodes().contains_key(addr)
            ==> post.available_branch_nodes()[addr] == if writes.contains_key(addr) {
                to_branch_nodes(writes)[addr]
            } else {
                pre.available_branch_nodes()[addr]
            },
{
    assert forall |addr: Address|
        #[trigger] post.available_branch_nodes().contains_key(addr)
            <==> pre.available_branch_nodes().dom().insert(fresh_addr).contains(addr)
    by {
        if post.available_branch_nodes().contains_key(addr) {
            if writes.contains_key(addr) {
                if addr == fresh_addr {
                } else {
                    assert(pre.available_branch_nodes().contains_key(addr));
                }
            } else if pre.available_branch_nodes().contains_key(addr) {
            } else {
                unavailable_branch_node_stays_unavailable_at_unwritten_addr(pre, post, reads, writes, addr);
                assert(false);
            }
        }
        if pre.available_branch_nodes().dom().insert(fresh_addr).contains(addr) {
            if writes.contains_key(addr) {
                written_addr_is_available_branch_node_after_access(pre, post, reads, writes, addr);
                assert(post.available_branch_nodes().contains_key(addr));
            } else {
                assert(pre.available_branch_nodes().contains_key(addr));
                assert(!writes.contains_key(addr));
                available_branch_node_unchanged_at_unwritten_addr(pre, post, reads, writes, addr);
                assert(post.available_branch_nodes().contains_key(addr));
            }
        }
    };
    assert(post.available_branch_nodes().dom() == pre.available_branch_nodes().dom().insert(fresh_addr));

    assert forall |addr: Address| #[trigger] post.available_branch_nodes().contains_key(addr)
        implies post.available_branch_nodes()[addr] == if writes.contains_key(addr) {
            to_branch_nodes(writes)[addr]
        } else {
            pre.available_branch_nodes()[addr]
        }
    by {
        if writes.contains_key(addr) {
            written_addr_is_available_branch_node_after_access(pre, post, reads, writes, addr);
        } else {
            available_branch_node_unchanged_at_unwritten_addr(pre, post, reads, writes, addr);
        }
    };
}

proof fn split_nonfresh_write_addrs_are_pre_available(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    new_cache: Cache::State,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Split,
        ConcreteBranch::State::split(pre, post, lbl, reads, writes, receipt, new_cache),
    ensures
        forall |addr: Address|
            #[trigger] writes.contains_key(addr) && addr != lbl->new_child_addr
            ==> {
                &&& pre.available_branch_nodes().contains_key(addr)
                &&& pre.overlay_branch_entries().contains_key(addr)
            },
{
    reveal(ConcreteBranch::State::split);
    match lbl {
        ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg} => {
            let branch = pre.overlay_branch().unwrap();
            let depth = receipt.depth();
            let read_nodes = to_branch_nodes(reads);
            let write_nodes = to_branch_nodes(writes);
            let path = BranchPath{branch, key: pivot, depth};
            let root = branch.root;

            assert(pre.active_cached_branch().can_split(
                pre.mini_allocator,
                new_child_addr,
                receipt,
                split_arg,
                read_nodes,
                write_nodes,
            ));
            assert(receipt.key == pivot);
            assert(pre.active_cached_branch().root == Some(branch.root));
            let child_addr = receipt.child_addr();
            let path_addrs = receipt.needed_addrs();
            let needed = path_addrs.insert(child_addr);
            assert(needed == path_addrs.insert(child_addr));
            assert(path_addrs <= reads.dom()) by {
                assert forall |addr: Address| #[trigger] path_addrs.contains(addr) implies reads.dom().contains(addr) by {
                    assert(needed.contains(addr));
                };
            };
            receipt_index_matches_branch_target_at(
                pre,
                new_cache,
                reads,
                writes,
                pre.active_idx() as nat,
                branch,
                receipt,
            );
            assert(path.valid());
            crate::betree::LinkedBranch_v::Refinement_v::lemma_path_target(path, branch.the_ranking());

            assert(write_nodes == crate::implementation::CachedBranch_v::loaded_split_write_nodes(
                receipt,
                read_nodes,
                split_arg,
                new_child_addr,
            ));
            assert(path.target().root() is Index);
            assert forall |addr: Address|
                #[trigger] writes.contains_key(addr) && addr != new_child_addr
                implies {
                    &&& pre.available_branch_nodes().contains_key(addr)
                    &&& pre.overlay_branch_entries().contains_key(addr)
                }
            by {
                assert(write_nodes.contains_key(addr));
                assert(addr == path.target().root || addr == child_addr);
                if addr == path.target().root {
                    assert(path.target().disk_view == branch.disk_view);
                    assert(path.target().wf());
                    assert(path.target().disk_view.valid_address(path.target().root));
                    assert(branch.disk_view.entries.contains_key(addr));
                } else {
                    let child_idx = path.target().root().route(pivot) + 1;
                    crate::betree::LinkedBranch_v::Refinement_v::lemma_route_ensures(path.target().root(), pivot);
                    assert(path.target().wf());
                    assert(path.target().disk_view.wf());
                    assert(path.target().disk_view.node_has_valid_child_address(path.target().root()));
                    assert(path.target().root().valid_child_index(child_idx));
                    assert(path.target().child_at_idx(child_idx).root == child_addr);
                    assert(path.target().child_at_idx(child_idx).disk_view == branch.disk_view);
                    assert(path.target().child_at_idx(child_idx).disk_view.valid_address(child_addr));
                    assert(branch.disk_view.entries.contains_key(addr));
                }
                overlay_entries_match_branch_disk(pre, pre.active_idx() as nat, branch, addr);
                ConcreteBranch::State::overlay_entry_matches_available(pre, pre.active_idx() as nat, addr);
            };
        }
        _ => { assert(false); }
    }
}

proof fn split_available_branch_nodes_domain(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    new_cache: Cache::State,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Split,
        ConcreteBranch::State::split(pre, post, lbl, reads, writes, receipt, new_cache),
        post.disk == pre.disk,
    ensures
        post.available_branch_nodes().dom() == pre.available_branch_nodes().dom().insert(lbl->new_child_addr),
        forall |addr: Address| #[trigger] post.available_branch_nodes().contains_key(addr)
            ==> post.available_branch_nodes()[addr] == if writes.contains_key(addr) {
                to_branch_nodes(writes)[addr]
            } else {
                pre.available_branch_nodes()[addr]
            },
{
    split_nonfresh_write_addrs_are_pre_available(pre, post, lbl, reads, writes, receipt, new_cache);
    match lbl {
        ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg} => {
            let depth = receipt.depth();
            let read_nodes = to_branch_nodes(reads);
            let write_nodes = to_branch_nodes(writes);
            assert(pre.active_cached_branch().can_split(
                pre.mini_allocator,
                new_child_addr,
                receipt,
                split_arg,
                read_nodes,
                write_nodes,
            ));
            assert(write_nodes == crate::implementation::CachedBranch_v::loaded_split_write_nodes(
                receipt,
                read_nodes,
                split_arg,
                new_child_addr,
            ));
            assert(write_nodes.contains_key(new_child_addr));
            access_updates_available_branch_nodes_with_one_fresh_write_set(pre, post, reads, writes, new_child_addr);
        }
        _ => { assert(false); }
    }
}

proof fn active_split_written_entries_match_split_branch(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    new_cache: Cache::State,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Split,
        ConcreteBranch::State::split(pre, post, lbl, reads, writes, receipt, new_cache),
        post.disk == pre.disk,
    ensures
        match lbl {
            ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg} => {
                let depth = receipt.depth();
                let branch = pre.overlay_branch().unwrap();
                let path = BranchPath{branch, key: pivot, depth};
                let read_nodes = to_branch_nodes(reads);
                let write_nodes = to_branch_nodes(writes);
                let child_addr = receipt.child_addr();
                let split_branch = branch.split(new_child_addr, path, split_arg);
                &&& post.available_branch_nodes().contains_key(path.target().root)
                &&& post.available_branch_nodes()[path.target().root] == split_branch.disk_view.entries[path.target().root]
                &&& post.available_branch_nodes().contains_key(child_addr)
                &&& post.available_branch_nodes()[child_addr] == split_branch.disk_view.entries[child_addr]
                &&& post.available_branch_nodes().contains_key(new_child_addr)
                &&& post.available_branch_nodes()[new_child_addr] == split_branch.disk_view.entries[new_child_addr]
            }
            _ => true,
        },
{
    reveal(ConcreteBranch::State::split);
    match lbl {
        ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg} => {
            let j = pre.active_idx() as nat;
            let branch = pre.overlay_branch().unwrap();
            let depth = receipt.depth();
            let path = BranchPath{branch, key: pivot, depth};
            let read_nodes = to_branch_nodes(reads);
            let write_nodes = to_branch_nodes(writes);
            let child_addr = receipt.child_addr();
            let path_addrs = receipt.needed_addrs();
            let needed = path_addrs.insert(child_addr);
            let split_branch = branch.split(new_child_addr, path, split_arg);

            assert(pre.active_cached_branch().can_split(
                pre.mini_allocator,
                new_child_addr,
                receipt,
                split_arg,
                read_nodes,
                write_nodes,
            ));
            assert(needed == path_addrs.insert(child_addr));
            assert(path_addrs <= reads.dom()) by {
                assert forall |addr: Address| #[trigger] path_addrs.contains(addr) implies reads.dom().contains(addr) by {
                    assert(needed.contains(addr));
                };
            };
            receipt_index_matches_branch_target_at(pre, new_cache, reads, writes, j, branch, receipt);
            assert(path.valid());
            assert(write_nodes == crate::implementation::CachedBranch_v::loaded_split_write_nodes(
                receipt,
                read_nodes,
                split_arg,
                new_child_addr,
            ));
            assert(write_nodes.contains_key(path.target().root));
            assert(write_nodes.contains_key(child_addr));
            assert(write_nodes.contains_key(new_child_addr));
            assert(write_nodes.contains_key(path.target().root) <==> writes.contains_key(path.target().root));
            assert(write_nodes.contains_key(child_addr) <==> writes.contains_key(child_addr));
            assert(write_nodes.contains_key(new_child_addr) <==> writes.contains_key(new_child_addr));

            split_available_branch_nodes_domain(pre, post, lbl, reads, writes, receipt, new_cache);
            written_addr_is_available_branch_node_after_access(pre, post, reads, writes, path.target().root);
            written_addr_is_available_branch_node_after_access(pre, post, reads, writes, child_addr);
            written_addr_is_available_branch_node_after_access(pre, post, reads, writes, new_child_addr);

            active_allocation_branch_can_split(pre, post, lbl, reads, writes, receipt, new_cache);
            LinkedBranchRefinement_v::split_refines(branch, new_child_addr, path, split_arg);
            let target = path.target();
            let split_child_idx = target.root().route(pivot) + 1;
            let split_child = target.child_at_idx(split_child_idx);
            let split_target = target.split_child_of_index(split_arg, new_child_addr);
            let ranking = branch.the_ranking();
            LinkedBranchRefinement_v::lemma_path_target(path, ranking);
            broadcast use crate::betree::LinkedBranch_v::Refinement_v::lemma_route_ensures;
            assert(target.valid_ranking(ranking));
            assert(target.root().valid_child_index(split_child_idx));
            assert(target.disk_view == branch.disk_view);
            overlay_entries_match_branch_disk(pre, j, branch, child_addr);
            assert(reads.contains_key(child_addr));
            assert(to_branch_nodes(reads).contains_key(child_addr));
            branch_read_agrees_with_overlay_at(pre, new_cache, reads, writes, j, child_addr);
            assert(read_nodes[path.target().root] == target.root());
            assert(read_nodes[child_addr] == target.disk_view.entries[child_addr]);
            assert(target.disk_view.entries[child_addr] == split_child.root());
            assert(child_addr == split_child.root);
            assert(split_branch.disk_view == split_target.disk_view);
            assert(branch.can_split(new_child_addr, path, split_arg));
            assert(target.can_split_child_of_index(split_arg, new_child_addr));
            assert(branch.disk_view.is_fresh(set!{new_child_addr}));
            assert(!branch.disk_view.entries.contains_key(new_child_addr));
            assert(new_child_addr != target.root);
            assert(new_child_addr != child_addr);
            assert(target.disk_view.node_children_respects_rank(ranking, target.root));
            assert(ranking.contains_key(target.root()->children[split_child_idx]));
            assert(ranking[target.root()->children[split_child_idx]] < ranking[target.root]);
            assert(child_addr != target.root);

            let new_parent = AllocationBranchNode::Index{
                pivots: target.root()->pivots.insert(split_child_idx, pivot),
                children: target.root()->children.insert(split_child_idx + 1, new_child_addr),
                aux_ptr: None,
            };
            assert(write_nodes[path.target().root] == new_parent);
            assert(split_target.disk_view.entries[path.target().root] == new_parent);

            match split_arg {
                SplitArg::SplitLeaf{pivot} => {
                    let child = read_nodes[child_addr];
                    assert(child == split_child.root());
                    assert(child is Leaf);
                    let split_index = Key::largest_lt(child->keys, pivot) + 1;
                    let left_root = AllocationBranchNode::Leaf{
                        keys: child->keys.take(split_index),
                        msgs: child->msgs.take(split_index),
                    };
                    let right_root = AllocationBranchNode::Leaf{
                        keys: child->keys.skip(split_index),
                        msgs: child->msgs.skip(split_index),
                    };
                    assert(write_nodes[child_addr] == left_root);
                    assert(write_nodes[new_child_addr] == right_root);
                    assert(split_child.split_node(split_arg, new_child_addr)
                        == split_child.split_leaf(split_arg, new_child_addr));
                    let (left_branch, right_branch) = split_child.split_leaf(split_arg, new_child_addr);
                    assert(left_branch.root == child_addr);
                    assert(right_branch.root == new_child_addr);
                    assert(left_branch.disk_view.entries[child_addr] == left_root);
                    assert(left_branch.disk_view.entries[new_child_addr] == right_root);
                    assert(split_target.disk_view.entries[child_addr] == left_branch.disk_view.entries[child_addr]);
                    assert(split_target.disk_view.entries[new_child_addr] == left_branch.disk_view.entries[new_child_addr]);
                }
                SplitArg::SplitIndex{pivot, pivot_index} => {
                    let child = read_nodes[child_addr];
                    assert(child == split_child.root());
                    assert(child is Index);
                    let left_root = AllocationBranchNode::Index{
                        pivots: child->pivots.subrange(0, pivot_index),
                        children: child->children.subrange(0, pivot_index + 1),
                        aux_ptr: None,
                    };
                    let right_root = AllocationBranchNode::Index{
                        pivots: child->pivots.subrange(pivot_index + 1, child->pivots.len() as int),
                        children: child->children.subrange(pivot_index + 1, child->children.len() as int),
                        aux_ptr: None,
                    };
                    assert(write_nodes[child_addr] == left_root);
                    assert(write_nodes[new_child_addr] == right_root);
                    assert(split_child.split_node(split_arg, new_child_addr)
                        == split_child.split_index(split_arg, new_child_addr));
                    let (left_branch, right_branch) = split_child.split_index(split_arg, new_child_addr);
                    assert(left_branch.root == child_addr);
                    assert(right_branch.root == new_child_addr);
                    assert(left_branch.disk_view.entries[child_addr] == left_root);
                    assert(left_branch.disk_view.entries[new_child_addr] == right_root);
                    assert(split_target.disk_view.entries[child_addr] == left_branch.disk_view.entries[child_addr]);
                    assert(split_target.disk_view.entries[new_child_addr] == left_branch.disk_view.entries[new_child_addr]);
                }
            }

            assert(split_branch.disk_view.entries[path.target().root] == write_nodes[path.target().root]);
            assert(split_branch.disk_view.entries[child_addr] == write_nodes[child_addr]);
            assert(split_branch.disk_view.entries[new_child_addr] == write_nodes[new_child_addr]);

            assert(post.available_branch_nodes()[path.target().root] == write_nodes[path.target().root]);
            assert(post.available_branch_nodes()[child_addr] == write_nodes[child_addr]);
            assert(post.available_branch_nodes()[new_child_addr] == write_nodes[new_child_addr]);
        }
        _ => { assert(false); }
    }
}

proof fn split_write_addr_in_active_allocator(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    new_cache: Cache::State,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Split,
        ConcreteBranch::State::split(pre, post, lbl, reads, writes, receipt, new_cache),
        writes.contains_key(addr),
    ensures
        pre.mini_allocator.all_aus().contains(addr.au),
{
    reveal(ConcreteBranch::State::split);
    match lbl {
        ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg} => {
            let read_nodes = to_branch_nodes(reads);
            let write_nodes = to_branch_nodes(writes);
            let depth = receipt.depth();
            let needed = receipt.needed_addrs().insert(receipt.child_addr());
            assert(pre.active_cached_branch().can_split(
                pre.mini_allocator,
                new_child_addr,
                receipt,
                split_arg,
                read_nodes,
                write_nodes,
            ));
            if addr == new_child_addr {
                assert(pre.mini_allocator.can_allocate(addr));
                assert(pre.mini_allocator.all_aus().contains(addr.au));
            } else {
                split_nonfresh_write_addrs_are_pre_available(pre, post, lbl, reads, writes, receipt, new_cache);
                assert(pre.overlay_branch_entries().contains_key(addr));
                assert(pre.active_branch_pages_in_allocator());
                assert(pre.mini_allocator.all_aus().contains(addr.au));
            }
        }
        _ => { assert(false); }
    }
}

proof fn active_available_entries_match_split_branch(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    new_cache: Cache::State,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Split,
        ConcreteBranch::State::split(pre, post, lbl, reads, writes, receipt, new_cache),
        post.disk == pre.disk,
        match lbl {
            ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg} => {
                let depth = receipt.depth();
                let branch = pre.overlay_branch().unwrap();
                let path = BranchPath{branch, key: pivot, depth};
                let split_branch = branch.split(new_child_addr, path, split_arg);
                split_branch.disk_view.entries.contains_key(addr)
            }
            _ => false,
        },
    ensures
        match lbl {
            ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg} => {
                let depth = receipt.depth();
                let branch = pre.overlay_branch().unwrap();
                let path = BranchPath{branch, key: pivot, depth};
                let split_branch = branch.split(new_child_addr, path, split_arg);
                &&& post.available_branch_nodes().contains_key(addr)
                &&& post.available_branch_nodes()[addr] == split_branch.disk_view.entries[addr]
            }
            _ => false,
        },
{
    reveal(ConcreteBranch::State::split);
    match lbl {
        ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg} => {
            let j = pre.active_idx() as nat;
            let branch = pre.overlay_branch().unwrap();
            let depth = receipt.depth();
            let path = BranchPath{branch, key: pivot, depth};
            let read_nodes = to_branch_nodes(reads);
            let write_nodes = to_branch_nodes(writes);
            let split_branch = branch.split(new_child_addr, path, split_arg);

            assert(pre.active_cached_branch().can_split(
                pre.mini_allocator,
                new_child_addr,
                receipt,
                split_arg,
                read_nodes,
                write_nodes,
            ));
            assert(receipt.key == pivot);
            let child_addr = receipt.child_addr();
            let except = set!{path.target().root, child_addr, new_child_addr};
            assert(write_nodes == crate::implementation::CachedBranch_v::loaded_split_write_nodes(
                receipt,
                read_nodes,
                split_arg,
                new_child_addr,
            ));
            let path_addrs = receipt.needed_addrs();
            let needed = path_addrs.insert(child_addr);
            assert(needed == path_addrs.insert(child_addr));
            assert(path_addrs <= reads.dom()) by {
                assert forall |a: Address| #[trigger] path_addrs.contains(a) implies reads.dom().contains(a) by {
                    assert(needed.contains(a));
                };
            };
            receipt_index_matches_branch_target_at(pre, new_cache, reads, writes, j, branch, receipt);
            active_allocation_branch_can_split(pre, post, lbl, reads, writes, receipt, new_cache);
            LinkedBranchRefinement_v::split_refines(branch, new_child_addr, path, split_arg);
            if except.contains(addr) {
                active_split_written_entries_match_split_branch(pre, post, lbl, reads, writes, receipt, new_cache);
            } else {
                assert(split_branch.disk_view.entries.contains_key(addr));
                assert(split_branch.disk_view.entries.remove_keys(except).contains_key(addr));
                assert(branch.disk_view.entries.remove_keys(except) == split_branch.disk_view.entries.remove_keys(except));
                assert(branch.disk_view.entries.remove_keys(except).contains_key(addr));
                assert(branch.disk_view.entries.contains_key(addr));
                overlay_entries_match_branch_disk(pre, j, branch, addr);
                ConcreteBranch::State::overlay_entry_matches_available(pre, j, addr);
                assert(!write_nodes.contains_key(addr));
                assert(!writes.contains_key(addr)) by {
                    if writes.contains_key(addr) {
                        assert(write_nodes.contains_key(addr));
                        assert(false);
                    }
                };
                available_branch_node_unchanged_at_unwritten_addr(pre, post, reads, writes, addr);
                assert(split_branch.disk_view.entries[addr] == branch.disk_view.entries[addr]);
            }
        }
        _ => { assert(false); }
    }
}

proof fn active_post_overlay_entry_in_split_branch(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    new_cache: Cache::State,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Split,
        ConcreteBranch::State::split(pre, post, lbl, reads, writes, receipt, new_cache),
        post.disk == pre.disk,
        post.overlay_branch_entries_at(pre.active_idx() as nat).contains_key(addr),
    ensures
        match lbl {
            ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg} => {
                let j = pre.active_idx() as nat;
                let depth = receipt.depth();
                let branch = pre.overlay_branch().unwrap();
                let path = BranchPath{branch, key: pivot, depth};
                let split_branch = branch.split(new_child_addr, path, split_arg);
                &&& split_branch.disk_view.entries.contains_key(addr)
                &&& post.overlay_branch_entries_at(j)[addr] == split_branch.disk_view.entries[addr]
            }
            _ => false,
        },
{
    match lbl {
        ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg} => {
            let j = pre.active_idx() as nat;
            let branch = pre.overlay_branch().unwrap();
            let depth = receipt.depth();
            let path = BranchPath{branch, key: pivot, depth};
            let read_nodes = to_branch_nodes(reads);
            let split_branch = branch.split(new_child_addr, path, split_arg);
            assert(post.cached_branches[j as int].root == Some(split_branch.root));
            assert(pre.active_cached_branch().can_split(
                pre.mini_allocator,
                new_child_addr,
                receipt,
                split_arg,
                read_nodes,
                to_branch_nodes(writes),
            ));
            assert(receipt.key == pivot);
            let child_addr = receipt.child_addr();
            let path_addrs = receipt.needed_addrs();
            let needed = path_addrs.insert(child_addr);
            assert(needed == path_addrs.insert(child_addr));
            assert(path_addrs <= reads.dom()) by {
                assert forall |a: Address| #[trigger] path_addrs.contains(a) implies reads.dom().contains(a) by {
                    assert(needed.contains(a));
                };
            };
            receipt_index_matches_branch_target_at(pre, new_cache, reads, writes, j, branch, receipt);
            active_allocation_branch_can_split(pre, post, lbl, reads, writes, receipt, new_cache);
            LinkedBranchRefinement_v::split_refines(branch, new_child_addr, path, split_arg);
            ConcreteBranch::State::overlay_entry_matches_available(post, j, addr);
            assert(post.reachable_branch_addrs_from_with_fuel_contains(
                j,
                split_branch.root,
                post.available_branch_nodes().dom().len(),
                addr,
            ));
            assert forall |a: Address| #[trigger] split_branch.disk_view.entries.contains_key(a) implies {
                &&& post.available_branch_nodes().contains_key(a)
                &&& post.available_branch_nodes()[a] == split_branch.disk_view.entries[a]
            } by {
                active_available_entries_match_split_branch(pre, post, lbl, reads, writes, receipt, new_cache, a);
            };
            concrete_reachable_implies_in_agreeing_branch_disk_view(
                post,
                j,
                split_branch,
                split_branch.root,
                post.available_branch_nodes().dom().len(),
                addr,
            );
            active_available_entries_match_split_branch(pre, post, lbl, reads, writes, receipt, new_cache, addr);
            assert(post.overlay_branch_entries_at(j)[addr] == post.available_branch_nodes()[addr]);
        }
        _ => { assert(false); }
    }
}

proof fn active_sparse_map_preserved_under_split(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    new_cache: Cache::State,
)
    requires
        pre.refinement_wf(),
        post.refinement_wf(),
        lbl is Split,
        ConcreteBranch::State::split(pre, post, lbl, reads, writes, receipt, new_cache),
        post.disk == pre.disk,
    ensures
        AllocationBranchStack::branch_sparse_map(post.branch_stack_i_at(pre.active_idx() as nat))
            == AllocationBranchStack::branch_sparse_map(pre.i().active_branch()),
{
    match lbl {
        ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg} => {
            let j = pre.active_idx() as nat;
            let branch = pre.overlay_branch().unwrap();
            let depth = receipt.depth();
            let path = BranchPath{branch, key: pivot, depth};
            let split_branch = branch.split(new_child_addr, path, split_arg);
            let post_active = post.branch_stack_i_at(j);
            let modeled_post = pre.i().active_branch().branch_split(new_child_addr, path, split_arg);

            branch_stack_entry_matches_overlay(pre, j);
            branch_stack_entry_matches_overlay(post, j);
            assert(pre.i().active_branch() == pre.branch_stack_i_at(j));
            assert(post.i().active_branch() == post.branch_stack_i_at(j));
            assert(pre.branch_stack_i_at(j).branch == Some(branch));
            assert(modeled_post.branch == Some(split_branch));
            assert(post_active.branch is Some);
            assert(post_active.branch.unwrap() == post.overlay_branch_at(j).unwrap());
            assert(post.overlay_branch_at(j) is Some);
            assert(post.overlay_branch_at(j).unwrap().root == split_branch.root);
            assert(post_active.inv()) by {
                assert(post.i().wf());
            };
            active_allocation_split_post_inv(pre, post, lbl, reads, writes, receipt, new_cache);
            assert(modeled_post.inv());
            assert(modeled_post.branch is Some);

            assert forall |addr: Address|
                #[trigger] post_active.branch.unwrap().disk_view.entries.contains_key(addr)
                    implies split_branch.disk_view.entries.contains_key(addr)
                        && post_active.branch.unwrap().disk_view.entries[addr] == split_branch.disk_view.entries[addr]
            by {
                active_post_overlay_entry_in_split_branch(pre, post, lbl, reads, writes, receipt, new_cache, addr);
                assert(post.overlay_branch_entries_at(j).contains_key(addr));
                assert(post_active.branch.unwrap().disk_view.entries == post.overlay_branch_entries_at(j));
            };
            assert(post_active.branch.unwrap().disk_view.entries <= split_branch.disk_view.entries);
            assert(post_active.branch.unwrap().disk_view.is_sub_disk(split_branch.disk_view));

            post_active.branch.unwrap().subdisk_same_i_internal(
                post_active.branch.unwrap().the_ranking(),
                split_branch,
                split_branch.the_ranking(),
            );
            assert(post_active.branch.unwrap().i() == split_branch.i());
            assert(post_active.branch.unwrap().i().i() == split_branch.i().i());

            active_allocation_branch_can_split(pre, post, lbl, reads, writes, receipt, new_cache);
            allocation_split_preserves_sparse_map(pre.i().active_branch(), new_child_addr, path, split_arg);
            branch_sparse_map_equal_from_equal_buffer(post_active, modeled_post);
            assert(AllocationBranchStack::branch_sparse_map(modeled_post)
                == AllocationBranchStack::branch_sparse_map(pre.i().active_branch()));
        }
        _ => { assert(false); }
    }
}

proof fn historical_split_writes_skip_branch_entry(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    new_cache: Cache::State,
    j: nat,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Split,
        ConcreteBranch::State::split(pre, post, lbl, reads, writes, receipt, new_cache),
        j < pre.active_idx(),
        pre.i().branches[j as int].branch is Some,
        pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(addr),
    ensures
        !writes.contains_key(addr),
{
    let hist = pre.i().branches[j as int];
    let branch = hist.branch.unwrap();
    assert(hist.inv());
    assert(hist.sealed);
    assert(branch.tight_disk_view_with_summary());
    assert(branch.valid_sealed_branch());
    assert(branch.inv());
    assert(branch.disk_view.valid_address(branch.root));
    assert(branch.get_summary() == hist.mini_allocator.all_aus());
    assert(branch.get_summary().contains(addr.au));
    assert(pre.sealed_branch_disjoint_from_active_allocator_at(j));
    assert(branch.get_summary().disjoint(pre.mini_allocator.all_aus()));
    if writes.contains_key(addr) {
        split_write_addr_in_active_allocator(pre, post, lbl, reads, writes, receipt, new_cache, addr);
        assert(pre.mini_allocator.all_aus().contains(addr.au));
        assert(false);
    }
}

proof fn historical_branch_entry_unchanged_under_split(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    new_cache: Cache::State,
    j: nat,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Split,
        ConcreteBranch::State::split(pre, post, lbl, reads, writes, receipt, new_cache),
        post.disk == pre.disk,
        j < pre.active_idx(),
        pre.i().branches[j as int].branch is Some,
        pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(addr),
    ensures
        post.available_branch_nodes().contains_key(addr),
        post.available_branch_nodes()[addr] == pre.i().branches[j as int].branch.unwrap().disk_view.entries[addr],
{
    let branch = pre.i().branches[j as int].branch.unwrap();
    historical_split_writes_skip_branch_entry(pre, post, lbl, reads, writes, receipt, new_cache, j, addr);
    branch_stack_entry_matches_overlay(pre, j);
    assert(pre.branch_stack_i_at(j).branch == Some(branch));
    assert(pre.overlay_branch_at(j) == Some(branch));
    assert(pre.overlay_branch_entries_at(j) == branch.disk_view.entries);
    ConcreteBranch::State::overlay_entry_matches_available(pre, j, addr);
    available_branch_node_unchanged_at_unwritten_addr(pre, post, reads, writes, addr);
}

proof fn historical_reachable_contains_unchanged_under_split(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    new_cache: Cache::State,
    j: nat,
    current_addr: Address,
    fuel: nat,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Split,
        ConcreteBranch::State::split(pre, post, lbl, reads, writes, receipt, new_cache),
        post.disk == pre.disk,
        j < pre.active_idx(),
        pre.i().branches[j as int].branch is Some,
        pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(current_addr),
    ensures
        pre.reachable_branch_addrs_from_with_fuel_contains(j, current_addr, fuel, addr)
            == post.reachable_branch_addrs_from_with_fuel_contains(j, current_addr, fuel, addr),
        pre.reachable_branch_addrs_from_with_fuel_contains(j, current_addr, fuel, addr)
            ==> pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(addr),
        post.reachable_branch_addrs_from_with_fuel_contains(j, current_addr, fuel, addr)
            ==> pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(addr),
    decreases fuel,
{
    reveal(ConcreteBranch::State::split);
    let branch = pre.i().branches[j as int].branch.unwrap();
    let hist = pre.i().branches[j as int];
    branch_stack_entry_matches_overlay(pre, j);
    assert(pre.overlay_branch_at(j) == Some(branch));
    assert(pre.overlay_branch_entries_at(j) == branch.disk_view.entries);

    if fuel == 0 {
    } else {
        historical_branch_entry_unchanged_under_split(pre, post, lbl, reads, writes, receipt, new_cache, j, current_addr);
        ConcreteBranch::State::overlay_entry_matches_available(pre, j, current_addr);
        assert(pre.available_branch_nodes()[current_addr] == branch.disk_view.entries[current_addr]);
        assert(post.available_branch_nodes()[current_addr] == branch.disk_view.entries[current_addr]);
        let node = branch.disk_view.entries[current_addr];

        assert(post.cached_branches[j as int] == pre.cached_branches[j as int]);
        assert(pre.follow_aux_ptr_at(j, current_addr, node) == post.follow_aux_ptr_at(j, current_addr, node));

        if node is Leaf || node is Auxiliary {
            assert(pre.reachable_branch_addrs_from_with_fuel_contains(j, current_addr, fuel, addr) == (addr == current_addr));
            assert(post.reachable_branch_addrs_from_with_fuel_contains(j, current_addr, fuel, addr) == (addr == current_addr));
        } else {
            assert(hist.inv());
            assert(hist.sealed);
            assert(branch.valid_sealed_branch());
            assert(branch.inv());
            assert(branch.disk_view.no_dangling_address());
            assert(branch.disk_view.node_has_valid_child_address(node));

            if pre.follow_aux_ptr_at(j, current_addr, node) {
                assert(current_addr == branch.root);
                assert(node->aux_ptr is Some);
                assert(branch.disk_view.valid_address(node->aux_ptr.unwrap()));
                historical_reachable_contains_unchanged_under_split(
                    pre,
                    post,
                    lbl,
                    reads,
                    writes,
                    receipt,
                    new_cache,
                    j,
                    node->aux_ptr.unwrap(),
                    (fuel - 1) as nat,
                    addr,
                );
            }

            assert forall |i: int|
                0 <= i < node->children.len()
                implies pre.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, addr)
                    == post.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, addr)
                && (pre.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, addr)
                    ==> branch.disk_view.entries.contains_key(addr))
                && (post.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, addr)
                    ==> branch.disk_view.entries.contains_key(addr))
            by {
                assert(branch.disk_view.valid_address(node->children[i]));
                historical_reachable_contains_unchanged_under_split(
                    pre,
                    post,
                    lbl,
                    reads,
                    writes,
                    receipt,
                    new_cache,
                    j,
                    node->children[i],
                    (fuel - 1) as nat,
                    addr,
                );
            };
        }
    }
}

proof fn historical_post_overlay_entry_in_pre_branch_under_split(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    new_cache: Cache::State,
    j: nat,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Split,
        ConcreteBranch::State::split(pre, post, lbl, reads, writes, receipt, new_cache),
        post.disk == pre.disk,
        j < pre.active_idx(),
        pre.i().branches[j as int].branch is Some,
        post.overlay_branch_entries_at(j).contains_key(addr),
    ensures
        pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(addr),
        post.overlay_branch_entries_at(j)[addr] == pre.i().branches[j as int].branch.unwrap().disk_view.entries[addr],
{
    let branch = pre.i().branches[j as int].branch.unwrap();
    branch_stack_entry_matches_overlay(pre, j);
    assert(pre.i().branches[j as int] == pre.branch_stack_i_at(j));
    assert(pre.i().branches[j as int].inv());
    assert(pre.i().branches[j as int].sealed);
    assert(pre.branch_stack_i_at(j).branch is Some);
    assert(pre.branch_stack_i_at(j).branch.unwrap() == branch);
    assert(branch.valid_sealed_branch());
    assert(branch.inv());
    assert(pre.overlay_branch_at(j) is Some);
    assert(pre.overlay_branch_at(j).unwrap() == branch);
    assert(pre.overlay_branch_entries_at(j) == branch.disk_view.entries);
    assert(branch.disk_view.entries.contains_key(branch.root));
    assert(post.cached_branches[j as int].root == pre.cached_branches[j as int].root);
    assert(post.cached_branches[j as int].sealed == pre.cached_branches[j as int].sealed);
    assert(post.overlay_branch_entries_at(j).contains_key(addr));
    ConcreteBranch::State::overlay_entry_matches_available(post, j, addr);
    historical_reachable_contains_unchanged_under_split(
        pre,
        post,
        lbl,
        reads,
        writes,
        receipt,
        new_cache,
        j,
        branch.root,
        post.available_branch_nodes().dom().len(),
        addr,
    );
    assert(post.reachable_branch_addrs_from_with_fuel_contains(j, branch.root, post.available_branch_nodes().dom().len(), addr));
    assert(branch.disk_view.entries.contains_key(addr));
    historical_branch_entry_unchanged_under_split(pre, post, lbl, reads, writes, receipt, new_cache, j, addr);
    ConcreteBranch::State::overlay_entry_matches_available(post, j, addr);
}

proof fn historical_pre_branch_entry_in_post_overlay_under_split(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    new_cache: Cache::State,
    j: nat,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Split,
        ConcreteBranch::State::split(pre, post, lbl, reads, writes, receipt, new_cache),
        post.disk == pre.disk,
        j < pre.active_idx(),
        pre.i().branches[j as int].branch is Some,
        pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(addr),
    ensures
        post.overlay_branch_entries_at(j).contains_key(addr),
        post.overlay_branch_entries_at(j)[addr] == pre.i().branches[j as int].branch.unwrap().disk_view.entries[addr],
{
    let branch = pre.i().branches[j as int].branch.unwrap();
    branch_stack_entry_matches_overlay(pre, j);
    assert(pre.i().branches[j as int].inv());
    assert(pre.i().branches[j as int].sealed);
    assert(branch.valid_sealed_branch());
    assert(branch.inv());
    assert(pre.overlay_branch_at(j) == Some(branch));
    assert(pre.overlay_branch_entries_at(j) == branch.disk_view.entries);
    assert(branch.disk_view.entries.contains_key(branch.root));
    historical_reachable_contains_unchanged_under_split(
        pre,
        post,
        lbl,
        reads,
        writes,
        receipt,
        new_cache,
        j,
        branch.root,
        pre.available_branch_nodes().dom().len(),
        addr,
    );
    assert(pre.reachable_branch_addrs_from_with_fuel_contains(j, branch.root, pre.available_branch_nodes().dom().len(), addr));
    assert(post.reachable_branch_addrs_from_with_fuel_contains(j, branch.root, pre.available_branch_nodes().dom().len(), addr));
    split_nonfresh_write_addrs_are_pre_available(pre, post, lbl, reads, writes, receipt, new_cache);
    match lbl {
        ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg} => {
            let depth = receipt.depth();
            let read_nodes = to_branch_nodes(reads);
            let write_nodes = to_branch_nodes(writes);
            assert(pre.active_cached_branch().can_split(
                pre.mini_allocator,
                new_child_addr,
                receipt,
                split_arg,
                read_nodes,
                write_nodes,
            ));
            assert(receipt.key == pivot);
            assert(pre.active_cached_branch().root is Some);
            assert(write_nodes == crate::implementation::CachedBranch_v::loaded_split_write_nodes(
                receipt,
                read_nodes,
                split_arg,
                new_child_addr,
            ));
            assert(write_nodes.contains_key(new_child_addr));
            access_updates_available_branch_nodes_with_one_fresh_write_set(pre, post, reads, writes, new_child_addr);
        }
        _ => { assert(false); }
    }
    assert(post.available_branch_nodes().dom().len() == pre.available_branch_nodes().dom().len() + 1);
    ConcreteBranch::State::reachable_branch_addrs_more_fuel(post, j, branch.root, pre.available_branch_nodes().dom().len(), addr);
    assert(post.reachable_branch_addrs_from_with_fuel_contains(j, branch.root, post.available_branch_nodes().dom().len(), addr));
    assert(post.overlay_branch_entries_at(j).contains_key(addr));
    historical_branch_entry_unchanged_under_split(pre, post, lbl, reads, writes, receipt, new_cache, j, addr);
    ConcreteBranch::State::overlay_entry_matches_available(post, j, addr);
}

proof fn historical_overlay_unchanged_under_split(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    new_cache: Cache::State,
    j: nat,
)
    requires
        pre.refinement_wf(),
        post.refinement_wf(),
        lbl is Split,
        ConcreteBranch::State::split(pre, post, lbl, reads, writes, receipt, new_cache),
        post.disk == pre.disk,
        j < pre.active_idx(),
        pre.i().branches[j as int].branch is Some,
    ensures
        post.overlay_branch_entries_at(j) == pre.overlay_branch_entries_at(j),
        post.overlay_branch_at(j) == pre.overlay_branch_at(j),
        post.branch_stack_i_at(j) == pre.branch_stack_i_at(j),
{
    let branch = pre.i().branches[j as int].branch.unwrap();
    branch_stack_entry_matches_overlay(pre, j);
    assert(pre.i().branches[j as int] == pre.branch_stack_i_at(j));
    assert(pre.i().branches[j as int].branch is Some);
    assert(pre.i().branches[j as int].branch.unwrap() == branch);
    assert(pre.branch_stack_i_at(j).branch is Some);
    assert(pre.branch_stack_i_at(j).branch.unwrap() == branch);
    assert(pre.overlay_branch_at(j) is Some);
    assert(pre.overlay_branch_at(j).unwrap() == branch);
    assert(pre.overlay_branch_entries_at(j) == branch.disk_view.entries);

    let pre_entries = pre.overlay_branch_entries_at(j);
    let post_entries = post.overlay_branch_entries_at(j);
    assert forall |addr: Address| #[trigger] post_entries.contains_key(addr) <==> pre_entries.contains_key(addr) by {
        if post_entries.contains_key(addr) {
            historical_post_overlay_entry_in_pre_branch_under_split(pre, post, lbl, reads, writes, receipt, new_cache, j, addr);
        } else if pre_entries.contains_key(addr) {
            historical_pre_branch_entry_in_post_overlay_under_split(pre, post, lbl, reads, writes, receipt, new_cache, j, addr);
        }
    };
    assert forall |addr: Address| #[trigger] pre_entries.contains_key(addr) implies post_entries[addr] == pre_entries[addr] by {
        historical_pre_branch_entry_in_post_overlay_under_split(pre, post, lbl, reads, writes, receipt, new_cache, j, addr);
        ConcreteBranch::State::overlay_entry_matches_available(post, j, addr);
        historical_branch_entry_unchanged_under_split(pre, post, lbl, reads, writes, receipt, new_cache, j, addr);
    };
    assert_maps_equal!(post_entries, pre_entries);

    assert(post.cached_branches[j as int] == pre.cached_branches[j as int]);
    assert(post.overlay_branch_at(j) == pre.overlay_branch_at(j));
    assert(post.branch_stack_i_at(j).branch == post.overlay_branch_at(j));
    assert(pre.branch_stack_i_at(j).branch == pre.overlay_branch_at(j));
    assert(post.branch_stack_i_at(j) == pre.branch_stack_i_at(j));
}

pub proof fn concrete_split_step_refines_to_abstract_map(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    new_cache: Cache::State,
)
    requires
        pre.refinement_wf(),
        post.refinement_wf(),
        lbl is Split,
        ConcreteBranch::State::split(pre, post, lbl, reads, writes, receipt, new_cache),
    ensures
        AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
{
    let pre_stack = pre.i();
    let post_stack = post.i();
    let j = pre.active_idx() as nat;

    active_sparse_map_preserved_under_split(pre, post, lbl, reads, writes, receipt, new_cache);
    assert(post.seq_end == pre.seq_end);
    assert(post_stack.seq_end == pre_stack.seq_end);
    assert(post_stack.branches.len() == pre_stack.branches.len());

    assert forall |i: int|
        0 <= i < post_stack.branches.len()
        implies #[trigger] AllocationBranchStack::branch_sparse_map(post_stack.branches[i])
            == AllocationBranchStack::branch_sparse_map(pre_stack.branches[i])
    by {
        assert(post_stack.branches[i] == post.branch_stack_i_at(i as nat));
        assert(pre_stack.branches[i] == pre.branch_stack_i_at(i as nat));
        if i < pre.active_idx() {
            assert(0 <= i < pre.cached_branches.len() - 1);
            assert(pre.cached_branches[i].wf()) by {
                assert(pre.wf());
            };
            assert(pre.cached_branches[i].sealed) by {
                assert(pre.wf());
            };
            assert(pre.overlay_branch_at(i as nat) is Some) by {
                assert(pre.wf());
            };
            historical_overlay_unchanged_under_split(pre, post, lbl, reads, writes, receipt, new_cache, i as nat);
            assert(post.branch_stack_i_at(i as nat) == pre.branch_stack_i_at(i as nat));
        } else {
            assert(i == pre.active_idx());
            assert(i == post.active_idx());
            assert(AllocationBranchStack::branch_sparse_map(post.branch_stack_i_at(i as nat))
                == AllocationBranchStack::branch_sparse_map(pre.i().active_branch()));
            assert(pre.i().active_branch() == pre.branch_stack_i_at(i as nat));
        }
    };
    crate::implementation::AllocationBranchStackRefinement_v::sparse_map_equal_from_pointwise_branch_sparse_map_equal(
        post_stack,
        pre_stack,
    );
    crate::implementation::AllocationBranchStackRefinement_v::kmmap_equal_from_sparse_map_equal(post_stack, pre_stack);
    assert(post.abstract_map_i() == pre.abstract_map_i());
    internal_step_refines_from_same_abstract_map(pre, post, lbl);
}

proof fn historical_grow_writes_skip_branch_entry(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    j: nat,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Grow,
        ConcreteBranch::State::grow(pre, post, lbl, reads, writes, new_cache),
        j < pre.active_idx(),
        pre.i().branches[j as int].branch is Some,
        pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(addr),
    ensures
        !writes.contains_key(addr),
{
    let hist = pre.i().branches[j as int];
    let branch = hist.branch.unwrap();
    assert(hist.inv());
    assert(hist.sealed);
    assert(branch.tight_disk_view_with_summary());
    assert(branch.valid_sealed_branch());
    assert(branch.inv());
    assert(branch.disk_view.valid_address(branch.root));
    assert(branch.valid_sealed_branch());
    assert(branch.get_summary() == hist.mini_allocator.all_aus());
    assert(branch.get_summary().contains(addr.au));
    assert(pre.sealed_branch_disjoint_from_active_allocator_at(j));
    assert(branch.get_summary().disjoint(pre.mini_allocator.all_aus()));
    if writes.contains_key(addr) {
        grow_write_addr_in_active_allocator(pre, post, lbl, reads, writes, new_cache, addr);
        assert(pre.mini_allocator.all_aus().contains(addr.au));
        assert(false);
    }
}

proof fn historical_branch_entry_unchanged_under_grow(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    j: nat,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Grow,
        ConcreteBranch::State::grow(pre, post, lbl, reads, writes, new_cache),
        post.disk == pre.disk,
        j < pre.active_idx(),
        pre.i().branches[j as int].branch is Some,
        pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(addr),
    ensures
        post.available_branch_nodes().contains_key(addr),
        post.available_branch_nodes()[addr] == pre.i().branches[j as int].branch.unwrap().disk_view.entries[addr],
{
    let branch = pre.i().branches[j as int].branch.unwrap();
    historical_grow_writes_skip_branch_entry(pre, post, lbl, reads, writes, new_cache, j, addr);
    branch_stack_entry_matches_overlay(pre, j);
    assert(pre.branch_stack_i_at(j).branch == Some(branch));
    assert(pre.overlay_branch_at(j) == Some(branch));
    assert(pre.overlay_branch_entries_at(j) == branch.disk_view.entries);
    ConcreteBranch::State::overlay_entry_matches_available(pre, j, addr);
    available_branch_node_unchanged_at_unwritten_addr(pre, post, reads, writes, addr);
}

proof fn historical_reachable_contains_unchanged_under_grow(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    j: nat,
    current_addr: Address,
    fuel: nat,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Grow,
        ConcreteBranch::State::grow(pre, post, lbl, reads, writes, new_cache),
        post.disk == pre.disk,
        j < pre.active_idx(),
        pre.i().branches[j as int].branch is Some,
        pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(current_addr),
    ensures
        pre.reachable_branch_addrs_from_with_fuel_contains(j, current_addr, fuel, addr)
            == post.reachable_branch_addrs_from_with_fuel_contains(j, current_addr, fuel, addr),
        pre.reachable_branch_addrs_from_with_fuel_contains(j, current_addr, fuel, addr)
            ==> pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(addr),
        post.reachable_branch_addrs_from_with_fuel_contains(j, current_addr, fuel, addr)
            ==> pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(addr),
    decreases fuel,
{
    reveal(ConcreteBranch::State::grow);
    let branch = pre.i().branches[j as int].branch.unwrap();
    let hist = pre.i().branches[j as int];
    branch_stack_entry_matches_overlay(pre, j);
    assert(pre.overlay_branch_at(j) == Some(branch));
    assert(pre.overlay_branch_entries_at(j) == branch.disk_view.entries);

    if fuel == 0 {
    } else {
        historical_branch_entry_unchanged_under_grow(pre, post, lbl, reads, writes, new_cache, j, current_addr);
        ConcreteBranch::State::overlay_entry_matches_available(pre, j, current_addr);
        assert(pre.available_branch_nodes()[current_addr] == branch.disk_view.entries[current_addr]);
        assert(post.available_branch_nodes()[current_addr] == branch.disk_view.entries[current_addr]);
        let node = branch.disk_view.entries[current_addr];

        assert(post.cached_branches[j as int] == pre.cached_branches[j as int]);
        assert(pre.follow_aux_ptr_at(j, current_addr, node) == post.follow_aux_ptr_at(j, current_addr, node));

        if node is Leaf || node is Auxiliary {
            assert(pre.reachable_branch_addrs_from_with_fuel_contains(j, current_addr, fuel, addr) == (addr == current_addr));
            assert(post.reachable_branch_addrs_from_with_fuel_contains(j, current_addr, fuel, addr) == (addr == current_addr));
        } else {
            assert(hist.inv());
            assert(hist.sealed);
            assert(branch.valid_sealed_branch());
            assert(branch.inv());
            assert(branch.disk_view.no_dangling_address());
            assert(branch.disk_view.node_has_valid_child_address(node));

            if pre.follow_aux_ptr_at(j, current_addr, node) {
                assert(current_addr == branch.root);
                assert(node->aux_ptr is Some);
                assert(branch.disk_view.valid_address(node->aux_ptr.unwrap()));
                historical_reachable_contains_unchanged_under_grow(
                    pre,
                    post,
                    lbl,
                    reads,
                    writes,
                    new_cache,
                    j,
                    node->aux_ptr.unwrap(),
                    (fuel - 1) as nat,
                    addr,
                );
            }

            assert forall |i: int|
                0 <= i < node->children.len()
                implies pre.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, addr)
                    == post.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, addr)
                && (pre.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, addr)
                    ==> branch.disk_view.entries.contains_key(addr))
                && (post.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, addr)
                    ==> branch.disk_view.entries.contains_key(addr))
            by {
                assert(branch.disk_view.valid_address(node->children[i]));
                historical_reachable_contains_unchanged_under_grow(
                    pre,
                    post,
                    lbl,
                    reads,
                    writes,
                    new_cache,
                    j,
                    node->children[i],
                    (fuel - 1) as nat,
                    addr,
                );
            };
        }
    }
}

proof fn historical_post_overlay_entry_in_pre_branch_under_grow(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    j: nat,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Grow,
        ConcreteBranch::State::grow(pre, post, lbl, reads, writes, new_cache),
        post.disk == pre.disk,
        j < pre.active_idx(),
        pre.i().branches[j as int].branch is Some,
        post.overlay_branch_entries_at(j).contains_key(addr),
    ensures
        pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(addr),
        post.overlay_branch_entries_at(j)[addr] == pre.i().branches[j as int].branch.unwrap().disk_view.entries[addr],
{
    let branch = pre.i().branches[j as int].branch.unwrap();
    branch_stack_entry_matches_overlay(pre, j);
    assert(pre.i().branches[j as int] == pre.branch_stack_i_at(j));
    assert(pre.i().branches[j as int].inv());
    assert(pre.i().branches[j as int].sealed);
    assert(pre.branch_stack_i_at(j).branch is Some);
    assert(pre.branch_stack_i_at(j).branch.unwrap() == branch);
    assert(branch.valid_sealed_branch());
    assert(branch.inv());
    assert(pre.overlay_branch_at(j) is Some);
    assert(pre.overlay_branch_at(j).unwrap() == branch);
    assert(pre.overlay_branch_entries_at(j) == branch.disk_view.entries);
    assert(branch.disk_view.entries.contains_key(branch.root));
    assert(post.cached_branches[j as int].root == pre.cached_branches[j as int].root);
    assert(post.cached_branches[j as int].sealed == pre.cached_branches[j as int].sealed);
    assert(post.overlay_branch_entries_at(j).contains_key(addr));
    ConcreteBranch::State::overlay_entry_matches_available(post, j, addr);
    historical_reachable_contains_unchanged_under_grow(
        pre,
        post,
        lbl,
        reads,
        writes,
        new_cache,
        j,
        branch.root,
        post.available_branch_nodes().dom().len(),
        addr,
    );
    assert(post.reachable_branch_addrs_from_with_fuel_contains(j, branch.root, post.available_branch_nodes().dom().len(), addr));
    assert(branch.disk_view.entries.contains_key(addr));
    historical_branch_entry_unchanged_under_grow(pre, post, lbl, reads, writes, new_cache, j, addr);
    ConcreteBranch::State::overlay_entry_matches_available(post, j, addr);
}

proof fn historical_pre_branch_entry_in_post_overlay_under_grow(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    j: nat,
    addr: Address,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Grow,
        ConcreteBranch::State::grow(pre, post, lbl, reads, writes, new_cache),
        post.disk == pre.disk,
        j < pre.active_idx(),
        pre.i().branches[j as int].branch is Some,
        pre.i().branches[j as int].branch.unwrap().disk_view.entries.contains_key(addr),
    ensures
        post.overlay_branch_entries_at(j).contains_key(addr),
        post.overlay_branch_entries_at(j)[addr] == pre.i().branches[j as int].branch.unwrap().disk_view.entries[addr],
{
    let branch = pre.i().branches[j as int].branch.unwrap();
    branch_stack_entry_matches_overlay(pre, j);
    assert(pre.i().branches[j as int].inv());
    assert(pre.i().branches[j as int].sealed);
    assert(branch.valid_sealed_branch());
    assert(branch.inv());
    assert(pre.overlay_branch_at(j) == Some(branch));
    assert(pre.overlay_branch_entries_at(j) == branch.disk_view.entries);
    assert(branch.disk_view.entries.contains_key(branch.root));
    historical_reachable_contains_unchanged_under_grow(
        pre,
        post,
        lbl,
        reads,
        writes,
        new_cache,
        j,
        branch.root,
        pre.available_branch_nodes().dom().len(),
        addr,
    );
    assert(pre.reachable_branch_addrs_from_with_fuel_contains(j, branch.root, pre.available_branch_nodes().dom().len(), addr));
    assert(post.reachable_branch_addrs_from_with_fuel_contains(j, branch.root, pre.available_branch_nodes().dom().len(), addr));
    grow_available_branch_nodes_domain(pre, post, lbl, reads, writes, new_cache);
    assert(post.available_branch_nodes().dom().len() == pre.available_branch_nodes().dom().len() + 1);
    ConcreteBranch::State::reachable_branch_addrs_more_fuel(post, j, branch.root, pre.available_branch_nodes().dom().len(), addr);
    assert(post.reachable_branch_addrs_from_with_fuel_contains(j, branch.root, post.available_branch_nodes().dom().len(), addr));
    assert(post.overlay_branch_entries_at(j).contains_key(addr));
    historical_branch_entry_unchanged_under_grow(pre, post, lbl, reads, writes, new_cache, j, addr);
    ConcreteBranch::State::overlay_entry_matches_available(post, j, addr);
}

proof fn historical_overlay_unchanged_under_grow(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    j: nat,
)
    requires
        pre.refinement_wf(),
        post.refinement_wf(),
        lbl is Grow,
        ConcreteBranch::State::grow(pre, post, lbl, reads, writes, new_cache),
        post.disk == pre.disk,
        j < pre.active_idx(),
        pre.i().branches[j as int].branch is Some,
    ensures
        post.overlay_branch_entries_at(j) == pre.overlay_branch_entries_at(j),
        post.overlay_branch_at(j) == pre.overlay_branch_at(j),
        post.branch_stack_i_at(j) == pre.branch_stack_i_at(j),
{
    let branch = pre.i().branches[j as int].branch.unwrap();
    branch_stack_entry_matches_overlay(pre, j);
    assert(pre.i().branches[j as int] == pre.branch_stack_i_at(j));
    assert(pre.i().branches[j as int].branch is Some);
    assert(pre.i().branches[j as int].branch.unwrap() == branch);
    assert(pre.branch_stack_i_at(j).branch is Some);
    assert(pre.branch_stack_i_at(j).branch.unwrap() == branch);
    assert(pre.overlay_branch_at(j) is Some);
    assert(pre.overlay_branch_at(j).unwrap() == branch);
    assert(pre.overlay_branch_entries_at(j) == branch.disk_view.entries);

    let pre_entries = pre.overlay_branch_entries_at(j);
    let post_entries = post.overlay_branch_entries_at(j);
    assert forall |addr: Address| #[trigger] post_entries.contains_key(addr) <==> pre_entries.contains_key(addr) by {
        if post_entries.contains_key(addr) {
            historical_post_overlay_entry_in_pre_branch_under_grow(pre, post, lbl, reads, writes, new_cache, j, addr);
        } else if pre_entries.contains_key(addr) {
            historical_pre_branch_entry_in_post_overlay_under_grow(pre, post, lbl, reads, writes, new_cache, j, addr);
        }
    };
    assert forall |addr: Address| #[trigger] pre_entries.contains_key(addr) implies post_entries[addr] == pre_entries[addr] by {
        historical_pre_branch_entry_in_post_overlay_under_grow(pre, post, lbl, reads, writes, new_cache, j, addr);
        ConcreteBranch::State::overlay_entry_matches_available(post, j, addr);
        historical_branch_entry_unchanged_under_grow(pre, post, lbl, reads, writes, new_cache, j, addr);
    };
    assert_maps_equal!(post_entries, pre_entries);

    assert(post.cached_branches[j as int] == pre.cached_branches[j as int]);
    assert(post.overlay_branch_at(j) == pre.overlay_branch_at(j));
    assert(post.branch_stack_i_at(j).branch == post.overlay_branch_at(j));
    assert(pre.branch_stack_i_at(j).branch == pre.overlay_branch_at(j));
    assert(post.branch_stack_i_at(j) == pre.branch_stack_i_at(j));
}

proof fn reachable_fresh_root_is_child_plus_self(
    s: ConcreteBranch::State,
    branch_idx: nat,
    new_root: Address,
    child: Address,
    fuel: nat,
)
    requires
        branch_idx < s.cached_branches.len(),
        fuel > 0,
        s.available_branch_nodes().contains_key(new_root),
        s.available_branch_nodes()[new_root] == (AllocationBranchNode::Index{
            pivots: seq![],
            children: seq![child],
            aux_ptr: None,
        }),
    ensures
        s.reachable_branch_addrs_from_with_fuel(branch_idx, new_root, fuel)
            == s.reachable_branch_addrs_from_with_fuel(branch_idx, child, (fuel - 1) as nat).insert(new_root),
{
    let node = s.available_branch_nodes()[new_root];
    assert(!s.follow_aux_ptr_at(branch_idx, new_root, node));
    assert forall |a: Address|
        #[trigger] s.reachable_branch_addrs_from_with_fuel_contains(branch_idx, new_root, fuel, a)
            <==> (a == new_root
                || s.reachable_branch_addrs_from_with_fuel_contains(branch_idx, child, (fuel - 1) as nat, a))
    by {
        assert(s.reachable_branch_addrs_from_with_fuel_contains(branch_idx, new_root, fuel, a)
            == (
                a == new_root
                || s.follow_aux_ptr_at(branch_idx, new_root, node)
                    && s.reachable_branch_addrs_from_with_fuel_contains(branch_idx, node->aux_ptr.unwrap(), (fuel - 1) as nat, a)
                || exists |i: int|
                    0 <= i < node->children.len()
                    && s.reachable_branch_addrs_from_with_fuel_contains(branch_idx, node->children[i], (fuel - 1) as nat, a)
            ));
        assert(node->children.len() == 1);
        assert(node->children[0] == child);
    };
    assert forall |a: Address|
        #[trigger] s.reachable_branch_addrs_from_with_fuel(branch_idx, new_root, fuel).contains(a)
            <==> s.reachable_branch_addrs_from_with_fuel(branch_idx, child, (fuel - 1) as nat).insert(new_root).contains(a)
    by {
        assert(s.reachable_branch_addrs_from_with_fuel(branch_idx, new_root, fuel).contains(a)
            == s.reachable_branch_addrs_from_with_fuel_contains(branch_idx, new_root, fuel, a));
        assert(s.reachable_branch_addrs_from_with_fuel(branch_idx, child, (fuel - 1) as nat).insert(new_root).contains(a)
            == (a == new_root
                || s.reachable_branch_addrs_from_with_fuel_contains(branch_idx, child, (fuel - 1) as nat, a)));
    };
}

proof fn active_reachable_contains_unchanged_under_grow(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    branch: LinkedBranch<Summary>,
    addr: Address,
    fuel: nat,
)
    requires
        pre.refinement_wf(),
        post.wf(),
        lbl is Grow,
        ConcreteBranch::State::grow(pre, post, lbl, reads, writes, new_cache),
        post.disk == pre.disk,
        pre.overlay_branch() == Some(branch),
        branch.inv(),
        !pre.active_cached_branch().sealed,
        !post.active_cached_branch().sealed,
        branch.disk_view.entries.contains_key(addr),
        forall |a: Address| #[trigger] branch.disk_view.entries.contains_key(a) ==> {
            &&& post.available_branch_nodes().contains_key(a)
            &&& post.available_branch_nodes()[a] == branch.disk_view.entries[a]
        },
    ensures
        pre.reachable_branch_addrs_from_with_fuel(pre.active_idx() as nat, addr, fuel)
            == post.reachable_branch_addrs_from_with_fuel(pre.active_idx() as nat, addr, fuel),
    decreases fuel,
{
    let j = pre.active_idx() as nat;
    if fuel == 0 {
    } else {
        overlay_entries_match_branch_disk(pre, j, branch, addr);
        ConcreteBranch::State::overlay_entry_matches_available(pre, j, addr);
        assert(post.available_branch_nodes().contains_key(addr));
        let node = branch.disk_view.entries[addr];
        assert(post.available_branch_nodes()[addr] == node);
        if node is Leaf || node is Auxiliary {
            assert forall |a: Address|
                #[trigger] pre.reachable_branch_addrs_from_with_fuel_contains(j, addr, fuel, a)
                    <==> post.reachable_branch_addrs_from_with_fuel_contains(j, addr, fuel, a)
            by {
                reachable_terminal_contains_only_self(pre, j, addr, fuel, a);
                reachable_terminal_contains_only_self(post, j, addr, fuel, a);
            };
            assert forall |a: Address|
                #[trigger] pre.reachable_branch_addrs_from_with_fuel(j, addr, fuel).contains(a)
                    <==> post.reachable_branch_addrs_from_with_fuel(j, addr, fuel).contains(a)
            by {
                assert(pre.reachable_branch_addrs_from_with_fuel(j, addr, fuel).contains(a)
                    == pre.reachable_branch_addrs_from_with_fuel_contains(j, addr, fuel, a));
                assert(post.reachable_branch_addrs_from_with_fuel(j, addr, fuel).contains(a)
                    == post.reachable_branch_addrs_from_with_fuel_contains(j, addr, fuel, a));
            };
            assert(pre.reachable_branch_addrs_from_with_fuel(j, addr, fuel)
                == post.reachable_branch_addrs_from_with_fuel(j, addr, fuel));
        } else {
            assert(!pre.follow_aux_ptr_at(j, addr, node));
            assert(!post.follow_aux_ptr_at(j, addr, node));
            let pre_child_sets = Seq::new(
                node->children.len(),
                |i: int| pre.reachable_branch_addrs_from_with_fuel(j, node->children[i], (fuel - 1) as nat),
            );
            let post_child_sets = Seq::new(
                node->children.len(),
                |i: int| post.reachable_branch_addrs_from_with_fuel(j, node->children[i], (fuel - 1) as nat),
            );
            assert forall |i: int| 0 <= i < pre_child_sets.len() implies #[trigger] pre_child_sets[i] == post_child_sets[i] by {
                assert(branch.disk_view.valid_address(node->children[i]));
                active_reachable_contains_unchanged_under_grow(
                    pre,
                    post,
                    lbl,
                    reads,
                    writes,
                    new_cache,
                    branch,
                    node->children[i],
                    (fuel - 1) as nat,
                );
            };
            union_seq_of_sets_equal(pre_child_sets, post_child_sets);
            assert forall |a: Address|
                #[trigger] pre.reachable_branch_addrs_from_with_fuel_contains(j, addr, fuel, a)
                    <==> post.reachable_branch_addrs_from_with_fuel_contains(j, addr, fuel, a)
            by {
                if pre.reachable_branch_addrs_from_with_fuel_contains(j, addr, fuel, a) {
                    if a != addr {
                        let i = choose |i: int|
                            0 <= i < node->children.len()
                            && pre.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, a);
                        assert(pre_child_sets[i].contains(a));
                        assert(post_child_sets[i].contains(a));
                        crate::betree::Utils_v::lemma_set_subset_of_union_seq_of_sets(pre_child_sets, a);
                        assert(crate::betree::Utils_v::union_seq_of_sets(post_child_sets).contains(a));
                        assert(post.reachable_branch_addrs_from_with_fuel_contains(
                            j,
                            node->children[i],
                            (fuel - 1) as nat,
                            a,
                        ));
                        assert(post.reachable_branch_addrs_from_with_fuel_contains(j, addr, fuel, a));
                    }
                }
                if post.reachable_branch_addrs_from_with_fuel_contains(j, addr, fuel, a) {
                    if a != addr {
                        let i = choose |i: int|
                            0 <= i < node->children.len()
                            && post.reachable_branch_addrs_from_with_fuel_contains(j, node->children[i], (fuel - 1) as nat, a);
                        assert(post_child_sets[i].contains(a));
                        assert(pre_child_sets[i].contains(a));
                        crate::betree::Utils_v::lemma_set_subset_of_union_seq_of_sets(post_child_sets, a);
                        assert(crate::betree::Utils_v::union_seq_of_sets(pre_child_sets).contains(a));
                        assert(pre.reachable_branch_addrs_from_with_fuel_contains(
                            j,
                            node->children[i],
                            (fuel - 1) as nat,
                            a,
                        ));
                        assert(pre.reachable_branch_addrs_from_with_fuel_contains(j, addr, fuel, a));
                    }
                }
            };
            assert forall |a: Address|
                #[trigger] pre.reachable_branch_addrs_from_with_fuel(j, addr, fuel).contains(a)
                    <==> post.reachable_branch_addrs_from_with_fuel(j, addr, fuel).contains(a)
            by {
                assert(pre.reachable_branch_addrs_from_with_fuel(j, addr, fuel).contains(a)
                    == pre.reachable_branch_addrs_from_with_fuel_contains(j, addr, fuel, a));
                assert(post.reachable_branch_addrs_from_with_fuel(j, addr, fuel).contains(a)
                    == post.reachable_branch_addrs_from_with_fuel_contains(j, addr, fuel, a));
            };
            assert(pre.reachable_branch_addrs_from_with_fuel(j, addr, fuel)
                == post.reachable_branch_addrs_from_with_fuel(j, addr, fuel));
        }
    }
}

proof fn active_sparse_map_preserved_under_grow(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
)
    requires
        pre.refinement_wf(),
        post.refinement_wf(),
        lbl is Grow,
        ConcreteBranch::State::grow(pre, post, lbl, reads, writes, new_cache),
    ensures
        AllocationBranchStack::branch_sparse_map(post.branch_stack_i_at(pre.active_idx() as nat))
            == AllocationBranchStack::branch_sparse_map(pre.i().active_branch()),
{
    reveal(ConcreteBranch::State::grow);
    let j = pre.active_idx() as nat;
    let branch = pre.overlay_branch().unwrap();
    let root = branch.root;
    let new_root = lbl->new_root_addr;
    let grown = branch.grow(new_root);
    let read_nodes = to_branch_nodes(reads);
    let write_nodes = to_branch_nodes(writes);
    let cache_lbl = Cache::Label::Access{reads, writes};

    branch_stack_entry_matches_overlay(pre, j);
    assert(pre.i().branches[j as int] == pre.branch_stack_i_at(j));
    assert(pre.i().active_branch() == pre.branch_stack_i_at(j));
    assert(pre.branch_stack_i_at(j).branch == Some(branch));
    assert(pre.overlay_branch_at(j) == Some(branch));
    assert(pre.overlay_branch_entries_at(j) == branch.disk_view.entries);
    assert(pre.active_cached_branch().can_grow(pre.mini_allocator, new_root, read_nodes, write_nodes));
    reveal(Cache::State::next_by);
    reveal(Cache::State::next);
    assert(Cache::State::next_by(pre.cache, new_cache, cache_lbl, Cache::Step::access()));
    assert(write_nodes == crate::implementation::CachedBranch_v::loaded_grow_write_nodes(root, new_root));
    assert(write_nodes.dom() == set!{new_root});
    assert(writes.contains_key(new_root));
    assert(!pre.available_branch_nodes().contains_key(new_root));
    assert(!branch.disk_view.entries.contains_key(new_root));
    assert(write_nodes[new_root] == AllocationBranchNode::Index{
        pivots: seq![],
        children: seq![root],
        aux_ptr: None,
    });
    assert(branch.can_grow(new_root));

    assert forall |addr: Address| #[trigger] branch.disk_view.entries.contains_key(addr) implies {
        &&& post.available_branch_nodes().contains_key(addr)
        &&& post.available_branch_nodes()[addr] == branch.disk_view.entries[addr]
    } by {
        overlay_entries_match_branch_disk(pre, j, branch, addr);
        ConcreteBranch::State::overlay_entry_matches_available(pre, j, addr);
        assert(addr != new_root);
        assert(!writes.contains_key(addr));
        available_branch_node_unchanged_at_unwritten_addr(pre, post, reads, writes, addr);
    };
    written_addr_is_available_branch_node_after_access(pre, post, reads, writes, new_root);
    assert(post.available_branch_nodes()[new_root] == write_nodes[new_root]);
    assert(post.available_branch_nodes()[new_root] == grown.disk_view.entries[new_root]);

    assert forall |addr: Address|
        #[trigger] post.available_branch_nodes().contains_key(addr)
            <==> pre.available_branch_nodes().dom().insert(new_root).contains(addr)
    by {
        if post.available_branch_nodes().contains_key(addr) {
            if addr == new_root {
            } else if writes.contains_key(addr) {
                assert(writes.dom() == set!{new_root});
                assert(writes.dom().contains(addr));
                assert(addr == new_root);
            } else if pre.available_branch_nodes().contains_key(addr) {
            } else {
                unavailable_branch_node_stays_unavailable_at_unwritten_addr(pre, post, reads, writes, addr);
                assert(false);
            }
        }
        if pre.available_branch_nodes().dom().insert(new_root).contains(addr) {
            if addr == new_root {
                assert(post.available_branch_nodes().contains_key(addr));
            } else {
                assert(!writes.contains_key(addr));
                available_branch_node_unchanged_at_unwritten_addr(pre, post, reads, writes, addr);
            }
        }
    };
    assert(post.available_branch_nodes().dom() == pre.available_branch_nodes().dom().insert(new_root));
    let pre_len = pre.available_branch_nodes().dom().len();
    vstd::set::axiom_set_insert_len(pre.available_branch_nodes().dom(), new_root);
    assert(post.available_branch_nodes().dom().len() == pre_len + 1);

    active_reachable_contains_unchanged_under_grow(
        pre,
        post,
        lbl,
        reads,
        writes,
        new_cache,
        branch,
        root,
        pre_len,
    );
    assert(pre.reachable_branch_addrs_from_with_fuel(j, root, pre_len)
        == post.reachable_branch_addrs_from_with_fuel(j, root, pre_len));
    reachable_fresh_root_is_child_plus_self(post, j, new_root, root, post.available_branch_nodes().dom().len());
    assert(post.reachable_branch_addrs_from_with_fuel(j, new_root, post.available_branch_nodes().dom().len())
        == post.reachable_branch_addrs_from_with_fuel(j, root, pre_len).insert(new_root));

    assert forall |addr: Address|
        #[trigger] post.overlay_branch_entries_at(j).contains_key(addr) <==> grown.disk_view.entries.contains_key(addr)
    by {
        if post.overlay_branch_entries_at(j).contains_key(addr) {
            if addr == new_root {
                assert(grown.disk_view.entries.contains_key(addr));
            } else {
                assert(post.reachable_branch_addrs_from_with_fuel_contains(j, new_root, post.available_branch_nodes().dom().len(), addr));
                assert(post.reachable_branch_addrs_from_with_fuel_contains(j, root, pre_len, addr));
                assert(pre.reachable_branch_addrs_from_with_fuel_contains(j, root, pre_len, addr));
                overlay_entries_match_branch_disk(pre, j, branch, addr);
                assert(branch.disk_view.entries.contains_key(addr));
                assert(grown.disk_view.entries.contains_key(addr));
            }
        }
        if grown.disk_view.entries.contains_key(addr) {
            if addr == new_root {
                assert(post.reachable_branch_addrs_from_with_fuel_contains(j, new_root, post.available_branch_nodes().dom().len(), addr));
                assert(post.overlay_branch_entries_at(j).contains_key(addr));
            } else {
                assert(branch.disk_view.entries.contains_key(addr));
                assert(post.reachable_branch_addrs_from_with_fuel_contains(j, root, pre_len, addr));
                ConcreteBranch::State::reachable_branch_addrs_more_fuel(post, j, root, pre_len, addr);
                assert(post.reachable_branch_addrs_from_with_fuel_contains(j, root, pre_len + 1, addr));
                assert(post.reachable_branch_addrs_from_with_fuel_contains(j, new_root, post.available_branch_nodes().dom().len(), addr));
                assert(post.overlay_branch_entries_at(j).contains_key(addr));
            }
        }
    };
    assert forall |addr: Address|
        #[trigger] post.overlay_branch_entries_at(j).contains_key(addr)
            implies post.overlay_branch_entries_at(j)[addr] == grown.disk_view.entries[addr]
    by {
        if addr == new_root {
            ConcreteBranch::State::overlay_entry_matches_available(post, j, addr);
        } else {
            ConcreteBranch::State::overlay_entry_matches_available(post, j, addr);
            ConcreteBranch::State::overlay_entry_matches_available(pre, j, addr);
            assert(post.overlay_branch_entries_at(j)[addr] == post.available_branch_nodes()[addr]);
            assert(pre.overlay_branch_entries_at(j)[addr] == pre.available_branch_nodes()[addr]);
            assert(pre.overlay_branch_entries_at(j)[addr] == branch.disk_view.entries[addr]);
            assert(grown.disk_view.entries[addr] == branch.disk_view.entries[addr]);
        }
    };
    assert_maps_equal!(post.overlay_branch_entries_at(j), grown.disk_view.entries);
    assert(post.cached_branches[j as int].root == Some(new_root));
    assert(post.overlay_branch_at(j) == Some(grown));
    branch_stack_entry_matches_overlay(post, j);
    assert(post.branch_stack_i_at(j).branch == Some(grown));

    LinkedBranchRefinement_v::grow_refines(branch, new_root);
    LinkedBranchRefinement_v::i_wf(branch);
    crate::betree::PivotBranchRefinement_v::grow_refines(branch.i(), PivotInternalLabel{});
    assert(grown.i().i() == branch.i().i());
    branch_sparse_map_equal_from_equal_buffer(post.branch_stack_i_at(j), pre.i().active_branch());
}

pub proof fn concrete_grow_step_refines_to_abstract_map(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
)
    requires
        pre.refinement_wf(),
        post.refinement_wf(),
        lbl is Grow,
        ConcreteBranch::State::grow(pre, post, lbl, reads, writes, new_cache),
    ensures
        AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
{
    let pre_stack = pre.i();
    let post_stack = post.i();
    let j = pre.active_idx() as nat;

    active_sparse_map_preserved_under_grow(pre, post, lbl, reads, writes, new_cache);
    assert(post.seq_end == pre.seq_end);
    assert(post_stack.seq_end == pre_stack.seq_end);
    assert(post_stack.branches.len() == pre_stack.branches.len());

    assert forall |i: int|
        0 <= i < post_stack.branches.len()
        implies #[trigger] AllocationBranchStack::branch_sparse_map(post_stack.branches[i])
            == AllocationBranchStack::branch_sparse_map(pre_stack.branches[i])
    by {
        assert(post_stack.branches[i] == post.branch_stack_i_at(i as nat));
        assert(pre_stack.branches[i] == pre.branch_stack_i_at(i as nat));
        if i < pre.active_idx() {
            assert(0 <= i < pre.cached_branches.len() - 1);
            assert(pre.cached_branches[i].wf()) by {
                assert(pre.wf());
            };
            assert(pre.cached_branches[i].sealed) by {
                assert(pre.wf());
            };
            assert(pre.overlay_branch_at(i as nat) is Some) by {
                assert(pre.wf());
            };
            historical_overlay_unchanged_under_grow(pre, post, lbl, reads, writes, new_cache, i as nat);
            assert(post.branch_stack_i_at(i as nat) == pre.branch_stack_i_at(i as nat));
        } else {
            assert(i == pre.active_idx());
            assert(i == post.active_idx());
            assert(AllocationBranchStack::branch_sparse_map(post.branch_stack_i_at(i as nat))
                == AllocationBranchStack::branch_sparse_map(pre.i().active_branch()));
            assert(pre.i().active_branch() == pre.branch_stack_i_at(i as nat));
        }
    };
    crate::implementation::AllocationBranchStackRefinement_v::sparse_map_equal_from_pointwise_branch_sparse_map_equal(
        post_stack,
        pre_stack,
    );
    crate::implementation::AllocationBranchStackRefinement_v::kmmap_equal_from_sparse_map_equal(post_stack, pre_stack);
    assert(post.abstract_map_i() == pre.abstract_map_i());
    internal_step_refines_from_same_abstract_map(pre, post, lbl);
}

proof fn linked_seal_preserves_buffer(branch: LinkedBranch<Summary>, aux_addr: Address, summary: Summary)
    requires
        branch.inv(),
        branch.root() is Index,
        branch.disk_view.is_fresh(set!{aux_addr}),
    ensures
        branch.seal(aux_addr, summary).i().i() == branch.i().i(),
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

proof fn active_sparse_map_preserved_under_leaf_seal(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
)
    requires
        pre.refinement_wf(),
        post.refinement_wf(),
        lbl is Seal,
        lbl->aux_ptr is None,
        ConcreteBranch::State::seal(pre, post, lbl, reads, writes, new_cache),
        post.disk == pre.disk,
    ensures
        AllocationBranchStack::branch_sparse_map(post.branch_stack_i_at(pre.active_idx() as nat))
            == AllocationBranchStack::branch_sparse_map(pre.i().active_branch()),
{
    reveal(ConcreteBranch::State::seal);
    let j = pre.active_idx() as nat;
    let branch = pre.overlay_branch().unwrap();
    let root = branch.root;
    let read_nodes = to_branch_nodes(reads);
    let write_nodes = to_branch_nodes(writes);
    let cache_lbl = Cache::Label::Access{reads, writes};

    branch_stack_entry_matches_overlay(pre, j);
    assert(pre.i().branches[j as int] == pre.branch_stack_i_at(j));
    assert(pre.i().active_branch() == pre.branch_stack_i_at(j));
    assert(pre.branch_stack_i_at(j).branch == Some(branch));
    assert(pre.active_cached_branch().can_seal(pre.mini_allocator, lbl->aux_ptr, read_nodes, write_nodes));
    reveal(Cache::State::next_by);
    reveal(Cache::State::next);
    assert(Cache::State::next_by(pre.cache, new_cache, cache_lbl, Cache::Step::access()));
    assert(cache_lbl->reads.contains_key(root));
    assert(pre.cache.valid_read(root, cache_lbl->reads[root])) by {};
    ConcreteBranch::State::overlay_entry_matches_available(pre, j, root);
    assert(read_nodes[root] == crate::implementation::ConcreteBranch_v::decode_branch_page(reads[root]));
    assert(pre.has_cached_page(root));
    assert(pre.available_branch_nodes()[root] == branch.disk_view.entries[root]);
    assert(read_nodes[root] == pre.available_branch_nodes()[root]);
    assert(branch.inv());
    assert(!(read_nodes[root] is Index));
    assert(!(read_nodes[root] is Auxiliary));
    assert(read_nodes[root] is Leaf);
    assert(branch.root() == read_nodes[root]);
    assert(branch.root() is Leaf);
    assert(write_nodes == crate::implementation::CachedBranch_v::loaded_seal_write_nodes(
        root,
        read_nodes,
        lbl->aux_ptr,
        pre.mini_allocator.reserved_aus(),
    ));
    assert(write_nodes == Map::<Address, AllocationBranchNode>::empty());
    assert forall |addr: Address| #[trigger] writes.contains_key(addr) implies false by {
        assert(write_nodes.contains_key(addr));
    };
    assert(writes == Map::<Address, RawPage>::empty());

    available_branch_nodes_unchanged_when_writes_empty(pre, post, reads);
    assert(post.cached_branches[j as int].root == Some(root));
    assert(post.available_branch_nodes().contains_key(root));
    assert(pre.available_branch_nodes().contains_key(root));
    assert(pre.available_branch_nodes()[root] is Leaf);
    assert(post.available_branch_nodes()[root] == pre.available_branch_nodes()[root]);

    let pre_fuel = pre.available_branch_nodes().dom().len();
    let post_fuel = post.available_branch_nodes().dom().len();
    assert(post.available_branch_nodes() == pre.available_branch_nodes());
    assert(post.available_branch_nodes().dom() == pre.available_branch_nodes().dom());
    assert(post_fuel == pre_fuel);

    assert forall |addr: Address|
        #[trigger] pre.overlay_branch_entries_at(j).contains_key(addr) <==> post.overlay_branch_entries_at(j).contains_key(addr)
    by {
        if pre.overlay_branch_entries_at(j).contains_key(addr) {
            ConcreteBranch::State::overlay_entry_matches_available(pre, j, addr);
            assert(addr == root) by {
                reachable_terminal_contains_only_self(pre, j, root, pre_fuel, addr);
            };
        }
        if post.overlay_branch_entries_at(j).contains_key(addr) {
            ConcreteBranch::State::overlay_entry_matches_available(post, j, addr);
            assert(addr == root) by {
                reachable_terminal_contains_only_self(post, j, root, post_fuel, addr);
            };
        }
    };
    assert forall |addr: Address|
        #[trigger] post.overlay_branch_entries_at(j).contains_key(addr)
            implies post.overlay_branch_entries_at(j)[addr] == pre.overlay_branch_entries_at(j)[addr]
    by {
        assert(addr == root) by {
            ConcreteBranch::State::overlay_entry_matches_available(post, j, addr);
            reachable_terminal_contains_only_self(post, j, root, post_fuel, addr);
        };
        ConcreteBranch::State::overlay_entry_matches_available(post, j, root);
        ConcreteBranch::State::overlay_entry_matches_available(pre, j, root);
    };
    assert_maps_equal!(post.overlay_branch_entries_at(j), pre.overlay_branch_entries_at(j));

    assert(post.overlay_branch_at(j) == pre.overlay_branch_at(j));
    assert(post.branch_stack_i_at(j).branch == pre.branch_stack_i_at(j).branch);
    assert(AllocationBranchStack::branch_sparse_map(post.branch_stack_i_at(j))
        == AllocationBranchStack::branch_sparse_map(pre.branch_stack_i_at(j)));
    assert(AllocationBranchStack::branch_sparse_map(pre.branch_stack_i_at(j))
        == AllocationBranchStack::branch_sparse_map(pre.i().active_branch()));
}

pub proof fn concrete_leaf_seal_step_refines_to_abstract_map(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
)
    requires
        pre.refinement_wf(),
        post.refinement_wf(),
        lbl is Seal,
        lbl->aux_ptr is None,
        ConcreteBranch::State::seal(pre, post, lbl, reads, writes, new_cache),
    ensures
        AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
{
    let pre_stack = pre.i();
    let post_stack = post.i();
    let old_active = pre.active_idx() as nat;
    let sealed_active = post.branch_stack_i_at(old_active);
    let empty_branch = post.branch_stack_i_at(post.active_idx() as nat);
    let modeled_post = AllocationBranchStack{
        branches: pre_stack.branches.update(pre.active_idx(), sealed_active).push(empty_branch),
        seq_end: pre_stack.seq_end,
    };

    active_sparse_map_preserved_under_leaf_seal(pre, post, lbl, reads, writes, new_cache);
    assert(post.seq_end == pre.seq_end);
    assert(post_stack.seq_end == pre_stack.seq_end);
    assert(post_stack.branches.len() == modeled_post.branches.len());
    assert(post_stack.branches[old_active as int] == sealed_active);
    assert(post_stack.branches[post.active_idx()] == empty_branch);
    assert(!empty_branch.sealed);
    assert(empty_branch.branch is None);
    assert(AllocationBranchStack::branch_sparse_map(empty_branch) == Map::<Key, Message>::empty());

    assert forall |j: int|
        0 <= j < post_stack.branches.len()
        implies #[trigger] AllocationBranchStack::branch_sparse_map(post_stack.branches[j])
            == AllocationBranchStack::branch_sparse_map(modeled_post.branches[j])
    by {
        if j < pre.active_idx() {
            assert(0 <= j < pre.cached_branches.len() - 1);
            assert(pre.cached_branches[j].wf()) by {
                assert(pre.wf());
            };
            assert(pre.cached_branches[j].sealed) by {
                assert(pre.wf());
            };
            assert(pre.overlay_branch_at(j as nat) is Some) by {
                assert(pre.wf());
            };
            branch_stack_entry_matches_overlay(pre, j as nat);
            assert(pre.i().branches[j].branch is Some);
            historical_overlay_unchanged_under_seal(pre, post, lbl, reads, writes, new_cache, j as nat);
            assert(post_stack.branches[j] == post.branch_stack_i_at(j as nat));
            assert(modeled_post.branches[j] == pre_stack.branches[j]);
            assert(pre_stack.branches[j] == pre.branch_stack_i_at(j as nat));
            assert(post.branch_stack_i_at(j as nat) == pre.branch_stack_i_at(j as nat));
        } else if j == pre.active_idx() {
            assert(modeled_post.branches[j] == sealed_active);
        } else {
            assert(j == post.active_idx());
            assert(modeled_post.branches[j] == empty_branch);
        }
    };
    crate::implementation::AllocationBranchStackRefinement_v::sparse_map_equal_from_pointwise_branch_sparse_map_equal(
        post_stack,
        modeled_post,
    );
    crate::implementation::AllocationBranchStackRefinement_v::sparse_map_seal_active_and_push_empty_preserves(
        pre_stack,
        sealed_active,
        empty_branch,
    );
    assert(modeled_post.sparse_map() == pre_stack.sparse_map());
    assert(post_stack.sparse_map() == pre_stack.sparse_map());
    crate::implementation::AllocationBranchStackRefinement_v::kmmap_equal_from_sparse_map_equal(post_stack, pre_stack);
    assert(post.abstract_map_i() == pre.abstract_map_i());
    internal_step_refines_from_same_abstract_map(pre, post, lbl);
}

pub proof fn concrete_aux_seal_step_refines_to_abstract_map(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
)
    requires
        pre.refinement_wf(),
        post.refinement_wf(),
        lbl is Seal,
        lbl->aux_ptr is Some,
        ConcreteBranch::State::seal(pre, post, lbl, reads, writes, new_cache),
    ensures
        AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
{
    let pre_stack = pre.i();
    let post_stack = post.i();
    let old_active = pre.active_idx() as nat;
    let sealed_active = post.branch_stack_i_at(old_active);
    let empty_branch = post.branch_stack_i_at(post.active_idx() as nat);
    let modeled_post = AllocationBranchStack{
        branches: pre_stack.branches.update(pre.active_idx(), sealed_active).push(empty_branch),
        seq_end: pre_stack.seq_end,
    };

    active_sparse_map_preserved_under_aux_seal(pre, post, lbl, reads, writes, new_cache);
    assert(post.seq_end == pre.seq_end);
    assert(post_stack.seq_end == pre_stack.seq_end);
    assert(post_stack.branches.len() == modeled_post.branches.len());
    assert(post_stack.branches[old_active as int] == sealed_active);
    assert(post_stack.branches[post.active_idx()] == empty_branch);
    assert(!empty_branch.sealed);
    assert(empty_branch.branch is None);
    assert(AllocationBranchStack::branch_sparse_map(empty_branch) == Map::<Key, Message>::empty());

    assert forall |j: int|
        0 <= j < post_stack.branches.len()
        implies #[trigger] AllocationBranchStack::branch_sparse_map(post_stack.branches[j])
            == AllocationBranchStack::branch_sparse_map(modeled_post.branches[j])
    by {
        if j < pre.active_idx() {
            assert(0 <= j < pre.cached_branches.len() - 1);
            assert(pre.cached_branches[j].wf()) by {
                assert(pre.wf());
            };
            assert(pre.cached_branches[j].sealed) by {
                assert(pre.wf());
            };
            assert(pre.overlay_branch_at(j as nat) is Some) by {
                assert(pre.wf());
            };
            branch_stack_entry_matches_overlay(pre, j as nat);
            assert(pre.i().branches[j].branch is Some);
            historical_overlay_unchanged_under_seal(pre, post, lbl, reads, writes, new_cache, j as nat);
            assert(post_stack.branches[j] == post.branch_stack_i_at(j as nat));
            assert(modeled_post.branches[j] == pre_stack.branches[j]);
            assert(pre_stack.branches[j] == pre.branch_stack_i_at(j as nat));
            assert(post.branch_stack_i_at(j as nat) == pre.branch_stack_i_at(j as nat));
        } else if j == pre.active_idx() {
            assert(modeled_post.branches[j] == sealed_active);
        } else {
            assert(j == post.active_idx());
            assert(modeled_post.branches[j] == empty_branch);
        }
    };
    crate::implementation::AllocationBranchStackRefinement_v::sparse_map_equal_from_pointwise_branch_sparse_map_equal(
        post_stack,
        modeled_post,
    );
    crate::implementation::AllocationBranchStackRefinement_v::sparse_map_seal_active_and_push_empty_preserves(
        pre_stack,
        sealed_active,
        empty_branch,
    );
    assert(modeled_post.sparse_map() == pre_stack.sparse_map());
    assert(post_stack.sparse_map() == pre_stack.sparse_map());
    crate::implementation::AllocationBranchStackRefinement_v::kmmap_equal_from_sparse_map_equal(post_stack, pre_stack);
    assert(post.abstract_map_i() == pre.abstract_map_i());
    internal_step_refines_from_same_abstract_map(pre, post, lbl);
}

pub proof fn concrete_seal_step_refines_to_abstract_map(
    pre: ConcreteBranch::State,
    post: ConcreteBranch::State,
    lbl: ConcreteBranch::Label,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
)
    requires
        pre.refinement_wf(),
        post.refinement_wf(),
        lbl is Seal,
        ConcreteBranch::State::seal(pre, post, lbl, reads, writes, new_cache),
    ensures
        AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
{
    if lbl->aux_ptr is Some {
        concrete_aux_seal_step_refines_to_abstract_map(pre, post, lbl, reads, writes, new_cache);
    } else {
        concrete_leaf_seal_step_refines_to_abstract_map(pre, post, lbl, reads, writes, new_cache);
    }
}

} // verus!

// Temporarily commented out during the stacked ConcreteBranch refactor.
// Original refinement proof body preserved below for future repair.

// // Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// // SPDX-License-Identifier: BSD-2-Clause
// 
// #![allow(unused_imports)]
// 
// use vstd::prelude::*;
// use vstd::map::*;
// 
// use crate::abstract_system::AbstractMap_v::AbstractMap;
// use crate::abstract_system::MsgHistory_v::{KeyedMessage, MsgHistory};
// use crate::abstract_system::StampedMap_v::{Stamped, StampedMap};
// use crate::allocation_layer::AllocationBranch_v::{AllocationBranch, Summary};
// use crate::betree::Buffer_v::SimpleBuffer;
// use crate::betree::LinkedBranch_v::{LinkedBranch, Path as BranchPath, SplitArg};
// use crate::betree::LinkedBranch_v::Refinement_v as LinkedBranchRefinement_v;
// use crate::betree::PivotBranchRefinement_v::{
//     self,
//     AppendLabel as PivotAppendLabel,
//     InternalLabel as PivotInternalLabel,
//     QueryLabel as PivotQueryLabel,
// };
// use crate::disk::GenericDisk_v::{Address, Pointer};
// use crate::implementation::ConcreteBranch_v::ConcreteBranch;
// use crate::spec::KeyType_t::Key;
// use crate::spec::Messages_t::{default_value, Message, Value};
// use crate::spec::TotalKMMap_t::TotalKMMap;
// 
// verus! {
// 
// pub open spec fn normalize_value(msg: Message) -> Value
// {
//     match msg {
//         Message::Define{value} => value,
//         Message::Update{delta} => Message::apply_delta(delta, default_value()),
//     }
// }
// 
// pub open spec fn normalize_message(msg: Message) -> Message
// {
//     Message::Define{value: normalize_value(msg)}
// }
// 
// pub open spec fn append_puts(start_lsn: nat, keys: Seq<Key>, msgs: Seq<Message>) -> MsgHistory
//     recommends
//         keys.len() == msgs.len(),
// {
//     let seq_end = start_lsn + keys.len();
//     let puts = Map::new(
//         |lsn: nat| start_lsn <= lsn < seq_end,
//         |lsn: nat| {
//             let idx = (lsn - start_lsn) as int;
//             KeyedMessage{ key: keys[idx], message: normalize_message(msgs[idx]) }
//         },
//     );
//     MsgHistory{ msgs: puts, seq_start: start_lsn, seq_end }
// }
// 
// pub proof fn append_puts_wf(start_lsn: nat, keys: Seq<Key>, msgs: Seq<Message>)
//     requires
//         keys.len() == msgs.len(),
//     ensures
//         append_puts(start_lsn, keys, msgs).wf(),
//         append_puts(start_lsn, keys, msgs).seq_start == start_lsn,
//         append_puts(start_lsn, keys, msgs).seq_end == start_lsn + keys.len(),
// {
//     let puts = append_puts(start_lsn, keys, msgs);
//     assert(puts.seq_start <= puts.seq_end);
//     assert forall |lsn: nat| #[trigger] puts.msgs.dom().contains(lsn) <==> puts.contains(lsn) by { };
// }
// 
// pub open spec fn buffer_as_kmmap(buffer: SimpleBuffer) -> TotalKMMap
// {
//     TotalKMMap(Map::new(|k: Key| true, |k: Key| normalize_message(buffer.query(k))))
// }
// 
// pub open spec fn branch_as_kmmap(branch: LinkedBranch<Summary>) -> TotalKMMap
// {
//     buffer_as_kmmap(branch.i().i())
// }
// 
// impl AllocationBranch {
//     pub open spec fn buffer_i(self) -> SimpleBuffer
//     {
//         if self.branch is Some {
//             self.branch.unwrap().i().i()
//         } else {
//             SimpleBuffer::empty()
//         }
//     }
// 
//     pub open spec fn kmmap_i(self) -> TotalKMMap
//     {
//         buffer_as_kmmap(self.buffer_i())
//     }
// }
// 
// impl ConcreteBranch::State {
//     pub open spec fn abstract_map_i(self) -> AbstractMap::State
//     {
//         AbstractMap::State{
//             stamped_map: Stamped{
//                 value: self.i().kmmap_i(),
//                 seq_end: self.cached_branch.seq_end,
//             }
//         }
//     }
// 
//     pub open spec fn label_to_abstract_map(self, lbl: ConcreteBranch::Label) -> AbstractMap::Label
//     {
//         match lbl {
//             ConcreteBranch::Label::Query{key, msg, depth} =>
//                 AbstractMap::Label::QueryLabel{
//                     end_lsn: self.cached_branch.seq_end,
//                     key,
//                     value: normalize_value(msg),
//                 },
//             ConcreteBranch::Label::Append{keys, msgs, depth} =>
//                 AbstractMap::Label::PutLabel{ puts: append_puts(self.cached_branch.seq_end, keys, msgs) },
//             ConcreteBranch::Label::Grow{new_root_addr} =>
//                 AbstractMap::Label::InternalLabel{},
//             ConcreteBranch::Label::Split{new_child_addr, pivot, depth, split_arg} =>
//                 AbstractMap::Label::InternalLabel{},
//             ConcreteBranch::Label::Seal{aux_ptr} =>
//                 AbstractMap::Label::InternalLabel{},
//             ConcreteBranch::Label::Internal{} =>
//                 AbstractMap::Label::InternalLabel{},
//         }
//     }
// }
// 
// proof fn allocation_query_refines_to_kmmap(branch: LinkedBranch<Summary>, key: Key)
//     requires
//         branch.inv(),
//     ensures
//         branch_as_kmmap(branch)[key] == normalize_message(branch.query(key)),
// {
//     let msg = branch.query(key);
//     LinkedBranchRefinement_v::query_refines(branch, key, msg);
//     LinkedBranchRefinement_v::i_internal_wf(branch, branch.the_ranking());
//     PivotBranchRefinement_v::query_refines(branch.i(), PivotQueryLabel{key, msg});
//     assert(branch.i().i().query(key) == msg);
// }
// 
// proof fn allocation_grow_preserves_kmmap(pre: AllocationBranch, addr: Address)
//     requires
//         pre.inv(),
//         crate::implementation::ConcreteBranchRefinement_v::allocation_branch_can_grow(pre, addr),
//     ensures
//         crate::implementation::ConcreteBranchRefinement_v::allocation_branch_grow(pre, addr).kmmap_i() == pre.kmmap_i(),
// {
//     let pre_branch = pre.branch.unwrap();
//     LinkedBranchRefinement_v::grow_refines(pre_branch, addr);
//     LinkedBranchRefinement_v::i_wf(pre_branch);
//     PivotBranchRefinement_v::grow_refines(pre_branch.i(), PivotInternalLabel{});
//     assert(pre_branch.grow(addr).i().i() == pre_branch.i().i());
// }
// 
// proof fn allocation_split_preserves_kmmap(
//     pre: AllocationBranch,
//     new_child_addr: Address,
//     path: BranchPath<Summary>,
//     split_arg: SplitArg,
// )
//     requires
//         pre.inv(),
//         pre.can_split(new_child_addr, path, split_arg),
//     ensures
//         pre.branch_split(new_child_addr, path, split_arg).kmmap_i() == pre.kmmap_i(),
// {
//     let pre_branch = pre.branch.unwrap();
//     let post_branch = pre.branch_split(new_child_addr, path, split_arg).branch.unwrap();
//     let ranking = pre_branch.the_ranking();
//     let post_ranking = post_branch.the_ranking();
//     let pre_i = pre_branch.i_internal(ranking);
//     let post_i = post_branch.i_internal(post_ranking);
//     let path_i = path.i_internal(ranking);
//     let pivot = split_arg.get_pivot();
//     let split_child_idx = path.target().root().route(pivot) + 1;
//     let split_child = path.target().child_at_idx(split_child_idx);
//     LinkedBranchRefinement_v::split_refines(pre_branch, new_child_addr, path, split_arg);
//     LinkedBranchRefinement_v::i_internal_wf(pre_branch, ranking);
//     LinkedBranchRefinement_v::lemma_path_i_valid(path, ranking);
//     LinkedBranchRefinement_v::lemma_path_target(path, ranking);
//     assert(post_branch.valid_ranking(post_ranking));
//     LinkedBranchRefinement_v::split_refines_internal(
//         pre_branch, ranking, post_ranking, new_child_addr, path, split_arg,
//     );
//     PivotBranchRefinement_v::lemma_path_target_is_wf(path_i);
//     broadcast use crate::betree::LinkedBranch_v::Refinement_v::lemma_route_ensures;
//     assert(path.target().root().valid_child_index(split_child_idx));
//     assert(split_child_idx == path_i.target().route(pivot) + 1);
//     assert(path_i.target()->children[split_child_idx] == split_child.i_internal(ranking));
//     assert(split_arg.wf(split_child));
//     assert(split_arg.i().wf(split_child.i_internal(ranking))) by { }
//     assert(path_i.target().can_split_child_of_index(split_arg.i())) by { }
//     PivotBranchRefinement_v::split_refines(pre_i, path_i, split_arg.i());
//     assert(post_i == pre_i.split(path_i, split_arg.i()));
//     assert(post_i.i() == pre_i.split(path_i, split_arg.i()).i());
//     assert(pre_i.split(path_i, split_arg.i()).i() == pre_i.i());
//     assert(pre_branch.i() == pre_i);
//     assert(post_branch.i() == post_i);
//     assert(post_branch.i().i() == pre_branch.i().i());
// }
// 
// proof fn linked_seal_preserves_kmmap(branch: LinkedBranch<Summary>, aux_addr: Address, summary: Summary)
//     requires
//         branch.inv(),
//         branch.root() is Index,
//         branch.disk_view.is_fresh(set!{aux_addr}),
//     ensures
//         branch_as_kmmap(branch.seal(aux_addr, summary)) == branch_as_kmmap(branch),
// {
//     let sealed = branch.seal(aux_addr, summary);
//     let ranking = branch.the_ranking();
//     LinkedBranchRefinement_v::i_internal_wf(branch, ranking);
// 
//     assert(sealed.wf()) by {
//         assert(sealed.disk_view.entries.contains_key(sealed.root));
//         assert(!(sealed.root() is Auxiliary));
//         assert(sealed.disk_view.entries_wf());
//         assert(sealed.disk_view.no_dangling_address());
//     }
// 
//     assert(sealed.valid_ranking(ranking)) by {
//         assert forall |addr| #[trigger] ranking.contains_key(addr) && sealed.disk_view.entries.contains_key(addr)
//         implies sealed.disk_view.node_children_respects_rank(ranking, addr) by {
//             if addr == branch.root {
//                 assert(sealed.disk_view.entries.contains_key(branch.root));
//                 assert(sealed.root() is Index);
//                 assert(sealed.root()->children == branch.root()->children);
//                 assert forall |child_idx: int| #[trigger] sealed.root().valid_child_index(child_idx) implies {
//                     &&& ranking.contains_key(sealed.root()->children[child_idx])
//                     &&& ranking[sealed.root()->children[child_idx]] < ranking[addr]
//                 } by {
//                     assert(branch.root().valid_child_index(child_idx));
//                     assert(branch.disk_view.node_children_respects_rank(ranking, addr));
//                 }
//             } else if addr == aux_addr {
//                 assert(sealed.disk_view.entries[addr] is Auxiliary);
//             } else {
//                 assert(branch.disk_view.entries.remove_keys(set!{branch.root, aux_addr}).contains_key(addr));
//                 assert(sealed.disk_view.entries[addr] == branch.disk_view.entries[addr]);
//                 assert forall |child_idx: int| #[trigger] sealed.disk_view.entries[addr].valid_child_index(child_idx) implies {
//                     &&& ranking.contains_key(sealed.disk_view.entries[addr]->children[child_idx])
//                     &&& ranking[sealed.disk_view.entries[addr]->children[child_idx]] < ranking[addr]
//                 } by {
//                     assert(branch.disk_view.entries[addr].valid_child_index(child_idx));
//                     assert(branch.disk_view.node_children_respects_rank(ranking, addr));
//                 }
//             }
//         }
//         assert(ranking.contains_key(sealed.root));
//     }
//     assert(sealed.acyclic());
//     let post_ranking = sealed.the_ranking();
//     let pre_i = branch.i_internal(ranking);
//     let post_i = sealed.i_internal(post_ranking);
// 
//     assert(branch.disk_view.entries.remove_keys(set!{branch.root, aux_addr})
//         == sealed.disk_view.entries.remove_keys(set!{branch.root, aux_addr}));
// 
//     assert forall |i| #[trigger] sealed.root().valid_child_index(i)
//     implies ({
//         &&& branch.root().valid_child_index(i)
//         &&& post_i->children[i] == pre_i->children[i]
//         &&& branch.child_at_idx(i).reachable_addrs_using_ranking(ranking)
//             == sealed.child_at_idx(i).reachable_addrs_using_ranking(post_ranking)
//     }) by {
//         let pre_child = branch.child_at_idx(i);
//         let post_child = sealed.child_at_idx(i);
//         assert(pre_child.reachable_addrs_using_ranking(ranking).disjoint(set!{branch.root, aux_addr})) by {
//             if pre_child.reachable_addrs_using_ranking(ranking).contains(branch.root) {
//                 LinkedBranchRefinement_v::lemma_reachable_child_has_smaller_rank(pre_child, ranking, branch.root);
//             }
//             if pre_child.reachable_addrs_using_ranking(ranking).contains(aux_addr) {
//                 LinkedBranchRefinement_v::lemma_reachable_implies_valid_address(pre_child, ranking, aux_addr);
//             }
//         }
//         LinkedBranchRefinement_v::lemma_reachable_unchanged_implies_same_i_internal(
//             pre_child, ranking, post_child, post_ranking, set!{branch.root, aux_addr},
//         );
//     }
// 
//     assert(post_i->children =~~= pre_i->children);
//     assert(post_i == pre_i);
//     assert(branch.i() == pre_i);
//     assert(sealed.i() == post_i);
//     assert(sealed.i() == branch.i());
//     assert(sealed.i().i() == branch.i().i());
// }
// 
// proof fn allocation_append_refines_to_abstract_map(
//     pre: AllocationBranch,
//     post: AllocationBranch,
//     seq_end: nat,
//     keys: Seq<Key>,
//     msgs: Seq<Message>,
//     path: BranchPath<Summary>,
// )
//     requires
//         pre.inv(),
//         pre.can_append(keys, msgs, path),
//         post == pre.branch_append(keys, msgs, path),
//     ensures
//         post.kmmap_i().wf(),
//         post.kmmap_i() == MsgHistory::map_plus_history(
//             Stamped{ value: pre.kmmap_i(), seq_end },
//             append_puts(seq_end, keys, msgs),
//         ).value,
// {
//     append_puts_wf(seq_end, keys, msgs);
//     MsgHistory::map_plus_history_lemma(
//         Stamped{ value: pre.kmmap_i(), seq_end },
//         append_puts(seq_end, keys, msgs),
//     );
//     let pre_branch = pre.branch.unwrap();
//     let post_branch = post.branch.unwrap();
//     let ranking = pre_branch.the_ranking();
//     let pivot_path = path.i_internal(ranking);
//     let pivot_lbl = PivotAppendLabel{keys, msgs, path: pivot_path};
//     LinkedBranchRefinement_v::append_refines(pre_branch, keys, msgs, path);
//     LinkedBranchRefinement_v::lemma_path_i_internal(path, ranking, keys.last());
//     PivotBranchRefinement_v::append_refines(pre_branch.i(), pivot_lbl);
//     assert(post_branch.i().i()
//         == SimpleBuffer{map: pre_branch.i().i().map.union_prefer_right(Map::new(
//             |key| keys.contains(key),
//             |key| msgs[(crate::betree::PivotBranch_v::Node::Leaf{ keys, msgs }).route(key)],
//         ))});
//     assert forall |key: Key| #[trigger] post.kmmap_i()[key]
//         == MsgHistory::map_plus_history(
//             Stamped{ value: pre.kmmap_i(), seq_end },
//             append_puts(seq_end, keys, msgs),
//         ).value[key] by {
//         allocation_append_updates_kmmap_pointwise(pre, post, keys, msgs, path, key);
//         append_puts_updates_stamped_map_pointwise(Stamped{ value: pre.kmmap_i(), seq_end }, keys, msgs, key);
//     };
//     assert(post.kmmap_i().wf());
//     assert(MsgHistory::map_plus_history(
//         Stamped{ value: pre.kmmap_i(), seq_end },
//         append_puts(seq_end, keys, msgs),
//     ).value.wf());
//     assert(post.kmmap_i().ext_equal(MsgHistory::map_plus_history(
//         Stamped{ value: pre.kmmap_i(), seq_end },
//         append_puts(seq_end, keys, msgs),
//     ).value)) by {
//         assert forall |key: Key|
//             #[trigger] post.kmmap_i().0.contains_key(key)
//             <==> MsgHistory::map_plus_history(
//                 Stamped{ value: pre.kmmap_i(), seq_end },
//                 append_puts(seq_end, keys, msgs),
//             ).value.0.contains_key(key) by {
//         };
//         assert forall |key: Key|
//             #[trigger] post.kmmap_i().0.contains_key(key)
//             implies post.kmmap_i().0[key] == MsgHistory::map_plus_history(
//                 Stamped{ value: pre.kmmap_i(), seq_end },
//                 append_puts(seq_end, keys, msgs),
//             ).value.0[key] by {
//             assert(post.kmmap_i()[key] == MsgHistory::map_plus_history(
//                 Stamped{ value: pre.kmmap_i(), seq_end },
//                 append_puts(seq_end, keys, msgs),
//             ).value[key]);
//         }
//     };
//     post.kmmap_i().ext_equal_is_equality(MsgHistory::map_plus_history(
//         Stamped{ value: pre.kmmap_i(), seq_end },
//         append_puts(seq_end, keys, msgs),
//     ).value);
//     assert(post.kmmap_i() == MsgHistory::map_plus_history(
//         Stamped{ value: pre.kmmap_i(), seq_end },
//         append_puts(seq_end, keys, msgs),
//     ).value);
// }
// 
// proof fn allocation_append_updates_kmmap_pointwise(
//     pre: AllocationBranch,
//     post: AllocationBranch,
//     keys: Seq<Key>,
//     msgs: Seq<Message>,
//     path: BranchPath<Summary>,
//     key: Key,
// )
//     requires
//         pre.inv(),
//         pre.can_append(keys, msgs, path),
//         post == pre.branch_append(keys, msgs, path),
//     ensures
//         post.kmmap_i()[key]
//             == if keys.contains(key) {
//                 normalize_message(msgs[keys.index_of(key)])
//             } else {
//                 pre.kmmap_i()[key]
//             },
// {
//     let pre_branch = pre.branch.unwrap();
//     let post_branch = post.branch.unwrap();
//     let ranking = pre_branch.the_ranking();
//     let pivot_path = path.i_internal(ranking);
//     let pivot_lbl = PivotAppendLabel{keys, msgs, path: pivot_path};
//     LinkedBranchRefinement_v::append_refines(pre_branch, keys, msgs, path);
//     LinkedBranchRefinement_v::lemma_path_i_internal(path, ranking, keys.last());
//     PivotBranchRefinement_v::append_refines(pre_branch.i(), pivot_lbl);
//     let pre_buffer = pre_branch.i().i();
//     let post_buffer =
//         SimpleBuffer{map: pre_buffer.map.union_prefer_right(Map::new(
//             |k| keys.contains(k),
//             |k| msgs[(crate::betree::PivotBranch_v::Node::Leaf{ keys, msgs }).route(k)],
//         ))};
//     assert(post_branch.i().i() == post_buffer);
//     allocation_query_refines_to_kmmap(pre_branch, key);
//     if keys.contains(key) {
//         Key::strictly_sorted_implies_unique(keys);
//         let i = keys.index_of(key);
//         assert(0 <= i < keys.len());
//         assert(keys[i] == key);
//         assert(post_buffer.map.contains_key(key));
//         Key::strictly_sorted_implies_sorted(keys);
//         let r = (crate::betree::PivotBranch_v::Node::Leaf{ keys, msgs }).route(key);
//         Key::largest_lte_ensures(keys, key, r);
//         assert(keys[r] == key);
//         assert(r == i);
//         assert(post_buffer.map[key] == msgs[i]);
//         assert(post_buffer.query(key) == msgs[i]);
//         assert(post.kmmap_i()[key] == normalize_message(msgs[i]));
//     } else {
//         assert(!post_buffer.map.contains_key(key) ==> !pre_buffer.map.contains_key(key)) by { };
//         if pre_buffer.map.contains_key(key) {
//             assert(post_buffer.map[key] == pre_buffer.map[key]);
//             assert(post_buffer.query(key) == pre_buffer.query(key));
//         } else {
//             assert(post_buffer.query(key) == pre_buffer.query(key));
//         }
//         assert(post.kmmap_i()[key] == pre.kmmap_i()[key]);
//     }
// }
// 
// proof fn append_puts_drop_last_lemma(start_lsn: nat, keys: Seq<Key>, msgs: Seq<Message>)
//     requires
//         keys.len() == msgs.len(),
//         0 < keys.len(),
//     ensures
//         append_puts(start_lsn, keys, msgs).discard_recent((start_lsn + keys.len() - 1) as nat)
//             == append_puts(start_lsn, keys.drop_last(), msgs.drop_last()),
// {
//     let history = append_puts(start_lsn, keys, msgs);
//     let prefix = append_puts(start_lsn, keys.drop_last(), msgs.drop_last());
//     let last_lsn = (start_lsn + keys.len() - 1) as nat;
//     assert(history.discard_recent(last_lsn).seq_start == prefix.seq_start);
//     assert(history.discard_recent(last_lsn).seq_end == prefix.seq_end);
//     assert forall |lsn: nat| #[trigger] history.discard_recent(last_lsn).msgs.contains_key(lsn)
//         <==> prefix.msgs.contains_key(lsn) by {
//     };
//     assert forall |lsn: nat| #[trigger] history.discard_recent(last_lsn).msgs.contains_key(lsn)
//         implies history.discard_recent(last_lsn).msgs[lsn] == prefix.msgs[lsn] by {
//         let idx = (lsn - start_lsn) as int;
//         assert(0 <= idx < keys.drop_last().len());
//         assert(keys.drop_last()[idx] == keys[idx]);
//         assert(msgs.drop_last()[idx] == msgs[idx]);
//     };
//     assert(history.discard_recent(last_lsn).ext_equal(prefix));
//     MsgHistory::ext_equal_is_equality();
// }
// 
// proof fn append_puts_updates_stamped_map_pointwise(
//     stamped_map: StampedMap,
//     keys: Seq<Key>,
//     msgs: Seq<Message>,
//     key: Key,
// )
//     requires
//         stamped_map.value.wf(),
//         keys.len() == msgs.len(),
//         Key::is_strictly_sorted(keys),
//     ensures
//         MsgHistory::map_plus_history(stamped_map, append_puts(stamped_map.seq_end, keys, msgs)).value[key]
//             == if keys.contains(key) {
//                 normalize_message(msgs[keys.index_of(key)])
//             } else {
//                 stamped_map.value[key]
//             },
//     decreases keys.len(),
// {
//     let history = append_puts(stamped_map.seq_end, keys, msgs);
//     append_puts_wf(stamped_map.seq_end, keys, msgs);
//     MsgHistory::map_plus_history_lemma(stamped_map, history);
//     if keys.len() == 0 {
//         assert(MsgHistory::map_plus_history(stamped_map, history) == stamped_map);
//         assert(!keys.contains(key));
//         assert(MsgHistory::map_plus_history(stamped_map, history).value[key] == stamped_map.value[key]);
//     } else {
//         let last_lsn = (history.seq_end - 1) as nat;
//         let prefix = append_puts(stamped_map.seq_end, keys.drop_last(), msgs.drop_last());
//         append_puts_drop_last_lemma(stamped_map.seq_end, keys, msgs);
//         append_puts_updates_stamped_map_pointwise(stamped_map, keys.drop_last(), msgs.drop_last(), key);
//         reveal_with_fuel(MsgHistory::apply_to_stamped_map, 2);
//         let sub_map = prefix.apply_to_stamped_map(stamped_map);
//         assert(sub_map == MsgHistory::map_plus_history(stamped_map, prefix));
//         assert(history.discard_recent(last_lsn) == prefix);
//         assert(history.apply_to_stamped_map(stamped_map)
//             == Stamped{
//                 value: sub_map.value.insert(keys.last(), sub_map.value[keys.last()].merge(normalize_message(msgs.last()))),
//                 seq_end: sub_map.seq_end + 1,
//             });
//         if key == keys.last() {
//             assert(history.apply_to_stamped_map(stamped_map).value[key]
//                 == sub_map.value[key].merge(normalize_message(msgs.last())));
//             assert(sub_map.value[key].merge(normalize_message(msgs.last())) == normalize_message(msgs.last()));
//             assert(keys.contains(key));
//             Key::strictly_sorted_implies_unique(keys);
//             let i = keys.index_of(key);
//             assert(0 <= i < keys.len());
//             assert(keys[i] == key);
//             assert(i == keys.len() - 1) by {
//                 if i < keys.len() - 1 {
//                     assert(keys[i] == keys.last());
//                 }
//             }
//             assert(msgs[i] == msgs.last());
//             assert(history.apply_to_stamped_map(stamped_map).value[key]
//                 == normalize_message(msgs[keys.index_of(key)]));
//         } else {
//             assert(history.apply_to_stamped_map(stamped_map).value[key] == sub_map.value[key]);
//             if keys.contains(key) {
//                 Key::strictly_sorted_implies_unique(keys);
//                 let i = keys.index_of(key);
//                 assert(0 <= i < keys.len());
//                 assert(keys[i] == key);
//                 assert(i < keys.len() - 1) by {
//                     if i == keys.len() - 1 {
//                         assert(keys.last() == key);
//                     }
//                 }
//                 assert(keys.drop_last()[i] == key);
//                 assert(keys.drop_last().contains(key));
//                 assert(msgs.drop_last()[i] == msgs[i]);
//                 Key::strictly_sorted_implies_unique(keys.drop_last());
//                 assert(msgs.drop_last()[keys.drop_last().index_of(key)] == msgs[i]);
//                 assert(sub_map.value[key] == normalize_message(msgs.drop_last()[keys.drop_last().index_of(key)]));
//                 assert(history.apply_to_stamped_map(stamped_map).value[key]
//                     == normalize_message(msgs[keys.index_of(key)]));
//             } else {
//                 assert(!keys.drop_last().contains(key));
//                 assert(sub_map.value[key] == stamped_map.value[key]);
//                 assert(history.apply_to_stamped_map(stamped_map).value[key] == stamped_map.value[key]);
//             }
//         }
//     }
// }
// 
// proof fn allocation_seal_preserves_kmmap(pre: AllocationBranch, aux_ptr: Pointer)
//     requires
//         pre.inv(),
//         crate::implementation::ConcreteBranchRefinement_v::allocation_branch_can_seal(pre, aux_ptr),
//     ensures
//         crate::implementation::ConcreteBranchRefinement_v::allocation_branch_seal(pre, aux_ptr).kmmap_i() == pre.kmmap_i(),
// {
//     let post = crate::implementation::ConcreteBranchRefinement_v::allocation_branch_seal(pre, aux_ptr);
//     if aux_ptr is Some {
//         let branch = pre.branch.unwrap();
//         let sealed_branch = branch.seal(aux_ptr.unwrap(), pre.mini_allocator.reserved_aus());
//         assert(post.branch == Some(sealed_branch));
//         assert(!pre.mini_allocator.page_is_reserved(aux_ptr.unwrap()));
//         assert(branch.disk_view.is_fresh(set!{aux_ptr.unwrap()}));
//         linked_seal_preserves_kmmap(branch, aux_ptr.unwrap(), pre.mini_allocator.reserved_aus());
//         assert(post.kmmap_i() == pre.kmmap_i());
//     } else {
//         assert(post.branch == pre.branch);
//         assert(post.kmmap_i() == pre.kmmap_i());
//     }
// }
// 
// proof fn query_step_refines_to_abstract_map(
//     pre: ConcreteBranch::State,
//     post: ConcreteBranch::State,
//     lbl: ConcreteBranch::Label,
//     reads: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
//     needed: Set<Address>,
// )
//     requires
//         pre.wf(),
//         post.wf(),
//         pre.refinement_wf(),
//         post.refinement_wf(),
//         ConcreteBranch::State::query(pre, post, lbl, reads, needed),
//     ensures
//         AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
// {
//     reveal(ConcreteBranch::State::query);
//     reveal(ConcreteBranch::State::next);
//     reveal(ConcreteBranch::State::next_by);
//     reveal(AbstractMap::State::next);
//     reveal(AbstractMap::State::next_by);
// 
//     assert(ConcreteBranch::State::next_by(pre, post, lbl, ConcreteBranch::Step::query(reads, needed)));
//     assert(ConcreteBranch::State::next(pre, post, lbl));
//     ConcreteBranch::State::next_refines(pre, post, lbl);
// 
//     match lbl {
//         ConcreteBranch::Label::Query{key, msg, depth} => {
//             let alloc = pre.i();
//             let branch = pre.overlay_branch().unwrap();
//             assert(alloc.branch == Some(branch));
//             allocation_query_refines_to_kmmap(branch, key);
//             assert(post.cached_branch == pre.cached_branch);
//             assert(post.abstract_map_i() == pre.abstract_map_i());
//             assert(pre.abstract_map_i().stamped_map.value[key] == normalize_message(msg));
//             assert(AbstractMap::State::next_by(
//                 pre.abstract_map_i(),
//                 post.abstract_map_i(),
//                 pre.label_to_abstract_map(lbl),
//                 AbstractMap::Step::query(),
//             ));
//         }
//         _ => { assert(false); }
//     }
// }
// 
// proof fn append_step_refines_to_abstract_map(
//     pre: ConcreteBranch::State,
//     post: ConcreteBranch::State,
//     lbl: ConcreteBranch::Label,
//     reads: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
//     writes: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
//     needed: Set<Address>,
//     new_cache: crate::implementation::Cache_v::Cache::State,
// )
//     requires
//         pre.wf(),
//         post.wf(),
//         pre.refinement_wf(),
//         post.refinement_wf(),
//         ConcreteBranch::State::append(pre, post, lbl, reads, writes, needed, new_cache),
//     ensures
//         AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
// {
//     reveal(ConcreteBranch::State::append);
//     reveal(ConcreteBranch::State::next);
//     reveal(ConcreteBranch::State::next_by);
//     reveal(AbstractMap::State::next);
//     reveal(AbstractMap::State::next_by);
// 
//     assert(ConcreteBranch::State::next_by(pre, post, lbl, ConcreteBranch::Step::append(reads, writes, needed, new_cache)));
//     assert(ConcreteBranch::State::next(pre, post, lbl));
//     ConcreteBranch::State::next_refines(pre, post, lbl);
// 
//     match lbl {
//         ConcreteBranch::Label::Append{keys, msgs, depth} => {
//             assert(keys.len() > 0);
//             let alloc = pre.i();
//             let first_key = keys[0];
//             let branch = pre.overlay_branch().unwrap();
//             assert(alloc.branch == Some(branch));
//             let path = BranchPath{branch, key: first_key, depth};
//             append_puts_wf(pre.cached_branch.seq_end, keys, msgs);
//             allocation_append_refines_to_abstract_map(alloc, post.i(), pre.cached_branch.seq_end, keys, msgs, path);
//             assert(post.cached_branch.seq_end == pre.cached_branch.seq_end + keys.len());
//             MsgHistory::map_plus_history_lemma(
//                 pre.abstract_map_i().stamped_map,
//                 append_puts(pre.cached_branch.seq_end, keys, msgs),
//             );
//             assert(post.abstract_map_i().stamped_map.value
//                 == MsgHistory::map_plus_history(pre.abstract_map_i().stamped_map, append_puts(pre.cached_branch.seq_end, keys, msgs)).value);
//             assert(post.abstract_map_i().stamped_map.seq_end
//                 == MsgHistory::map_plus_history(pre.abstract_map_i().stamped_map, append_puts(pre.cached_branch.seq_end, keys, msgs)).seq_end);
//             assert(post.abstract_map_i().stamped_map
//                 == MsgHistory::map_plus_history(pre.abstract_map_i().stamped_map, append_puts(pre.cached_branch.seq_end, keys, msgs)));
//             assert(AbstractMap::State::next_by(
//                 pre.abstract_map_i(),
//                 post.abstract_map_i(),
//                 pre.label_to_abstract_map(lbl),
//                 AbstractMap::Step::put(),
//             ));
//         }
//         _ => { assert(false); }
//     }
// }
// 
// proof fn grow_step_refines_to_abstract_map(
//     pre: ConcreteBranch::State,
//     post: ConcreteBranch::State,
//     lbl: ConcreteBranch::Label,
//     reads: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
//     writes: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
//     new_cache: crate::implementation::Cache_v::Cache::State,
// )
//     requires
//         pre.wf(),
//         post.wf(),
//         pre.refinement_wf(),
//         post.refinement_wf(),
//         ConcreteBranch::State::grow(pre, post, lbl, reads, writes, new_cache),
//     ensures
//         AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
// {
//     reveal(ConcreteBranch::State::grow);
//     reveal(ConcreteBranch::State::next);
//     reveal(ConcreteBranch::State::next_by);
//     reveal(AbstractMap::State::next);
//     reveal(AbstractMap::State::next_by);
// 
//     assert(ConcreteBranch::State::next_by(pre, post, lbl, ConcreteBranch::Step::grow(reads, writes, new_cache)));
//     assert(ConcreteBranch::State::next(pre, post, lbl));
//     ConcreteBranch::State::next_refines(pre, post, lbl);
// 
//     match lbl {
//         ConcreteBranch::Label::Grow{new_root_addr} => {
//             let alloc = pre.i();
//             let branch = pre.overlay_branch().unwrap();
//             assert(alloc.branch == Some(branch));
//             allocation_grow_preserves_kmmap(alloc, new_root_addr);
//             assert(post.cached_branch.seq_end == pre.cached_branch.seq_end);
//             assert(post.abstract_map_i() == pre.abstract_map_i());
//             assert(AbstractMap::State::next_by(
//                 pre.abstract_map_i(),
//                 post.abstract_map_i(),
//                 pre.label_to_abstract_map(lbl),
//                 AbstractMap::Step::internal(),
//             ));
//         }
//         _ => { assert(false); }
//     }
// }
// 
// proof fn split_step_refines_to_abstract_map(
//     pre: ConcreteBranch::State,
//     post: ConcreteBranch::State,
//     lbl: ConcreteBranch::Label,
//     reads: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
//     writes: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
//     needed: Set<Address>,
//     new_cache: crate::implementation::Cache_v::Cache::State,
// )
//     requires
//         pre.wf(),
//         post.wf(),
//         pre.refinement_wf(),
//         post.refinement_wf(),
//         ConcreteBranch::State::split(pre, post, lbl, reads, writes, needed, new_cache),
//     ensures
//         AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
// {
//     reveal(ConcreteBranch::State::split);
//     reveal(ConcreteBranch::State::next);
//     reveal(ConcreteBranch::State::next_by);
//     reveal(AbstractMap::State::next);
//     reveal(AbstractMap::State::next_by);
// 
//     assert(ConcreteBranch::State::next_by(pre, post, lbl, ConcreteBranch::Step::split(reads, writes, needed, new_cache)));
//     assert(ConcreteBranch::State::next(pre, post, lbl));
//     ConcreteBranch::State::next_refines(pre, post, lbl);
// 
//     match lbl {
//         ConcreteBranch::Label::Split{new_child_addr, pivot, depth, split_arg} => {
//             let alloc = pre.i();
//             let branch = pre.overlay_branch().unwrap();
//             assert(alloc.branch == Some(branch));
//             let path = BranchPath{branch, key: pivot, depth};
//             allocation_split_preserves_kmmap(alloc, new_child_addr, path, split_arg);
//             assert(post.cached_branch.seq_end == pre.cached_branch.seq_end);
//             assert(post.abstract_map_i() == pre.abstract_map_i());
//             assert(AbstractMap::State::next_by(
//                 pre.abstract_map_i(),
//                 post.abstract_map_i(),
//                 pre.label_to_abstract_map(lbl),
//                 AbstractMap::Step::internal(),
//             ));
//         }
//         _ => { assert(false); }
//     }
// }
// 
// proof fn seal_step_refines_to_abstract_map(
//     pre: ConcreteBranch::State,
//     post: ConcreteBranch::State,
//     lbl: ConcreteBranch::Label,
//     reads: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
//     writes: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
//     new_cache: crate::implementation::Cache_v::Cache::State,
// )
//     requires
//         pre.wf(),
//         post.wf(),
//         pre.refinement_wf(),
//         post.refinement_wf(),
//         ConcreteBranch::State::seal(pre, post, lbl, reads, writes, new_cache),
//     ensures
//         AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
// {
//     reveal(ConcreteBranch::State::seal);
//     reveal(ConcreteBranch::State::next);
//     reveal(ConcreteBranch::State::next_by);
//     reveal(AbstractMap::State::next);
//     reveal(AbstractMap::State::next_by);
// 
//     assert(ConcreteBranch::State::next_by(pre, post, lbl, ConcreteBranch::Step::seal(reads, writes, new_cache)));
//     assert(ConcreteBranch::State::next(pre, post, lbl));
//     ConcreteBranch::State::next_refines(pre, post, lbl);
// 
//     match lbl {
//         ConcreteBranch::Label::Seal{aux_ptr} => {
//             let alloc = pre.i();
//             if alloc.branch is Some {
//                 assert(pre.overlay_branch() == alloc.branch);
//             }
//             allocation_seal_preserves_kmmap(alloc, aux_ptr);
//             assert(post.cached_branch.seq_end == pre.cached_branch.seq_end);
//             assert(post.abstract_map_i() == pre.abstract_map_i());
//             assert(AbstractMap::State::next_by(
//                 pre.abstract_map_i(),
//                 post.abstract_map_i(),
//                 pre.label_to_abstract_map(lbl),
//                 AbstractMap::Step::internal(),
//             ));
//         }
//         _ => { assert(false); }
//     }
// }
// 
// proof fn internal_cache_step_refines_to_abstract_map(
//     pre: ConcreteBranch::State,
//     post: ConcreteBranch::State,
//     lbl: ConcreteBranch::Label,
//     new_cache: crate::implementation::Cache_v::Cache::State,
// )
//     requires
//         pre.wf(),
//         post.wf(),
//         pre.refinement_wf(),
//         post.refinement_wf(),
//         ConcreteBranch::State::internal_cache(pre, post, lbl, new_cache),
//     ensures
//         AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
// {
//     reveal(ConcreteBranch::State::internal_cache);
//     reveal(ConcreteBranch::State::next);
//     reveal(ConcreteBranch::State::next_by);
//     reveal(AbstractMap::State::next);
//     reveal(AbstractMap::State::next_by);
//     assert(ConcreteBranch::State::next_by(pre, post, lbl, ConcreteBranch::Step::internal_cache(new_cache)));
//     assert(ConcreteBranch::State::next(pre, post, lbl));
//     ConcreteBranch::State::next_refines(pre, post, lbl);
//     assert(post.abstract_map_i() == pre.abstract_map_i());
//     assert(AbstractMap::State::next_by(
//         pre.abstract_map_i(),
//         post.abstract_map_i(),
//         pre.label_to_abstract_map(lbl),
//         AbstractMap::Step::internal(),
//     ));
// }
// 
// proof fn internal_disk_step_refines_to_abstract_map(
//     pre: ConcreteBranch::State,
//     post: ConcreteBranch::State,
//     lbl: ConcreteBranch::Label,
//     new_disk: crate::spec::AsyncDisk_t::AsyncDisk::State,
// )
//     requires
//         pre.wf(),
//         post.wf(),
//         pre.refinement_wf(),
//         post.refinement_wf(),
//         ConcreteBranch::State::internal_disk(pre, post, lbl, new_disk),
//     ensures
//         AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
// {
//     reveal(ConcreteBranch::State::internal_disk);
//     reveal(ConcreteBranch::State::next);
//     reveal(ConcreteBranch::State::next_by);
//     reveal(AbstractMap::State::next);
//     reveal(AbstractMap::State::next_by);
//     assert(ConcreteBranch::State::next_by(pre, post, lbl, ConcreteBranch::Step::internal_disk(new_disk)));
//     assert(ConcreteBranch::State::next(pre, post, lbl));
//     ConcreteBranch::State::next_refines(pre, post, lbl);
//     assert(post.i() == pre.i());
//     assert(post.cached_branch == pre.cached_branch);
//     assert(post.abstract_map_i().stamped_map.seq_end == pre.abstract_map_i().stamped_map.seq_end);
//     assert(post.abstract_map_i().stamped_map.value == pre.abstract_map_i().stamped_map.value);
//     assert(post.abstract_map_i() == pre.abstract_map_i());
//     assert(AbstractMap::State::next_by(
//         pre.abstract_map_i(),
//         post.abstract_map_i(),
//         pre.label_to_abstract_map(lbl),
//         AbstractMap::Step::internal(),
//     ));
// }
// 
// proof fn cache_disk_ops_step_refines_to_abstract_map(
//     pre: ConcreteBranch::State,
//     post: ConcreteBranch::State,
//     lbl: ConcreteBranch::Label,
//     new_cache: crate::implementation::Cache_v::Cache::State,
//     new_disk: crate::spec::AsyncDisk_t::AsyncDisk::State,
//     cache_requests: Set<crate::spec::AsyncDisk_t::DiskRequest>,
//     cache_responses: Map<Address, crate::spec::AsyncDisk_t::DiskResponse>,
//     disk_requests: Map<crate::spec::MapSpec_t::ID, crate::spec::AsyncDisk_t::DiskRequest>,
//     disk_responses: Map<crate::spec::MapSpec_t::ID, crate::spec::AsyncDisk_t::DiskResponse>,
// )
//     requires
//         pre.wf(),
//         post.wf(),
//         pre.refinement_wf(),
//         post.refinement_wf(),
//         ConcreteBranch::State::cache_disk_ops(
//             pre,
//             post,
//             lbl,
//             new_cache,
//             new_disk,
//             cache_requests,
//             cache_responses,
//             disk_requests,
//             disk_responses,
//         ),
//     ensures
//         AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
// {
//     reveal(ConcreteBranch::State::cache_disk_ops);
//     reveal(ConcreteBranch::State::next);
//     reveal(ConcreteBranch::State::next_by);
//     reveal(AbstractMap::State::next);
//     reveal(AbstractMap::State::next_by);
//     assert(ConcreteBranch::State::next_by(
//         pre,
//         post,
//         lbl,
//         ConcreteBranch::Step::cache_disk_ops(
//             new_cache,
//             new_disk,
//             cache_requests,
//             cache_responses,
//             disk_requests,
//             disk_responses,
//         ),
//     ));
//     assert(ConcreteBranch::State::next(pre, post, lbl));
//     ConcreteBranch::State::next_refines(pre, post, lbl);
//     assert(post.abstract_map_i() == pre.abstract_map_i());
//     assert(AbstractMap::State::next_by(
//         pre.abstract_map_i(),
//         post.abstract_map_i(),
//         pre.label_to_abstract_map(lbl),
//         AbstractMap::Step::internal(),
//     ));
// }
// 
// pub proof fn next_refines_to_abstract_map(
//     pre: ConcreteBranch::State,
//     post: ConcreteBranch::State,
//     lbl: ConcreteBranch::Label,
// )
//     requires
//         pre.wf(),
//         post.wf(),
//         pre.refinement_wf(),
//         post.refinement_wf(),
//         ConcreteBranch::State::next(pre, post, lbl),
//     ensures
//         AbstractMap::State::next(pre.abstract_map_i(), post.abstract_map_i(), pre.label_to_abstract_map(lbl)),
// {
//     reveal(ConcreteBranch::State::next);
//     reveal(ConcreteBranch::State::next_by);
// 
//     let step = choose |step| ConcreteBranch::State::next_by(pre, post, lbl, step);
//     match step {
//         ConcreteBranch::Step::query(reads, needed) =>
//             query_step_refines_to_abstract_map(pre, post, lbl, reads, needed),
//         ConcreteBranch::Step::append(reads, writes, needed, new_cache) =>
//             append_step_refines_to_abstract_map(pre, post, lbl, reads, writes, needed, new_cache),
//         ConcreteBranch::Step::grow(reads, writes, new_cache) =>
//             grow_step_refines_to_abstract_map(pre, post, lbl, reads, writes, new_cache),
//         ConcreteBranch::Step::split(reads, writes, needed, new_cache) =>
//             split_step_refines_to_abstract_map(pre, post, lbl, reads, writes, needed, new_cache),
//         ConcreteBranch::Step::seal(reads, writes, new_cache) =>
//             seal_step_refines_to_abstract_map(pre, post, lbl, reads, writes, new_cache),
//         ConcreteBranch::Step::internal_cache(new_cache) =>
//             internal_cache_step_refines_to_abstract_map(pre, post, lbl, new_cache),
//         ConcreteBranch::Step::internal_disk(new_disk) =>
//             internal_disk_step_refines_to_abstract_map(pre, post, lbl, new_disk),
//         ConcreteBranch::Step::cache_disk_ops(
//             new_cache,
//             new_disk,
//             cache_requests,
//             cache_responses,
//             disk_requests,
//             disk_responses,
//         ) =>
//             cache_disk_ops_step_refines_to_abstract_map(
//                 pre,
//                 post,
//                 lbl,
//                 new_cache,
//                 new_disk,
//                 cache_requests,
//                 cache_responses,
//                 disk_requests,
//                 disk_responses,
//             ),
//         _ => { }
//     }
// }
// 
// } // verus!
