// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Cache and query proof utilities shared by the active bulk-branch path.

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::assert_sets_equal;

use crate::allocation_layer::BranchTypes_v::Summary;
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::LinkedBranch_v::{
    LinkedBranch, Refinement_v as LinkedBranchRefinement,
};
use crate::betree::PivotBranchRefinement_v::{
    self as PivotBranchRefinement, QueryLabel,
};
use crate::disk::GenericDisk_v::{AU, Address, Ranking};
use crate::implementation::CachedBranch_v::{
    LoadedBranch, LoadedPathReceipt, receipt_valid_implies_tail_valid,
};
use crate::implementation::CachingDiskBranchBetree_v::to_branch_nodes;
use crate::implementation::CachingDisk_v::{CachingDisk, PageStatus};
use crate::spec::AsyncDisk_t::RawPage;
use crate::spec::KeyType_t::Key;

verus! {

pub open spec fn mini_allocator_allocated_addrs(
    mini_allocator: MiniAllocator,
) -> Set<Address>
{
    Set::new(|addr: Address| {
        &&& mini_allocator.allocs.contains_key(addr.au)
        &&& (mini_allocator.allocs[addr.au].allocated
            + mini_allocator.allocs[addr.au].allocated).contains(addr)
    })
}

pub open spec fn active_loaded_nodes_of(
    disk: CachingDisk::State,
    mini_allocator: MiniAllocator,
) -> LoadedBranch
{
    let nodes = to_branch_nodes(disk.visible());
    nodes.restrict(Set::new(|addr: Address|
        nodes.contains_key(addr)
            && mini_allocator_allocated_addrs(mini_allocator).contains(addr)
    ))
}

pub proof fn active_loaded_nodes_follow_readable_writes(
    pre_disk: CachingDisk::State,
    post_disk: CachingDisk::State,
    mini_allocator: MiniAllocator,
    writes: Map<Address, RawPage>,
)
    requires
        writes.dom() <= mini_allocator_allocated_addrs(mini_allocator),
        forall |addr: Address| #[trigger] mini_allocator_allocated_addrs(mini_allocator).contains(addr) ==> {
            &&& post_disk.visible().contains_key(addr)
                == pre_disk.visible().union_prefer_right(writes).contains_key(addr)
            &&& post_disk.visible().contains_key(addr) ==> {
                post_disk.visible()[addr]
                    == pre_disk.visible().union_prefer_right(writes)[addr]
            }
        },
    ensures
        active_loaded_nodes_of(post_disk, mini_allocator)
            == active_loaded_nodes_of(pre_disk, mini_allocator)
                .union_prefer_right(to_branch_nodes(writes)),
{
    let allocated = mini_allocator_allocated_addrs(mini_allocator);
    let post_nodes = to_branch_nodes(post_disk.visible());
    let pre_nodes = to_branch_nodes(pre_disk.visible());
    let write_nodes = to_branch_nodes(writes);
    assert_maps_equal!(
        active_loaded_nodes_of(post_disk, mini_allocator),
        active_loaded_nodes_of(pre_disk, mini_allocator).union_prefer_right(write_nodes),
        addr => {
            if active_loaded_nodes_of(post_disk, mini_allocator).contains_key(addr) {
                assert(post_nodes.contains_key(addr));
                assert(allocated.contains(addr));
                assert(pre_disk.visible().union_prefer_right(writes).contains_key(addr));
                if writes.contains_key(addr) {
                    assert(write_nodes.contains_key(addr));
                    assert(post_disk.visible()[addr] == writes[addr]);
                    assert(post_nodes[addr] == write_nodes[addr]);
                } else {
                    assert(pre_disk.visible().contains_key(addr));
                    assert(pre_nodes.contains_key(addr));
                    assert(active_loaded_nodes_of(pre_disk, mini_allocator).contains_key(addr));
                    assert(post_disk.visible()[addr] == pre_disk.visible()[addr]);
                    assert(post_nodes[addr] == pre_nodes[addr]);
                }
            }
            if active_loaded_nodes_of(pre_disk, mini_allocator)
                .union_prefer_right(write_nodes).contains_key(addr) {
                if write_nodes.contains_key(addr) {
                    assert(writes.contains_key(addr));
                    assert(mini_allocator_allocated_addrs(mini_allocator).contains(addr));
                    assert(post_disk.visible().contains_key(addr));
                    assert(post_disk.visible()[addr] == writes[addr]);
                    assert(post_nodes.contains_key(addr));
                    assert(post_nodes[addr] == write_nodes[addr]);
                    assert(active_loaded_nodes_of(post_disk, mini_allocator).contains_key(addr));
                } else {
                    assert(active_loaded_nodes_of(pre_disk, mini_allocator).contains_key(addr));
                    assert(pre_nodes.contains_key(addr));
                    assert(allocated.contains(addr));
                    assert(pre_disk.visible().contains_key(addr));
                    assert(post_disk.visible().contains_key(addr));
                    assert(post_disk.visible()[addr] == pre_disk.visible()[addr]);
                    assert(post_nodes.contains_key(addr));
                    assert(post_nodes[addr] == pre_nodes[addr]);
                    assert(active_loaded_nodes_of(post_disk, mini_allocator).contains_key(addr));
                }
            }
        }
    );
}

pub proof fn mini_allocator_allocated_addrs_subset_all_aus(mini_allocator: MiniAllocator)
    ensures
        forall |addr: Address| #[trigger] mini_allocator_allocated_addrs(mini_allocator).contains(addr)
            ==> mini_allocator.all_aus().contains(addr.au),
{
}

pub proof fn mini_allocator_add_aus_preserves_allocated_addrs(
    mini_allocator: MiniAllocator,
    aus: Set<AU>,
)
    requires
        mini_allocator.wf(),
        aus.disjoint(mini_allocator.all_aus()),
    ensures
        mini_allocator_allocated_addrs(mini_allocator.add_aus(aus))
            == mini_allocator_allocated_addrs(mini_allocator),
{
    assert_sets_equal!(
        mini_allocator_allocated_addrs(mini_allocator.add_aus(aus)),
        mini_allocator_allocated_addrs(mini_allocator),
        addr => {
            if mini_allocator_allocated_addrs(mini_allocator.add_aus(aus)).contains(addr) {
                assert(mini_allocator.add_aus(aus).allocs.contains_key(addr.au));
                if mini_allocator.allocs.contains_key(addr.au) {
                    assert(mini_allocator.add_aus(aus).allocs[addr.au]
                        == mini_allocator.allocs[addr.au]);
                } else {
                    assert(aus.contains(addr.au));
                    assert(mini_allocator.add_aus(aus).allocs[addr.au]
                        == crate::allocation_layer::MiniAllocator_v::PageAllocator::new(addr.au));
                    assert(false);
                }
            }
            if mini_allocator_allocated_addrs(mini_allocator).contains(addr) {
                assert(mini_allocator.allocs.contains_key(addr.au));
                assert(mini_allocator.all_aus().contains(addr.au));
                assert(!aus.contains(addr.au));
                assert(mini_allocator.add_aus(aus).allocs[addr.au]
                    == mini_allocator.allocs[addr.au]);
            }
        }
    );
}

pub proof fn child_branch_inv_internal_from_parent(
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
        QueryLabel { key, msg: branch_i.query(key) },
    );
    PivotBranchRefinement::query_refines_to_routed_child(
        branch_i,
        QueryLabel { key, msg: branch_i.query(key) },
    );
    PivotBranchRefinement::query_refines(
        child_i,
        QueryLabel { key, msg: child_i.query(key) },
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

pub proof fn query_read_node_matches_visible(
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

pub proof fn receipt_query_matches_branch_query(
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

} // verus!
