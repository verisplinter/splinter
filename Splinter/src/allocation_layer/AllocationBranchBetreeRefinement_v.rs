// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]
use vstd::prelude::*;
//use vstd::prelude_macros::*;
use vstd::prelude::*;
use vstd::{map::*, seq_lib::*, set_lib::*, multiset::*};
use vstd::map_lib::lemma_values_finite;

use crate::spec::KeyType_t::Key;
use crate::disk::GenericDisk_v::{Address, Ranking, addrs_closed, to_aus_additive, to_aus_domain};
use crate::betree::Buffer_v::{Buffer, SimpleBuffer};
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::SplitRequest_v::SplitRequest;
use crate::betree::LinkedSeq_v::LinkedSeq;
use crate::betree::LinkedBetree_v::{Addrs, BetreeNode, LinkedBetree, LinkedBetreeVars, Path, PathAddrs, QueryReceipt, QueryReceiptLine, SplitAddrs, TwoAddrs};
use crate::betree::LinkedBranch_v::Refinement_v;
use crate::betree::Utils_v::{lemma_subset_union_seq_of_sets, lemma_union_set_of_sets_subset};
use crate::betree::PivotBranchRefinement_v;
use crate::allocation_layer::Likes_v::{Likes, restrict_domain_au, restrict_domain_au_ensures, to_au_likes, to_au_likes_domain, to_au_likes_singleton};
use crate::allocation_layer::LikesBetree_v::{Likeable, LikesBetree, compact_add_buffers, split_add_buffers, split_discard_betree};
use crate::allocation_layer::AllocationBetree_v::AllocationBetree;
use crate::allocation_layer::BranchTypes_v::BranchNode;
use crate::allocation_layer::AllocationBulkBranch_v::AllocationBulkBranch;
use crate::allocation_layer::AllocationBranchBetree_v::{AllocationBranchBetree, CompactorInput, Internal, read_ref_aus, summary_aus};

verus! {

impl AllocationBranchBetree::Label {
    pub open spec(checked) fn i(self) -> AllocationBetree::Label
    {
        match self {
            Self::Label{linked_lbl} => { AllocationBetree::Label::Label{linked_lbl} }
            Self::Internal =>  { AllocationBetree::Label::Label{linked_lbl: LinkedBetreeVars::Label::Internal{}} }
        }
    }
} // end impl AllocationBranchBetree::Label

impl<T> LinkedBetree<T> {
    proof fn same_dv_same_buffer_likes<A>(self, other: LinkedBetree<A>, betree_likes: Likes)
        requires self.dv == other.dv
        ensures self.buffer_likes(betree_likes) == other.buffer_likes(betree_likes)
        decreases betree_likes.len()
    {
        if betree_likes.len() > 0 {
            let addr = betree_likes.choose();
            self.same_dv_same_buffer_likes(other, betree_likes.remove(addr));
        }
    }
}

impl Path<BranchNode> {
    pub open spec fn i(self) -> Path<SimpleBuffer>
    {
        Path{
            linked: self.linked.i(),
            key: self.key,
            depth: self.depth,
        }
    }

    proof fn i_ensures(self)
        requires self.valid(),
        ensures
            self.i().valid(), 
            self.addrs_on_path() == self.i().addrs_on_path(),
            self.target().i() == self.i().target(),
        decreases self.depth
    {
        assert(self.i().linked.valid_ranking(self.linked.the_ranking())); // witness
        if self.depth > 0 {
            self.subpath().i_ensures();
        }
    }

    proof fn i_substitute_ensures(self, replacement: LinkedBetree<BranchNode>, path_addrs: PathAddrs)
        requires self.can_substitute(replacement, path_addrs)
        ensures self.substitute(replacement, path_addrs).dv == self.i().substitute(replacement.i(), path_addrs).dv
        decreases self.depth
    {
        if self.depth > 0 {
            self.subpath().i_substitute_ensures(replacement, path_addrs.subrange(1, path_addrs.len() as int));
        }
    }
}

impl<T> Path<T> {
    proof fn substitute_same_dv_root(
        self,
        left: LinkedBetree<T>,
        right: LinkedBetree<T>,
        path_addrs: PathAddrs,
    )
        requires
            self.depth == path_addrs.len(),
            left.dv == right.dv,
            left.root == right.root,
        ensures
            self.substitute(left, path_addrs).dv
                == self.substitute(right, path_addrs).dv,
            self.substitute(left, path_addrs).root
                == self.substitute(right, path_addrs).root,
        decreases self.depth,
    {
        if self.depth > 0 {
            self.subpath().substitute_same_dv_root(
                left,
                right,
                path_addrs.subrange(1, path_addrs.len() as int),
            );
        }
    }
}

impl<T> LinkedBetree<T>{
    proof fn children_likes_ignores_buffer_dv<A>(self, other: LinkedBetree<A>, ranking: Ranking, start: nat)
    requires 
        self.has_root(),
        self.valid_ranking(ranking),
        self.root == other.root,
        self.dv == other.dv,
        start <= self.root().children.len()
    ensures
        self.children_likes(ranking, start) == other.children_likes(ranking, start)
    decreases self.get_rank(ranking), self.root().children.len() - start
    {
        if start < self.root().children.len() {
            assert(self.root().valid_child_index(start)); // trigger
            self.child_at_idx(start).tree_likes_ignores_buffer_dv(other.child_at_idx(start), ranking);
            self.children_likes_ignores_buffer_dv(other, ranking, start+1);
        }
    }

    proof fn tree_likes_ignores_buffer_dv<A>(self, other: LinkedBetree<A>, ranking: Ranking)
    requires self.valid_ranking(ranking), self.root == other.root, self.dv == other.dv,
    ensures self.tree_likes(ranking) == other.tree_likes(ranking)
    decreases self.get_rank(ranking)
    {
        if self.has_root() {
            self.children_likes_ignores_buffer_dv(other, ranking, 0);
        }
    }

    proof fn buffer_likes_ignores_buffer_dv<A>(self, other: LinkedBetree<A>, betree_likes: Likes)
    requires self.dv == other.dv
    ensures self.buffer_likes(betree_likes) == other.buffer_likes(betree_likes)
    decreases betree_likes.len()
    {
        if betree_likes.len() > 0 {
            let addr = betree_likes.choose();
            self.buffer_likes_ignores_buffer_dv(other, betree_likes.remove(addr));
        }
    }

    pub proof fn transitive_likes_ignores_buffer_dv<A>(self, other: LinkedBetree<A>)
        requires 
            self.acyclic(), 
            self.dv == other.dv,
            self.root == other.root,
        ensures 
            self.transitive_likes() == other.transitive_likes()
    {
        let ranking = self.the_ranking();
        assert(other.valid_ranking(ranking)); // trigger
        self.tree_likes_ignores_buffer_dv(other, ranking);
        other.tree_likes_ignore_ranking(ranking, other.the_ranking());
        self.buffer_likes_ignores_buffer_dv(other, self.tree_likes(ranking));
    }
}

impl LinkedBetree<BranchNode> {
    pub open spec(checked) fn i(self) -> LinkedBetree<SimpleBuffer>
    {
        LinkedBetree{
            root: self.root,
            dv: self.dv,
            buffer_dv: self.buffer_dv.i(),
        }
    }

    pub proof fn i_valid(self) 
    requires 
        self.inv()
    ensures 
        self.i().inv(),
        self.transitive_likes() == self.i().transitive_likes(),
        self.transitive_likes().1.dom() == self.reachable_buffer_addrs(),
        self.i().transitive_likes().1.dom() == self.i().reachable_buffer_addrs(),
    {
        let i_linked = self.i();
        let ranking = self.the_ranking();

        assert(i_linked.valid_ranking(ranking)); // witness
        self.transitive_likes_ignores_buffer_dv(i_linked);

        self.tree_likes_domain(ranking);
        self.buffer_likes_domain(self.tree_likes(ranking));
        i_linked.tree_likes_domain(i_linked.the_ranking());
        i_linked.buffer_likes_domain(i_linked.tree_likes(i_linked.the_ranking()));
    }
}

impl LinkedBetreeVars::State<BranchNode> {
    pub open spec(checked) fn i(self) -> LinkedBetreeVars::State<SimpleBuffer>
    {
        LinkedBetreeVars::State{
            memtable: self.memtable,
            linked: self.linked.i(),
        }  
    }
}

impl BufferDisk<BranchNode> {
    // to refine query refines, we need to know that addr get banch is inv
    proof fn query_refines(self, buffer: Address, k: Key)
        requires self.get_branch(buffer).inv()
        ensures self.query(buffer, k) == self.i().query(buffer, k)
    {
        let branch = self.get_branch(buffer);
        Refinement_v::query_refines(branch, k, self.query(buffer, k));

        let pivot_branch = branch.i();
        Refinement_v::i_internal_wf(branch, branch.the_ranking());

        let lbl = PivotBranchRefinement_v::QueryLabel{key: k, msg: self.query(buffer, k)};
        PivotBranchRefinement_v::query_refines(pivot_branch, lbl);
    }

    proof fn query_from_refines(self, buffers: LinkedSeq, k: Key, start: int)
        requires 
            0 <= start <= buffers.len(),
            forall |i| start <= i < buffers.len() ==> #[trigger] self.get_branch(buffers[i]).inv()
        ensures 
            self.query_from(buffers, k, start) == self.i().query_from(buffers, k, start)
        decreases buffers.len() - start 
    {
        if start < buffers.len() {
            self.query_refines(buffers[start], k);
            self.query_from_refines(buffers, k, start+1);
        }
    }

    proof fn buffer_contains_refines(self, addr: Address, k: Key)
        requires self.get_branch(addr).inv()
        ensures self.buffer_contains(addr, k) == self.i().buffer_contains(addr, k)
    {
        let branch = self.get_branch(addr);
        let ranking = branch.the_ranking();
        let result = self.entries[addr].linked_contains(self, addr, k);

        Refinement_v::i_wf(branch);
        Refinement_v::contains_internal_refines(branch, ranking, k, result);
        PivotBranchRefinement_v::contains_refines(branch.i(), k, result);
    }

    pub proof fn i_preserves_sub_disk(self, other: Self)
        requires 
            self.to_branch_disk().wf(),
            other.to_branch_disk().wf(),
            self.is_sub_disk(other),
        ensures 
            self.i().is_sub_disk(other.i())
    {
        assert forall |addr| self.entries.contains_key(addr) 
        implies self.i().entries[addr] == #[trigger] other.i().entries[addr]
        by {
            let branch = self.get_branch(addr);
            let other_branch = other.get_branch(addr);
            assert(self.entries[addr] == other.entries[addr]); // trigger
            assert(self.i().entries[addr] == branch.i().i()); // trigger
            assert(other.i().entries[addr] == other_branch.i().i()); // trigger

            if branch.has_root() {
                if branch.acyclic() {
                    let finite_ranking = branch.the_ranking().restrict(branch.disk_view.entries.dom());
                    assert(other_branch.valid_ranking(finite_ranking)); // trigger
                    branch.subdisk_same_i_internal(branch.the_ranking(), other_branch, other_branch.the_ranking());
                } else {
                    if other_branch.acyclic() {
                        assert(branch.valid_ranking(other_branch.the_ranking())); // trigger
                    }
                }
            } else {
            }
        }
    }
}

impl<T: Buffer> QueryReceipt<T> {
    proof fn receipt_line_root_is_reachable(self, i: int)
    requires self.valid(), 0 <= i < self.lines.len(),
    ensures forall |j| i <= j < self.lines.len()-1 ==>
        #[trigger] self.lines[i].linked.reachable_betree_addrs().contains(self.lines[j].linked.root.unwrap())
    decreases self.lines.len() - i
    {
        let linked = self.lines[i].linked;
        let ranking = linked.the_ranking();
        assert(linked.acyclic()); // trigger

        if i < self.lines.len() - 1 {
            assert(self.node(i).key_in_domain(self.key)); // trigger
            let r = linked.root().pivots.route(self.key) as nat;
            linked.root().pivots.route_lemma(self.key);
            linked.reachable_betree_addrs_using_ranking_closed(ranking);

            assert forall |j| i < j < self.lines.len()-1
            implies #[trigger] linked.reachable_betree_addrs().contains(self.lines[j].linked.root.unwrap())
            by {
                linked.reachable_betree_addrs_using_ranking_recur_lemma(ranking, 0);
                assert(linked.child_at_idx(r).reachable_betree_addrs_using_ranking(ranking) <= linked.reachable_betree_addrs()); // trigger

                self.receipt_line_root_is_reachable(i+1);
                assert(self.lines[i+1].linked.acyclic()); // trigger

                assert(self.lines[i+1].linked.reachable_betree_addrs() <= linked.reachable_betree_addrs()) by {
                    assert(self.child_linked_at(i)); // trigger
                    assert(linked.root().valid_child_index(r)); // trigger
                    self.lines[i+1].linked.reachable_betree_addrs_ignore_ranking(ranking, self.lines[i+1].linked.the_ranking());
                }
            }
        }
    }
}

impl QueryReceipt<BranchNode> {
    pub open spec fn i(self) -> QueryReceipt<SimpleBuffer>
    {
        QueryReceipt{
            key: self.key,
            linked: self.linked.i(),
            lines: Seq::new(self.lines.len(), 
                |i| QueryReceiptLine{
                    linked: LinkedBetree{
                        root: self.lines[i].linked.root,
                        dv: self.lines[i].linked.dv,
                        buffer_dv: self.linked.i().buffer_dv,
                    },
                    result: self.lines[i].result
                }
            )
        }
    }

    proof fn i_preserves_valid(self)
        requires 
            self.valid(), 
            self.linked.inv(),
            self.linked.buffer_dv.sealed_branch_roots(
                self.linked.reachable_buffer_addrs()), // callsite issue
        ensures self.i().valid()
    {
        assert forall |i:nat| i < self.i().lines.len()
        implies (#[trigger] self.i().lines[i as int]).linked.has_root() <==> i < self.i().lines.len()-1
        by {
            if self.i().lines[i as int].linked.has_root() || i < self.i().lines.len()-1 {
                assert(self.lines[i as int].linked.has_root()); // trigger
            }
        }

        assert forall |i| 0 <= i < self.i().lines.len()
        implies ({
            &&& (#[trigger] self.i().lines[i]).wf()
            &&& self.i().lines[i].linked.acyclic()
        }) by {
            let linked = self.lines[i].linked;
            let i_linked = self.i().lines[i].linked;
            let ranking = linked.the_ranking();

            assert(self.lines[i].wf()); // trigger
            assert(linked.acyclic()); // trigger
            assert(i_linked.valid_ranking(ranking)); // witness
        }

        self.receipt_line_root_is_reachable(0);

        assert forall |i| 0 <= i < self.i().lines.len()-1
        implies ({
            &&& self.i().linked.buffer_dv.valid_buffers(self.i().node(i).buffers)
            &&& (#[trigger] self.i().node(i)).key_in_domain(self.key)
            &&& self.i().child_linked_at(i)
            &&& self.i().result_linked_at(i)
        }) by {
            self.linked.i_valid();
            assert(self.linked.buffer_dv.valid_buffers(self.node(i).buffers)); // trigger

            assert(self.child_linked_at(i)); // trigger
            assert(self.result_linked_at(i)); // trigger

            let linked = self.lines[i].linked;

            assert forall |idx| 0 <= idx < self.node(i).buffers.len()
            implies self.linked.buffer_dv.get_branch(#[trigger] self.node(i).buffers[idx]).inv()
            by {
                assert(self.linked.reachable_buffer(linked.root.unwrap(), self.node(i).buffers[idx])); // witness
                assert(self.linked.reachable_buffer_addrs().contains(self.node(i).buffers[idx]));
                self.linked.buffer_dv.sealed_branch_roots_contains(
                    self.linked.reachable_buffer_addrs(),
                    self.node(i).buffers[idx],
                );
            }

            let start = self.node(i).flushed_ofs(self.key);
            let msg = self.linked.buffer_dv.query_from(self.node(i).buffers, self.key, start as int);

            assert(self.node(i).key_in_domain(self.key)); // trigger
            self.node(i).pivots.route_lemma(self.key);
            self.linked.buffer_dv.query_from_refines(self.node(i).buffers, self.key, start as int);
        }
    }
}

impl AllocationBranchBetree::State { 
    pub open spec(checked) fn i(self) -> AllocationBetree::State
    {
        AllocationBetree::State{
            betree: self.betree.i(),
            betree_aus: self.betree_aus,
            buffer_aus: self.branch_aus,
        }
    }

    pub proof fn i_inv(self)
        requires self.inv()
        ensures self.i().inv()
    {
        self.betree.linked.i_valid();
    }

    pub proof fn init_refines(self, v: LinkedBetreeVars::State<BranchNode>)
        requires self.inv(), AllocationBranchBetree::State::initialize(self, v), 
        ensures AllocationBetree::State::initialize(self.i(), v.i()), 
    {
        v.linked.i_valid();
    }

    proof fn au_likes_noop_refines(pre: Self, post: Self, lbl: AllocationBranchBetree::Label, new_betree: LinkedBetreeVars::State<BranchNode>)
    requires 
        pre.inv(),
        post.inv(),
        AllocationBranchBetree::State::au_likes_noop(pre, post, lbl, new_betree),
    ensures
        AllocationBetree::State::next_by(pre.i(), post.i(), lbl.i(), AllocationBetree::Step::au_likes_noop(new_betree.i())),
    {
        reveal(LinkedBetreeVars::State::next);
        reveal(LinkedBetreeVars::State::next_by);
        reveal(AllocationBetree::State::next_by);

        match lbl->linked_lbl {
            LinkedBetreeVars::Label::Query{end_lsn, key, value} => {
                let receipt = choose |receipt| LinkedBetreeVars::State::query(
                            pre.betree, post.betree, lbl->linked_lbl, receipt);
                let (tree_likes, branch_likes) = pre.betree.linked.transitive_likes();
                let compactor_roots = CompactorInput::input_roots(pre.compactors);
                pre.betree.linked.tree_likes_domain(pre.betree.linked.the_ranking());
                pre.betree.linked.buffer_likes_domain(tree_likes);
                pre.betree.linked.i_valid();
                assert(pre.betree.linked.reachable_buffer_addrs() == branch_likes.dom());
                assert(pre.betree.linked.reachable_buffer_addrs() <= branch_likes.dom() + compactor_roots);
                pre.betree.linked.buffer_dv.sealed_branch_roots_subset(
                    branch_likes.dom() + compactor_roots,
                    pre.betree.linked.reachable_buffer_addrs(),
                );
                receipt.i_preserves_valid();
                assert(LinkedBetreeVars::State::next_by(pre.betree.i(), post.betree.i(), 
                    lbl->linked_lbl, LinkedBetreeVars::Step::query(receipt.i())));
            }
            LinkedBetreeVars::Label::Put{puts} => {
                assert(LinkedBetreeVars::State::next_by(pre.betree.i(), new_betree.i(), 
                    lbl->linked_lbl, LinkedBetreeVars::Step::put()));
            }
            LinkedBetreeVars::Label::FreezeAs{stamped_betree} => {
                assert(pre.betree.linked.i().i_bdv().buffer_dv == pre.betree.linked.i().buffer_dv); // trigger
                assert(LinkedBetreeVars::State::next_by(pre.betree.i(), new_betree.i(), 
                    lbl->linked_lbl, LinkedBetreeVars::Step::freeze_as()));
            }
            _ => { assert(false); }
        }
    }

    proof fn internal_flush_memtable_refines(pre: Self, post: Self, lbl: AllocationBranchBetree::Label, 
        new_betree: LinkedBetreeVars::State<BranchNode>, branch_idx: int, new_root_addr: Address)
    requires 
        pre.inv(), 
        post.inv(),
        AllocationBranchBetree::State::internal_flush_memtable(pre, post, lbl, new_betree, branch_idx, new_root_addr),
    ensures ({
        let new_branch = pre.wip_branches[branch_idx].sealed_branch();
        let new_addrs = TwoAddrs{addr1: new_root_addr, addr2: new_branch.root};
        &&& AllocationBetree::State::next_by(pre.i(), post.i(), lbl.i(), 
            AllocationBetree::Step::internal_flush_memtable(new_betree.i(), new_addrs))}) 
    {
        let new_branch = pre.wip_branches[branch_idx].sealed_branch();
        let new_addrs = TwoAddrs{addr1: new_root_addr, addr2: new_branch.root};
        let step = AllocationBetree::Step::internal_flush_memtable(new_betree.i(), new_addrs);

        let i_buffer = new_branch.root().i(new_betree.linked.buffer_dv, new_addrs.addr2);
        let i_pushed = pre.i().betree.linked.push_memtable(i_buffer, new_addrs);    
        let pushed = pre.betree.linked.push_memtable(new_branch.root(), new_addrs);

        assert(pushed.valid_view(new_betree.linked));
        assert(pre.betree.linked.is_fresh(new_addrs.repr())) by {
            AllocationBulkBranch::alloc_aus_ensures(pre.wip_branches, branch_idx);
        }
        pre.inv_implies_wf_branch_dv();
        post.inv_implies_wf_branch_dv();
        pre.betree.linked.buffer_dv.i_preserves_sub_disk(new_betree.linked.buffer_dv);
        assert(i_pushed.valid_view(new_betree.i().linked));

        assert(LinkedBetreeVars::State::internal_flush_memtable(pre.i().betree, new_betree.i(), 
            lbl.i()->linked_lbl, i_buffer, new_betree.i().linked, new_addrs));
        assert(AllocationBetree::State::internal_flush_memtable(pre.i(), post.i(), lbl.i(), new_betree.i(), new_addrs));
        reveal(AllocationBetree::State::next_by);
    }

    proof fn internal_split_refines(pre: Self, post: Self, lbl: AllocationBranchBetree::Label, new_betree: LinkedBetreeVars::State<BranchNode>, 
        path: Path<BranchNode>, request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs)
    requires 
        pre.inv(), 
        post.inv(),
        AllocationBranchBetree::State::internal_split(pre, post, lbl, new_betree, path, request, new_addrs, path_addrs),
    ensures
        AllocationBetree::State::next_by(pre.i(), post.i(), lbl.i(), 
            AllocationBetree::Step::internal_split(new_betree.i(), path.i(), request, new_addrs, path_addrs))
    {
        assert(pre.betree.linked.is_fresh(new_addrs.repr().union(path_addrs.to_set()))) by {
            to_aus_domain(path_addrs.to_set());
            to_aus_domain(new_addrs.repr());
        }

        path.i_ensures();
        pre.betree.post_split_ensures(path, request, new_addrs, path_addrs);

        let splitted = LinkedBetreeVars::State::post_split(path, request, new_addrs, path_addrs);
        let i_splitted = LinkedBetreeVars::State::post_split(path.i(), request, new_addrs, path_addrs);

        path.target_ensures();
        path.i_substitute_ensures(path.target().split_parent(request, new_addrs), path_addrs);


        assert(LinkedBetreeVars::State::internal_split(pre.i().betree, new_betree.i(), 
            lbl.i()->linked_lbl, new_betree.i().linked, path.i(), request, new_addrs, path_addrs));

        let old_child = path.target().child_at_idx(request.get_child_idx());
        let i_child = path.i().target().child_at_idx(request.get_child_idx());


        old_child.same_dv_same_buffer_likes(old_child.i(), old_child.root_likes());

        reveal(AllocationBetree::State::next_by);
    }

    proof fn internal_flush_refines(pre: Self, post: Self, lbl: AllocationBranchBetree::Label, 
        new_betree: LinkedBetreeVars::State<BranchNode>, path: Path<BranchNode>, 
        child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs)
    requires 
        pre.inv(), 
        post.inv(),
        AllocationBranchBetree::State::internal_flush(pre, post, lbl, new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs),
    ensures
        AllocationBetree::State::next_by(pre.i(), post.i(), lbl.i(), 
            AllocationBetree::Step::internal_flush(new_betree.i(), path.i(), child_idx, buffer_gc, new_addrs, path_addrs))
    {
        assert(pre.betree.linked.is_fresh(new_addrs.repr() + path_addrs.to_set())) by {
            to_aus_domain(path_addrs.to_set());
            to_aus_domain(new_addrs.repr());    
        }

        path.i_ensures();
        path.target_ensures();
        pre.betree.post_flush_ensures(path, child_idx, buffer_gc, new_addrs, path_addrs);
        path.i_substitute_ensures(path.target().flush(child_idx, buffer_gc, new_addrs), path_addrs);

        let flushed = LinkedBetreeVars::State::post_flush(path, child_idx, buffer_gc, new_addrs, path_addrs);
        pre.inv_implies_wf_branch_dv();
        post.inv_implies_wf_branch_dv();
        new_betree.linked.buffer_dv.i_preserves_sub_disk(pre.betree.linked.buffer_dv);

        assert(LinkedBetreeVars::State::internal_flush(pre.i().betree, new_betree.i(), lbl.i()->linked_lbl, 
            new_betree.i().linked, path.i(), child_idx, buffer_gc, new_addrs, path_addrs));

        let (new_betree_aus, new_buffer_aus) = AllocationBetree::State::internal_flush_au_likes(path.i(), child_idx, 
            buffer_gc, new_addrs, path_addrs, pre.i().betree_aus, pre.i().buffer_aus);

        post.inv_branch_summary_ensures();
        assert(AllocationBetree::State::internal_flush(pre.i(), post.i(), lbl.i(), 
            new_betree.i(), path.i(), child_idx, buffer_gc, new_addrs, path_addrs));
        reveal(AllocationBetree::State::next_by);
    }

    proof fn internal_compact_complete_inv_refines(pre: Self, post: Self, lbl: AllocationBranchBetree::Label, 
        new_betree: LinkedBetreeVars::State<BranchNode>, path: Path<BranchNode>, 
        start: nat, end: nat, input_idx: int, branch_idx: int, new_node_addr: Address, path_addrs: PathAddrs)
    requires 
        pre.inv(), 
        post.inv(),
        AllocationBranchBetree::State::internal_compact_complete(pre, post, lbl, new_betree,
            path, start, end, input_idx, branch_idx, new_node_addr, path_addrs),
    ensures ({
        let new_branch = pre.wip_branches[branch_idx].sealed_branch();
        let new_addrs = TwoAddrs{addr1: new_node_addr, addr2: new_branch.root};

        &&& AllocationBetree::State::next_by(pre.i(), post.i(), lbl.i(), 
            AllocationBetree::Step::internal_compact_complete(new_betree.i(), path.i(), start, end, new_branch.i().i(), new_addrs, path_addrs))
    }) {
        let new_branch = pre.wip_branches[branch_idx].sealed_branch();
        let buffer = new_branch.i().i();

        let linked_new_addrs = TwoAddrs{addr1: new_node_addr, addr2: new_branch.root};
        assert(pre.betree.linked.is_fresh(linked_new_addrs.repr() + path_addrs.to_set())) by {
            to_aus_domain(path_addrs.to_set());
            AllocationBulkBranch::alloc_aus_ensures(pre.wip_branches, branch_idx);
        }

        path.i_ensures();
        path.target_ensures();

        let pre_bdv = pre.betree.linked.buffer_dv;
        let bdv = new_betree.linked.buffer_dv;
        assert(path.target().compact_buffer_valid_domain(start, end, new_branch.root(), bdv, new_branch.root));

        assert(new_branch.inv());
        post.inv_implies_wf_branch_dv();

        // Prove sub-disk relation: new_branch entries are retained in the post buffer disk.
        assert(new_branch.disk_view.is_sub_disk(bdv.to_branch_disk())) by {
            let pre_buffer_dv = pre.betree.linked.buffer_dv;
            let full_buffer_dv = pre_buffer_dv.entries.union_prefer_right(new_branch.disk_view.entries);

            let new_compactors = pre.compactors.remove(input_idx);
            let (new_betree_aus, new_branch_aus) = AllocationBetree::State::internal_compact_complete_au_likes(
                path, start, end, linked_new_addrs, path_addrs, pre.betree_aus, pre.branch_aus);
            let branch_deallocs = pre.branch_summary.dom() - new_branch_aus.dom() - read_ref_aus(new_compactors);
            let new_branch_summary = pre.branch_summary.insert(new_branch.root.au, new_branch.get_summary())
                .remove_keys(branch_deallocs);
            let new_summary_aus = summary_aus(new_branch_summary);
            let post_buffer_domain = restrict_domain_au(full_buffer_dv, new_summary_aus);

            // From the transition definition.
            assert(bdv.entries == full_buffer_dv.restrict(post_buffer_domain));

            // Sealed branch summary contains all entries' AUs.
            assert(pre.wip_branches[branch_idx].inv());
            assert(pre.wip_branches[branch_idx].is_sealed());
            assert(new_branch.valid_sealed_branch());
            assert(new_branch.tight_disk_view_with_summary());

            // new_branch.root.au is preserved in new_branch_aus, so it is not removed.
            let add_buffer_aus = to_au_likes(compact_add_buffers(linked_new_addrs));
            to_au_likes_singleton(linked_new_addrs.addr2);
            assert(add_buffer_aus.contains(linked_new_addrs.addr2.au));
            assert(add_buffer_aus <= new_branch_aus);
            assert(new_branch_aus.contains(linked_new_addrs.addr2.au));
            assert(new_branch_aus.dom().contains(new_branch.root.au));
            assert(!branch_deallocs.contains(new_branch.root.au));

            assert(new_branch_summary.contains_key(new_branch.root.au)); // trigger

            // Show every entry of new_branch is kept by the post buffer domain.
            assert forall |addr: Address| #![auto] new_branch.disk_view.entries.contains_key(addr)
            implies post_buffer_domain.contains(addr) by {
                assert(new_branch.disk_view.entries.dom().contains(addr));
                assert(new_branch.full_repr().contains(addr));
                assert(new_branch.get_summary().contains(addr.au));
                assert(new_branch_summary[new_branch.root.au] == new_branch.get_summary());
                assert(new_branch_summary.values().contains(new_branch.get_summary()));
                // Establish finiteness of summary values via the post-state invariant.
                assert(post.branch_summary == new_branch_summary);
                let (_, post_branch_likes) = post.betree.linked.transitive_likes();
                let post_compactor_roots = CompactorInput::input_roots(post.compactors);
                let post_branch_roots = post_branch_likes.dom() + post_compactor_roots;
                CompactorInput::input_roots_finite(post.compactors);
                to_au_likes_domain(post_branch_likes);
                to_aus_additive(post_branch_likes.dom(), post_compactor_roots);
                post.betree.linked.buffer_dv.build_branch_summary_finite(post_branch_roots);
                assert(post.branch_summary =~= post.betree.linked.buffer_dv.build_branch_summary(post_branch_roots));
                assert(new_branch_summary.values().finite());
                lemma_union_set_of_sets_subset(new_branch_summary.values(), new_branch.get_summary());
                assert(new_summary_aus.contains(addr.au));
                assert(full_buffer_dv.contains_key(addr));
            }

            // Therefore entries are preserved in bdv.
            assert forall |addr: Address| #![auto] new_branch.disk_view.entries.contains_key(addr)
            implies bdv.entries.contains_key(addr) && bdv.entries[addr] == new_branch.disk_view.entries[addr] by {
                assert(post_buffer_domain.contains(addr));
                assert(bdv.entries.contains_key(addr));
                assert(bdv.entries[addr] == full_buffer_dv[addr]);
                assert(full_buffer_dv[addr] == new_branch.disk_view.entries[addr]);
            }
        }

        let embedded_branch = bdv.get_branch(new_branch.root);
        let new_summary = new_branch.get_summary();
        let pre_summary_aus = summary_aus(pre.branch_summary);
        let extra_entries = embedded_branch.disk_view.representation()
            - new_branch.disk_view.representation();

        assert(new_branch.full_repr() <= embedded_branch.disk_view.representation()) by {
            assert(new_branch.full_repr() == new_branch.disk_view.representation());
            assert(new_branch.disk_view.is_sub_disk(embedded_branch.disk_view));
        }
        assert(addrs_closed(new_branch.disk_view.entries.dom(), new_summary));
        assert forall |addr: Address| #[trigger] extra_entries.contains(addr)
            implies !new_summary.contains(addr.au) by {
            if new_summary.contains(addr.au) {
                assert(bdv.entries.contains_key(addr));
                assert(!new_branch.disk_view.entries.contains_key(addr));

                let full_buffer_dv = pre_bdv.entries.union_prefer_right(
                    new_branch.disk_view.entries,
                );
                assert(full_buffer_dv.contains_key(addr));
                assert(pre_bdv.entries.contains_key(addr));
                assert(pre_summary_aus.contains(addr.au));

                assert(new_summary <= pre.wip_branches[branch_idx].mini_allocator.all_aus());
                AllocationBulkBranch::alloc_aus_ensures(pre.wip_branches, branch_idx);
                assert(pre.wip_branches[branch_idx].mini_allocator.all_aus()
                    <= pre.branch_allocator_aus());
                assert(pre_summary_aus.disjoint(pre.branch_allocator_aus()));
                assert(false);
            }
        }
        new_branch.valid_subdisk_preserves_valid_sealed_branch(
            embedded_branch,
            new_summary,
        );
        assert(embedded_branch.inv());
        assert(embedded_branch.i() == new_branch.i());

        assert forall |k| true 
        implies (buffer.linked_contains(bdv.i(), new_branch.root, k) <==> 
            #[trigger] pre_bdv.i().valid_compact_key_domain(path.i().target().root(), start, end, k))
        by {
            let node = path.target().root();
            let compact_slice = node.buffers.slice(start as int, end as int);
            let compact_ofs_map = node.make_offset_map().decrement(start);
            let compactor_roots = CompactorInput::input_roots(pre.compactors);
            let roots_seq = Seq::new(
                pre.compactors.len(),
                |i| pre.compactors[i].input_buffers.addrs.to_set(),
            );

            assert(pre.compactors[input_idx].input_buffers == compact_slice);
            lemma_subset_union_seq_of_sets(roots_seq, input_idx);
            assert(compact_slice.addrs.to_set() <= compactor_roots);

            assert forall |idx: int| true implies
                (pre_bdv.key_in_buffer_filtered(compact_slice, compact_ofs_map, 0, k, idx)
                    <==> pre_bdv.i().key_in_buffer_filtered(
                        compact_slice,
                        compact_ofs_map,
                        0,
                        k,
                        idx,
                    )) by {
                if pre_bdv.key_in_buffer_filtered(
                    compact_slice,
                    compact_ofs_map,
                    0,
                    k,
                    idx,
                ) || pre_bdv.i().key_in_buffer_filtered(
                    compact_slice,
                    compact_ofs_map,
                    0,
                    k,
                    idx,
                ) {
                    assert(0 <= idx < compact_slice.len());
                    let addr = compact_slice[idx];
                    assert(compact_slice.addrs.to_set().contains(addr));
                    assert(compactor_roots.contains(addr));
                    pre_bdv.sealed_branch_roots_contains(
                        pre.betree.linked.transitive_likes().1.dom() + compactor_roots,
                        addr,
                    );
                    pre_bdv.buffer_contains_refines(addr, k);
                }
            }

            assert(pre_bdv.valid_compact_key_domain(node, start, end, k)
                <==> pre_bdv.i().valid_compact_key_domain(node, start, end, k)) by {
                if pre_bdv.valid_compact_key_domain(node, start, end, k) {
                    let idx = choose |idx: int|
                        #[trigger] pre_bdv.key_in_buffer_filtered(
                            compact_slice,
                            compact_ofs_map,
                            0,
                            k,
                            idx,
                        );
                    assert(pre_bdv.i().key_in_buffer_filtered(
                        compact_slice,
                        compact_ofs_map,
                        0,
                        k,
                        idx,
                    ));
                }
                if pre_bdv.i().valid_compact_key_domain(node, start, end, k) {
                    let idx = choose |idx: int|
                        #[trigger] pre_bdv.i().key_in_buffer_filtered(
                            compact_slice,
                            compact_ofs_map,
                            0,
                            k,
                            idx,
                        );
                    assert(pre_bdv.key_in_buffer_filtered(
                        compact_slice,
                        compact_ofs_map,
                        0,
                        k,
                        idx,
                    ));
                }
            }
            assert(path.i().target().root() == node);

            bdv.buffer_contains_refines(new_branch.root, k);
            assert(bdv.i().entries[new_branch.root] == embedded_branch.i().i());
            assert(bdv.i().entries[new_branch.root] == buffer);
            assert(buffer.linked_contains(bdv.i(), new_branch.root, k)
                <==> bdv.i().buffer_contains(new_branch.root, k));
            assert(new_branch.root().linked_contains(bdv, new_branch.root, k)
                <==> bdv.buffer_contains(new_branch.root, k));

        }

        assert(path.i().target().compact_buffer_valid_domain(start, end, buffer, bdv.i(), new_branch.root));
        assert(path.target().compact_buffer_valid_range(start, end, new_branch.root(), bdv, new_branch.root));
        assert(path.i().target().compact_buffer_valid_range(
            start,
            end,
            buffer,
            bdv.i(),
            new_branch.root,
        )) by {
            assert forall |k| buffer.linked_contains(bdv.i(), new_branch.root, k)
                implies #[trigger] buffer.linked_query(bdv.i(), new_branch.root, k)
                    == pre_bdv.i().compact_key_value(
                        path.i().target().root(),
                        start,
                        end,
                        k,
                    ) by {
                let node = path.target().root();
                let compact_slice = node.buffers.slice(start as int, end as int);
                let compactor_roots = CompactorInput::input_roots(pre.compactors);
                let roots_seq = Seq::new(
                    pre.compactors.len(),
                    |i| pre.compactors[i].input_buffers.addrs.to_set(),
                );
                assert(pre.compactors[input_idx].input_buffers == compact_slice);
                lemma_subset_union_seq_of_sets(roots_seq, input_idx);
                assert(compact_slice.addrs.to_set() <= compactor_roots);
                assert forall |idx: int| 0 <= idx < compact_slice.len()
                    implies pre_bdv.get_branch(#[trigger] compact_slice[idx]).inv() by {
                    let addr = compact_slice[idx];
                    assert(compact_slice.addrs.to_set().contains(addr));
                    assert(compactor_roots.contains(addr));
                    pre_bdv.sealed_branch_roots_contains(
                        pre.betree.linked.transitive_likes().1.dom() + compactor_roots,
                        addr,
                    );
                }

                let from = if node.flushed_ofs(k) <= start {
                    0
                } else {
                    node.flushed_ofs(k) - start
                };
                assert(pre_bdv.i().valid_compact_key_domain(node, start, end, k));
                assert(node.flushed_ofs(k) <= end);
                assert(compact_slice.len() == end - start);
                assert(from <= compact_slice.len());
                pre_bdv.query_from_refines(compact_slice, k, from as int);
                bdv.query_refines(new_branch.root, k);

                assert(bdv.i().entries[new_branch.root] == buffer);
                assert(bdv.i().buffer_contains(new_branch.root, k));
                bdv.buffer_contains_refines(new_branch.root, k);
                assert(bdv.buffer_contains(new_branch.root, k));
                assert(new_branch.root().linked_contains(bdv, new_branch.root, k));
                assert(new_branch.root().linked_query(bdv, new_branch.root, k)
                    == pre_bdv.compact_key_value(node, start, end, k));
                assert(bdv.query(new_branch.root, k)
                    == new_branch.root().linked_query(bdv, new_branch.root, k));
                assert(bdv.i().query(new_branch.root, k)
                    == buffer.linked_query(bdv.i(), new_branch.root, k));
                assert(pre_bdv.compact_key_value(node, start, end, k)
                    == pre_bdv.query_from(compact_slice, k, from as int));
                assert(pre_bdv.i().compact_key_value(node, start, end, k)
                    == pre_bdv.i().query_from(compact_slice, k, from as int));
                assert(path.i().target().root() == node);
            }
        }

        assert(path.i().target().can_compact(start, end, buffer, bdv.i(), linked_new_addrs));

        let compacted = LinkedBetreeVars::State::post_compact(
            path,
            start,
            end,
            new_branch.root(),
            linked_new_addrs,
            path_addrs,
        );
        let i_compacted = LinkedBetreeVars::State::post_compact(
            path.i(),
            start,
            end,
            buffer,
            linked_new_addrs,
            path_addrs,
        );
        let full_buffer_dv = BufferDisk{
            entries: pre_bdv.entries.union_prefer_right(new_branch.disk_view.entries),
        };

        pre.inv_implies_wf_branch_dv();
        assert(new_branch.disk_view.wf());
        assert(full_buffer_dv.to_branch_disk().wf()) by {
            assert forall |addr| #[trigger] full_buffer_dv.entries.contains_key(addr)
                implies new_branch.full_repr().contains(addr)
                    || pre_bdv.entries.contains_key(addr) by {
                if new_branch.disk_view.entries.contains_key(addr) {
                    assert(new_branch.disk_view.representation().contains(addr));
                    assert(new_branch.full_repr() == new_branch.disk_view.representation());
                } else {
                    assert(pre_bdv.entries.contains_key(addr));
                }
            }
        }
        let full_embedded_branch = full_buffer_dv.get_branch(new_branch.root);
        let full_extra_entries = full_embedded_branch.disk_view.representation()
            - new_branch.disk_view.representation();
        assert forall |addr: Address| #[trigger] full_extra_entries.contains(addr)
            implies !new_summary.contains(addr.au) by {
            if new_summary.contains(addr.au) {
                assert(full_buffer_dv.entries.contains_key(addr));
                assert(!new_branch.disk_view.entries.contains_key(addr));
                assert(pre_bdv.entries.contains_key(addr));
                assert(pre_summary_aus.contains(addr.au));
                assert(new_summary <= pre.wip_branches[branch_idx].mini_allocator.all_aus());
                AllocationBulkBranch::alloc_aus_ensures(pre.wip_branches, branch_idx);
                assert(pre.wip_branches[branch_idx].mini_allocator.all_aus()
                    <= pre.branch_allocator_aus());
                assert(pre_summary_aus.disjoint(pre.branch_allocator_aus()));
                assert(false);
            }
        }
        new_branch.valid_subdisk_preserves_valid_sealed_branch(
            full_embedded_branch,
            new_summary,
        );
        assert(full_embedded_branch.i() == new_branch.i());
        assert(pre_bdv.is_sub_disk(full_buffer_dv));
        assert(bdv.is_sub_disk(full_buffer_dv));
        pre_bdv.i_preserves_sub_disk(full_buffer_dv);
        bdv.i_preserves_sub_disk(full_buffer_dv);
        assert(pre_bdv.i().entries <= full_buffer_dv.i().entries);
        assert(bdv.i().entries <= full_buffer_dv.i().entries);

        assert(i_compacted.buffer_dv
            == pre_bdv.i().modify_disk(new_branch.root, buffer));
        assert(i_compacted.buffer_dv.is_sub_disk(full_buffer_dv.i())) by {
            assert forall |addr| i_compacted.buffer_dv.entries.contains_key(addr)
                implies i_compacted.buffer_dv.entries[addr]
                    == #[trigger] full_buffer_dv.i().entries[addr] by {
                if addr == new_branch.root {
                    assert(full_embedded_branch.i() == new_branch.i());
                    assert(full_buffer_dv.i().entries[addr] == new_branch.i().i());
                } else {
                    assert(pre_bdv.i().entries.contains_key(addr));
                    assert(full_buffer_dv.i().entries.contains_key(addr));
                    assert(pre_bdv.i().entries[addr] == full_buffer_dv.i().entries[addr]);
                }
            }
        }
        assert(bdv.i().agrees_with(i_compacted.buffer_dv)) by {
            assert forall |addr| bdv.i().entries.contains_key(addr)
                && i_compacted.buffer_dv.entries.contains_key(addr)
                implies bdv.i().entries[addr]
                    == #[trigger] i_compacted.buffer_dv.entries[addr] by {
                assert(full_buffer_dv.i().entries.contains_key(addr));
                assert(bdv.i().entries[addr] == full_buffer_dv.i().entries[addr]);
                assert(i_compacted.buffer_dv.entries[addr]
                    == full_buffer_dv.i().entries[addr]);
            }
        }

        assert(compacted.valid_view(new_betree.linked));
        pre.betree.post_compact_ensures(
            path,
            start,
            end,
            new_branch.root(),
            linked_new_addrs,
            path_addrs,
        );
        path.i_substitute_ensures(
            path.target().compact(start, end, new_branch.root(), linked_new_addrs),
            path_addrs,
        );
        let native_replacement = path.target().compact(
            start,
            end,
            new_branch.root(),
            linked_new_addrs,
        ).i();
        let interpreted_replacement = path.i().target().compact(
            start,
            end,
            buffer,
            linked_new_addrs,
        );
        assert(native_replacement.dv == interpreted_replacement.dv);
        assert(native_replacement.root == interpreted_replacement.root);
        path.i().substitute_same_dv_root(
            native_replacement,
            interpreted_replacement,
            path_addrs,
        );
        assert(i_compacted.dv == compacted.dv);
        assert(i_compacted.root == compacted.root);
        post.betree.linked.i_valid();
        assert(i_compacted.valid_view(new_betree.i().linked));

        assert(LinkedBetreeVars::State::internal_compact(pre.i().betree, new_betree.i(), lbl.i()->linked_lbl,
            new_betree.i().linked, path.i(), start, end, new_branch.i().i(), linked_new_addrs, path_addrs));

        let (_, new_buffer_aus) = AllocationBetree::State::internal_compact_complete_au_likes(
            path.i(),
            start,
            end,
            linked_new_addrs,
            path_addrs,
            pre.i().betree_aus,
            pre.i().buffer_aus,
        );
        post.inv_branch_summary_ensures();
        assert(new_buffer_aus == post.branch_aus);
        assert(new_buffer_aus.dom() <= summary_aus(post.branch_summary));
        let post_buffer_domain = restrict_domain_au(
            full_buffer_dv.entries,
            summary_aus(post.branch_summary),
        );
        assert(restrict_domain_au(i_compacted.buffer_dv.entries, new_buffer_aus.dom())
            <= bdv.i().repr()) by {
            assert forall |addr| #[trigger] restrict_domain_au(
                i_compacted.buffer_dv.entries,
                new_buffer_aus.dom(),
            ).contains(addr) implies bdv.i().repr().contains(addr) by {
                assert(i_compacted.buffer_dv.entries.contains_key(addr));
                assert(full_buffer_dv.i().entries.contains_key(addr));
                assert(full_buffer_dv.entries.contains_key(addr));
                assert(new_buffer_aus.dom().contains(addr.au));
                assert(summary_aus(post.branch_summary).contains(addr.au));
                assert(post_buffer_domain.contains(addr));
                assert(bdv.entries.contains_key(addr));
                assert(bdv.i().entries.contains_key(addr));
            }
        }

        reveal(AllocationBetree::State::next_by);
        assert(AllocationBetree::State::next_by(
            pre.i(),
            post.i(),
            lbl.i(),
            AllocationBetree::Step::internal_compact_complete(
                new_betree.i(),
                path.i(),
                start,
                end,
                buffer,
                linked_new_addrs,
                path_addrs,
            ),
        ));
    }

    pub proof fn next_refines(pre: Self, post: Self, lbl: AllocationBranchBetree::Label)
        requires 
            pre.inv(),
            post.inv(),
            AllocationBranchBetree::State::next(pre, post, lbl),
        ensures
            AllocationBetree::State::next(pre.i(), post.i(), lbl.i())
    {
        reveal(AllocationBetree::State::next);
        reveal(AllocationBetree::State::next_by);
        reveal(AllocationBranchBetree::State::next);
        reveal(AllocationBranchBetree::State::next_by);

        match choose |step| Self::next_by(pre, post, lbl, step) {
            AllocationBranchBetree::Step::au_likes_noop(new_betree) => { 
                Self::au_likes_noop_refines(pre, post, lbl, new_betree);
            }
            AllocationBranchBetree::Step::internal_noop() => {



                assert(post == pre);
                assert(AllocationBetree::State::next_by(
                    pre.i(),
                    post.i(),
                    lbl.i(),
                    AllocationBetree::Step::internal_noop(),
                ));
                assert(AllocationBetree::State::next(
                    pre.i(),
                    post.i(),
                    lbl.i(),
                ));
            }
            AllocationBranchBetree::Step::branch_begin() => { 
                assert(AllocationBetree::State::next_by(pre.i(), post.i(), lbl.i(), AllocationBetree::Step::internal_noop())); // trigger
            }
            AllocationBranchBetree::Step::branch_fill(
                idx,
                post_branch,
                allocs,
                deallocs,
            ) => {
                assert(AllocationBetree::State::next_by(
                    pre.i(), post.i(), lbl.i(),
                    AllocationBetree::Step::internal_noop(),
                ));
            }
            AllocationBranchBetree::Step::branch_build(
                idx,
                post_branch,
                event,
                allocs,
                deallocs,
            ) => {
                assert(AllocationBetree::State::next_by(
                    pre.i(), post.i(), lbl.i(), AllocationBetree::Step::internal_noop(),
                ));
            }
            AllocationBranchBetree::Step::branch_abort(idx) => { 
                assert(AllocationBetree::State::next_by(
                    pre.i(), post.i(), lbl.i(), AllocationBetree::Step::internal_noop(),
                ));
            }
            AllocationBranchBetree::Step::internal_flush_memtable(new_betree, branch_idx, new_root_addr) => {
                Self::internal_flush_memtable_refines(pre, post, lbl, new_betree, branch_idx, new_root_addr);
            }
            AllocationBranchBetree::Step::internal_grow(new_betree, new_root_addr) => {
                assert(AllocationBetree::State::next_by(pre.i(), post.i(), lbl.i(), 
                    AllocationBetree::Step::internal_grow(new_betree.i(), new_root_addr)));
            }
            AllocationBranchBetree::Step::internal_split(new_betree, path, request, new_addrs, path_addrs) => {
                Self::internal_split_refines(pre, post, lbl, new_betree, path, request, new_addrs, path_addrs);
            }
            AllocationBranchBetree::Step::internal_flush(new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs) => {
                Self::internal_flush_refines(pre, post, lbl, new_betree, path, child_idx, buffer_gc, new_addrs, path_addrs);
            }
            AllocationBranchBetree::Step::internal_compact_begin(path, start, end, input) => {
                assert(AllocationBetree::State::next_by(
                    pre.i(), post.i(), lbl.i(), AllocationBetree::Step::internal_noop(),
                ));
            }
            AllocationBranchBetree::Step::internal_compact_abort(input_idx, new_betree) => {
                assert(pre.i().betree.linked.valid_view(new_betree.i().linked)) by {
                    pre.inv_implies_wf_branch_dv();
                    post.inv_implies_wf_branch_dv();
                    new_betree.linked.buffer_dv.i_preserves_sub_disk(pre.betree.linked.buffer_dv);
                }

                assert(pre.i().betree.linked.reachable_buffers_preserved(new_betree.i().linked)) by {
                    pre.betree.linked.i_valid();
                    post.betree.linked.i_valid();
                    pre.betree.linked.transitive_likes_ignores_buffer_dv(post.betree.linked);
                }

                assert(AllocationBetree::State::next_by(pre.i(), post.i(), lbl.i(), AllocationBetree::Step::internal_buffer_noop(new_betree.i()))); // trigger
            }
            AllocationBranchBetree::Step::internal_compact_complete(input_idx, new_betree, path, start, end, compacted_buffer, new_addrs, path_addrs) => {
                Self::internal_compact_complete_inv_refines(
                    pre,
                    post,
                    lbl,
                    input_idx,
                    new_betree,
                    path,
                    start,
                    end,
                    compacted_buffer,
                    new_addrs,
                    path_addrs,
                );
            }
            _ => { assert(false); }
        }
    }
} // end impl AllocationBranchBetree::State

}//verus
