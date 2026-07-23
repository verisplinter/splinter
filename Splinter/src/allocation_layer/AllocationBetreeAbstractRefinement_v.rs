// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::abstract_system::AbstractMap_v::AbstractMap;
use crate::abstract_system::StampedMap_v::StampedMap;
use crate::allocation_layer::AllocationBetree_v::AllocationBetree;
use crate::allocation_layer::AllocationBetreeRefinement_v;
use crate::allocation_layer::LikesBetreeRefinement_v;
use crate::allocation_layer::LikesBetree_v::LikesBetree;
use crate::betree::Buffer_v::SimpleBuffer;
use crate::betree::FilteredBetreeRefinement_v;
use crate::betree::FilteredBetree_v::FilteredBetree;
use crate::betree::LinkedBetreeRefinement_v;
use crate::betree::LinkedBetree_v::LinkedBetreeVars;
use crate::betree::PagedBetreeRefinement_v;
use crate::betree::PagedBetree_v::PagedBetree;
use crate::betree::PivotBetreeRefinement_v;
use crate::betree::PivotBetree_v::PivotBetree;

verus! {

impl AllocationBetree::Label {
    pub open spec(checked) fn i_abstract(self) -> AbstractMap::Label {
        self.i().i().i().i().i().i()
    }
}

impl AllocationBetree::State {
    pub open spec(checked) fn i_abstract(self) -> AbstractMap::State
        recommends self.refinement_inv(),
    {
        let linked = self.i().i();
        let filtered = linked.i();
        if filtered.wf() {
            filtered.i().i().i()
        } else {
            arbitrary()
        }
    }

    pub open spec(checked) fn initial_i_abstract(
        v: LinkedBetreeVars::State<SimpleBuffer>,
    ) -> StampedMap
        recommends v.inv(),
    {
        let filtered = LinkedBetreeRefinement_v::i_stamped_betree(v);
        if filtered.value.wf() {
            PagedBetreeRefinement_v::i_stamped_betree(
                PivotBetreeRefinement_v::i_stamped_betree(
                    FilteredBetreeRefinement_v::i_stamped_betree(filtered),
                ),
            )
        } else {
            arbitrary()
        }
    }

    pub proof fn init_refines_abstract(
        self,
        v: LinkedBetreeVars::State<SimpleBuffer>,
    )
        requires AllocationBetree::State::initialize(self, v),
        ensures
            self.refinement_inv(),
            AbstractMap::State::initialize(self.i_abstract(), Self::initial_i_abstract(v)),
    {
        self.init_refines(v);
        self.i().init_refines(v);
        self.i().i().init_refines(v);

        let filtered_initial = LinkedBetreeRefinement_v::i_stamped_betree(v);
        self.i().i().i().init_refines(filtered_initial);

        let pivot_initial =
            FilteredBetreeRefinement_v::i_stamped_betree(filtered_initial);
        self.i().i().i().i().init_refines(pivot_initial);

        let paged_initial =
            PivotBetreeRefinement_v::i_stamped_betree(pivot_initial);
        self.i().i().i().i().i().init_refines(paged_initial);
    }

    pub proof fn next_refines_abstract(
        pre: Self,
        post: Self,
        lbl: AllocationBetree::Label,
    )
        requires
            pre.refinement_inv(),
            AllocationBetree::State::next(pre, post, lbl),
        ensures
            post.refinement_inv(),
            AbstractMap::State::next(
                pre.i_abstract(),
                post.i_abstract(),
                lbl.i_abstract(),
            ),
    {
        Self::next_refines(pre, post, lbl);

        let likes_pre = pre.i();
        let likes_post = post.i();
        let likes_lbl = lbl.i();
        let linked_step =
            LikesBetree::State::next_refines(likes_pre, likes_post, likes_lbl);

        let linked_pre = likes_pre.i();
        let linked_post = likes_post.i();
        let linked_lbl = likes_lbl.i();
        linked_pre.next_by_refines(linked_post, linked_lbl, linked_step);

        let filtered_pre = linked_pre.i();
        let filtered_post = linked_post.i();
        let filtered_lbl = linked_lbl.i();
        linked_pre.i_inv();
        filtered_pre.next_refines(filtered_post, filtered_lbl);

        let pivot_pre = filtered_pre.i();
        let pivot_post = filtered_post.i();
        let pivot_lbl = filtered_lbl.i();
        filtered_pre.i_inv();
        pivot_pre.next_refines(pivot_post, pivot_lbl);

        let paged_pre = pivot_pre.i();
        let paged_post = pivot_post.i();
        let paged_lbl = pivot_lbl.i();
        pivot_pre.i_inv();
        paged_pre.next_refines(paged_post, paged_lbl);
    }
}

} // verus!
