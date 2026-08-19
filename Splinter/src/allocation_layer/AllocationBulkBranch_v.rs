// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;

use crate::allocation_layer::BranchTypes_v::Summary;
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::Buffer_v::SimpleBuffer;
use crate::betree::LinkedBranch_v::LinkedBranch;
use crate::betree::Utils_v::{
    lemma_set_subset_of_union_seq_of_sets,
    lemma_union_seq_of_sets_contains,
    union_seq_of_sets,
};
use crate::disk::GenericDisk_v::{AU, Address, Pointer};

verus! {

// The active Betree bulk loader never mutates a linked branch in place. It
// accumulates allocated pages while building and installs the complete physical
// branch as one witness at seal time.
pub enum BulkBranchPhase {
    Building,
    Sealed { branch: LinkedBranch<Summary> },
}

pub struct AllocationBulkBranch {
    pub phase: BulkBranchPhase,
    pub mini_allocator: MiniAllocator,
}

pub enum BulkBranchEvent {
    StagePage { addr: Address },
    BulkSeal {
        root: Address,
        aux_ptr: Pointer,
        branch: LinkedBranch<Summary>,
    },
}

impl AllocationBulkBranch {
    pub open spec fn new(free_aus: Set<AU>) -> Self {
        Self {
            phase: BulkBranchPhase::Building,
            mini_allocator: MiniAllocator::empty().add_aus(free_aus),
        }
    }

    pub open spec fn is_building(self) -> bool {
        self.phase is Building
    }

    pub open spec fn is_sealed(self) -> bool {
        self.phase is Sealed
    }

    pub open spec fn sealed_branch(self) -> LinkedBranch<Summary>
        recommends self.is_sealed()
    {
        self.phase->branch
    }

    pub open spec fn sealed_buffer(self) -> SimpleBuffer
        recommends self.is_sealed()
    {
        self.sealed_branch().i().i()
    }

    pub open spec fn summary(self) -> Summary
        recommends self.is_sealed()
    {
        self.sealed_branch().get_summary()
    }

    pub open spec fn can_fill(self, aus: Set<AU>) -> bool {
        &&& self.is_building()
        &&& self.mini_allocator.allocs.dom().disjoint(aus)
    }

    pub open spec fn fill_aus(self, aus: Set<AU>) -> Self
        recommends self.can_fill(aus)
    {
        Self {
            mini_allocator: self.mini_allocator.add_aus(aus),
            ..self
        }
    }

    pub open spec fn fill_next(
        pre: Self,
        post: Self,
        allocs: Set<AU>,
        deallocs: Set<AU>,
    ) -> bool {
        &&& deallocs.is_empty()
        &&& pre.can_fill(allocs)
        &&& post == pre.fill_aus(allocs)
    }

    pub open spec fn can_stage_page(self, addr: Address) -> bool {
        &&& self.is_building()
        &&& self.mini_allocator.can_allocate(addr)
    }

    pub open spec fn stage_page(self, addr: Address) -> Self
        recommends self.can_stage_page(addr)
    {
        Self {
            mini_allocator: self.mini_allocator.allocate(addr),
            ..self
        }
    }

    pub open spec fn bulk_allocator(
        self,
        root: Address,
        aux_ptr: Pointer,
    ) -> MiniAllocator {
        let with_root = self.mini_allocator.allocate(root);
        if aux_ptr is Some {
            with_root.allocate(aux_ptr.unwrap())
        } else {
            with_root
        }
    }

    pub open spec fn can_bulk_seal(
        self,
        root: Address,
        aux_ptr: Pointer,
        branch: LinkedBranch<Summary>,
        deallocs: Set<AU>,
    ) -> bool {
        let allocator = self.bulk_allocator(root, aux_ptr);
        &&& self.is_building()
        &&& self.mini_allocator.can_allocate(root)
        &&& if aux_ptr is Some {
            &&& root != aux_ptr.unwrap()
            &&& self.mini_allocator.allocate(root).can_allocate(aux_ptr.unwrap())
        } else {
            true
        }
        &&& allocator.removable_aus() == deallocs
        &&& branch.root == root
        &&& branch.valid_sealed_branch()
        &&& branch.tight_disk_view_with_summary()
        &&& branch.get_summary() == allocator.all_aus() - deallocs
    }

    pub open spec fn bulk_seal(
        self,
        root: Address,
        aux_ptr: Pointer,
        branch: LinkedBranch<Summary>,
        deallocs: Set<AU>,
    ) -> Self
        recommends self.can_bulk_seal(root, aux_ptr, branch, deallocs)
    {
        Self {
            phase: BulkBranchPhase::Sealed { branch },
            mini_allocator: self.bulk_allocator(root, aux_ptr).prune(deallocs),
        }
    }

    pub open spec fn build_next(
        pre: Self,
        post: Self,
        event: BulkBranchEvent,
        allocs: Set<AU>,
        deallocs: Set<AU>,
    ) -> bool {
        match event {
            BulkBranchEvent::StagePage { addr } => {
                &&& allocs.is_empty()
                &&& deallocs.is_empty()
                &&& pre.can_stage_page(addr)
                &&& post == pre.stage_page(addr)
            }
            BulkBranchEvent::BulkSeal { root, aux_ptr, branch } => {
                &&& allocs.is_empty()
                &&& pre.can_bulk_seal(root, aux_ptr, branch, deallocs)
                &&& post == pre.bulk_seal(root, aux_ptr, branch, deallocs)
            }
        }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.mini_allocator.wf()
        &&& self.is_sealed() ==> {
            let branch = self.sealed_branch();
            &&& branch.valid_sealed_branch()
            &&& branch.tight_disk_view_with_summary()
            &&& branch.get_summary() == self.mini_allocator.all_aus()
        }
    }

    pub proof fn fill_next_preserves_inv(
        pre: Self,
        post: Self,
        allocs: Set<AU>,
        deallocs: Set<AU>,
    )
        requires
            pre.inv(),
            Self::fill_next(pre, post, allocs, deallocs),
        ensures post.inv()
    {
    }

    pub proof fn build_next_preserves_inv(
        pre: Self,
        post: Self,
        event: BulkBranchEvent,
        allocs: Set<AU>,
        deallocs: Set<AU>,
    )
        requires
            pre.inv(),
            Self::build_next(pre, post, event, allocs, deallocs),
        ensures post.inv()
    {
        match event {
            BulkBranchEvent::StagePage { .. } => {}
            BulkBranchEvent::BulkSeal { root, aux_ptr, branch } => {
                let allocator = pre.bulk_allocator(root, aux_ptr);
                allocator.prune_preserves_wf(deallocs);
            }
        }
    }

    pub open spec fn alloc_aus(branches: Seq<Self>) -> Set<AU> {
        union_seq_of_sets(Seq::new(
            branches.len(),
            |i: int| branches[i].mini_allocator.all_aus(),
        ))
    }

    pub proof fn alloc_aus_singleton(self)
        ensures Self::alloc_aus(seq![self]) == self.mini_allocator.all_aus()
    {
        let aus = Seq::new(
            seq![self].len(),
            |i: int| seq![self][i].mini_allocator.all_aus(),
        );
        assert(union_seq_of_sets(aus.drop_last()) == Set::<AU>::empty());
    }

    pub proof fn alloc_aus_append(branches: Seq<Self>, append: Self)
        ensures
            Self::alloc_aus(branches.push(append))
                == Self::alloc_aus(branches) + append.mini_allocator.all_aus(),
    {
        let total = branches.push(append);
        let total_aus = Seq::new(
            total.len(),
            |i: int| total[i].mini_allocator.all_aus(),
        );
        let branch_aus = Seq::new(
            branches.len(),
            |i: int| branches[i].mini_allocator.all_aus(),
        );
        assert(total_aus.drop_last() == branch_aus);
        append.alloc_aus_singleton();
    }

    pub proof fn alloc_aus_remove(branches: Seq<Self>, idx: int)
        requires 0 <= idx < branches.len()
        ensures
            Self::alloc_aus(branches.remove(idx))
                + branches[idx].mini_allocator.all_aus()
                == Self::alloc_aus(branches),
        decreases branches.len()
    {
        if idx == branches.len() - 1 {
            Self::alloc_aus_append(branches.drop_last(), branches.last());
            assert(branches.drop_last().push(branches.last()) == branches);
            branches[idx].alloc_aus_singleton();
        } else {
            Self::alloc_aus_remove(branches.drop_last(), idx);
            assert(branches.drop_last().remove(idx) == branches.remove(idx).drop_last());
            Self::alloc_aus_append(branches.remove(idx).drop_last(), branches.last());
            Self::alloc_aus_append(branches.drop_last(), branches.last());
            assert(branches.drop_last().push(branches.last()) == branches);
            assert(branches.remove(idx).drop_last().push(branches.last()) == branches.remove(idx));
        }
    }

    pub proof fn alloc_aus_update(branches: Seq<Self>, idx: int, update: Self)
        requires
            0 <= idx < branches.len(),
            branches[idx].mini_allocator.all_aus()
                <= update.mini_allocator.all_aus(),
        ensures
            Self::alloc_aus(branches.update(idx, update))
                == Self::alloc_aus(branches)
                    + (update.mini_allocator.all_aus()
                        - branches[idx].mini_allocator.all_aus()),
        decreases branches.len()
    {
        if idx == branches.len() - 1 {
            let updated = branches.update(idx, update);
            Self::alloc_aus_append(branches.drop_last(), branches.last());
            Self::alloc_aus_append(updated.drop_last(), updated.last());
            assert(branches.drop_last().push(branches.last()) == branches);
            assert(updated.drop_last().push(updated.last()) == updated);
            branches.last().alloc_aus_singleton();
            updated.last().alloc_aus_singleton();
            assert(updated.drop_last() == branches.drop_last());
        } else {
            Self::alloc_aus_update(branches.drop_last(), idx, update);
            assert(branches.drop_last().update(idx, update)
                == branches.update(idx, update).drop_last());
            Self::alloc_aus_append(branches.update(idx, update).drop_last(), branches.last());
            Self::alloc_aus_append(branches.drop_last(), branches.last());
            assert(branches.drop_last().push(branches.last()) == branches);
            assert(branches.update(idx, update).drop_last().push(branches.last())
                == branches.update(idx, update));
        }
    }

    pub broadcast proof fn alloc_aus_ensures(branches: Seq<Self>, i: int)
        requires 0 <= i < branches.len()
        ensures
            #[trigger] branches[i].mini_allocator.all_aus()
                <= Self::alloc_aus(branches)
    {
        let aus = Seq::new(
            branches.len(),
            |j: int| branches[j].mini_allocator.all_aus(),
        );
        assert forall |au| #[trigger] branches[i].mini_allocator.all_aus().contains(au)
            implies Self::alloc_aus(branches).contains(au) by {
            assert(aus[i].contains(au));
            lemma_set_subset_of_union_seq_of_sets(aus, au);
        }
    }

    pub proof fn alloc_aus_contains(branches: Seq<Self>, au: AU) -> (i: int)
        requires Self::alloc_aus(branches).contains(au)
        ensures
            0 <= i < branches.len(),
            branches[i].mini_allocator.all_aus().contains(au),
    {
        let aus = Seq::new(
            branches.len(),
            |j: int| branches[j].mini_allocator.all_aus(),
        );
        lemma_union_seq_of_sets_contains(aus, au);
        choose |j: int| 0 <= j < aus.len() && #[trigger] aus[j].contains(au)
    }
}

} // verus!
