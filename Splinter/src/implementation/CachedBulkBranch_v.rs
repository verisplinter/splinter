// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;

use crate::allocation_layer::BranchTypes_v::{BranchNode, Summary};
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::LinkedBranch_v::{DiskView as BranchDiskView, LinkedBranch};
use crate::disk::GenericDisk_v::{AU, Address, Pointer};
use crate::implementation::CachedBranch_v::LoadedBranch;

verus! {

pub enum CachedBulkBranchPhase {
    Building { staged_nodes: LoadedBranch },
    Sealed { branch: LinkedBranch<Summary> },
}

pub struct CachedBulkBranch {
    pub phase: CachedBulkBranchPhase,
    pub mini_allocator: MiniAllocator,
}

pub enum CachedBulkBranchEvent {
    StagePage {
        addr: Address,
        write_nodes: LoadedBranch,
    },
    BulkSeal {
        root: Address,
        aux_ptr: Pointer,
        write_nodes: LoadedBranch,
    },
}

impl CachedBulkBranch {
    pub open spec fn new(aus: Set<AU>) -> Self {
        Self {
            phase: CachedBulkBranchPhase::Building {
                staged_nodes: Map::empty(),
            },
            mini_allocator: MiniAllocator::empty().add_aus(aus),
        }
    }

    pub open spec fn is_building(self) -> bool {
        self.phase is Building
    }

    pub open spec fn is_sealed(self) -> bool {
        self.phase is Sealed
    }

    pub open spec fn staged_nodes(self) -> LoadedBranch
        recommends self.is_building()
    {
        self.phase->staged_nodes
    }

    pub open spec fn sealed_root(self) -> Address
        recommends self.is_sealed()
    {
        self.phase->branch.root
    }

    pub open spec fn sealed_branch(self) -> LinkedBranch<Summary>
        recommends self.is_sealed()
    {
        self.phase->branch
    }

    pub open spec fn summary(self) -> Summary {
        self.mini_allocator.all_aus()
    }

    pub open spec fn can_fill(self, allocs: Set<AU>) -> bool {
        &&& self.is_building()
        &&& self.mini_allocator.all_aus().disjoint(allocs)
    }

    pub open spec fn fill_aus(self, allocs: Set<AU>) -> Self
        recommends self.can_fill(allocs)
    {
        Self {
            mini_allocator: self.mini_allocator.add_aus(allocs),
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

    pub open spec fn staged_branch(
        self,
        root: Address,
        write_nodes: LoadedBranch,
    ) -> LinkedBranch<Summary>
        recommends self.is_building()
    {
        LinkedBranch {
            root,
            disk_view: BranchDiskView {
                entries: self.staged_nodes().union_prefer_right(write_nodes),
            },
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

    pub open spec fn build_next(
        pre: Self,
        post: Self,
        event: CachedBulkBranchEvent,
        allocs: Set<AU>,
        deallocs: Set<AU>,
    ) -> bool {
        match event {
            CachedBulkBranchEvent::StagePage { addr, write_nodes } => {
                &&& pre.is_building()
                &&& allocs.is_empty()
                &&& deallocs.is_empty()
                &&& pre.mini_allocator.can_allocate(addr)
                &&& !pre.staged_nodes().contains_key(addr)
                &&& write_nodes.dom() == set![addr]
                &&& write_nodes[addr].wf()
                &&& write_nodes[addr].keys_strictly_sorted()
                &&& !(write_nodes[addr] is Auxiliary)
                &&& post == Self {
                    phase: CachedBulkBranchPhase::Building {
                        staged_nodes: pre.staged_nodes().insert(
                            addr,
                            write_nodes[addr],
                        ),
                    },
                    mini_allocator: pre.mini_allocator.allocate(addr),
                }
            }
            CachedBulkBranchEvent::BulkSeal { root, aux_ptr, write_nodes } => {
                let allocator = pre.bulk_allocator(root, aux_ptr);
                let branch = pre.staged_branch(root, write_nodes);
                &&& pre.is_building()
                &&& allocs.is_empty()
                &&& pre.mini_allocator.can_allocate(root)
                &&& !pre.staged_nodes().contains_key(root)
                &&& if aux_ptr is Some {
                    &&& root != aux_ptr.unwrap()
                    &&& pre.mini_allocator.allocate(root)
                        .can_allocate(aux_ptr.unwrap())
                    &&& !pre.staged_nodes().contains_key(aux_ptr.unwrap())
                    &&& write_nodes.dom() == set![root, aux_ptr.unwrap()]
                } else {
                    write_nodes.dom() == set![root]
                }
                &&& deallocs == allocator.removable_aus()
                &&& branch.valid_sealed_branch()
                &&& branch.tight_disk_view_with_summary()
                &&& branch.get_summary() == allocator.all_aus() - deallocs
                &&& post == Self {
                    phase: CachedBulkBranchPhase::Sealed { branch },
                    mini_allocator: allocator.prune(deallocs),
                }
            }
        }
    }
}

pub open spec fn cached_bulk_branch_alloc_aus(
    branches: Seq<CachedBulkBranch>,
) -> Set<AU> {
    crate::betree::Utils_v::union_seq_of_sets(Seq::new(
        branches.len(),
        |i: int| branches[i].mini_allocator.all_aus(),
    ))
}

pub proof fn cached_bulk_branch_alloc_aus_contains(
    branches: Seq<CachedBulkBranch>,
    au: AU,
) -> (idx: int)
    requires cached_bulk_branch_alloc_aus(branches).contains(au)
    ensures
        0 <= idx < branches.len(),
        branches[idx].mini_allocator.all_aus().contains(au),
{
    let sets = Seq::new(
        branches.len(),
        |i: int| branches[i].mini_allocator.all_aus(),
    );
    crate::betree::Utils_v::lemma_union_seq_of_sets_contains(sets, au);
    choose |i: int| 0 <= i < sets.len() && #[trigger] sets[i].contains(au)
}

pub proof fn cached_bulk_branch_alloc_aus_update_subset(
    branches: Seq<CachedBulkBranch>,
    idx: int,
    update: CachedBulkBranch,
    extra: Set<AU>,
)
    requires
        0 <= idx < branches.len(),
        update.mini_allocator.all_aus()
            <= branches[idx].mini_allocator.all_aus() + extra,
    ensures
        cached_bulk_branch_alloc_aus(branches.update(idx, update))
            <= cached_bulk_branch_alloc_aus(branches) + extra,
{
    let updated = branches.update(idx, update);
    assert forall |au: AU|
        #[trigger] cached_bulk_branch_alloc_aus(updated).contains(au)
        implies (cached_bulk_branch_alloc_aus(branches) + extra).contains(au)
    by {
        let source_idx = cached_bulk_branch_alloc_aus_contains(updated, au);
        if source_idx == idx {
            if !extra.contains(au) {
                let sets = Seq::new(
                    branches.len(),
                    |i: int| branches[i].mini_allocator.all_aus(),
                );
                assert(sets[idx].contains(au));
                crate::betree::Utils_v::lemma_set_subset_of_union_seq_of_sets(
                    sets,
                    au,
                );
            }
        } else {
            let sets = Seq::new(
                branches.len(),
                |i: int| branches[i].mini_allocator.all_aus(),
            );
            assert(updated[source_idx] == branches[source_idx]);
            assert(sets[source_idx].contains(au));
            crate::betree::Utils_v::lemma_set_subset_of_union_seq_of_sets(
                sets,
                au,
            );
        }
    }
}

pub proof fn cached_bulk_branch_alloc_aus_update_remove_exact(
    branches: Seq<CachedBulkBranch>,
    idx: int,
    update: CachedBulkBranch,
    removed: Set<AU>,
)
    requires
        0 <= idx < branches.len(),
        update.mini_allocator.all_aus()
            == branches[idx].mini_allocator.all_aus() - removed,
        removed <= branches[idx].mini_allocator.all_aus(),
        forall |left: int, right: int|
            0 <= left < right < branches.len()
            ==> (#[trigger] branches[left]).mini_allocator.all_aus().disjoint(
                (#[trigger] branches[right]).mini_allocator.all_aus(),
            ),
    ensures
        cached_bulk_branch_alloc_aus(branches.update(idx, update))
            == cached_bulk_branch_alloc_aus(branches) - removed,
{
    let updated = branches.update(idx, update);
    cached_bulk_branch_alloc_aus_update_subset(
        branches,
        idx,
        update,
        Set::empty(),
    );
    assert forall |au: AU|
        #[trigger] cached_bulk_branch_alloc_aus(updated).contains(au)
        <==> (cached_bulk_branch_alloc_aus(branches) - removed).contains(au)
    by {
        if cached_bulk_branch_alloc_aus(updated).contains(au) {
            let source_idx = cached_bulk_branch_alloc_aus_contains(updated, au);
            if source_idx == idx {
                assert(update.mini_allocator.all_aus().contains(au));
                assert(branches[idx].mini_allocator.all_aus().contains(au));
                assert(!removed.contains(au));
            } else {
                assert(updated[source_idx] == branches[source_idx]);
                assert(branches[source_idx].mini_allocator.all_aus().contains(au));
                if branches[idx].mini_allocator.all_aus().contains(au) {
                    let (left, right) = if source_idx < idx {
                        (source_idx, idx)
                    } else {
                        (idx, source_idx)
                    };
                    assert(branches[left].mini_allocator.all_aus().disjoint(
                        branches[right].mini_allocator.all_aus(),
                    ));
                    assert(false);
                }
                assert(!removed.contains(au));
            }
        } else if cached_bulk_branch_alloc_aus(branches).contains(au)
            && !removed.contains(au)
        {
            let source_idx = cached_bulk_branch_alloc_aus_contains(branches, au);
            if source_idx == idx {
                assert(update.mini_allocator.all_aus().contains(au));
                let sets = Seq::new(
                    updated.len(),
                    |i: int| updated[i].mini_allocator.all_aus(),
                );
                assert(sets[idx].contains(au));
                crate::betree::Utils_v::lemma_set_subset_of_union_seq_of_sets(
                    sets,
                    au,
                );
            } else {
                assert(updated[source_idx] == branches[source_idx]);
                let sets = Seq::new(
                    updated.len(),
                    |i: int| updated[i].mini_allocator.all_aus(),
                );
                assert(sets[source_idx].contains(au));
                crate::betree::Utils_v::lemma_set_subset_of_union_seq_of_sets(
                    sets,
                    au,
                );
            }
        }
    }
}

pub proof fn cached_bulk_branch_alloc_aus_remove_subset(
    branches: Seq<CachedBulkBranch>,
    idx: int,
)
    requires 0 <= idx < branches.len()
    ensures
        cached_bulk_branch_alloc_aus(branches.remove(idx))
            <= cached_bulk_branch_alloc_aus(branches),
{
    let removed = branches.remove(idx);
    assert forall |au: AU|
        #[trigger] cached_bulk_branch_alloc_aus(removed).contains(au)
        implies cached_bulk_branch_alloc_aus(branches).contains(au)
    by {
        let removed_idx = cached_bulk_branch_alloc_aus_contains(removed, au);
        let source_idx = if removed_idx < idx {
            removed_idx
        } else {
            removed_idx + 1
        };
        let sets = Seq::new(
            branches.len(),
            |i: int| branches[i].mini_allocator.all_aus(),
        );
        assert(branches[source_idx] == removed[removed_idx]);
        assert(sets[source_idx].contains(au));
        crate::betree::Utils_v::lemma_set_subset_of_union_seq_of_sets(sets, au);
    }
}

pub proof fn cached_bulk_branch_alloc_aus_remove_exact(
    branches: Seq<CachedBulkBranch>,
    idx: int,
)
    requires
        0 <= idx < branches.len(),
        forall |left: int, right: int|
            0 <= left < right < branches.len()
            ==> (#[trigger] branches[left]).mini_allocator.all_aus().disjoint(
                (#[trigger] branches[right]).mini_allocator.all_aus(),
            ),
    ensures
        cached_bulk_branch_alloc_aus(branches.remove(idx))
            == cached_bulk_branch_alloc_aus(branches)
                - branches[idx].mini_allocator.all_aus(),
{
    let removed = branches.remove(idx);
    cached_bulk_branch_alloc_aus_remove_subset(branches, idx);
    assert forall |au: AU|
        #[trigger] cached_bulk_branch_alloc_aus(removed).contains(au)
        <==> (cached_bulk_branch_alloc_aus(branches)
            - branches[idx].mini_allocator.all_aus()).contains(au)
    by {
        if cached_bulk_branch_alloc_aus(removed).contains(au) {
            let removed_idx = cached_bulk_branch_alloc_aus_contains(removed, au);
            let source_idx = if removed_idx < idx {
                removed_idx
            } else {
                removed_idx + 1
            };
            assert(branches[source_idx].mini_allocator.all_aus().contains(au));
            assert(source_idx != idx);
            let (left, right) = if source_idx < idx {
                (source_idx, idx)
            } else {
                (idx, source_idx)
            };
            assert(branches[left].mini_allocator.all_aus().disjoint(
                branches[right].mini_allocator.all_aus(),
            ));
            assert(!branches[idx].mini_allocator.all_aus().contains(au));
        } else if cached_bulk_branch_alloc_aus(branches).contains(au)
            && !branches[idx].mini_allocator.all_aus().contains(au)
        {
            let source_idx = cached_bulk_branch_alloc_aus_contains(branches, au);
            assert(source_idx != idx);
            let removed_idx = if source_idx < idx {
                source_idx
            } else {
                source_idx - 1
            };
            assert(0 <= removed_idx < removed.len());
            assert(removed[removed_idx] == branches[source_idx]);
            let sets = Seq::new(
                removed.len(),
                |i: int| removed[i].mini_allocator.all_aus(),
            );
            assert(sets[removed_idx].contains(au));
            crate::betree::Utils_v::lemma_set_subset_of_union_seq_of_sets(
                sets,
                au,
            );
        }
    }
}

pub proof fn cached_bulk_branch_alloc_aus_push_subset(
    branches: Seq<CachedBulkBranch>,
    append: CachedBulkBranch,
    extra: Set<AU>,
)
    requires append.mini_allocator.all_aus() <= extra
    ensures
        cached_bulk_branch_alloc_aus(branches.push(append))
            <= cached_bulk_branch_alloc_aus(branches) + extra,
{
    let pushed = branches.push(append);
    assert forall |au: AU|
        #[trigger] cached_bulk_branch_alloc_aus(pushed).contains(au)
        implies (cached_bulk_branch_alloc_aus(branches) + extra).contains(au)
    by {
        let pushed_idx = cached_bulk_branch_alloc_aus_contains(pushed, au);
        if pushed_idx < branches.len() {
            let sets = Seq::new(
                branches.len(),
                |i: int| branches[i].mini_allocator.all_aus(),
            );
            assert(pushed[pushed_idx] == branches[pushed_idx]);
            assert(sets[pushed_idx].contains(au));
            crate::betree::Utils_v::lemma_set_subset_of_union_seq_of_sets(
                sets,
                au,
            );
        } else {
            assert(pushed_idx == branches.len());
        }
    }
}

pub proof fn cached_bulk_branch_build_all_aus(
    pre: CachedBulkBranch,
    post: CachedBulkBranch,
    event: CachedBulkBranchEvent,
    allocs: Set<AU>,
    deallocs: Set<AU>,
)
    requires
        pre.mini_allocator.wf(),
        CachedBulkBranch::build_next(pre, post, event, allocs, deallocs),
    ensures
        post.mini_allocator.all_aus()
            <= pre.mini_allocator.all_aus() + allocs,
        post.mini_allocator.all_aus()
            == (pre.mini_allocator.all_aus() + allocs) - deallocs,
{

    match event {
        CachedBulkBranchEvent::StagePage { addr, .. } => {
            crate::implementation::BranchProofUtils_v::
                mini_allocator_allocate_preserves_all_aus(
                    pre.mini_allocator,
                    addr,
                );
        }
        CachedBulkBranchEvent::BulkSeal { root, aux_ptr, .. } => {
            let with_root = pre.mini_allocator.allocate(root);
            crate::implementation::BranchProofUtils_v::
                mini_allocator_allocate_preserves_all_aus(
                    pre.mini_allocator,
                    root,
                );
            let allocator = if aux_ptr is Some {
                crate::implementation::BranchProofUtils_v::
                    mini_allocator_allocate_preserves_all_aus(
                        with_root,
                        aux_ptr.unwrap(),
                    );
                with_root.allocate(aux_ptr.unwrap())
            } else {
                with_root
            };
            allocator.prune_preserves_wf(deallocs);
        }
    }
}

pub proof fn cached_bulk_branch_fill_all_aus(
    pre: CachedBulkBranch,
    post: CachedBulkBranch,
    allocs: Set<AU>,
    deallocs: Set<AU>,
)
    requires
        pre.mini_allocator.wf(),
        CachedBulkBranch::fill_next(pre, post, allocs, deallocs),
    ensures
        post.mini_allocator.all_aus()
            == pre.mini_allocator.all_aus() + allocs,
{

    crate::implementation::BranchProofUtils_v::
        mini_allocator_add_aus_preserves_all_aus(
            pre.mini_allocator,
            allocs,
        );
}

} // verus!
