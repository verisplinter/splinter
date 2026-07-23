// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Direct refinement from CrashAwareCachingDiskBranchBetree to
// AbstractCrashAwareMap.

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::assert_maps_equal;

use crate::abstract_system::AbstractCrashAwareMap_v::{
    AbstractCrashAwareMap, Ephemeral as AbstractEphemeral,
};
use crate::abstract_system::AbstractMap_v::AbstractMap;
use crate::abstract_system::StampedMap_v::{empty, StampedMap};
use crate::allocation_layer::AllocationBetree_v::AllocationBetree;
use crate::allocation_layer::AllocationBetreeAbstractRefinement_v::*;
use crate::allocation_layer::AllocationBranchBetree_v::AllocationBranchBetree;
use crate::allocation_layer::AllocationBranchBetreeRefinement_v::*;
use crate::allocation_layer::AllocationBranch_v::{BranchNode, Summary};
use crate::allocation_layer::Likes_v::AULikes;
use crate::allocation_layer::LikesBetree_v::LikesBetree;
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::Buffer_v::SimpleBuffer;
use crate::betree::LinkedBetree_v::LinkedBetreeVars;
use crate::betree::PagedBetree_v::PagedBetree;
use crate::disk::GenericDisk_v::{
    set_addrs_disjoint_aus, to_aus, AU, Address,
};
use crate::implementation::CachedBranchBetree_v::{
    cached_branch_alloc_aus, CachedBranchBetree,
};
use crate::implementation::CachingDiskBranchBetree_v::{
    CachingDiskBranchBetree, loose_disk_for_summary, tight_branch_addrs,
    tight_branch_of, tight_sealed_branch_disk, to_betree_nodes,
    to_branch_nodes, visible_branch_disk,
};
use crate::implementation::CachingDiskBranchBetreeRefinement_v::*;
use crate::implementation::CachingDisk_v::CachingDisk;
use crate::implementation::CrashAwareCachingDiskBranchBetree_v::*;

verus! {

proof fn abstract_internal_stutters(
    pre: AbstractMap::State,
    post: AbstractMap::State,
)
    requires AbstractMap::State::next(
        pre,
        post,
        AbstractMap::Label::InternalLabel,
    )
    ensures post == pre
{
    reveal(AbstractMap::State::next);
    reveal(AbstractMap::State::next_by);
    let step = choose |step: AbstractMap::Step|
        AbstractMap::State::next_by(
            pre,
            post,
            AbstractMap::Label::InternalLabel,
            step,
        );
    match step {
        AbstractMap::Step::internal() => {
            reveal(AbstractMap::State::internal);
        }
        _ => {
            assert(false);
        }
    }
}

proof fn abstract_query_stutters(
    pre: AbstractMap::State,
    post: AbstractMap::State,
    lbl: AbstractMap::Label,
)
    requires
        lbl is QueryLabel,
        AbstractMap::State::next(pre, post, lbl),
    ensures post == pre
{
    reveal(AbstractMap::State::next);
    reveal(AbstractMap::State::next_by);
    let step = choose |step: AbstractMap::Step|
        AbstractMap::State::next_by(pre, post, lbl, step);
    match step {
        AbstractMap::Step::query() => {
            reveal(AbstractMap::State::query);
        }
        _ => {
            assert(false);
        }
    }
}

proof fn abstract_freeze_matches(
    state: AbstractMap::State,
    stamped_map: StampedMap,
)
    requires AbstractMap::State::next(
        state,
        state,
        AbstractMap::Label::FreezeAsLabel{stamped_map},
    )
    ensures stamped_map == state.stamped_map
{
    reveal(AbstractMap::State::next);
    reveal(AbstractMap::State::next_by);
    let step = choose |step: AbstractMap::Step|
        AbstractMap::State::next_by(
            state,
            state,
            AbstractMap::Label::FreezeAsLabel{stamped_map},
            step,
        );
    match step {
        AbstractMap::Step::freeze_as() => {
            reveal(AbstractMap::State::freeze_as);
        }
        _ => {
            assert(false);
        }
    }
}

impl CachingDiskBranchBetree::Label {
    pub open spec fn i_abstract(
        self,
        pre: CachingDiskBranchBetree::State,
    ) -> AbstractMap::Label {
        self.i(pre).i().i_abstract()
    }
}

impl CachingDiskBranchBetree::State {
    pub open spec fn i_abstract(self) -> AbstractMap::State
        recommends self.refinement_inv(),
    {
        self.i().i().i_abstract()
    }

    pub proof fn next_refines_abstract(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::next(pre, post, lbl),
        ensures
            post.refinement_inv(),
            AbstractMap::State::next(
                pre.i_abstract(),
                post.i_abstract(),
                lbl.i_abstract(pre),
            ),
    {
        Self::next_refines(pre, post, lbl);
        pre.i().i_inv();
        AllocationBranchBetree::State::next_refines(
            pre.i(),
            post.i(),
            lbl.i(pre),
        );
        AllocationBetree::State::next_refines_abstract(
            pre.i().i(),
            post.i().i(),
            lbl.i(pre).i(),
        );
    }

    pub proof fn i_abstract_seq_end(self)
        requires self.refinement_inv()
        ensures
            self.i_abstract().stamped_map.seq_end
                == self.betree.memtable.seq_end
    {
        self.i().i_inv();
        let allocation = self.i().i();
        assert(allocation.refinement_inv());
        let likes = allocation.i();
        assert(likes.inv());
        let linked = likes.i();
        assert(linked.inv());
        linked.i_inv();
        reveal(CachingDiskBranchBetree::State::i_abstract);
        reveal(AllocationBetree::State::i_abstract);
        reveal(PagedBetree::State::i);
    }
}

impl CachingDiskBranchBetreeImage {
    pub open spec fn recovery_witness(self)
        -> RecoveredCachingDiskBranchBetreeMetadata
        recommends self.valid()
    {
        choose |witness: RecoveredCachingDiskBranchBetreeMetadata|
            witness.valid_for(self)
    }

    pub open spec fn load(self) -> CachingDiskBranchBetree::State
        recommends self.valid()
    {
        let witness = self.recovery_witness();
        self.load_metadata(
            witness.betree_aus,
            witness.branch_aus,
            witness.branch_summary,
        )
    }

    pub proof fn recovery_witness_valid(self)
        requires self.valid()
        ensures self.recovery_witness().valid_for(self)
    {
        reveal(CachingDiskBranchBetreeImage::valid);
        assert forall |
            betree_aus: AULikes,
            branch_aus: AULikes,
            branch_summary: Map<AU, Summary>,
            initial_betree: LinkedBetreeVars::State<BranchNode>,
        | #[trigger] initial_refinement_witness_valid(
            self.disk(),
            self.metadata.root,
            self.metadata.seq_end,
            betree_aus,
            branch_aus,
            branch_summary,
            initial_betree,
        ) implies exists |witness: RecoveredCachingDiskBranchBetreeMetadata|
            witness.valid_for(self) by {
            let witness = RecoveredCachingDiskBranchBetreeMetadata {
                betree_aus,
                branch_aus,
                branch_summary,
                initial_betree,
            };
            assert(witness.valid_for(self));
        };
        assert(exists |candidate: RecoveredCachingDiskBranchBetreeMetadata|
            candidate.valid_for(self));
    }

    pub open spec fn i_abstract(self) -> AbstractMap::State
        recommends self.valid(),
    {
        self.load().i_abstract()
    }

    pub proof fn valid_refines(self)
        requires self.valid()
        ensures
            self.load().refinement_inv(),
            AllocationBranchBetree::State::initialize(
                self.load().i(),
                self.load().i().betree,
            ),
            AllocationBetree::State::initialize(
                self.load().i().i(),
                self.load().i().betree.i(),
            ),
            AbstractMap::State::initialize(
                self.i_abstract(),
                AllocationBetree::State::initial_i_abstract(
                    self.load().i().betree.i(),
                ),
            ),
    {
        let witness = self.recovery_witness();
        let initial = witness.initial_betree;
        let loaded = self.load();
        let cached = self.cached_betree(
            witness.betree_aus,
            witness.branch_aus,
            witness.branch_summary,
        );
        self.recovery_witness_valid();
        assert(CachingDiskBranchBetree::State::initialize(
            loaded,
            self.disk(),
            cached,
            self.metadata.root,
            self.metadata.seq_end,
            witness.betree_aus,
            witness.branch_aus,
            witness.branch_summary,
        )) by {
            reveal(CachingDiskBranchBetree::State::initialize);
            reveal(crate::implementation::CachedBranchBetree_v::CachedBranchBetree::State::initialize);
        }
        CachingDiskBranchBetree::State::init_refines(
            loaded,
            self.disk(),
            cached,
            self.metadata.root,
            self.metadata.seq_end,
            witness.betree_aus,
            witness.branch_aus,
            witness.branch_summary,
            initial,
        );
        loaded.i().init_refines(loaded.i().betree);
        loaded.i().i().init_refines_abstract(loaded.i().betree.i());
    }

    pub proof fn i_abstract_seq_end(self)
        requires self.valid()
        ensures self.i_abstract().stamped_map.seq_end == self.metadata.seq_end
    {
        self.valid_refines();
        self.load().i_abstract_seq_end();
    }

    pub proof fn empty_i_is_empty()
        ensures CachingDiskBranchBetreeImage::empty()
            .i_abstract().stamped_map == empty()
    {
        let image = CachingDiskBranchBetreeImage::empty();
        empty_image_valid();
        image.valid_refines();
        let loaded = image.load();
        let paged = loaded.i().i().i().i().i().i().i();
        assert(paged.root is Nil);
        assert(paged.memtable
            == crate::betree::Memtable_v::Memtable::empty_memtable(0));
        paged.empty_i_is_empty();
    }
}

pub struct RecoveredCachingDiskBranchBetreeMetadata {
    pub betree_aus: AULikes,
    pub branch_aus: AULikes,
    pub branch_summary: Map<AU, Summary>,
    pub initial_betree: LinkedBetreeVars::State<BranchNode>,
}

impl RecoveredCachingDiskBranchBetreeMetadata {
    pub open spec fn valid_for(
        self,
        image: CachingDiskBranchBetreeImage,
    ) -> bool {
        initial_refinement_witness_valid(
            image.disk(),
            image.metadata.root,
            image.metadata.seq_end,
            self.betree_aus,
            self.branch_aus,
            self.branch_summary,
            self.initial_betree,
        )
    }
}

pub open spec fn loaded_branch_roots(
    betree_nodes: Map<Address, crate::betree::LinkedBetree_v::BetreeNode>,
) -> Set<Address> {
    Set::new(|root: Address| exists |tree_addr: Address|
        betree_nodes.contains_key(tree_addr)
        && betree_buffer_roots(betree_nodes[tree_addr]).contains(root))
}

pub open spec fn recovery_frontier_inv(
    recovery: BetreeMetadataRecovery,
    image: CachingDiskBranchBetreeImage,
) -> bool
    recommends image.valid(),
{
    let witness = image.recovery_witness();
    let tree = initial_tight_tree(witness.initial_betree);
    let roots = tree.reachable_buffer_addrs();
    let summary = witness.branch_summary;
    let buffer = witness.initial_betree.linked.buffer_dv;
    let loaded = recovery.betree_nodes.dom();
    &&& recovery.disk.inv()
    &&& recovery.disk.visible() == image.disk().visible()
    &&& recovery.betree_nodes <= tree.dv.entries
    &&& recovery.pending_betree <= tree.dv.entries.dom()
    &&& loaded.disjoint(recovery.pending_betree)
    &&& image.metadata.root is Some ==> {
        let root = image.metadata.root.unwrap();
        loaded.contains(root)
            || recovery.pending_betree.contains(root)
    }
    &&& forall |addr: Address|
        #[trigger] loaded.contains(addr) ==> {
            betree_child_addrs(recovery.betree_nodes[addr])
                <= loaded + recovery.pending_betree
        }
    &&& recovery.branch_roots
        == loaded_branch_roots(recovery.betree_nodes)
    &&& recovery.branch_roots <= roots
    &&& set_addrs_disjoint_aus(recovery.branch_roots)
    &&& recovery.pending_branch_roots <= recovery.branch_roots
    &&& recovery.pending_branch_aux.dom() <= recovery.branch_roots
    &&& recovery.branch_summary <= summary
    &&& recovery.branch_summary.dom()
        <= to_aus(recovery.branch_roots)
    &&& forall |root: Address|
        #[trigger] recovery.branch_roots.contains(root) ==> {
            &&& recovery.pending_branch_roots.contains(root)
                || recovery.pending_branch_aux.contains_key(root)
                || recovery.branch_summary.contains_key(root.au)
            &&& recovery.pending_branch_roots.contains(root) ==> {
                &&& !recovery.pending_branch_aux.contains_key(root)
                &&& !recovery.branch_summary.contains_key(root.au)
            }
            &&& recovery.pending_branch_aux.contains_key(root) ==> {
                &&& !recovery.branch_summary.contains_key(root.au)
                &&& buffer.entries.contains_key(root)
                &&& buffer.entries[root] is Index
                &&& buffer.entries[root].arrow_Index_aux_ptr()
                    == Option::Some(
                        recovery.pending_branch_aux[root],
                    )
            }
        }
}

impl BetreeMetadataRecovery {
    pub open spec fn refinement_inv(
        self,
        image: CachingDiskBranchBetreeImage,
    ) -> bool {
        &&& image.valid()
        &&& recovery_frontier_inv(self, image)
    }
}

pub proof fn recovery_witnesses_same_initial(
    image: CachingDiskBranchBetreeImage,
    left: RecoveredCachingDiskBranchBetreeMetadata,
    right: RecoveredCachingDiskBranchBetreeMetadata,
)
    requires
        left.valid_for(image),
        right.valid_for(image),
    ensures left.initial_betree == right.initial_betree,
{
    reveal(initial_refinement_witness_valid);
    let left_tree = initial_tight_tree(left.initial_betree);
    let right_tree = initial_tight_tree(right.initial_betree);
    let full_tree_entries = to_betree_nodes(image.disk().visible());

    assert(tight_betree_candidate(
        image.metadata.root,
        full_tree_entries,
        left_tree,
    )) by {
        let bounded = full_tree_entries.restrict(
            crate::implementation::CachingDisk_v::addresses_in_aus(
                left.betree_aus.dom(),
            ),
        );
        assert(left_tree.dv.entries <= bounded);
        assert(bounded <= full_tree_entries);
        vstd::map_lib::lemma_submap_of_trans(
            left_tree.dv.entries,
            bounded,
            full_tree_entries,
        );
    }
    assert(tight_betree_candidate(
        image.metadata.root,
        full_tree_entries,
        right_tree,
    )) by {
        let bounded = full_tree_entries.restrict(
            crate::implementation::CachingDisk_v::addresses_in_aus(
                right.betree_aus.dom(),
            ),
        );
        assert(right_tree.dv.entries <= bounded);
        assert(bounded <= full_tree_entries);
        vstd::map_lib::lemma_submap_of_trans(
            right_tree.dv.entries,
            bounded,
            full_tree_entries,
        );
    }
    tight_betree_unique(
        image.metadata.root,
        full_tree_entries,
        left_tree,
        right_tree,
    );
    assert(left_tree == right_tree);
    assert(left.initial_betree.memtable
        == right.initial_betree.memtable);
    assert(left.initial_betree.linked.root
        == right.initial_betree.linked.root);
    assert(left.initial_betree.linked.dv
        == right.initial_betree.linked.dv);

    let roots = left_tree.reachable_buffer_addrs();
    let full_branch_disk = BufferDisk {
        entries: to_branch_nodes(image.disk().visible()),
    };
    let left_loose = visible_branch_disk(
        image.disk(),
        left.branch_summary,
    );
    let right_loose = visible_branch_disk(
        image.disk(),
        right.branch_summary,
    );
    let left_buffer = left.initial_betree.linked.buffer_dv;
    let right_buffer = right.initial_betree.linked.buffer_dv;
    assert(left_buffer == tight_sealed_branch_disk(
        left_loose,
        roots,
        left.branch_summary,
    ));
    assert(right_tree.reachable_buffer_addrs() == roots);
    assert(right_buffer == tight_sealed_branch_disk(
        right_loose,
        roots,
        right.branch_summary,
    ));
    assert(left_loose.entries <= full_branch_disk.entries);
    assert(right_loose.entries <= full_branch_disk.entries);
    assert(left_buffer.entries <= left_loose.entries);
    assert(right_buffer.entries <= right_loose.entries);
    vstd::map_lib::lemma_submap_of_trans(
        left_buffer.entries,
        left_loose.entries,
        full_branch_disk.entries,
    );
    vstd::map_lib::lemma_submap_of_trans(
        right_buffer.entries,
        right_loose.entries,
        full_branch_disk.entries,
    );

    assert_maps_equal!(
        left_buffer.entries,
        right_buffer.entries,
        addr => {
            if left_buffer.entries.contains_key(addr) {
                assert(tight_branch_addrs(
                    left_loose,
                    roots,
                    left.branch_summary,
                ).contains(addr));
                let root = choose |root: Address| {
                    &&& roots.contains(root)
                    &&& tight_branch_of(
                        loose_disk_for_summary(
                            left_loose,
                            left.branch_summary[root.au],
                        ),
                        root,
                        left.branch_summary[root.au],
                    ).disk_view.entries.contains_key(addr)
                };
                assert(left.branch_summary.contains_key(root.au));
                assert(right.branch_summary.contains_key(root.au));
                let left_summary = left.branch_summary[root.au];
                let right_summary = right.branch_summary[root.au];
                let left_root_loose = loose_disk_for_summary(
                    left_loose,
                    left_summary,
                );
                let right_root_loose = loose_disk_for_summary(
                    right_loose,
                    right_summary,
                );
                let left_branch = tight_branch_of(
                    left_root_loose,
                    root,
                    left_summary,
                );
                let right_branch = tight_branch_of(
                    right_root_loose,
                    root,
                    right_summary,
                );
                tight_branch_of_is_candidate(
                    left_root_loose,
                    root,
                    left_summary,
                );
                tight_branch_of_is_candidate(
                    right_root_loose,
                    root,
                    right_summary,
                );
                assert(left_root_loose.entries <= left_loose.entries);
                assert(left_loose.entries <= full_branch_disk.entries);
                vstd::map_lib::lemma_submap_of_trans(
                    left_branch.disk_view.entries,
                    left_root_loose.entries,
                    left_loose.entries,
                );
                vstd::map_lib::lemma_submap_of_trans(
                    left_branch.disk_view.entries,
                    left_loose.entries,
                    full_branch_disk.entries,
                );
                assert(right_root_loose.entries <= right_loose.entries);
                assert(right_loose.entries <= full_branch_disk.entries);
                vstd::map_lib::lemma_submap_of_trans(
                    right_branch.disk_view.entries,
                    right_root_loose.entries,
                    right_loose.entries,
                );
                vstd::map_lib::lemma_submap_of_trans(
                    right_branch.disk_view.entries,
                    right_loose.entries,
                    full_branch_disk.entries,
                );
                assert(left_branch.disk_view.entries
                    <= full_branch_disk.entries);
                assert(right_branch.disk_view.entries
                    <= full_branch_disk.entries);
                tight_branch_unique_in_unbounded_disk(
                    full_branch_disk,
                    root,
                    left_branch,
                    right_branch,
                );
                assert(left_branch == right_branch);
                assert(right_branch.disk_view.entries.contains_key(addr));
                assert(tight_branch_addrs(
                    right_loose,
                    roots,
                    right.branch_summary,
                ).contains(addr)) by {
                    assert(exists |candidate_root: Address| {
                        &&& roots.contains(candidate_root)
                        &&& tight_branch_of(
                            loose_disk_for_summary(
                                right_loose,
                                right.branch_summary[candidate_root.au],
                            ),
                            candidate_root,
                            right.branch_summary[candidate_root.au],
                        ).disk_view.entries.contains_key(addr)
                    }) by {
                        assert(roots.contains(root));
                    };
                }
                assert(right_buffer.entries
                    == right_loose.entries.restrict(tight_branch_addrs(
                        right_loose,
                        roots,
                        right.branch_summary,
                    )));
                assert(right_buffer.entries.contains_key(addr));
                assert(left_buffer.entries[addr]
                    == full_branch_disk.entries[addr]);
                assert(right_buffer.entries[addr]
                    == full_branch_disk.entries[addr]);
            }
            if right_buffer.entries.contains_key(addr) {
                assert(tight_branch_addrs(
                    right_loose,
                    roots,
                    right.branch_summary,
                ).contains(addr));
                let root = choose |root: Address| {
                    &&& roots.contains(root)
                    &&& tight_branch_of(
                        loose_disk_for_summary(
                            right_loose,
                            right.branch_summary[root.au],
                        ),
                        root,
                        right.branch_summary[root.au],
                    ).disk_view.entries.contains_key(addr)
                };
                assert(right.branch_summary.contains_key(root.au));
                assert(left.branch_summary.contains_key(root.au));
                let right_summary = right.branch_summary[root.au];
                let left_summary = left.branch_summary[root.au];
                let right_root_loose = loose_disk_for_summary(
                    right_loose,
                    right_summary,
                );
                let left_root_loose = loose_disk_for_summary(
                    left_loose,
                    left_summary,
                );
                let right_branch = tight_branch_of(
                    right_root_loose,
                    root,
                    right_summary,
                );
                let left_branch = tight_branch_of(
                    left_root_loose,
                    root,
                    left_summary,
                );
                tight_branch_of_is_candidate(
                    right_root_loose,
                    root,
                    right_summary,
                );
                tight_branch_of_is_candidate(
                    left_root_loose,
                    root,
                    left_summary,
                );
                assert(right_root_loose.entries <= right_loose.entries);
                assert(right_loose.entries <= full_branch_disk.entries);
                vstd::map_lib::lemma_submap_of_trans(
                    right_branch.disk_view.entries,
                    right_root_loose.entries,
                    right_loose.entries,
                );
                vstd::map_lib::lemma_submap_of_trans(
                    right_branch.disk_view.entries,
                    right_loose.entries,
                    full_branch_disk.entries,
                );
                assert(left_root_loose.entries <= left_loose.entries);
                assert(left_loose.entries <= full_branch_disk.entries);
                vstd::map_lib::lemma_submap_of_trans(
                    left_branch.disk_view.entries,
                    left_root_loose.entries,
                    left_loose.entries,
                );
                vstd::map_lib::lemma_submap_of_trans(
                    left_branch.disk_view.entries,
                    left_loose.entries,
                    full_branch_disk.entries,
                );
                assert(right_branch.disk_view.entries
                    <= full_branch_disk.entries);
                assert(left_branch.disk_view.entries
                    <= full_branch_disk.entries);
                tight_branch_unique_in_unbounded_disk(
                    full_branch_disk,
                    root,
                    right_branch,
                    left_branch,
                );
                assert(right_branch == left_branch);
                assert(left_branch.disk_view.entries.contains_key(addr));
                assert(tight_branch_addrs(
                    left_loose,
                    roots,
                    left.branch_summary,
                ).contains(addr)) by {
                    assert(exists |candidate_root: Address| {
                        &&& roots.contains(candidate_root)
                        &&& tight_branch_of(
                            loose_disk_for_summary(
                                left_loose,
                                left.branch_summary[candidate_root.au],
                            ),
                            candidate_root,
                            left.branch_summary[candidate_root.au],
                        ).disk_view.entries.contains_key(addr)
                    }) by {
                        assert(roots.contains(root));
                    };
                }
                assert(left_buffer.entries
                    == left_loose.entries.restrict(tight_branch_addrs(
                        left_loose,
                        roots,
                        left.branch_summary,
                    )));
                assert(left_buffer.entries.contains_key(addr));
            }
        }
    );
    assert(left.initial_betree.linked.buffer_dv
        == right.initial_betree.linked.buffer_dv);
}

pub proof fn valid_recovery_matches_image(
    image: CachingDiskBranchBetreeImage,
    recovered: RecoveredCachingDiskBranchBetreeMetadata,
)
    requires
        image.valid(),
        recovered.valid_for(image),
    ensures
        image.load_metadata(
            recovered.betree_aus,
            recovered.branch_aus,
            recovered.branch_summary,
        ).i_abstract() == image.i_abstract(),
{
    image.recovery_witness_valid();
    let canonical = image.recovery_witness();
    recovery_witnesses_same_initial(image, recovered, canonical);
    let recovered_state = image.load_metadata(
        recovered.betree_aus,
        recovered.branch_aus,
        recovered.branch_summary,
    );
    let canonical_state = image.load();
    CachingDiskBranchBetree::State::init_refines(
        recovered_state,
        image.disk(),
        recovered_state.betree,
        image.metadata.root,
        image.metadata.seq_end,
        recovered.betree_aus,
        recovered.branch_aus,
        recovered.branch_summary,
        recovered.initial_betree,
    );
    CachingDiskBranchBetree::State::init_refines(
        canonical_state,
        image.disk(),
        canonical_state.betree,
        image.metadata.root,
        image.metadata.seq_end,
        canonical.betree_aus,
        canonical.branch_aus,
        canonical.branch_summary,
        canonical.initial_betree,
    );
    assert(recovered_state.i().betree
        == recovered.initial_betree);
    assert(canonical_state.i().betree
        == canonical.initial_betree);
    assert(recovered_state.i().betree
        == canonical_state.i().betree);
    recovered_state.i().i_inv();
    canonical_state.i().i_inv();
    reveal(CachingDiskBranchBetree::State::i_abstract);
}

pub proof fn frozen_image_from_current_refines(
    state: CachingDiskBranchBetree::State,
    frozen: FrozenCachingDiskBranchBetree,
)
    requires
        state.refinement_inv(),
        state.betree.memtable.is_empty(),
        state.betree.compactors.len() == 0,
        state.betree.wip_branches.len() == 0,
        frozen.metadata.root == state.betree.root,
        frozen.metadata.seq_end == state.betree.memtable.seq_end,
        frozen.aus == state.betree.durable_aus(),
    ensures
        CachingDiskBranchBetreeImage::materialized_from_visible(
            state,
            frozen,
        ).valid(),
        CachingDiskBranchBetreeImage::materialized_from_visible(
            state,
            frozen,
        ).i_abstract() == state.i_abstract(),
{
    let image =
        CachingDiskBranchBetreeImage::materialized_from_visible(
            state,
            frozen,
        );
    let recovered = RecoveredCachingDiskBranchBetreeMetadata {
        betree_aus: state.betree.betree_aus,
        branch_aus: state.betree.branch_aus,
        branch_summary: state.betree.branch_summary,
        initial_betree: state.i().betree,
    };
    assert(image.disk() == durable_recovery_disk(state)) by {
        assert_maps_equal!(
            image.disk().persistent,
            durable_recovery_disk(state).persistent,
            addr => {}
        );
    }
    durable_recovery_witness_valid(state);
    CachingDisk::State::persistent_only_inv(image.persistent);
    assert(image.disk().inv());
    assert(recovered.valid_for(image));
    assert(image.valid()) by {
        reveal(CachingDiskBranchBetreeImage::valid);
        assert(exists |
            betree_aus: AULikes,
            branch_aus: AULikes,
            branch_summary: Map<AU, Summary>,
            initial_betree: LinkedBetreeVars::State<BranchNode>,
        | #[trigger] initial_refinement_witness_valid(
            image.disk(),
            image.metadata.root,
            image.metadata.seq_end,
            betree_aus,
            branch_aus,
            branch_summary,
            initial_betree,
        )) by {
            assert(recovered.valid_for(image));
        };
    }
    valid_recovery_matches_image(image, recovered);
    let recovered_state = image.load_metadata(
        recovered.betree_aus,
        recovered.branch_aus,
        recovered.branch_summary,
    );
    CachingDiskBranchBetree::State::init_refines(
        recovered_state,
        image.disk(),
        recovered_state.betree,
        image.metadata.root,
        image.metadata.seq_end,
        recovered.betree_aus,
        recovered.branch_aus,
        recovered.branch_summary,
        recovered.initial_betree,
    );
    assert(recovered_state.i() == state.i());
    state.i().i_inv();
    recovered_state.i().i_inv();
    reveal(CachingDiskBranchBetree::State::i_abstract);
}

impl EphemeralCachingDiskBranchBetree {
    pub open spec fn i_abstract(
        self,
        persistent: CachingDiskBranchBetreeImage,
    ) -> AbstractEphemeral {
        match self {
            EphemeralCachingDiskBranchBetree::Unknown =>
                AbstractEphemeral::Unknown,
            EphemeralCachingDiskBranchBetree::Loading{..} =>
                AbstractEphemeral::Known{v: persistent.i_abstract()},
            EphemeralCachingDiskBranchBetree::Known{v, ..} =>
                AbstractEphemeral::Known{v: v.i_abstract()},
        }
    }
}

impl CrashAwareCachingDiskBranchBetree::State {
    pub open spec fn persistent_i(self) -> StampedMap {
        self.persistent.i_abstract().stamped_map
    }

    pub open spec fn frozen_i(self) -> Option<StampedMap> {
        if self.frozen is Some && self.ephemeral is Known {
            Option::Some(self.frozen_image().i_abstract().stamped_map)
        } else {
            Option::None
        }
    }

    pub open spec fn frozen_image(
        self,
    ) -> CachingDiskBranchBetreeImage
        recommends
            self.frozen is Some,
            self.ephemeral is Known,
    {
        CachingDiskBranchBetreeImage::materialized_from_visible(
            self.ephemeral->v,
            self.frozen.unwrap(),
        )
    }

    pub open spec fn i_abstract(self) -> AbstractCrashAwareMap::State {
        AbstractCrashAwareMap::State {
            persistent: self.persistent_i(),
            ephemeral: self.ephemeral.i_abstract(self.persistent),
            frozen: self.frozen_i(),
        }
    }

    pub open spec fn refinement_inv(self) -> bool {
        &&& self.inv()
        &&& self.ephemeral is Loading ==>
            self.ephemeral->recovery.refinement_inv(self.persistent)
        &&& self.ephemeral is Known ==>
            self.ephemeral->v.refinement_inv()
        &&& self.frozen is Some ==>
            self.frozen_image().valid()
        &&& self.frozen is Some ==>
            cached_branch_alloc_aus(
                self.ephemeral->v.betree.wip_branches,
            ).disjoint(self.frozen.unwrap().aus)
        &&& self.prepared is Some ==> {
            &&& self.ephemeral is Known
            &&& self.prepared.unwrap().i_abstract()
                == self.frozen_image().i_abstract()
        }
    }

    pub open spec fn label_i_abstract(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskBranchBetree::Label,
    ) -> AbstractCrashAwareMap::Label {
        match lbl {
            CrashAwareCachingDiskBranchBetree::Label::LoadEphemeral => {
                AbstractCrashAwareMap::Label::LoadEphemeralFromPersistentLabel {
                    end_lsn: self.persistent_i().seq_end,
                }
            }
            CrashAwareCachingDiskBranchBetree::Label::RecoverMetadata{..} =>
                AbstractCrashAwareMap::Label::InternalLabel,
            CrashAwareCachingDiskBranchBetree::Label::LoadMetadata =>
                AbstractCrashAwareMap::Label::InternalLabel,
            CrashAwareCachingDiskBranchBetree::Label::Ephemeral{op, ..} => {
                match op.i_abstract(self.ephemeral->v) {
                    AbstractMap::Label::QueryLabel{end_lsn, key, value} =>
                        AbstractCrashAwareMap::Label::QueryLabel {
                            end_lsn,
                            key,
                            value,
                        },
                    AbstractMap::Label::PutLabel{puts} =>
                        AbstractCrashAwareMap::Label::PutRecordsLabel {
                            records: puts,
                        },
                    _ => AbstractCrashAwareMap::Label::InternalLabel,
                }
            }
            CrashAwareCachingDiskBranchBetree::Label::CommitStart{image} => {
                AbstractCrashAwareMap::Label::CommitStartLabel {
                    new_boundary_lsn: image.seq_end,
                    frozen_map: post.frozen_i().unwrap(),
                }
            }
            CrashAwareCachingDiskBranchBetree::Label::CommitPrepared =>
                AbstractCrashAwareMap::Label::InternalLabel,
            CrashAwareCachingDiskBranchBetree::Label::CommitComplete{..} =>
                AbstractCrashAwareMap::Label::CommitCompleteLabel,
            CrashAwareCachingDiskBranchBetree::Label::Crash{keep_in_flight} =>
                AbstractCrashAwareMap::Label::CrashLabel{keep_in_flight},
        }
    }

    proof fn prepared_refines_internal(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskBranchBetree::Label,
    )
        requires
            self.refinement_inv(),
            CrashAwareCachingDiskBranchBetree::State::commit_prepared(
                self,
                post,
                lbl,
                post.prepared.unwrap(),
            ),
        ensures
            post.refinement_inv(),
            AbstractCrashAwareMap::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        reveal(CrashAwareCachingDiskBranchBetree::State::commit_prepared);
        reveal(AbstractCrashAwareMap::State::next);
        reveal(AbstractCrashAwareMap::State::next_by);
        reveal(AbstractCrashAwareMap::State::ephemeral_internal);
        reveal(AbstractMap::State::next);
        reveal(AbstractMap::State::next_by);
        reveal(AbstractMap::State::internal);
        assert(self.ephemeral == post.ephemeral);
        assert(self.persistent == post.persistent);
        assert(self.frozen == post.frozen);
        let state = self.ephemeral->v;
        let frozen = self.frozen.unwrap();
        state.disk.
            aus_clean_or_evictable_implies_persistent_visible_agree(
                frozen.aus,
            );
        assert(
            CachingDiskBranchBetreeImage::materialized_from_persistent(
                state,
                frozen,
            ) == CachingDiskBranchBetreeImage::materialized_from_visible(
                state,
                frozen,
            )
        ) by {
            assert_maps_equal!(
                CachingDiskBranchBetreeImage::materialized_from_persistent(
                    state,
                    frozen,
                ).persistent,
                CachingDiskBranchBetreeImage::materialized_from_visible(
                    state,
                    frozen,
                ).persistent,
                addr => {}
            );
        }
        assert(post.prepared.unwrap() == self.frozen_image());
        assert(post.frozen_image() == self.frozen_image());
        assert(post.refinement_inv());
        assert(AbstractMap::State::next_by(
            self.ephemeral->v.i_abstract(),
            self.ephemeral->v.i_abstract(),
            AbstractMap::Label::InternalLabel,
            AbstractMap::Step::internal(),
        ));
        assert(AbstractMap::State::next(
            self.ephemeral->v.i_abstract(),
            self.ephemeral->v.i_abstract(),
            AbstractMap::Label::InternalLabel,
        ));
        assert(AbstractCrashAwareMap::State::next_by(
            self.i_abstract(),
            post.i_abstract(),
            self.label_i_abstract(post, lbl),
            AbstractCrashAwareMap::Step::ephemeral_internal(
                post.ephemeral->v.i_abstract(),
            ),
        ));
    }

    pub proof fn next_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskBranchBetree::Label,
    )
        requires
            self.refinement_inv(),
            CrashAwareCachingDiskBranchBetree::State::next(self, post, lbl),
        ensures
            post.refinement_inv(),
            AbstractCrashAwareMap::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        CrashAwareCachingDiskBranchBetree::State::inv_next(self, post, lbl);
        reveal(CrashAwareCachingDiskBranchBetree::State::next);
        reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
        reveal(AbstractCrashAwareMap::State::next);
        reveal(AbstractCrashAwareMap::State::next_by);

        let step = choose |step: CrashAwareCachingDiskBranchBetree::Step|
            CrashAwareCachingDiskBranchBetree::State::next_by(
                self,
                post,
                lbl,
                step,
            );
        match step {
            CrashAwareCachingDiskBranchBetree::Step::load_ephemeral() => {
                reveal(CrashAwareCachingDiskBranchBetree::State::load_ephemeral);
                self.persistent.valid_refines();
                self.persistent.i_abstract_seq_end();
                reveal(AbstractCrashAwareMap::State::load_ephemeral_from_persistent);
                assert(AbstractMap::State::init_by(
                    self.persistent.i_abstract(),
                    AbstractMap::Config::initialize(self.persistent_i()),
                )) by {
                    reveal(AbstractMap::State::init_by);
                    reveal(AbstractMap::State::initialize);
                }
                assert(AbstractCrashAwareMap::State::next_by(
                    self.i_abstract(),
                    post.i_abstract(),
                    self.label_i_abstract(post, lbl),
                    AbstractCrashAwareMap::Step::load_ephemeral_from_persistent(),
                ));
            }
            CrashAwareCachingDiskBranchBetree::Step::recover_metadata(
                new_recovery,
            ) => {
                reveal(CrashAwareCachingDiskBranchBetree::State::recover_metadata);
                reveal(AbstractCrashAwareMap::State::ephemeral_internal);
                reveal(AbstractMap::State::next);
                reveal(AbstractMap::State::next_by);
                reveal(AbstractMap::State::internal);
                assert(AbstractMap::State::next_by(
                    self.persistent.i_abstract(),
                    self.persistent.i_abstract(),
                    AbstractMap::Label::InternalLabel,
                    AbstractMap::Step::internal(),
                ));
                assert(AbstractCrashAwareMap::State::next_by(
                    self.i_abstract(),
                    post.i_abstract(),
                    self.label_i_abstract(post, lbl),
                    AbstractCrashAwareMap::Step::ephemeral_internal(
                        self.persistent.i_abstract(),
                    ),
                ));
            }
            CrashAwareCachingDiskBranchBetree::Step::load_metadata() => {
                reveal(CrashAwareCachingDiskBranchBetree::State::load_metadata);
                let recovery = self.ephemeral->recovery;
                let loaded = post.ephemeral->v;
                let initial_betree =
                    recovery.initial_betree(self.persistent);
                let betree_aus =
                    recovery.betree_aus(self.persistent);
                let branch_aus =
                    recovery.branch_aus(self.persistent);
                let branch_summary = recovery.branch_summary;
                CachingDiskBranchBetree::State::init_refines(
                    loaded,
                    recovery.disk,
                    loaded.betree,
                    self.persistent.metadata.root,
                    self.persistent.metadata.seq_end,
                    betree_aus,
                    branch_aus,
                    branch_summary,
                    initial_betree,
                );
                self.persistent.valid_refines();
                let recovered =
                    RecoveredCachingDiskBranchBetreeMetadata {
                        betree_aus,
                        branch_aus,
                        branch_summary,
                        initial_betree,
                    };
                assert(recovered.valid_for(self.persistent));
                valid_recovery_matches_image(
                    self.persistent,
                    recovered,
                );
                assert(loaded.i_abstract()
                    == self.persistent.i_abstract());
                reveal(AbstractCrashAwareMap::State::ephemeral_internal);
                reveal(AbstractMap::State::next);
                reveal(AbstractMap::State::next_by);
                reveal(AbstractMap::State::internal);
                assert(AbstractMap::State::next_by(
                    self.persistent.i_abstract(),
                    loaded.i_abstract(),
                    AbstractMap::Label::InternalLabel,
                    AbstractMap::Step::internal(),
                ));
                assert(AbstractMap::State::next(
                    self.persistent.i_abstract(),
                    loaded.i_abstract(),
                    AbstractMap::Label::InternalLabel,
                ));
                assert(AbstractCrashAwareMap::State::next_by(
                    self.i_abstract(),
                    post.i_abstract(),
                    self.label_i_abstract(post, lbl),
                    AbstractCrashAwareMap::Step::ephemeral_internal(
                        loaded.i_abstract(),
                    ),
                ));
            }
            CrashAwareCachingDiskBranchBetree::Step::ephemeral_step(
                new_ephemeral,
            ) => {
                reveal(CrashAwareCachingDiskBranchBetree::State::ephemeral_step);
                let op = lbl->op;
                let old_ephemeral = self.ephemeral->v;
                CachingDiskBranchBetree::State::next_refines_abstract(
                    old_ephemeral,
                    new_ephemeral,
                    op,
                );
                if self.frozen is Some {
                    let frozen = self.frozen.unwrap();
                    let frozen_aus = frozen.aus;
                    let protected = protected_aus(
                        self.ephemeral->persistent_aus,
                        self.frozen,
                    );
                    assert(frozen_aus <= protected);
                    if op is InternalAlloc {
                        assert(logical_guard_aus(op) == protected);
                        assert(frozen_aus
                            <= op.arrow_InternalAlloc_guard_aus());
                    }
                    assert(logical_allocs(op) == op.allocs());
                    assert(frozen_aus.disjoint(op.allocs()));
                    CachingDiskBranchBetree::State::
                        next_wip_alloc_aus_subset(
                            old_ephemeral,
                            new_ephemeral,
                            op,
                        );
                    assert(cached_branch_alloc_aus(
                        new_ephemeral.betree.wip_branches,
                    ).disjoint(frozen_aus));
                    CachingDiskBranchBetree::State::
                        next_preserves_guarded_visible_aus(
                            old_ephemeral,
                            new_ephemeral,
                            op,
                            frozen_aus,
                        );
                    assert(post.frozen_image() == self.frozen_image()) by {
                        assert_maps_equal!(
                            post.frozen_image().persistent,
                            self.frozen_image().persistent,
                            addr => {}
                        );
                    }
                    assert(post.frozen_i() == self.frozen_i());
                } else {
                    assert(self.prepared is None);
                }
                match op.i_abstract(old_ephemeral) {
                    AbstractMap::Label::QueryLabel{end_lsn, key, value} => {
                        abstract_query_stutters(
                            old_ephemeral.i_abstract(),
                            new_ephemeral.i_abstract(),
                            op.i_abstract(old_ephemeral),
                        );
                        reveal(AbstractCrashAwareMap::State::query);
                        assert(AbstractCrashAwareMap::State::next_by(
                            self.i_abstract(),
                            post.i_abstract(),
                            self.label_i_abstract(post, lbl),
                            AbstractCrashAwareMap::Step::query(
                                new_ephemeral.i_abstract(),
                            ),
                        ));
                    }
                    AbstractMap::Label::PutLabel{puts} => {
                        reveal(AbstractCrashAwareMap::State::put_records);
                        assert(AbstractCrashAwareMap::State::next_by(
                            self.i_abstract(),
                            post.i_abstract(),
                            self.label_i_abstract(post, lbl),
                            AbstractCrashAwareMap::Step::put_records(
                                new_ephemeral.i_abstract(),
                            ),
                        ));
                    }
                    AbstractMap::Label::InternalLabel => {
                        abstract_internal_stutters(
                            old_ephemeral.i_abstract(),
                            new_ephemeral.i_abstract(),
                        );
                        reveal(AbstractCrashAwareMap::State::ephemeral_internal);
                        assert(AbstractCrashAwareMap::State::next_by(
                            self.i_abstract(),
                            post.i_abstract(),
                            self.label_i_abstract(post, lbl),
                            AbstractCrashAwareMap::Step::ephemeral_internal(
                                new_ephemeral.i_abstract(),
                            ),
                        ));
                    }
                    AbstractMap::Label::FreezeAsLabel{stamped_map} => {
                        assert(false);
                    }
                }
                assert(post.refinement_inv());
            }
            CrashAwareCachingDiskBranchBetree::Step::commit_start() => {
                reveal(CrashAwareCachingDiskBranchBetree::State::commit_start);
                let image = lbl->image;
                let old_ephemeral = self.ephemeral->v;
                let freeze_lbl =
                    CachingDiskBranchBetree::Label::FreezeAs{image};
                CachingDiskBranchBetree::State::freeze_as_next_facts(
                    old_ephemeral,
                    image,
                );
                assert(old_ephemeral.betree.memtable.is_empty());
                CachingDiskBranchBetree::State::next_refines_abstract(
                    old_ephemeral,
                    old_ephemeral,
                    freeze_lbl,
                );
                old_ephemeral.i_abstract_seq_end();
                abstract_freeze_matches(
                    old_ephemeral.i_abstract(),
                    freeze_lbl.i_abstract(old_ephemeral)->stamped_map,
                );
                let frozen = post.frozen.unwrap();
                frozen_image_from_current_refines(
                    old_ephemeral,
                    frozen,
                );
                assert(cached_branch_alloc_aus(
                    post.ephemeral->v.betree.wip_branches,
                ).is_empty());
                assert(cached_branch_alloc_aus(
                    post.ephemeral->v.betree.wip_branches,
                ).disjoint(frozen.aus));
                self.persistent.i_abstract_seq_end();
                reveal(AbstractCrashAwareMap::State::commit_start_ephemeral);
                assert(post.frozen_i()
                    == Option::Some(old_ephemeral.i_abstract().stamped_map));
                assert(AbstractCrashAwareMap::State::next_by(
                    self.i_abstract(),
                    post.i_abstract(),
                    self.label_i_abstract(post, lbl),
                    AbstractCrashAwareMap::Step::commit_start_ephemeral(),
                ));
                assert(post.refinement_inv());
            }
            CrashAwareCachingDiskBranchBetree::Step::commit_prepared(image) => {
                assert(post.prepared == Option::Some(image));
                self.prepared_refines_internal(post, lbl);
            }
            CrashAwareCachingDiskBranchBetree::Step::commit_complete(
                new_ephemeral,
            ) => {
                reveal(CrashAwareCachingDiskBranchBetree::State::commit_complete);
                reveal(AbstractCrashAwareMap::State::commit_complete);
                let deallocs = match lbl {
                    CrashAwareCachingDiskBranchBetree::Label::CommitComplete{
                        deallocs,
                    } => deallocs,
                    _ => Set::empty(),
                };
                let persistent_aus =
                    self.ephemeral->persistent_aus;
                let guard_aus = self.frozen.unwrap().aus
                    + self.ephemeral->v.betree.owned_aus();
                assert((persistent_aus - guard_aus).disjoint(
                    self.ephemeral->v.betree.owned_aus(),
                ));
                CachingDiskBranchBetree::State::
                    reclaim_guarded_aus_refines_stutter(
                        self.ephemeral->v,
                        new_ephemeral,
                        persistent_aus,
                        guard_aus,
                    );
                assert(new_ephemeral.i_abstract()
                    == self.ephemeral->v.i_abstract());
                assert(self.prepared.unwrap().i_abstract()
                    == self.frozen_image().i_abstract());
                assert(post.persistent_i() == self.frozen_i().unwrap());
                assert(AbstractCrashAwareMap::State::next_by(
                    self.i_abstract(),
                    post.i_abstract(),
                    self.label_i_abstract(post, lbl),
                    AbstractCrashAwareMap::Step::commit_complete(),
                ));
                assert(post.refinement_inv());
            }
            CrashAwareCachingDiskBranchBetree::Step::crash() => {
                reveal(CrashAwareCachingDiskBranchBetree::State::crash);
                reveal(AbstractCrashAwareMap::State::crash);
                if lbl->keep_in_flight {
                    assert(self.prepared.unwrap().i_abstract()
                        == self.frozen_image().i_abstract());
                    assert(post.persistent_i() == self.frozen_i().unwrap());
                } else {
                    assert(post.persistent_i() == self.persistent_i());
                }
                assert(AbstractCrashAwareMap::State::next_by(
                    self.i_abstract(),
                    post.i_abstract(),
                    self.label_i_abstract(post, lbl),
                    AbstractCrashAwareMap::Step::crash(),
                ));
                assert(post.refinement_inv());
            }
            CrashAwareCachingDiskBranchBetree::Step::dummy_to_use_type_params(_) => {
                assert(false);
            }
        }
    }

    pub proof fn init_refines(self)
        requires
            CrashAwareCachingDiskBranchBetree::State::initialize(self),
        ensures
            self.refinement_inv(),
            AbstractCrashAwareMap::State::initialize(self.i_abstract()),
    {
        self.init_inv();
        empty_image_valid();
        self.persistent.valid_refines();
        let initial = empty_initial_betree();
        let loaded = self.persistent.load();
        loaded.i().init_refines(loaded.i().betree);
        loaded.i().i().init_refines_abstract(loaded.i().betree.i());
        reveal(AbstractCrashAwareMap::State::initialize);
        assert(self.persistent == CachingDiskBranchBetreeImage::empty());
        CachingDiskBranchBetreeImage::empty_i_is_empty();
        assert(self.persistent_i() == empty());
    }
}

} // verus!
