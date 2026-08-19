// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Direct refinement from CrashAwareCachingDiskBranchBetree to
// AbstractCrashAwareMap.

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::assert_sets_equal;

use crate::abstract_system::AbstractCrashAwareMap_v::{
    AbstractCrashAwareMap, Ephemeral as AbstractEphemeral,
};
use crate::abstract_system::AbstractMap_v::AbstractMap;
use crate::abstract_system::StampedMap_v::{empty, StampedMap};
use crate::allocation_layer::AllocationBetree_v::AllocationBetree;
use crate::allocation_layer::AllocationBetreeAbstractRefinement_v::*;
use crate::allocation_layer::AllocationBranchBetree_v::AllocationBranchBetree;
use crate::allocation_layer::AllocationBranchBetreeRefinement_v::*;
use crate::allocation_layer::BranchTypes_v::{BranchNode, Summary};
use crate::allocation_layer::Likes_v::AULikes;
use crate::allocation_layer::LikesBetree_v::LikesBetree;
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::Buffer_v::SimpleBuffer;
use crate::betree::LinkedBetree_v::{LinkedBetree, LinkedBetreeVars};
use crate::betree::PagedBetree_v::PagedBetree;
use crate::disk::GenericDisk_v::{
    addrs_with_different_au, set_addrs_disjoint_aus, to_aus, AU,
    Address,
};
use crate::implementation::CachedBranchBetree_v::CachedBranchBetree;
use crate::implementation::CachedBulkBranch_v::cached_bulk_branch_alloc_aus;
use crate::implementation::CachingDiskBranchBetree_v::{
    CachingDiskBranchBetree, loose_disk_for_summary, tight_branch_addrs,
    tight_branch_of, tight_sealed_branch_disk, to_betree_nodes,
    to_branch_nodes, visible_branch_disk,
};
use crate::implementation::CachingDiskBranchBetreeRefinement_v::*;
use crate::implementation::CachingDisk_v::CachingDisk;
use crate::implementation::CrashAwareCachingDiskBranchBetree_v::*;

verus! {

pub proof fn abstract_internal_stutters(
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
        }
        _ => {
            assert(false);
        }
    }
}

pub proof fn abstract_query_stutters(
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
        CachingDiskBranchBetree::State::initialize_from_cached(
            loaded,
            self.disk(),
            cached,
            self.metadata.root,
            self.metadata.seq_end,
            witness.betree_aus,
            witness.branch_aus,
            witness.branch_summary,
        );
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

pub proof fn loaded_branch_roots_empty()
    ensures
        loaded_branch_roots(
            Map::<Address, crate::betree::LinkedBetree_v::BetreeNode>::empty(),
        ).is_empty(),
{
}

pub proof fn recovery_core_next_preserves_loaded_branch_roots(
    pre: BetreeMetadataRecoveryCore,
    post: BetreeMetadataRecoveryCore,
    lbl: BetreeMetadataRecoveryLabel,
)
    requires
        BetreeMetadataRecoveryCore::next(pre, post, lbl),
        pre.branch_roots == loaded_branch_roots(pre.betree_nodes),
        pre.betree_nodes.dom().disjoint(pre.pending_betree),
    ensures
        post.branch_roots == loaded_branch_roots(post.betree_nodes),
{
    match lbl {
        BetreeMetadataRecoveryLabel::DiskInternal => {}
        BetreeMetadataRecoveryLabel::ReadBetree{addr, reads} => {
            let node = to_betree_nodes(reads)[addr];
            assert(!pre.betree_nodes.contains_key(addr));
            assert_sets_equal!(
                post.branch_roots,
                loaded_branch_roots(post.betree_nodes),
                root => {
                    if post.branch_roots.contains(root) {
                        if pre.branch_roots.contains(root) {
                            let tree_addr = choose |tree_addr: Address|
                                pre.betree_nodes.contains_key(tree_addr)
                                && betree_buffer_roots(
                                    pre.betree_nodes[tree_addr],
                                ).contains(root);
                            assert(post.betree_nodes.contains_key(tree_addr));
                            assert(post.betree_nodes[tree_addr]
                                == pre.betree_nodes[tree_addr]);
                        } else {
                            assert(betree_buffer_roots(node).contains(root));
                            assert(post.betree_nodes.contains_key(addr));
                            assert(post.betree_nodes[addr] == node);
                        }
                    }
                    if loaded_branch_roots(
                        post.betree_nodes,
                    ).contains(root) {
                        let tree_addr = choose |tree_addr: Address|
                            post.betree_nodes.contains_key(tree_addr)
                            && betree_buffer_roots(
                                post.betree_nodes[tree_addr],
                            ).contains(root);
                        if tree_addr == addr {
                            assert(post.betree_nodes[tree_addr] == node);
                        } else {
                            assert(pre.betree_nodes.contains_key(tree_addr));
                            assert(pre.betree_nodes[tree_addr]
                                == post.betree_nodes[tree_addr]);
                            assert(loaded_branch_roots(
                                pre.betree_nodes,
                            ).contains(root));
                        }
                    }
                }
            );
        }
        BetreeMetadataRecoveryLabel::ReadBranchRoot{..} => {
        }
        BetreeMetadataRecoveryLabel::ReadBranchAux{..} => {
        }
    }
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

pub proof fn recovery_frontier_start_with_disk(
    image: CachingDiskBranchBetreeImage,
    initial_disk: CachingDisk::State,
)
    requires
        image.valid(),
        initial_disk.inv(),
        initial_disk.visible() == image.disk().visible(),
    ensures
        BetreeMetadataRecovery::from_core(
            initial_disk,
            BetreeMetadataRecoveryCore::start(image.metadata),
        ).refinement_inv(image),
{
    image.recovery_witness_valid();
    let witness = image.recovery_witness();
    let tree = initial_tight_tree(witness.initial_betree);
    let recovery = BetreeMetadataRecovery::from_core(
        initial_disk,
        BetreeMetadataRecoveryCore::start(image.metadata),
    );
    loaded_branch_roots_empty();
    if image.metadata.root is Some {
        assert(tree.dv.entries.contains_key(
            image.metadata.root.unwrap(),
        ));
    }
}

pub proof fn recovery_frontier_start(
    image: CachingDiskBranchBetreeImage,
)
    requires image.valid()
    ensures BetreeMetadataRecovery::start(image).refinement_inv(image)
{
    recovery_frontier_start_with_disk(image, image.disk());
}

pub proof fn recovery_frontier_pending_reads_persistent(
    recovery: BetreeMetadataRecovery,
    image: CachingDiskBranchBetreeImage,
)
    requires recovery.refinement_inv(image)
    ensures
        recovery.pending_betree <= image.persistent.dom(),
        recovery.pending_branch_roots <= image.persistent.dom(),
        forall |root: Address|
            #[trigger] recovery.pending_branch_aux.contains_key(root)
            ==> image.persistent.contains_key(
                recovery.pending_branch_aux[root],
            ),
{
    recovery_witness_branch_facts(image);
    let witness = image.recovery_witness();
    let tree = initial_tight_tree(witness.initial_betree);
    let roots = tree.reachable_buffer_addrs();
    let buffer = witness.initial_betree.linked.buffer_dv;
    let loose_branches = visible_branch_disk(
        image.disk(),
        witness.branch_summary,
    );

    image.recovery_witness_valid();
    assert(tree.dv.entries
        <= to_betree_nodes(image.disk().visible()));
    assert(image.disk().visible() == image.persistent) by {
    }
    assert(recovery.pending_betree
        <= image.persistent.dom()) by {
        assert forall |addr: Address|
            #[trigger] recovery.pending_betree.contains(addr)
            implies image.persistent.contains_key(addr) by {
            assert(tree.dv.entries.contains_key(addr));
            assert(to_betree_nodes(
                image.disk().visible(),
            ).contains_key(addr));
        }
    }

    assert(buffer.entries
        <= to_branch_nodes(image.disk().visible())) by {
        assert(buffer == tight_sealed_branch_disk(
            loose_branches,
            roots,
            witness.branch_summary,
        ));
    }
    assert(recovery.pending_branch_roots
        <= image.persistent.dom()) by {
        assert forall |root: Address|
            #[trigger] recovery.pending_branch_roots.contains(root)
            implies image.persistent.contains_key(root) by {
            assert(recovery.branch_roots.contains(root));
            assert(roots.contains(root));
            buffer.sealed_branch_roots_contains(roots, root);
            let branch = buffer.get_branch(root);
            assert(branch.valid_sealed_branch());
            assert(branch.has_root());
            assert(branch.disk_view.entries.contains_key(root));
            assert(buffer.entries.contains_key(root));
            assert(to_branch_nodes(
                image.disk().visible(),
            ).contains_key(root));
        }
    }

    assert forall |root: Address|
        #[trigger] recovery.pending_branch_aux.contains_key(root)
        implies image.persistent.contains_key(
            recovery.pending_branch_aux[root],
        ) by {
        let aux = recovery.pending_branch_aux[root];
        assert(recovery.branch_roots.contains(root));
        assert(roots.contains(root));
        buffer.sealed_branch_roots_contains(roots, root);
        let branch = buffer.get_branch(root);
        assert(branch.valid_sealed_branch());
        assert(branch.sealed_root());
        assert(buffer.entries.contains_key(root));
        assert(buffer.entries[root] is Index);
        assert(buffer.entries[root].arrow_Index_aux_ptr()
            == Option::Some(aux));
        assert(branch.root() == buffer.entries[root]);
        assert(branch.root()->aux_ptr == Option::Some(aux));
        assert(branch.disk_view.valid_address(aux));
        assert(buffer.entries.contains_key(aux));
        assert(to_branch_nodes(
            image.disk().visible(),
        ).contains_key(aux));
    }
}

pub proof fn same_betree_root_disk_same_transitive_likes(
    left: LinkedBetree<BranchNode>,
    right: LinkedBetree<BranchNode>,
)
    requires
        left.acyclic(),
        right.acyclic(),
        left.root == right.root,
        left.dv == right.dv,
    ensures
        left.transitive_likes() == right.transitive_likes(),
{
    let ranking = right.the_ranking();
    assert(left.valid_ranking(ranking));
    left.subdisk_implies_same_tree_likes(right, ranking);
    left.tree_likes_ignore_ranking(
        ranking,
        left.the_ranking(),
    );
    right.tree_likes_ignore_ranking(
        ranking,
        right.the_ranking(),
    );
    let tree_likes = left.tree_likes(left.the_ranking());
    assert(tree_likes
        == right.tree_likes(right.the_ranking()));
    left.tree_likes_domain(left.the_ranking());
    left.subdisk_implies_same_buffer_likes(
        right,
        tree_likes,
    );
    assert(left.transitive_likes()
        == right.transitive_likes()) by {
    }
}

pub proof fn recovery_core_loaded_betree_matches(
    recovery: BetreeMetadataRecovery,
    image: CachingDiskBranchBetreeImage,
)
    requires
        recovery.refinement_inv(image),
        recovery.complete(),
    ensures
        recovery.core().loaded_betree(image.metadata)
            == recovery.loaded_state(image).betree,
        recovery.core().recovered_likes_tree(image.metadata).acyclic(),
        recovery.core().recovered_likes_tree(image.metadata)
            .dv.entries.dom()
            == recovery.core().recovered_likes_tree(image.metadata)
                .reachable_betree_addrs(),
{
    recovery_complete_witness_valid(recovery, image);
    let core = recovery.core();
    let core_tree = core.recovered_likes_tree(image.metadata);
    let full_tree = recovery.recovered_tree(image);
    let recovered =
        RecoveredCachingDiskBranchBetreeMetadata {
            betree_aus: recovery.betree_aus(image),
            branch_aus: recovery.branch_aus(image),
            branch_summary: recovery.branch_summary,
            initial_betree: recovery.initial_betree(image),
        };

    assert(recovered.valid_for(image));
    let tight = initial_tight_tree(recovered.initial_betree);
    assert(tight.dv.entries.dom()
        == tight.reachable_betree_addrs());
    assert(tight.root == full_tree.root);
    assert(tight.dv == full_tree.dv);
    assert(full_tree.acyclic());
    assert(core_tree.root == full_tree.root);
    assert(core_tree.dv == full_tree.dv);
    assert(core_tree.acyclic()) by {
    }
    assert(core_tree.dv.entries.dom()
        == core_tree.reachable_betree_addrs()) by {
        assert(core_tree.dv == full_tree.dv);
        assert(full_tree.reachable_betree_addrs()
            == tight.reachable_betree_addrs()) by {
            assert(full_tree.valid_ranking(tight.the_ranking()));
            tight.agreeable_disks_same_reachable_betree_addrs(
                full_tree,
                tight.the_ranking(),
            );
            tight.reachable_betree_addrs_ignore_ranking(
                tight.the_ranking(),
                tight.the_ranking(),
            );
            full_tree.reachable_betree_addrs_ignore_ranking(
                tight.the_ranking(),
                full_tree.the_ranking(),
            );
        }
        assert(full_tree.dv.entries.dom()
            == full_tree.reachable_betree_addrs());
        assert(core_tree.root == full_tree.root);
        assert(core_tree.dv == full_tree.dv);
        assert(core_tree.reachable_betree_addrs()
            == full_tree.reachable_betree_addrs()) by {
            core_tree.reachable_betree_addrs_ignore_ranking(
                core_tree.the_ranking(),
                full_tree.the_ranking(),
            );
        }
    }
    same_betree_root_disk_same_transitive_likes(
        core_tree,
        full_tree,
    );

}

pub proof fn recovery_complete_metadata_matches_image(
    recovery: BetreeMetadataRecovery,
    image: CachingDiskBranchBetreeImage,
)
    requires
        recovery.refinement_inv(image),
        recovery.complete(),
    ensures ({
        let recovered =
            RecoveredCachingDiskBranchBetreeMetadata {
                betree_aus: recovery.betree_aus(image),
                branch_aus: recovery.branch_aus(image),
                branch_summary: recovery.branch_summary,
                initial_betree: recovery.initial_betree(image),
            };
        recovered == image.recovery_witness()
    }),
{
    recovery_complete_witness_valid(recovery, image);
    image.recovery_witness_valid();
    let recovered =
        RecoveredCachingDiskBranchBetreeMetadata {
            betree_aus: recovery.betree_aus(image),
            branch_aus: recovery.branch_aus(image),
            branch_summary: recovery.branch_summary,
            initial_betree: recovery.initial_betree(image),
        };
    let canonical = image.recovery_witness();
    recovery_witnesses_same_initial(
        image,
        recovered,
        canonical,
    );
    assert(recovered.betree_aus == canonical.betree_aus);
    assert(recovered.branch_aus == canonical.branch_aus);
    assert(recovered.branch_summary == canonical.branch_summary);
}

pub proof fn recovery_witness_branch_facts(
    image: CachingDiskBranchBetreeImage,
)
    requires image.valid()
    ensures ({
        let witness = image.recovery_witness();
        let tree = initial_tight_tree(witness.initial_betree);
        let roots = tree.reachable_buffer_addrs();
        let buffer = witness.initial_betree.linked.buffer_dv;
        &&& tree.dv.entries
            <= to_betree_nodes(image.disk().visible())
        &&& buffer.sealed_branch_roots(roots)
        &&& witness.branch_summary
            == buffer.build_branch_summary(roots)
        &&& set_addrs_disjoint_aus(roots)
    })
{
    image.recovery_witness_valid();
    let witness = image.recovery_witness();
    let tree = initial_tight_tree(witness.initial_betree);
    let linked = witness.initial_betree.linked;
    let roots = tree.reachable_buffer_addrs();
    let buffer = linked.buffer_dv;
    let visible_tree = to_betree_nodes(image.disk().visible()).restrict(
        crate::implementation::CachingDisk_v::addresses_in_aus(
            witness.betree_aus.dom(),
        ),
    );
    let target = initial_allocation_state(
        witness.initial_betree,
        witness.betree_aus,
        witness.branch_aus,
        witness.branch_summary,
    );
    assert(tree.dv.entries <= visible_tree);
    assert(visible_tree <= to_betree_nodes(image.disk().visible()));
    vstd::map_lib::lemma_submap_of_trans(
        tree.dv.entries,
        visible_tree,
        to_betree_nodes(image.disk().visible()),
    );

    assert(linked.acyclic());
    assert(tree.acyclic());
    assert(linked.dv == tree.dv);
    assert(linked.valid_view(tree)) by {
    }
    linked.valid_view_ensures(tree);
    assert(linked.reachable_buffer_addrs() == roots);

    linked.tree_likes_domain(linked.the_ranking());
    let linked_tree_likes = linked.tree_likes(linked.the_ranking());
    linked.buffer_likes_domain(linked_tree_likes);
    assert(linked.transitive_likes().1.dom()
        == linked.reachable_buffer_addrs());
    assert(linked.transitive_likes().1.dom() == roots);
    assert(buffer.sealed_branch_roots(roots));
    assert(witness.branch_summary
        == buffer.build_branch_summary(roots));
    assert(set_addrs_disjoint_aus(roots));
}

pub proof fn recovery_frontier_next(
    pre: BetreeMetadataRecovery,
    post: BetreeMetadataRecovery,
    image: CachingDiskBranchBetreeImage,
    lbl: BetreeMetadataRecoveryLabel,
)
    requires
        pre.refinement_inv(image),
        BetreeMetadataRecovery::next(pre, post, lbl),
    ensures
        post.refinement_inv(image),
{
    image.recovery_witness_valid();
    let witness = image.recovery_witness();
    let tree = initial_tight_tree(witness.initial_betree);
    let roots = tree.reachable_buffer_addrs();
    let summary = witness.branch_summary;
    let buffer = witness.initial_betree.linked.buffer_dv;
    recovery_witness_branch_facts(image);
    assert(buffer.sealed_branch_roots(roots));
    assert(summary == buffer.build_branch_summary(roots));
    assert(set_addrs_disjoint_aus(roots));

    match lbl {
        BetreeMetadataRecoveryLabel::DiskInternal => {
            CachingDisk::State::inv_next(
                pre.disk,
                post.disk,
                CachingDisk::Label::Internal{},
            );
            CachingDisk::State::internal_visible_unchanged(
                pre.disk,
                post.disk,
            );
            assert(post.disk.inv());
            assert(recovery_frontier_inv(post, image));
        }
        BetreeMetadataRecoveryLabel::ReadBetree{addr, reads} => {
            assert(post.disk == pre.disk);
            assert(post.disk.inv());
            CachingDisk::State::access_effect(
                pre.disk,
                pre.disk,
                reads,
                Map::empty(),
            );
            assert(tree.dv.entries.contains_key(addr));
            assert(to_betree_nodes(image.disk().visible())
                .contains_key(addr));
            assert(pre.disk.visible().contains_key(addr));
            CachingDisk::State::access_read_matches_visible(
                pre.disk,
                pre.disk,
                reads,
                Map::empty(),
                addr,
            );
            assert(reads[addr] == pre.disk.visible()[addr]);
            assert(pre.disk.visible()[addr]
                == image.disk().visible()[addr]);
            assert(to_betree_nodes(reads)[addr]
                == tree.dv.entries[addr]);
            let node = tree.dv.entries[addr];
            assert(betree_child_addrs(node)
                <= tree.dv.entries.dom()) by {
                assert forall |child: Address|
                    #[trigger] betree_child_addrs(node).contains(child)
                    implies tree.dv.entries.dom().contains(child) by {
                    let i = choose |i: int|
                        0 <= i
                        && i < node.children.len()
                        && node.children[i] == Option::Some(child);
                    assert(node.valid_child_index(i as nat));
                    assert(tree.dv.node_has_nondangling_child_ptrs(node));
                    assert(tree.dv.is_nondangling_ptr(
                        node.children[i],
                    ));
                };
            }
            recovery_core_next_preserves_loaded_branch_roots(
                pre.core(),
                post.core(),
                lbl,
            );
            assert(post.betree_nodes <= tree.dv.entries);
            assert(post.pending_betree <= tree.dv.entries.dom());
            assert(post.betree_nodes.dom()
                .disjoint(post.pending_betree));
            assert(post.branch_roots <= roots) by {
                assert forall |root: Address|
                    #[trigger] post.branch_roots.contains(root)
                    implies roots.contains(root) by {
                    if !pre.branch_roots.contains(root) {
                        assert(betree_buffer_roots(node)
                            .contains(root));
                        assert(tree.reachable_betree_addrs()
                            .contains(addr));
                        assert(exists |tree_addr: Address|
                            tree.reachable_buffer(tree_addr, root)) by {
                            assert(tree.reachable_buffer(addr, root));
                        };
                    }
                };
            }
            assert(pre.branch_roots <= post.branch_roots);
            crate::disk::GenericDisk_v::to_aus_preserves_lte(
                pre.branch_roots,
                post.branch_roots,
            );
            assert(post.branch_summary == pre.branch_summary);
            assert(post.branch_summary.dom()
                <= to_aus(post.branch_roots));
            assert forall |pending_root: Address|
                #[trigger] post.pending_branch_roots.contains(pending_root)
                implies !post.branch_summary.contains_key(
                    pending_root.au,
                ) by {
                if pre.pending_branch_roots.contains(pending_root) {
                    assert(!pre.branch_summary.contains_key(
                        pending_root.au,
                    ));
                } else {
                    assert(!pre.branch_roots.contains(pending_root));
                    if post.branch_summary.contains_key(
                        pending_root.au,
                    ) {
                        assert(to_aus(pre.branch_roots).contains(
                            pending_root.au,
                        ));
                        let old_root =
                            crate::disk::GenericDisk_v::to_aus_get_addr(
                                pre.branch_roots,
                                pending_root.au,
                            );
                        assert(post.branch_roots.contains(old_root));
                        assert(post.branch_roots.contains(pending_root));
                        if old_root != pending_root {
                            assert(addrs_with_different_au(
                                old_root,
                                pending_root,
                            ));
                            assert(old_root.au != pending_root.au);
                        }
                    }
                }
            };
            assert(recovery_frontier_inv(post, image));
        }
        BetreeMetadataRecoveryLabel::ReadBranchRoot{root, reads} => {
            let node = to_branch_nodes(reads)[root];
            assert(post.disk == pre.disk);
            assert(post.disk.inv());
            assert(roots.contains(root));
            assert(buffer.entries.contains_key(root)) by {
                assert(buffer.sealed_branch_roots(roots));
                buffer.sealed_branch_roots_contains(roots, root);
                assert(buffer.get_branch(root).has_root());
            }
            assert(to_branch_nodes(image.disk().visible())
                .contains_key(root));
            assert(image.disk().visible().contains_key(root));
            CachingDisk::State::access_read_matches_visible(
                pre.disk,
                pre.disk,
                reads,
                Map::empty(),
                root,
            );
            assert(node == buffer.entries[root]);
            buffer.build_branch_summary_contains(roots, root);
            assert(summary.contains_key(root.au));
            assert(summary[root.au]
                == buffer.get_branch(root).get_summary());
            if node is Leaf {
                assert(buffer.get_branch(root).get_summary()
                    == set![root.au]);
            } else {
                assert(node is Index);
                assert(node.arrow_Index_aux_ptr() is Some);
            }
            assert(pre.branch_roots == post.branch_roots);
            crate::disk::GenericDisk_v::to_aus_domain(
                post.branch_roots,
            );
            assert(post.branch_summary.dom()
                <= to_aus(post.branch_roots)) by {
                assert forall |au: AU|
                    #[trigger] post.branch_summary.dom().contains(au)
                    implies to_aus(post.branch_roots).contains(au) by {
                    if !pre.branch_summary.contains_key(au) {
                        assert(au == root.au);
                        assert(post.branch_roots.contains(root));
                    } else {
                        assert(pre.branch_summary.dom()
                            .contains(au));
                        assert(to_aus(pre.branch_roots)
                            .contains(au));
                    }
                };
            }
            assert forall |pending_root: Address|
                #[trigger] post.pending_branch_roots.contains(pending_root)
                implies !post.branch_summary.contains_key(
                    pending_root.au,
                ) by {
                assert(pre.pending_branch_roots.contains(pending_root));
                assert(!pre.branch_summary.contains_key(
                    pending_root.au,
                ));
                if post.branch_summary.contains_key(
                    pending_root.au,
                ) {
                    assert(pending_root.au == root.au);
                    assert(post.branch_roots.contains(pending_root));
                    assert(post.branch_roots.contains(root));
                    assert(pending_root != root);
                    assert(addrs_with_different_au(pending_root, root));
                }
            };
            assert forall |aux_root: Address|
                #[trigger] post.pending_branch_aux.contains_key(aux_root)
                implies !post.branch_summary.contains_key(
                    aux_root.au,
                ) by {
                if pre.pending_branch_aux.contains_key(aux_root) {
                    assert(!pre.branch_summary.contains_key(aux_root.au));
                    if post.branch_summary.contains_key(aux_root.au) {
                        assert(aux_root.au == root.au);
                        assert(post.branch_roots.contains(aux_root));
                        assert(post.branch_roots.contains(root));
                        assert(aux_root != root) by {
                            if aux_root == root {
                                assert(!pre.pending_branch_aux
                                    .contains_key(root));
                            }
                        }
                        assert(addrs_with_different_au(aux_root, root));
                    }
                } else {
                    assert(aux_root == root);
                    assert(node is Index);
                    assert(post.branch_summary == pre.branch_summary);
                    assert(!pre.branch_summary.contains_key(root.au));
                }
            };
            assert(recovery_frontier_inv(post, image));
        }
        BetreeMetadataRecoveryLabel::ReadBranchAux{root, reads} => {
            let aux = pre.pending_branch_aux[root];
            let node = to_branch_nodes(reads)[aux];
            assert(post.disk == pre.disk);
            assert(post.disk.inv());
            assert(roots.contains(root));
            assert(buffer.entries.contains_key(root));
            assert(buffer.entries[root] is Index);
            assert(buffer.entries[root].arrow_Index_aux_ptr()
                == Option::Some(aux));
            assert(buffer.get_branch(root).valid_sealed_branch()) by {
                assert(buffer.sealed_branch_roots(roots));
                buffer.sealed_branch_roots_contains(roots, root);
            }
            assert(buffer.entries.contains_key(aux));
            assert(to_branch_nodes(image.disk().visible())
                .contains_key(aux));
            assert(image.disk().visible().contains_key(aux));
            CachingDisk::State::access_read_matches_visible(
                pre.disk,
                pre.disk,
                reads,
                Map::empty(),
                aux,
            );
            assert(node == buffer.entries[aux]);
            buffer.build_branch_summary_contains(roots, root);
            assert(summary.contains_key(root.au));
            assert(summary[root.au]
                == buffer.get_branch(root).get_summary());
            assert(buffer.get_branch(root).get_summary()
                == node.arrow_Auxiliary_0());
            assert(pre.branch_roots == post.branch_roots);
            crate::disk::GenericDisk_v::to_aus_domain(
                post.branch_roots,
            );
            assert(post.branch_summary.dom()
                <= to_aus(post.branch_roots)) by {
                assert forall |au: AU|
                    #[trigger] post.branch_summary.dom().contains(au)
                    implies to_aus(post.branch_roots).contains(au) by {
                    if !pre.branch_summary.contains_key(au) {
                        assert(au == root.au);
                        assert(post.branch_roots.contains(root));
                    } else {
                        assert(pre.branch_summary.dom()
                            .contains(au));
                        assert(to_aus(pre.branch_roots)
                            .contains(au));
                    }
                };
            }
            assert forall |pending_root: Address|
                #[trigger] post.pending_branch_roots.contains(pending_root)
                implies !post.branch_summary.contains_key(
                    pending_root.au,
                ) by {
                assert(pre.pending_branch_roots.contains(pending_root));
                assert(!pre.branch_summary.contains_key(
                    pending_root.au,
                ));
                if post.branch_summary.contains_key(
                    pending_root.au,
                ) {
                    assert(pending_root.au == root.au);
                    assert(pre.branch_roots.contains(pending_root));
                    assert(pre.branch_roots.contains(root));
                    assert(pending_root != root) by {
                        if pending_root == root {
                            assert(!pre.pending_branch_aux
                                .contains_key(root));
                        }
                    }
                    assert(addrs_with_different_au(pending_root, root));
                }
            };
            assert forall |aux_root: Address|
                #[trigger] post.pending_branch_aux.contains_key(aux_root)
                implies !post.branch_summary.contains_key(
                    aux_root.au,
                ) by {
                assert(pre.pending_branch_aux.contains_key(aux_root));
                assert(aux_root != root);
                assert(!pre.branch_summary.contains_key(aux_root.au));
                if post.branch_summary.contains_key(aux_root.au) {
                    assert(aux_root.au == root.au);
                    assert(post.branch_roots.contains(aux_root));
                    assert(post.branch_roots.contains(root));
                    assert(addrs_with_different_au(aux_root, root));
                }
            };
            assert(recovery_frontier_inv(post, image));
        }
    }
    assert(post.refinement_inv(image));
}

pub proof fn recovery_complete_witness_valid(
    recovery: BetreeMetadataRecovery,
    image: CachingDiskBranchBetreeImage,
)
    requires
        recovery.refinement_inv(image),
        recovery.complete(),
    ensures ({
        let recovered = RecoveredCachingDiskBranchBetreeMetadata {
            betree_aus: recovery.betree_aus(image),
            branch_aus: recovery.branch_aus(image),
            branch_summary: recovery.branch_summary,
            initial_betree: recovery.initial_betree(image),
        };
        recovered.valid_for(image)
    })
{
    image.recovery_witness_valid();
    recovery_witness_branch_facts(image);
    let witness = image.recovery_witness();
    let tree = initial_tight_tree(witness.initial_betree);
    let roots = tree.reachable_buffer_addrs();
    let buffer = witness.initial_betree.linked.buffer_dv;
    let loaded = recovery.betree_nodes.dom();
    let ranking = tree.the_ranking();

    assert(recovery.pending_betree.is_empty());
    assert(tree.has_root() ==> loaded.contains(tree.root.unwrap())) by {
        if tree.has_root() {
            assert(image.metadata.root is Some);
            assert(tree.root == image.metadata.root);
        }
    }
    assert forall |addr: Address, idx: nat|
        #[trigger] loaded.contains(addr)
            && tree.dv.entries.contains_key(addr)
            && #[trigger] tree.dv.entries[addr].valid_child_index(idx)
            && tree.dv.entries[addr].children[idx as int] is Some
        implies loaded.contains(
                tree.dv.entries[addr].children[idx as int].unwrap(),
            ) by {
        let child =
            tree.dv.entries[addr].children[idx as int].unwrap();
        assert(recovery.betree_nodes[addr]
            == tree.dv.entries[addr]);
        assert(betree_child_addrs(
            recovery.betree_nodes[addr],
        ).contains(child)) by {
            assert(exists |i: int|
                0 <= i
                && i < recovery.betree_nodes[addr].children.len()
                && recovery.betree_nodes[addr].children[i]
                    == Option::Some(child)) by {
                assert(recovery.betree_nodes[addr]
                    .children[idx as int] == Option::Some(child));
            };
        }
    };
    tree.closed_set_contains_reachable(ranking, loaded);
    tree.reachable_betree_addrs_ignore_ranking(
        ranking,
        tree.the_ranking(),
    );
    assert(tree.dv.entries.dom() <= loaded);
    assert(loaded == tree.dv.entries.dom());
    assert_maps_equal!(
        recovery.betree_nodes,
        tree.dv.entries,
        addr => {}
    );

    assert_sets_equal!(
        recovery.branch_roots,
        roots,
        root => {
        }
    );
    assert(recovery.branch_roots == roots);

    assert(recovery.pending_branch_roots.is_empty());
    assert(recovery.pending_branch_aux.dom().is_empty());
    assert(to_aus(roots) <= recovery.branch_summary.dom()) by {
        assert forall |au: AU|
            #[trigger] to_aus(roots).contains(au)
            implies recovery.branch_summary.dom().contains(au) by {
            let root = crate::disk::GenericDisk_v::to_aus_get_addr(
                roots,
                au,
            );
            assert(recovery.branch_roots.contains(root));
        };
    }
    assert(recovery.branch_summary.dom() == to_aus(roots));
    buffer.build_branch_domain(roots);
    assert(witness.branch_summary.dom() == to_aus(roots));
    assert_maps_equal!(
        recovery.branch_summary,
        witness.branch_summary,
        au => {}
    );

    assert(recovery.recovered_tree(image)
        == witness.initial_betree.linked) by {
    }
    assert(recovery.initial_betree(image)
        == witness.initial_betree) by {
    }

    let recovered = RecoveredCachingDiskBranchBetreeMetadata {
        betree_aus: recovery.betree_aus(image),
        branch_aus: recovery.branch_aus(image),
        branch_summary: recovery.branch_summary,
        initial_betree: recovery.initial_betree(image),
    };
    let target = initial_allocation_state(
        witness.initial_betree,
        witness.betree_aus,
        witness.branch_aus,
        witness.branch_summary,
    );
    assert(recovery.recovered_tree(image).acyclic());
    assert(recovered.betree_aus == witness.betree_aus);
    assert(recovered.branch_aus == witness.branch_aus);
    assert(recovered.branch_summary == witness.branch_summary);
    assert(recovered.initial_betree == witness.initial_betree);
    assert(recovered == witness);
    assert(recovered.valid_for(image));
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

pub proof fn valid_recovery_allocation_matches_image(
    image: CachingDiskBranchBetreeImage,
    recovered: RecoveredCachingDiskBranchBetreeMetadata,
)
    requires
        image.valid(),
        recovered.valid_for(image),
    ensures ({
        let canonical = image.recovery_witness();
        &&& recovered.betree_aus == canonical.betree_aus
        &&& recovered.branch_aus == canonical.branch_aus
        &&& recovered.branch_summary
            == canonical.branch_summary
    }),
{
    image.recovery_witness_valid();
    let canonical = image.recovery_witness();
    recovery_witnesses_same_initial(
        image,
        recovered,
        canonical,
    );
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
    CachingDiskBranchBetree::State::initialize_from_cached(
        recovered_state,
        image.disk(),
        recovered_state.betree,
        image.metadata.root,
        image.metadata.seq_end,
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
    CachingDiskBranchBetree::State::initialize_from_cached(
        canonical_state,
        image.disk(),
        canonical_state.betree,
        image.metadata.root,
        image.metadata.seq_end,
        canonical.betree_aus,
        canonical.branch_aus,
        canonical.branch_summary,
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
        ).load().betree.durable_aus() == frozen.aus,
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
    valid_recovery_allocation_matches_image(
        image,
        recovered,
    );
    assert(image.load().betree.durable_aus()
        == state.betree.durable_aus());
    assert(image.load().betree.durable_aus()
        == frozen.aus);
    let recovered_state = image.load_metadata(
        recovered.betree_aus,
        recovered.branch_aus,
        recovered.branch_summary,
    );
    CachingDiskBranchBetree::State::initialize_from_cached(
        recovered_state,
        image.disk(),
        recovered_state.betree,
        image.metadata.root,
        image.metadata.seq_end,
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
        &&& self.ephemeral is Known ==> {
            self.ephemeral->persistent_aus
                == self.persistent.load().betree.durable_aus()
        }
        &&& self.frozen is Some ==>
            self.frozen_image().valid()
        &&& self.frozen is Some ==>
            self.frozen_image().load().betree.durable_aus()
                == self.frozen.unwrap().aus
        &&& self.frozen is Some ==>
            cached_bulk_branch_alloc_aus(
                self.ephemeral->v.betree.wip_branches,
            ).disjoint(self.frozen.unwrap().aus)
        &&& self.prepared is Some ==> {
            &&& self.ephemeral is Known
            &&& self.prepared.unwrap().i_abstract()
                == self.frozen_image().i_abstract()
            &&& self.prepared.unwrap().load().betree
                .durable_aus()
                == self.frozen.unwrap().aus
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
        reveal(AbstractCrashAwareMap::State::next);
        reveal(AbstractCrashAwareMap::State::next_by);
        reveal(AbstractMap::State::next);
        reveal(AbstractMap::State::next_by);
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
        assert(post.prepared.unwrap().load().betree
            .durable_aus() == post.frozen.unwrap().aus);
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
            CrashAwareCachingDiskBranchBetree::Step::load_ephemeral(
                initial_disk,
            ) => {
                recovery_frontier_start_with_disk(
                    self.persistent,
                    initial_disk,
                );
                self.persistent.valid_refines();
                self.persistent.i_abstract_seq_end();
                assert(AbstractMap::State::init_by(
                    self.persistent.i_abstract(),
                    AbstractMap::Config::initialize(self.persistent_i()),
                )) by {
                    reveal(AbstractMap::State::init_by);
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
                recovery_frontier_next(
                    self.ephemeral->recovery,
                    new_recovery,
                    self.persistent,
                    lbl->recovery_op,
                );
                reveal(AbstractMap::State::next);
                reveal(AbstractMap::State::next_by);
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
                let recovery = self.ephemeral->recovery;
                let loaded = post.ephemeral->v;
                let initial_betree =
                    recovery.initial_betree(self.persistent);
                let betree_aus =
                    recovery.betree_aus(self.persistent);
                let branch_aus =
                    recovery.branch_aus(self.persistent);
                let branch_summary = recovery.branch_summary;
                recovery_complete_witness_valid(
                    recovery,
                    self.persistent,
                );
                CachingDiskBranchBetree::State::initialize_from_cached(
                    loaded,
                    recovery.disk,
                    loaded.betree,
                    self.persistent.metadata.root,
                    self.persistent.metadata.seq_end,
                    betree_aus,
                    branch_aus,
                    branch_summary,
                );
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
                valid_recovery_allocation_matches_image(
                    self.persistent,
                    recovered,
                );
                assert(post.ephemeral->persistent_aus
                    == post.ephemeral->v.betree.durable_aus());
                assert(post.ephemeral->persistent_aus
                    == self.persistent.load().betree
                        .durable_aus());
                assert(loaded.i_abstract()
                    == self.persistent.i_abstract());
                reveal(AbstractMap::State::next);
                reveal(AbstractMap::State::next_by);
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
                    if op is InternalAllocAccess {
                        assert(logical_guard_aus(op) == protected);
                        assert(frozen_aus
                            <= op.arrow_InternalAllocAccess_guard_aus());
                    }
                    assert(logical_allocs(op) == op.allocs());
                    assert(frozen_aus.disjoint(op.allocs()));
                    CachingDiskBranchBetree::State::
                        next_wip_alloc_aus_subset(
                            old_ephemeral,
                            new_ephemeral,
                            op,
                        );
                    assert(cached_bulk_branch_alloc_aus(
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
                assert(post.frozen_image().load().betree
                    .durable_aus() == frozen.aus);
                assert(cached_bulk_branch_alloc_aus(
                    post.ephemeral->v.betree.wip_branches,
                ).is_empty());
                assert(cached_bulk_branch_alloc_aus(
                    post.ephemeral->v.betree.wip_branches,
                ).disjoint(frozen.aus));
                self.persistent.i_abstract_seq_end();
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
                assert(post.ephemeral->persistent_aus
                    == self.frozen.unwrap().aus);
                assert(post.persistent == self.prepared.unwrap());
                assert(post.ephemeral->persistent_aus
                    == post.persistent.load().betree
                        .durable_aus());
                assert(AbstractCrashAwareMap::State::next_by(
                    self.i_abstract(),
                    post.i_abstract(),
                    self.label_i_abstract(post, lbl),
                    AbstractCrashAwareMap::Step::commit_complete(),
                ));
                assert(post.refinement_inv());
            }
            CrashAwareCachingDiskBranchBetree::Step::crash() => {
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
        assert(self.persistent == CachingDiskBranchBetreeImage::empty());
        CachingDiskBranchBetreeImage::empty_i_is_empty();
        assert(self.persistent_i() == empty());
    }
}

} // verus!
