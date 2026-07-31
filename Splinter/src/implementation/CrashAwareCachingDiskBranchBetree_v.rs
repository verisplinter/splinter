// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Crash-aware wrapper for CachingDiskBranchBetree. Durable images contain only
// persistent pages and superblock-style Betree metadata.

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::map::*;
use vstd::multiset::*;
use vstd::assert_maps_equal;

use verus_state_machines_macros::state_machine;

use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::AllocationBranch_v::{BranchNode, Summary};
use crate::allocation_layer::AllocationBranchBetree_v::summary_aus;
use crate::allocation_layer::Likes_v::{to_au_likes, AULikes};
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::LinkedBetree_v::{
    empty_disk as empty_betree_disk, BetreeNode,
    DiskView as BetreeDiskView, LinkedBetree, LinkedBetreeVars,
};
use crate::betree::Memtable_v::Memtable;
use crate::betree::LinkedBranch_v::Node as BranchNodeValue;
use crate::disk::GenericDisk_v::{Address, AU, Pointer};
use crate::implementation::CachedBranchBetree_v::{
    CachedBranchBetree, FrozenBranchBetree,
};
use crate::implementation::CachingDisk_v::{
    addresses_in_aus, CachingDisk, PageStatus,
};
use crate::implementation::CachingDiskBranchBetree_v::{
    reclaim_guarded_aus, reclaim_guarded_aus_preserves_inv,
    tight_sealed_branch_disk, to_betree_nodes, to_branch_nodes,
    visible_branch_disk, CachingDiskBranchBetree,
};
use crate::implementation::CachingDiskBranchBetreeRefinement_v::{
    initial_refinement_witness_valid,
};
use crate::spec::AsyncDisk_t::RawPage;

verus! {

#[verifier::ext_equal]
pub struct CachingDiskBranchBetreeMetadata {
    pub root: Pointer,
    pub seq_end: LSN,
}

#[verifier::ext_equal]
pub struct CachingDiskBranchBetreeImage {
    pub persistent: Map<Address, RawPage>,
    pub metadata: CachingDiskBranchBetreeMetadata,
}

#[verifier::ext_equal]
pub struct FrozenCachingDiskBranchBetree {
    pub metadata: CachingDiskBranchBetreeMetadata,
    pub aus: Set<AU>,
}

pub enum EphemeralCachingDiskBranchBetree {
    Unknown,
    Loading {
        recovery: BetreeMetadataRecovery,
    },
    Known {
        v: CachingDiskBranchBetree::State,
        persistent_aus: Set<AU>,
    },
}

impl CachingDiskBranchBetreeMetadata {
    pub open spec fn empty() -> Self {
        Self {
            root: Option::None,
            seq_end: 0,
        }
    }
}

#[verifier::ext_equal]
pub struct BetreeMetadataRecoveryCore {
    pub betree_nodes: Map<Address, BetreeNode>,
    pub pending_betree: Set<Address>,
    pub branch_roots: Set<Address>,
    pub pending_branch_roots: Set<Address>,
    pub pending_branch_aux: Map<Address, Address>,
    pub branch_summary: Map<AU, Summary>,
}

#[verifier::ext_equal]
pub struct BetreeMetadataRecovery {
    pub disk: CachingDisk::State,
    pub betree_nodes: Map<Address, BetreeNode>,
    pub pending_betree: Set<Address>,
    pub branch_roots: Set<Address>,
    pub pending_branch_roots: Set<Address>,
    pub pending_branch_aux: Map<Address, Address>,
    pub branch_summary: Map<AU, Summary>,
}

pub enum BetreeMetadataRecoveryLabel {
    DiskInternal,
    ReadBetree {
        addr: Address,
        reads: Map<Address, RawPage>,
    },
    ReadBranchRoot {
        root: Address,
        reads: Map<Address, RawPage>,
    },
    ReadBranchAux {
        root: Address,
        reads: Map<Address, RawPage>,
    },
}

pub open spec fn betree_child_addrs(node: BetreeNode) -> Set<Address> {
    Set::new(|addr: Address| exists |i: int|
        0 <= i < node.children.len()
        && node.children[i] == Option::Some(addr))
}

pub open spec fn betree_buffer_roots(node: BetreeNode) -> Set<Address> {
    node.buffers.addrs.to_set()
}

impl BetreeMetadataRecoveryCore {
    pub open spec fn start(
        metadata: CachingDiskBranchBetreeMetadata,
    ) -> Self {
        Self {
            betree_nodes: Map::empty(),
            pending_betree: if metadata.root is Some {
                set![metadata.root.unwrap()]
            } else {
                Set::empty()
            },
            branch_roots: Set::empty(),
            pending_branch_roots: Set::empty(),
            pending_branch_aux: Map::empty(),
            branch_summary: Map::empty(),
        }
    }

    pub open spec fn read_betree(
        self,
        addr: Address,
        node: BetreeNode,
    ) -> Self {
        let betree_nodes = self.betree_nodes.insert(addr, node);
        let new_branch_roots =
            betree_buffer_roots(node) - self.branch_roots;
        Self {
            betree_nodes,
            pending_betree:
                (self.pending_betree.remove(addr)
                    + betree_child_addrs(node))
                    - betree_nodes.dom(),
            branch_roots:
                self.branch_roots + new_branch_roots,
            pending_branch_roots:
                self.pending_branch_roots + new_branch_roots,
            ..self
        }
    }

    pub open spec fn read_branch_root(
        self,
        root: Address,
        node: BranchNode,
    ) -> Self
        recommends
            self.pending_branch_roots.contains(root),
            node is Leaf || node is Index,
            node is Index ==> node.arrow_Index_aux_ptr() is Some,
    {
        match node {
            BranchNodeValue::Leaf{..} => Self {
                pending_branch_roots:
                    self.pending_branch_roots.remove(root),
                branch_summary:
                    self.branch_summary.insert(root.au, set![root.au]),
                ..self
            },
            BranchNodeValue::Index{aux_ptr, ..} => Self {
                pending_branch_roots:
                    self.pending_branch_roots.remove(root),
                pending_branch_aux:
                    self.pending_branch_aux.insert(
                        root,
                        aux_ptr.unwrap(),
                    ),
                ..self
            },
            BranchNodeValue::Auxiliary{..} => self,
        }
    }

    pub open spec fn read_branch_aux(
        self,
        root: Address,
        node: BranchNode,
    ) -> Self
        recommends
            self.pending_branch_aux.contains_key(root),
            node is Auxiliary,
    {
        Self {
            pending_branch_aux:
                self.pending_branch_aux.remove(root),
            branch_summary:
                self.branch_summary.insert(
                    root.au,
                    node.arrow_Auxiliary_0(),
                ),
            ..self
        }
    }

    pub open spec fn next(
        pre: Self,
        post: Self,
        lbl: BetreeMetadataRecoveryLabel,
    ) -> bool {
        match lbl {
            BetreeMetadataRecoveryLabel::DiskInternal => {
                post == pre
            },
            BetreeMetadataRecoveryLabel::ReadBetree{addr, reads} => {
                &&& pre.pending_betree.contains(addr)
                &&& reads.dom() == set![addr]
                &&& post == pre.read_betree(
                    addr,
                    to_betree_nodes(reads)[addr],
                )
            },
            BetreeMetadataRecoveryLabel::ReadBranchRoot{root, reads} => {
                let node = to_branch_nodes(reads)[root];
                &&& pre.pending_branch_roots.contains(root)
                &&& reads.dom() == set![root]
                &&& node is Leaf || node is Index
                &&& node is Index ==>
                    node.arrow_Index_aux_ptr() is Some
                &&& post == pre.read_branch_root(root, node)
            },
            BetreeMetadataRecoveryLabel::ReadBranchAux{root, reads} => {
                let aux = pre.pending_branch_aux[root];
                let node = to_branch_nodes(reads)[aux];
                &&& pre.pending_branch_aux.contains_key(root)
                &&& reads.dom() == set![aux]
                &&& node is Auxiliary
                &&& post == pre.read_branch_aux(root, node)
            },
        }
    }

    pub open spec fn complete(self) -> bool {
        &&& self.pending_betree.is_empty()
        &&& self.pending_branch_roots.is_empty()
        &&& self.pending_branch_aux.dom().is_empty()
    }

    pub open spec fn recovered_likes_tree(
        self,
        metadata: CachingDiskBranchBetreeMetadata,
    ) -> LinkedBetree<BranchNode> {
        LinkedBetree {
            root: metadata.root,
            dv: BetreeDiskView {
                entries: self.betree_nodes,
            },
            // Transitive likes are determined by Betree nodes and their
            // branch-root pointers. Physical branch contents are supplied
            // and validated by the enclosing caching-disk refinement.
            buffer_dv: BufferDisk::empty_disk(),
        }
    }

    pub open spec fn betree_aus(
        self,
        metadata: CachingDiskBranchBetreeMetadata,
    ) -> AULikes {
        let tree = self.recovered_likes_tree(metadata);
        if tree.acyclic() {
            to_au_likes(tree.transitive_likes().0)
        } else {
            Multiset::empty()
        }
    }

    pub open spec fn branch_aus(
        self,
        metadata: CachingDiskBranchBetreeMetadata,
    ) -> AULikes {
        let tree = self.recovered_likes_tree(metadata);
        if tree.acyclic() {
            to_au_likes(tree.transitive_likes().1)
        } else {
            Multiset::empty()
        }
    }

    pub open spec fn loaded_betree(
        self,
        metadata: CachingDiskBranchBetreeMetadata,
    ) -> CachedBranchBetree::State {
        CachedBranchBetree::State {
            root: metadata.root,
            memtable: Memtable::empty_memtable(metadata.seq_end),
            betree_aus: self.betree_aus(metadata),
            branch_aus: self.branch_aus(metadata),
            branch_summary: self.branch_summary,
            compactors: Seq::empty(),
            wip_branches: Seq::empty(),
        }
    }
}

impl BetreeMetadataRecovery {
    pub open spec fn from_core(
        disk: CachingDisk::State,
        core: BetreeMetadataRecoveryCore,
    ) -> Self {
        Self {
            disk,
            betree_nodes: core.betree_nodes,
            pending_betree: core.pending_betree,
            branch_roots: core.branch_roots,
            pending_branch_roots: core.pending_branch_roots,
            pending_branch_aux: core.pending_branch_aux,
            branch_summary: core.branch_summary,
        }
    }

    pub open spec fn core(self) -> BetreeMetadataRecoveryCore {
        BetreeMetadataRecoveryCore {
            betree_nodes: self.betree_nodes,
            pending_betree: self.pending_betree,
            branch_roots: self.branch_roots,
            pending_branch_roots: self.pending_branch_roots,
            pending_branch_aux: self.pending_branch_aux,
            branch_summary: self.branch_summary,
        }
    }

    pub open spec fn start(image: CachingDiskBranchBetreeImage) -> Self {
        Self {
            disk: image.disk(),
            betree_nodes: Map::empty(),
            pending_betree: if image.metadata.root is Some {
                set![image.metadata.root.unwrap()]
            } else {
                Set::empty()
            },
            branch_roots: Set::empty(),
            pending_branch_roots: Set::empty(),
            pending_branch_aux: Map::empty(),
            branch_summary: Map::empty(),
        }
    }

    pub open spec fn read_betree(
        self,
        addr: Address,
        node: BetreeNode,
    ) -> Self {
        let betree_nodes = self.betree_nodes.insert(addr, node);
        let new_branch_roots =
            betree_buffer_roots(node) - self.branch_roots;
        Self {
            betree_nodes,
            pending_betree:
                (self.pending_betree.remove(addr)
                    + betree_child_addrs(node))
                    - betree_nodes.dom(),
            branch_roots:
                self.branch_roots + new_branch_roots,
            pending_branch_roots:
                self.pending_branch_roots + new_branch_roots,
            ..self
        }
    }

    pub open spec fn read_branch_root(
        self,
        root: Address,
        node: BranchNode,
    ) -> Self
        recommends
            self.pending_branch_roots.contains(root),
            node is Leaf || node is Index,
            node is Index ==> node.arrow_Index_aux_ptr() is Some,
    {
        match node {
            BranchNodeValue::Leaf{..} => Self {
                pending_branch_roots:
                    self.pending_branch_roots.remove(root),
                branch_summary:
                    self.branch_summary.insert(root.au, set![root.au]),
                ..self
            },
            BranchNodeValue::Index{aux_ptr, ..} => Self {
                pending_branch_roots:
                    self.pending_branch_roots.remove(root),
                pending_branch_aux:
                    self.pending_branch_aux.insert(
                        root,
                        aux_ptr.unwrap(),
                    ),
                ..self
            },
            BranchNodeValue::Auxiliary{..} => self,
        }
    }

    pub open spec fn read_branch_aux(
        self,
        root: Address,
        node: BranchNode,
    ) -> Self
        recommends
            self.pending_branch_aux.contains_key(root),
            node is Auxiliary,
    {
        Self {
            pending_branch_aux:
                self.pending_branch_aux.remove(root),
            branch_summary:
                self.branch_summary.insert(
                    root.au,
                    node.arrow_Auxiliary_0(),
                ),
            ..self
        }
    }

    pub open spec fn next(
        pre: Self,
        post: Self,
        lbl: BetreeMetadataRecoveryLabel,
    ) -> bool {
        match lbl {
            BetreeMetadataRecoveryLabel::DiskInternal => {
                &&& CachingDisk::State::next(
                    pre.disk,
                    post.disk,
                    CachingDisk::Label::Internal{},
                )
                &&& post.betree_nodes == pre.betree_nodes
                &&& post.pending_betree == pre.pending_betree
                &&& post.branch_roots == pre.branch_roots
                &&& post.pending_branch_roots
                    == pre.pending_branch_roots
                &&& post.pending_branch_aux
                    == pre.pending_branch_aux
                &&& post.branch_summary == pre.branch_summary
            },
            BetreeMetadataRecoveryLabel::ReadBetree{addr, reads} => {
                &&& pre.pending_betree.contains(addr)
                &&& reads.dom() == set![addr]
                &&& CachingDisk::State::next(
                    pre.disk,
                    pre.disk,
                    CachingDisk::Label::Access{
                        reads,
                        writes: Map::empty(),
                    },
                )
                &&& post == pre.read_betree(
                    addr,
                    to_betree_nodes(reads)[addr],
                )
            },
            BetreeMetadataRecoveryLabel::ReadBranchRoot{root, reads} => {
                let node = to_branch_nodes(reads)[root];
                &&& pre.pending_branch_roots.contains(root)
                &&& reads.dom() == set![root]
                &&& node is Leaf || node is Index
                &&& node is Index ==>
                    node.arrow_Index_aux_ptr() is Some
                &&& CachingDisk::State::next(
                    pre.disk,
                    pre.disk,
                    CachingDisk::Label::Access{
                        reads,
                        writes: Map::empty(),
                    },
                )
                &&& post == pre.read_branch_root(root, node)
            },
            BetreeMetadataRecoveryLabel::ReadBranchAux{root, reads} => {
                let aux = pre.pending_branch_aux[root];
                let node = to_branch_nodes(reads)[aux];
                &&& pre.pending_branch_aux.contains_key(root)
                &&& reads.dom() == set![aux]
                &&& node is Auxiliary
                &&& CachingDisk::State::next(
                    pre.disk,
                    pre.disk,
                    CachingDisk::Label::Access{
                        reads,
                        writes: Map::empty(),
                    },
                )
                &&& post == pre.read_branch_aux(root, node)
            },
        }
    }

    pub open spec fn complete(self) -> bool {
        &&& self.pending_betree.is_empty()
        &&& self.pending_branch_roots.is_empty()
        &&& self.pending_branch_aux.dom().is_empty()
    }

    pub open spec fn recovered_tree(
        self,
        image: CachingDiskBranchBetreeImage,
    ) -> LinkedBetree<BranchNode> {
        LinkedBetree {
            root: image.metadata.root,
            dv: BetreeDiskView {
                entries: self.betree_nodes,
            },
            buffer_dv: tight_sealed_branch_disk(
                visible_branch_disk(
                    self.disk,
                    self.branch_summary,
                ),
                self.branch_roots,
                self.branch_summary,
            ),
        }
    }

    pub open spec fn initial_betree(
        self,
        image: CachingDiskBranchBetreeImage,
    ) -> LinkedBetreeVars::State<BranchNode> {
        LinkedBetreeVars::State {
            memtable:
                Memtable::empty_memtable(image.metadata.seq_end),
            linked: self.recovered_tree(image),
        }
    }

    pub open spec fn betree_aus(
        self,
        image: CachingDiskBranchBetreeImage,
    ) -> AULikes {
        let tree = self.recovered_tree(image);
        if tree.acyclic() {
            to_au_likes(tree.transitive_likes().0)
        } else {
            Multiset::empty()
        }
    }

    pub open spec fn branch_aus(
        self,
        image: CachingDiskBranchBetreeImage,
    ) -> AULikes {
        let tree = self.recovered_tree(image);
        if tree.acyclic() {
            to_au_likes(tree.transitive_likes().1)
        } else {
            Multiset::empty()
        }
    }

    pub open spec fn loaded_state(
        self,
        image: CachingDiskBranchBetreeImage,
    ) -> CachingDiskBranchBetree::State {
        CachingDiskBranchBetree::State {
            disk: self.disk,
            betree: image.cached_betree(
                self.betree_aus(image),
                self.branch_aus(image),
                self.branch_summary,
            ),
        }
    }
}

impl CachingDiskBranchBetreeImage {
    pub open spec fn empty() -> Self {
        Self {
            persistent: Map::empty(),
            metadata: CachingDiskBranchBetreeMetadata::empty(),
        }
    }

    pub open spec fn disk(self) -> CachingDisk::State {
        CachingDisk::State {
            cache: Map::empty(),
            persistent: self.persistent,
            status: Map::empty(),
        }
    }

    pub open spec fn cached_betree(
        self,
        betree_aus: AULikes,
        branch_aus: AULikes,
        branch_summary: Map<AU, Summary>,
    ) -> CachedBranchBetree::State {
        CachedBranchBetree::State {
            root: self.metadata.root,
            memtable: Memtable::empty_memtable(self.metadata.seq_end),
            betree_aus,
            branch_aus,
            branch_summary,
            compactors: Seq::empty(),
            wip_branches: Seq::empty(),
        }
    }

    pub open spec fn load_metadata(
        self,
        betree_aus: AULikes,
        branch_aus: AULikes,
        branch_summary: Map<AU, Summary>,
    ) -> CachingDiskBranchBetree::State {
        let betree = self.cached_betree(
            betree_aus,
            branch_aus,
            branch_summary,
        );
        CachingDiskBranchBetree::State {
            disk: self.disk(),
            betree,
        }
    }

    pub open spec fn valid(self) -> bool {
        &&& self.disk().inv()
        &&& exists |
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
        )
    }

    pub open spec fn materialized_from_persistent(
        state: CachingDiskBranchBetree::State,
        frozen: FrozenCachingDiskBranchBetree,
    ) -> Self {
        Self {
            persistent: state.disk.persistent.restrict(
                addresses_in_aus(frozen.aus),
            ),
            metadata: frozen.metadata,
        }
    }

    pub open spec fn materialized_from_visible(
        state: CachingDiskBranchBetree::State,
        frozen: FrozenCachingDiskBranchBetree,
    ) -> Self {
        Self {
            persistent: state.disk.visible().restrict(
                addresses_in_aus(frozen.aus),
            ),
            metadata: frozen.metadata,
        }
    }
}

pub open spec fn logical_allocs(
    op: CachingDiskBranchBetree::Label,
) -> Set<AU> {
    match op {
        CachingDiskBranchBetree::Label::InternalAlloc{allocs, ..} =>
            allocs,
        _ => Set::empty(),
    }
}

pub open spec fn logical_deallocs(
    op: CachingDiskBranchBetree::Label,
) -> Set<AU> {
    match op {
        CachingDiskBranchBetree::Label::InternalAlloc{deallocs, ..} =>
            deallocs,
        _ => Set::empty(),
    }
}

pub open spec fn logical_guard_aus(
    op: CachingDiskBranchBetree::Label,
) -> Set<AU> {
    match op {
        CachingDiskBranchBetree::Label::InternalAlloc{guard_aus, ..} =>
            guard_aus,
        _ => Set::empty(),
    }
}

pub open spec fn protected_aus(
    persistent_aus: Set<AU>,
    frozen: Option<FrozenCachingDiskBranchBetree>,
) -> Set<AU> {
    persistent_aus + if frozen is Some {
        frozen.unwrap().aus
    } else {
        Set::empty()
    }
}

pub open spec fn empty_initial_betree()
    -> LinkedBetreeVars::State<BranchNode>
{
    LinkedBetreeVars::State {
        memtable: Memtable::empty_memtable(0),
        linked: LinkedBetree {
            root: Option::None,
            dv: empty_betree_disk(),
            buffer_dv: BufferDisk::empty_disk(),
        },
    }
}

pub proof fn empty_image_valid()
    ensures CachingDiskBranchBetreeImage::empty().valid()
{
    let image = CachingDiskBranchBetreeImage::empty();
    let initial = empty_initial_betree();
    CachingDisk::State::persistent_only_inv(image.persistent);
    reveal(initial_refinement_witness_valid);
    reveal(LinkedBetree::transitive_likes);
    reveal(LinkedBetree::tree_likes);
    reveal(LinkedBetree::buffer_likes);
    reveal(LinkedBetree::acyclic);
    reveal(LinkedBetree::valid_ranking);
    reveal(LinkedBetree::wf);
    reveal(LinkedBetree::has_root);
    reveal(LinkedBetree::reachable_betree_addrs);
    reveal(LinkedBetree::reachable_betree_addrs_using_ranking);
    reveal(LinkedBetree::reachable_buffer_addrs);
    reveal(LinkedBetree::reachable_buffer);
    reveal(crate::implementation::CachingDiskBranchBetreeRefinement_v::tight_betree_candidate);
    reveal(crate::allocation_layer::AllocationBranchBetree_v::AllocationBranchBetree::State::initialize);
    reveal(LinkedBetreeVars::State::initialize);
    assert(initial.linked.valid_ranking(Map::empty()));
    assert(initial.linked.acyclic());
    assert(initial.linked.transitive_likes()
        == (
            Multiset::<Address>::empty(),
            Multiset::<Address>::empty(),
        ));
    let betree_likes = initial.linked.transitive_likes().0;
    let branch_likes = initial.linked.transitive_likes().1;
    assert(betree_likes == Multiset::<Address>::empty());
    assert(branch_likes == Multiset::<Address>::empty());
    assert(branch_likes.dom() =~= Set::<Address>::empty());
    assert(crate::implementation::CachingDiskBranchBetreeRefinement_v::tight_betree_candidate(
        Option::None,
        Map::empty(),
        initial.linked,
    ));
    let roots = initial.linked.reachable_buffer_addrs();
    assert(roots =~= Set::<Address>::empty()) by {
        assert forall |addr: Address| #[trigger] roots.contains(addr)
            implies false by {
            let node_addr = choose |node_addr: Address|
                initial.linked.reachable_buffer(node_addr, addr);
            assert(initial.linked.reachable_betree_addrs().contains(node_addr));
            assert(false);
        }
    }
    let branch_disk = initial.linked.buffer_dv;
    assert(branch_disk.sealed_branch_roots(Set::<Address>::empty())) by {
        reveal(BufferDisk::<_>::sealed_branch_roots);
    }
    assert(branch_disk.sealed_branch_roots(branch_likes.dom())) by {
        reveal(BufferDisk::<_>::sealed_branch_roots);
    }
    branch_disk.build_branch_domain(Set::<Address>::empty());
    assert(branch_disk.build_branch_summary(Set::<Address>::empty())
        =~= Map::<AU, Summary>::empty()) by {
        assert_maps_equal!(
            branch_disk.build_branch_summary(Set::<Address>::empty()),
            Map::<AU, Summary>::empty(),
            au => {
                if branch_disk.build_branch_summary(
                    Set::<Address>::empty(),
                ).contains_key(au) {
                    assert(branch_disk.build_branch_summary(
                        Set::<Address>::empty(),
                    ).dom().contains(au));
                    assert(false);
                }
            }
        );
    }
    crate::allocation_layer::Likes_v::to_au_likes_empty();
    branch_disk.build_branch_domain(branch_likes.dom());
    assert(branch_disk.build_branch_summary(branch_likes.dom())
        == Map::<AU, Summary>::empty()) by {
        assert_maps_equal!(
            branch_disk.build_branch_summary(branch_likes.dom()),
            Map::<AU, Summary>::empty(),
            au => {
                if branch_disk.build_branch_summary(
                    branch_likes.dom(),
                ).contains_key(au) {
                    assert(branch_disk.build_branch_summary(
                        branch_likes.dom(),
                    ).dom().contains(au));
                    assert(false);
                }
            }
        );
    }
    reveal(crate::implementation::CachingDiskBranchBetree_v::tight_sealed_branch_disk);
    reveal(crate::implementation::CachingDiskBranchBetree_v::tight_branch_addrs);
    assert(crate::implementation::CachingDiskBranchBetree_v::tight_sealed_branch_disk(
        branch_disk,
        Set::<Address>::empty(),
        Map::<AU, Summary>::empty(),
    ) == branch_disk) by {
        assert_maps_equal!(
            crate::implementation::CachingDiskBranchBetree_v::tight_sealed_branch_disk(
                branch_disk,
                Set::<Address>::empty(),
                Map::<AU, Summary>::empty(),
            ).entries,
            branch_disk.entries,
            addr => {}
        );
    }
    let initial_tree =
        crate::implementation::CachingDiskBranchBetreeRefinement_v::initial_tight_tree(
            initial,
        );
    let loose_branches =
        crate::implementation::CachingDiskBranchBetree_v::visible_branch_disk(
            image.disk(),
            Map::empty(),
        );
    assert(initial_tree == initial.linked);
    assert(initial_tree.reachable_buffer_addrs() == roots);
    assert(loose_branches == branch_disk) by {
        assert_maps_equal!(loose_branches.entries, branch_disk.entries, addr => {});
    }
    assert(crate::implementation::CachingDiskBranchBetree_v::tight_sealed_branch_disk(
        loose_branches,
        initial_tree.reachable_buffer_addrs(),
        Map::empty(),
    ) == initial.linked.buffer_dv);
    assert(initial_refinement_witness_valid(
        image.disk(),
        image.metadata.root,
        image.metadata.seq_end,
        Multiset::empty(),
        Multiset::empty(),
        Map::empty(),
        initial,
    ));
}

state_machine! { CrashAwareCachingDiskBranchBetree {
    fields {
        pub persistent: CachingDiskBranchBetreeImage,
        pub ephemeral: EphemeralCachingDiskBranchBetree,
        pub frozen: Option<FrozenCachingDiskBranchBetree>,
        pub prepared: Option<CachingDiskBranchBetreeImage>,
    }

    pub enum Label {
        LoadEphemeral,
        RecoverMetadata {
            recovery_op: BetreeMetadataRecoveryLabel,
        },
        LoadMetadata,
        Ephemeral {
            op: CachingDiskBranchBetree::Label,
            deallocs: Set<AU>,
        },
        CommitStart { image: FrozenBranchBetree },
        CommitPrepared,
        CommitComplete { deallocs: Set<AU> },
        Crash { keep_in_flight: bool },
    }

    init! { initialize() {
        init persistent = CachingDiskBranchBetreeImage::empty();
        init ephemeral = EphemeralCachingDiskBranchBetree::Unknown;
        init frozen = Option::None;
        init prepared = Option::None;
    }}

    transition! { load_ephemeral(
        lbl: Label,
        initial_disk: CachingDisk::State,
    ) {
        require lbl is LoadEphemeral;
        require pre.ephemeral is Unknown;
        require pre.persistent.valid();
        require initial_disk.inv();
        require initial_disk.persistent
            == pre.persistent.persistent;
        require initial_disk.visible()
            == pre.persistent.disk().visible();

        update ephemeral =
            EphemeralCachingDiskBranchBetree::Loading {
                recovery: BetreeMetadataRecovery::from_core(
                    initial_disk,
                    BetreeMetadataRecoveryCore::start(
                        pre.persistent.metadata,
                    ),
                ),
            };
    }}

    transition! { recover_metadata(
        lbl: Label,
        new_recovery: BetreeMetadataRecovery,
    ) {
        require let Label::RecoverMetadata{recovery_op} = lbl;
        require pre.ephemeral is Loading;
        require BetreeMetadataRecovery::next(
            pre.ephemeral->recovery,
            new_recovery,
            recovery_op,
        );

        update ephemeral =
            EphemeralCachingDiskBranchBetree::Loading {
                recovery: new_recovery,
            };
    }}

    transition! { load_metadata(lbl: Label) {
        require lbl is LoadMetadata;
        require pre.ephemeral is Loading;
        let image = pre.persistent;
        let recovery = pre.ephemeral->recovery;
        require recovery.complete();
        let loaded = recovery.loaded_state(image);

        update ephemeral =
            EphemeralCachingDiskBranchBetree::Known{
                v: loaded,
                persistent_aus: loaded.betree.durable_aus(),
            };
    }}

    transition! { ephemeral_step(
        lbl: Label,
        new_ephemeral: CachingDiskBranchBetree::State,
    ) {
        require let Label::Ephemeral{op, deallocs} = lbl;
        require pre.ephemeral is Known;
        require !(op is FreezeAs);
        let old_ephemeral = pre.ephemeral->v;
        let persistent_aus = pre.ephemeral->persistent_aus;
        let protected = protected_aus(persistent_aus, pre.frozen);
        require op is InternalAlloc
            ==> logical_guard_aus(op) == protected;
        require logical_allocs(op).disjoint(protected);
        require deallocs == logical_deallocs(op) - protected;
        require CachingDiskBranchBetree::State::next(
            old_ephemeral,
            new_ephemeral,
            op,
        );

        update ephemeral =
            EphemeralCachingDiskBranchBetree::Known{
                v: new_ephemeral,
                persistent_aus,
            };
    }}

    transition! { commit_start(lbl: Label) {
        require let Label::CommitStart{image} = lbl;
        require pre.ephemeral is Known;
        require pre.frozen is None;
        require pre.prepared is None;
        require pre.persistent.metadata.seq_end <= image.seq_end;
        require pre.ephemeral->v.betree.compactors.len() == 0;
        require pre.ephemeral->v.betree.wip_branches.len() == 0;
        require CachingDiskBranchBetree::State::next(
            pre.ephemeral->v,
            pre.ephemeral->v,
            CachingDiskBranchBetree::Label::FreezeAs{image},
        );

        update frozen = Option::Some(
            FrozenCachingDiskBranchBetree {
                metadata: CachingDiskBranchBetreeMetadata {
                    root: image.root,
                    seq_end: image.seq_end,
                },
                aus: pre.ephemeral->v.betree.durable_aus(),
            },
        );
    }}

    transition! { commit_prepared(
        lbl: Label,
        image: CachingDiskBranchBetreeImage,
    ) {
        require lbl is CommitPrepared;
        require pre.ephemeral is Known;
        require pre.frozen is Some;
        require pre.prepared is None;
        let frozen = pre.frozen.unwrap();
        require pre.ephemeral->v.disk.aus_clean_or_evictable(
            frozen.aus,
        );
        require image
            == CachingDiskBranchBetreeImage::materialized_from_persistent(
                pre.ephemeral->v,
                frozen,
            );
        require image.valid();

        update prepared = Option::Some(image);
    }}

    transition! { commit_complete(
        lbl: Label,
        new_ephemeral: CachingDiskBranchBetree::State,
    ) {
        require let Label::CommitComplete{deallocs} = lbl;
        require pre.ephemeral is Known;
        require pre.frozen is Some;
        require pre.prepared is Some;
        let current = pre.ephemeral->v;
        let persistent_aus = pre.ephemeral->persistent_aus;
        let frozen = pre.frozen.unwrap();
        let guard_aus = frozen.aus + current.betree.owned_aus();
        require deallocs == persistent_aus
            - frozen.aus
            - current.betree.owned_aus();
        require reclaim_guarded_aus(
            current,
            new_ephemeral,
            persistent_aus,
            guard_aus,
        );

        update persistent = pre.prepared.unwrap();
        update ephemeral =
            EphemeralCachingDiskBranchBetree::Known{
                v: new_ephemeral,
                persistent_aus: frozen.aus,
            };
        update frozen = Option::None;
        update prepared = Option::None;
    }}

    transition! { crash(lbl: Label) {
        require let Label::Crash{keep_in_flight} = lbl;
        require keep_in_flight ==> pre.prepared is Some;

        update persistent =
            if keep_in_flight { pre.prepared.unwrap() } else { pre.persistent };
        update ephemeral = EphemeralCachingDiskBranchBetree::Unknown;
        update frozen = Option::None;
        update prepared = Option::None;
    }}

    #[invariant]
    pub open spec fn inv(self) -> bool {
        &&& self.persistent.valid()
        &&& self.ephemeral is Loading ==>
            self.ephemeral->recovery.disk.inv()
        &&& self.ephemeral is Known ==> self.ephemeral->v.inv()
        &&& self.frozen is Some ==> self.ephemeral is Known
        &&& self.prepared is Some ==> self.frozen is Some
        &&& self.prepared is Some ==> self.prepared.unwrap().valid()
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) {
        empty_image_valid();
    }

    #[inductive(load_ephemeral)]
    fn load_ephemeral_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        initial_disk: CachingDisk::State,
    ) {
        assert(post.ephemeral->recovery.disk == initial_disk);
        assert(post.ephemeral->recovery.disk.inv());
    }

    #[inductive(recover_metadata)]
    fn recover_metadata_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_recovery: BetreeMetadataRecovery,
    ) {
        let old_recovery = pre.ephemeral->recovery;
        match lbl->recovery_op {
            BetreeMetadataRecoveryLabel::DiskInternal => {
                CachingDisk::State::inv_next(
                    old_recovery.disk,
                    new_recovery.disk,
                    CachingDisk::Label::Internal{},
                );
            },
            BetreeMetadataRecoveryLabel::ReadBetree{..}
            | BetreeMetadataRecoveryLabel::ReadBranchRoot{..}
            | BetreeMetadataRecoveryLabel::ReadBranchAux{..} => {
                assert(new_recovery.disk == old_recovery.disk);
            },
        }
    }

    #[inductive(load_metadata)]
    fn load_metadata_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
    ) {
        assert(post.ephemeral->v.disk
            == pre.ephemeral->recovery.disk);
        assert(post.ephemeral->v.inv());
    }

    #[inductive(ephemeral_step)]
    fn ephemeral_step_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_ephemeral: CachingDiskBranchBetree::State,
    ) {
        CachingDiskBranchBetree::State::inv_next(
            pre.ephemeral->v,
            new_ephemeral,
            lbl->op,
        );
    }

    #[inductive(commit_start)]
    fn commit_start_inductive(pre: Self, post: Self, lbl: Label) {
    }

    #[inductive(commit_prepared)]
    fn commit_prepared_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        image: CachingDiskBranchBetreeImage,
    ) {
    }

    #[inductive(commit_complete)]
    fn commit_complete_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_ephemeral: CachingDiskBranchBetree::State,
    ) {
        reclaim_guarded_aus_preserves_inv(
            pre.ephemeral->v,
            new_ephemeral,
            pre.ephemeral->persistent_aus,
            pre.frozen.unwrap().aus
                + pre.ephemeral->v.betree.owned_aus(),
        );
    }

    #[inductive(crash)]
    fn crash_inductive(pre: Self, post: Self, lbl: Label) {
    }

    pub proof fn init_inv(self)
        requires CrashAwareCachingDiskBranchBetree::State::initialize(self)
        ensures self.inv()
    {
        Self::initialize_inductive(self);
    }

    pub proof fn inv_next(
        pre: Self,
        post: Self,
        lbl: CrashAwareCachingDiskBranchBetree::Label,
    )
        requires
            pre.inv(),
            CrashAwareCachingDiskBranchBetree::State::next(pre, post, lbl),
        ensures post.inv()
    {
        reveal(CrashAwareCachingDiskBranchBetree::State::next);
        reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
        let step = choose |step: CrashAwareCachingDiskBranchBetree::Step|
            CrashAwareCachingDiskBranchBetree::State::next_by(
                pre, post, lbl, step,
            );
        match step {
            CrashAwareCachingDiskBranchBetree::Step::load_ephemeral(
                initial_disk,
            ) => {
                Self::load_ephemeral_inductive(
                    pre,
                    post,
                    lbl,
                    initial_disk,
                );
            }
            CrashAwareCachingDiskBranchBetree::Step::recover_metadata(
                new_recovery,
            ) => {
                Self::recover_metadata_inductive(
                    pre,
                    post,
                    lbl,
                    new_recovery,
                );
            }
            CrashAwareCachingDiskBranchBetree::Step::load_metadata() => {
                Self::load_metadata_inductive(
                    pre,
                    post,
                    lbl,
                );
            }
            CrashAwareCachingDiskBranchBetree::Step::ephemeral_step(
                new_ephemeral,
            ) => {
                Self::ephemeral_step_inductive(
                    pre,
                    post,
                    lbl,
                    new_ephemeral,
                );
            }
            CrashAwareCachingDiskBranchBetree::Step::commit_start() => {
                Self::commit_start_inductive(pre, post, lbl);
            }
            CrashAwareCachingDiskBranchBetree::Step::commit_prepared(image) => {
                Self::commit_prepared_inductive(pre, post, lbl, image);
            }
            CrashAwareCachingDiskBranchBetree::Step::commit_complete(
                new_ephemeral,
            ) => {
                Self::commit_complete_inductive(
                    pre,
                    post,
                    lbl,
                    new_ephemeral,
                );
            }
            CrashAwareCachingDiskBranchBetree::Step::crash() => {
                Self::crash_inductive(pre, post, lbl);
            }
            CrashAwareCachingDiskBranchBetree::Step::dummy_to_use_type_params(_) => {
                assert(false);
            }
        }
    }
}}

} // verus!
