// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::assert_seqs_equal;
use vstd::assert_sets_equal;
use vstd::arithmetic::div_mod::{
    group_div_basics, lemma_basic_div, lemma_div_nonincreasing,
    lemma_fundamental_div_mod,
};
use vstd::arithmetic::mul::{
    group_mul_properties, lemma_mul_basics, lemma_mul_is_commutative,
    lemma_mul_inequality,
    lemma_mul_inequality_converse, lemma_mul_strict_inequality_converse,
};

use crate::disk::GenericDisk_v::{Address, addrs_closed};
use crate::disk::GenericDisk_v::Ranking;
use crate::allocation_layer::BranchTypes_v::{
    BranchNode, Summary,
};
use crate::allocation_layer::Likes_v::restrict_domain_au;
use crate::betree::LinkedBranch_v::{
    DiskView as BranchDiskView, LinkedBranch,
};
use crate::betree::LinkedBranch_v::Refinement_v as LinkedBranchRefinement;
use crate::betree::PivotBranch_v::Node as PivotNode;
use crate::betree::PivotBranchRefinement_v as PivotBranchRefinement;
use crate::betree::Utils_v::{
    lemma_set_subset_of_union_seq_of_sets,
    lemma_union_seq_of_sets_contains,
    union_seq_of_sets,
};
use crate::implementation::CachedBranch_v::LoadedBranch;
use crate::implementation::IBranchNode_v::{IBranchNode, iopt_addr};
use crate::implementation::MemtableImpl_v::{
    MemtableBucket, MemtableEntry, MemtableImpl, MemtableSortedCursor,
};
use crate::implementation::BranchPageImpl_v::{
    branch_index_capacity, branch_index_capacity_spec, branch_leaf_capacity,
};
use crate::marshalling::WF_v::WF;
use crate::spec::ImplDisk_t::IAddress;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::Message;

verus! {

pub struct BalancedPartition {
    pub total: usize,
    pub capacity: usize,
    pub node_count: usize,
    pub base: usize,
    pub extra: usize,
    pub emitted: usize,
}

#[derive(Clone, Copy)]
pub struct BranchChildDescriptor {
    pub first_key: Key,
    pub addr: IAddress,
    pub receipt: Ghost<BranchSubtreeReceipt>,
}

pub struct BranchSubtreeReceipt {
    pub root: Address,
    pub nodes: LoadedBranch,
    pub ranking: Ranking,
    pub pivot: PivotNode,
    pub first_key: Key,
    pub last_key: Key,
    pub height: nat,
}

pub struct BranchBuildLevel {
    pub input: Vec<BranchChildDescriptor>,
    pub next_input: usize,
    pub partition: BalancedPartition,
    pub output: Vec<BranchChildDescriptor>,
}

pub enum BranchBulkPhase {
    Leaves,
    Index,
    ReadyLeafRoot,
    ReadyIndexRoot,
    Sealed,
}

pub struct BranchBulkBuilder {
    pub cursor: MemtableSortedCursor,
    pub phase: BranchBulkPhase,
    pub index_fanout: usize,
    pub leaf_partition: BalancedPartition,
    pub leaf_output: Vec<BranchChildDescriptor>,
    pub level: Option<BranchBuildLevel>,
    pub root_leaf: Vec<MemtableEntry>,
    pub root_children: Vec<BranchChildDescriptor>,
    pub staged_nodes: Ghost<LoadedBranch>,
    pub source: Ghost<Map<Key, crate::spec::Messages_t::Message>>,
}

pub enum BranchBulkStartResult {
    Started { builder: BranchBulkBuilder },
    Empty,
    Overflow,
    InvalidCapacity,
}

pub enum BranchBulkNodeResult {
    Page {
        node: IBranchNode,
        descriptor: BranchChildDescriptor,
    },
    NotReady,
}

proof fn balanced_partition_arithmetic(
    total: int,
    capacity: int,
    node_count: int,
    base: int,
    extra: int,
    quotient: int,
    remainder: int,
)
    requires
        total > 0,
        capacity > 0,
        quotient >= 0,
        remainder >= 0,
        remainder < capacity,
        node_count == quotient + 1,
        total == capacity * quotient + remainder + 1,
        base >= 0,
        extra >= 0,
        extra < node_count,
        total == node_count * base + extra,
    ensures
        node_count > 0,
        node_count <= total,
        base > 0,
        base <= capacity,
        extra > 0 ==> base < capacity,
        total <= node_count * capacity,
{
    broadcast use group_mul_properties;
    assert(remainder + 1 <= capacity);
    lemma_mul_inequality(1, capacity, quotient);
    assert(quotient <= capacity * quotient);
    assert(node_count <= total);
    assert(total <= node_count * capacity);
    if base == 0 {
        assert(total == extra);
        assert(false);
    }
    assert(base > 0);
    assert(node_count * base <= node_count * capacity);
    assert(base * node_count <= capacity * node_count);
    lemma_mul_inequality_converse(base, capacity, node_count);
    assert(base <= capacity);
    if extra > 0 {
        assert(node_count * base < node_count * capacity);
        assert(base * node_count < capacity * node_count);
        lemma_mul_strict_inequality_converse(base, capacity, node_count);
        assert(base < capacity);
    }
}

impl BalancedPartition {
    pub open spec fn target_size(&self, index: int) -> int
        recommends 0 <= index < self.node_count as int
    {
        self.base as int + if index < self.extra as int { 1int } else { 0int }
    }

    pub open spec fn prefix_size(&self, count: int) -> int
        recommends 0 <= count <= self.node_count as int
    {
        count * self.base as int
            + if count <= self.extra as int {
                count
            } else {
                self.extra as int
            }
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.total > 0
        &&& self.capacity > 0
        &&& self.node_count > 0
        &&& self.base > 0
        &&& self.extra < self.node_count
        &&& self.emitted <= self.node_count
        &&& self.total as int
            == self.base as int * self.node_count as int
                + self.extra as int
        &&& self.base <= self.capacity
        &&& self.extra > 0 ==> self.base < self.capacity
        &&& self.total as int
            <= self.node_count as int * self.capacity as int
        &&& self.node_count as nat
            == 1 + ((self.total as nat - 1) as nat)
                / (self.capacity as nat)
        &&& self.prefix_size(self.node_count as int) == self.total as int
    }

    pub fn new(total: usize, capacity: usize) -> (out: Option<Self>)
        ensures
            match out {
                Some(partition) => {
                    &&& total > 0
                    &&& capacity > 0
                    &&& partition.wf()
                    &&& partition.total == total
                    &&& partition.capacity == capacity
                    &&& partition.emitted == 0
                },
                None => total == 0 || capacity == 0,
            },
    {
        if total == 0 || capacity == 0 {
            return None;
        }
        proof {
            broadcast use group_div_basics;
            lemma_div_nonincreasing((total - 1) as int, capacity as int);
            assert(((total as nat - 1) as nat) / (capacity as nat)
                < usize::MAX as nat);
        }
        let prior = total - 1;
        let quotient = prior / capacity;
        let node_count = 1 + quotient;
        let base = total / node_count;
        let extra = total % node_count;
        let out = Self {
            total,
            capacity,
            node_count,
            base,
            extra,
            emitted: 0,
        };
        proof {
            broadcast use group_div_basics;
            lemma_div_nonincreasing(prior as int, capacity as int);
            lemma_fundamental_div_mod(prior as int, capacity as int);
            assert(quotient as int == prior as int / capacity as int);
            assert((prior % capacity) as int
                == prior as int % capacity as int);
            assert(prior as int
                == capacity as int * quotient as int
                    + (prior % capacity) as int);
            assert((prior % capacity) < capacity);
            assert(prior as nat + 1 == total as nat);
            assert(node_count as nat == quotient as nat + 1);
            assert(quotient as nat <= prior as nat);
            assert(total as int == prior as int + 1);
            assert(node_count as int == quotient as int + 1);
            assert(node_count > 0);
            assert(node_count as int <= total as int);
            assert(node_count as nat <= total as nat);
            lemma_fundamental_div_mod(total as int, node_count as int);
            assert(base as int == total as int / node_count as int);
            assert(extra as int == total as int % node_count as int);
            assert(total as int
                == node_count as int * base as int + extra as int);
            assert(extra < node_count);
            assert(node_count as nat
                == 1 + ((total as nat - 1) as nat) / (capacity as nat));
            assert(0 < (capacity as int));
            assert(total as int
                == capacity as int * quotient as int
                    + (prior % capacity) as int + 1);
            assert(node_count as int == quotient as int + 1);
            assert(0 <= (quotient as int));
            assert(0 <= ((prior % capacity) as int));
            assert(0 <= (extra as int));
            assert(0 <= (base as int));
            balanced_partition_arithmetic(
                total as int,
                capacity as int,
                node_count as int,
                base as int,
                extra as int,
                quotient as int,
                (prior % capacity) as int,
            );
            assert(base > 0);
            assert(base <= capacity);
            assert(extra > 0 ==> base < capacity);
            assert(out.prefix_size(node_count as int) == total as int) by {
                assert(node_count as int > extra as int);
            }
            assert(total as int
                == base as int * node_count as int + extra as int) by {
                lemma_mul_is_commutative(
                    node_count as int,
                    base as int,
                );
                assert(total as int
                    == node_count as int * base as int + extra as int);
            }
            assert(out.wf());
        }
        Some(out)
    }

    pub fn next_size(&mut self) -> (out: Option<usize>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self.total == old(self).total,
            self.capacity == old(self).capacity,
            self.node_count == old(self).node_count,
            self.base == old(self).base,
            self.extra == old(self).extra,
            match out {
                Some(size) => {
                    &&& old(self).emitted < old(self).node_count
                    &&& self.emitted == old(self).emitted + 1
                    &&& size as int
                        == old(self).target_size(old(self).emitted as int)
                    &&& 0 < size <= old(self).capacity
                    &&& old(self).prefix_size(old(self).emitted as int)
                        + size as int
                        == self.prefix_size(self.emitted as int)
                    &&& self.prefix_size(self.emitted as int)
                        <= self.total as int
                },
                None => {
                    &&& old(self).emitted == old(self).node_count
                    &&& *self == *old(self)
                },
            },
    {
        if self.emitted == self.node_count {
            return None;
        }
        proof {
            self.prefix_step();
        }
        proof {
            assert(self.emitted < usize::MAX);
        }
        let size = if self.emitted < self.extra {
            self.base + 1
        } else {
            self.base
        };
        self.emitted = self.emitted + 1;
        proof {
            assert(size > 0);
            assert(size <= self.capacity);
            assert(self.wf());
        }
        Some(size)
    }

    #[verifier::spinoff_prover]
    pub proof fn prefix_step(&self)
        requires
            self.wf(),
            self.emitted < self.node_count,
        ensures
            self.target_size(self.emitted as int) > 0,
            self.prefix_size(self.emitted as int)
                + self.target_size(self.emitted as int)
                == self.prefix_size(self.emitted as int + 1),
            self.prefix_size(self.emitted as int + 1)
                <= self.total as int,
    {
        broadcast use group_mul_properties;
        let emitted = self.emitted as int;
        let nodes = self.node_count as int;
        let base = self.base as int;
        let extra = self.extra as int;
        assert(0 <= emitted < nodes);
        assert(0 <= extra < nodes);
        assert(0 < base);
        if emitted < extra {
            assert(emitted + 1 <= extra);
        } else {
            assert(extra <= emitted);
        }
        assert(self.prefix_size(emitted)
            + self.target_size(emitted)
            == self.prefix_size(emitted + 1)) by (nonlinear_arith);
        lemma_mul_inequality(emitted + 1, nodes, base);
        if emitted + 1 <= extra {
            assert(self.prefix_size(emitted + 1)
                <= self.prefix_size(nodes));
        } else {
            assert(self.prefix_size(emitted + 1)
                <= self.prefix_size(nodes));
        }
    }

    pub fn complete(&self) -> (out: bool)
        requires self.wf()
        ensures out == (self.emitted == self.node_count)
    {
        self.emitted == self.node_count
    }
}

impl BranchChildDescriptor {
    pub open spec fn wf(&self) -> bool {
        &&& self.first_key.wf()
        &&& self.addr@.wf()
        &&& self.receipt@.wf()
        &&& self.receipt@.root == self.addr@
        &&& self.receipt@.first_key == self.first_key
    }
}

impl BranchSubtreeReceipt {
    pub open spec fn branch(&self) -> LinkedBranch<Summary> {
        LinkedBranch {
            root: self.root,
            disk_view: BranchDiskView { entries: self.nodes },
        }
    }

    pub open spec fn wf(&self) -> bool {
        let branch = self.branch();
        &&& self.root.wf()
        &&& branch.wf()
        &&& branch.valid_ranking(self.ranking)
        &&& self.ranking.dom() == self.nodes.dom()
        &&& self.ranking[self.root] == self.height
        &&& branch.reachable_addrs_using_ranking(self.ranking)
            == self.nodes.dom()
        &&& self.pivot == branch.i_internal(self.ranking)
        &&& self.pivot.wf()
        &&& self.pivot.all_keys().contains(self.first_key)
        &&& self.pivot.all_keys().contains(self.last_key)
        &&& forall |key: Key|
            #[trigger] self.pivot.all_keys().contains(key) ==> {
                &&& Key::lte(self.first_key, key)
                &&& Key::lte(key, self.last_key)
            }
    }

    pub proof fn finalize(&self)
        requires self.wf()
        ensures
            self.branch().inv(),
            self.branch().tight_disk_view(),
            self.branch().i().i().map == self.pivot.i().map,
    {
        let branch = self.branch();
        LinkedBranchRefinement::lemma_i_wf_implies_inv(
            branch,
            self.ranking,
        );
        assert(branch.inv_internal(self.ranking));
        assert(branch.acyclic()) by {
            assert(exists |ranking: Ranking|
                branch.valid_ranking(ranking)) by {
                assert(branch.valid_ranking(self.ranking));
            }
        }
        let canonical = branch.the_ranking();
        LinkedBranchRefinement::lemma_reachable_unchanged_implies_same_i_internal(
            branch,
            self.ranking,
            branch,
            canonical,
            Set::empty(),
        );
        assert(branch.i_internal(canonical) == self.pivot);
        LinkedBranchRefinement::lemma_i_wf_implies_inv(branch, canonical);
        assert(branch.inv());
        assert(branch.representation() == self.nodes.dom());
        assert(branch.tight_disk_view());
        assert(branch.i() == self.pivot);
    }
}

pub open spec fn descriptor_forest_nodes(
    descriptors: Seq<BranchChildDescriptor>,
) -> LoadedBranch
    decreases descriptors.len(),
{
    if descriptors.len() == 0 {
        Map::empty()
    } else {
        descriptor_forest_nodes(descriptors.drop_last())
            .union_prefer_right(descriptors.last().receipt@.nodes)
    }
}

pub open spec fn descriptor_forest_ranking(
    descriptors: Seq<BranchChildDescriptor>,
) -> Ranking
    decreases descriptors.len(),
{
    if descriptors.len() == 0 {
        Map::empty()
    } else {
        descriptor_forest_ranking(descriptors.drop_last())
            .union_prefer_right(descriptors.last().receipt@.ranking)
    }
}

pub open spec fn descriptor_pivot_children(
    descriptors: Seq<BranchChildDescriptor>,
) -> Seq<PivotNode> {
    descriptors.map(
        |i: int, descriptor: BranchChildDescriptor|
            descriptor.receipt@.pivot,
    )
}

pub open spec fn descriptor_pivots(
    descriptors: Seq<BranchChildDescriptor>,
) -> Seq<Key> {
    if descriptors.len() == 0 {
        Seq::empty()
    } else {
        descriptors.skip(1).map(
            |i: int, descriptor: BranchChildDescriptor|
                descriptor.first_key,
        )
    }
}

pub open spec fn descriptor_forest_contents(
    descriptors: Seq<BranchChildDescriptor>,
) -> Map<Key, Message>
    decreases descriptors.len(),
{
    if descriptors.len() == 0 {
        Map::empty()
    } else {
        descriptor_forest_contents(descriptors.drop_last())
            .union_prefer_right(descriptors.last().receipt@.pivot.i().map)
    }
}

pub open spec fn descriptor_forest_wf(
    descriptors: Seq<BranchChildDescriptor>,
) -> bool {
    &&& descriptors.len() > 0
    &&& descriptor_sequence_wf(descriptors)
}

pub open spec fn descriptor_sequence_wf(
    descriptors: Seq<BranchChildDescriptor>,
) -> bool {
    &&& forall |i: int| 0 <= i < descriptors.len()
        ==> (#[trigger] descriptors[i]).wf()
    &&& forall |i: int, j: int|
        #![trigger descriptors[i], descriptors[j]]
        0 <= i < j < descriptors.len() ==>
            descriptors[i].receipt@.nodes.dom().disjoint(
                descriptors[j].receipt@.nodes.dom(),
            )
    &&& forall |i: int, j: int|
        #![trigger descriptors[i], descriptors[j]]
        0 <= i < j < descriptors.len() ==>
            descriptors[i].receipt@.last_key.0
                < descriptors[j].first_key.0
    &&& forall |i: int, j: int|
        #![trigger descriptors[i], descriptors[j]]
        0 <= i < j < descriptors.len() ==>
            descriptors[i].receipt@.height
                == descriptors[j].receipt@.height
}

proof fn descriptor_forest_contains_iff(
    descriptors: Seq<BranchChildDescriptor>,
    addr: Address,
)
    ensures
        descriptor_forest_nodes(descriptors).contains_key(addr)
            <==> exists |i: int| 0 <= i < descriptors.len()
                && #[trigger] descriptors[i].receipt@.nodes
                    .contains_key(addr),
        descriptor_forest_ranking(descriptors).contains_key(addr)
            <==> exists |i: int| 0 <= i < descriptors.len()
                && #[trigger] descriptors[i].receipt@.ranking
                    .contains_key(addr),
    decreases descriptors.len(),
{
    if descriptors.len() > 0 {
        descriptor_forest_contains_iff(descriptors.drop_last(), addr);
        assert(descriptors.drop_last().len()
            == descriptors.len() - 1);


        assert(descriptor_forest_nodes(descriptors).contains_key(addr)
            <==> descriptor_forest_nodes(descriptors.drop_last())
                .contains_key(addr)
                || descriptors.last().receipt@.nodes.contains_key(addr));
        assert(descriptor_forest_ranking(descriptors).contains_key(addr)
            <==> descriptor_forest_ranking(descriptors.drop_last())
                .contains_key(addr)
                || descriptors.last().receipt@.ranking.contains_key(addr));
        assert(descriptor_forest_nodes(descriptors).contains_key(addr)
            <==> exists |i: int| 0 <= i < descriptors.len()
                && #[trigger] descriptors[i].receipt@.nodes
                    .contains_key(addr)) by {
            if descriptor_forest_nodes(descriptors).contains_key(addr) {
                if descriptors.last().receipt@.nodes.contains_key(addr) {
                    assert(exists |i: int| 0 <= i < descriptors.len()
                        && #[trigger] descriptors[i].receipt@.nodes
                            .contains_key(addr)) by {
                        let i = descriptors.len() - 1;
                        assert(descriptors[i] == descriptors.last());
                    }
                } else {
                    let i = choose |i: int|
                        0 <= i < descriptors.drop_last().len()
                        && #[trigger] descriptors.drop_last()[i]
                            .receipt@.nodes.contains_key(addr);
                    assert(descriptors.drop_last()[i] == descriptors[i]);
                }
            }
            if exists |i: int| 0 <= i < descriptors.len()
                && #[trigger] descriptors[i].receipt@.nodes
                    .contains_key(addr)
            {
                let i = choose |i: int| 0 <= i < descriptors.len()
                    && #[trigger] descriptors[i].receipt@.nodes
                        .contains_key(addr);
                if i == descriptors.len() - 1 {
                    assert(descriptors[i] == descriptors.last());
                } else {
                    assert(i < descriptors.drop_last().len());
                    assert(descriptors.drop_last()[i] == descriptors[i]);
                    assert(descriptor_forest_nodes(descriptors.drop_last())
                        .contains_key(addr));
                }
            }
        }
        assert(descriptor_forest_ranking(descriptors).contains_key(addr)
            <==> exists |i: int| 0 <= i < descriptors.len()
                && #[trigger] descriptors[i].receipt@.ranking
                    .contains_key(addr)) by {
            if descriptor_forest_ranking(descriptors).contains_key(addr) {
                if descriptors.last().receipt@.ranking.contains_key(addr) {
                    assert(exists |i: int| 0 <= i < descriptors.len()
                        && #[trigger] descriptors[i].receipt@.ranking
                            .contains_key(addr)) by {
                        let i = descriptors.len() - 1;
                        assert(descriptors[i] == descriptors.last());
                    }
                } else {
                    let i = choose |i: int|
                        0 <= i < descriptors.drop_last().len()
                        && #[trigger] descriptors.drop_last()[i]
                            .receipt@.ranking.contains_key(addr);
                    assert(descriptors.drop_last()[i] == descriptors[i]);
                }
            }
            if exists |i: int| 0 <= i < descriptors.len()
                && #[trigger] descriptors[i].receipt@.ranking
                    .contains_key(addr)
            {
                let i = choose |i: int| 0 <= i < descriptors.len()
                    && #[trigger] descriptors[i].receipt@.ranking
                        .contains_key(addr);
                if i == descriptors.len() - 1 {
                    assert(descriptors[i] == descriptors.last());
                } else {
                    assert(i < descriptors.drop_last().len());
                    assert(descriptors.drop_last()[i] == descriptors[i]);
                    assert(descriptor_forest_ranking(descriptors.drop_last())
                        .contains_key(addr));
                }
            }
        }
    }
}

proof fn descriptor_forest_contents_contains_iff(
    descriptors: Seq<BranchChildDescriptor>,
    key: Key,
)
    ensures
        descriptor_forest_contents(descriptors).contains_key(key)
            <==> exists |i: int| 0 <= i < descriptors.len()
                && #[trigger] descriptors[i].receipt@.pivot.i().map
                    .contains_key(key),
    decreases descriptors.len(),
{
    if descriptors.len() > 0 {
        descriptor_forest_contents_contains_iff(
            descriptors.drop_last(),
            key,
        );

        if descriptor_forest_contents(descriptors).contains_key(key) {
            if descriptors.last().receipt@.pivot.i().map
                .contains_key(key)
            {
                let i = descriptors.len() - 1;
                assert(descriptors[i] == descriptors.last());
            } else {
                let i = choose |i: int|
                    0 <= i < descriptors.drop_last().len()
                    && #[trigger] descriptors.drop_last()[i]
                        .receipt@.pivot.i().map.contains_key(key);
                assert(descriptors.drop_last()[i] == descriptors[i]);
            }
        }
        if exists |i: int| 0 <= i < descriptors.len()
            && #[trigger] descriptors[i].receipt@.pivot.i().map
                .contains_key(key)
        {
            let i = choose |i: int| 0 <= i < descriptors.len()
                && #[trigger] descriptors[i].receipt@.pivot.i().map
                    .contains_key(key);
            if i == descriptors.len() - 1 {
                assert(descriptors[i] == descriptors.last());
            } else {
                assert(descriptors.drop_last()[i] == descriptors[i]);
                assert(descriptor_forest_contents(descriptors.drop_last())
                    .contains_key(key));
            }
        }
    }
}

proof fn descriptor_forest_contents_value(
    descriptors: Seq<BranchChildDescriptor>,
    i: int,
    key: Key,
)
    requires
        descriptor_sequence_wf(descriptors),
        0 <= i < descriptors.len(),
        descriptors[i].receipt@.pivot.i().map.contains_key(key),
    ensures
        descriptor_forest_contents(descriptors).contains_key(key),
        descriptor_forest_contents(descriptors)[key]
            == descriptors[i].receipt@.pivot.i().map[key],
    decreases descriptors.len(),
{
    let last = descriptors.len() - 1;
    if i == last {

        assert(descriptors[i] == descriptors.last());
    } else {
        assert(descriptor_sequence_wf(descriptors.drop_last())) by {
            assert forall |x: int| 0 <= x < descriptors.drop_last().len()
                implies (#[trigger] descriptors.drop_last()[x]).wf() by {}
            assert forall |x: int, y: int|
                #![trigger descriptors.drop_last()[x],
                    descriptors.drop_last()[y]]
                0 <= x < y < descriptors.drop_last().len()
                implies descriptors.drop_last()[x].receipt@.nodes.dom()
                    .disjoint(
                        descriptors.drop_last()[y].receipt@.nodes.dom(),
                    ) by {}
            assert forall |x: int, y: int|
                #![trigger descriptors.drop_last()[x],
                    descriptors.drop_last()[y]]
                0 <= x < y < descriptors.drop_last().len()
                implies descriptors.drop_last()[x].receipt@.last_key.0
                    < descriptors.drop_last()[y].first_key.0 by {}
            assert forall |x: int, y: int|
                #![trigger descriptors.drop_last()[x],
                    descriptors.drop_last()[y]]
                0 <= x < y < descriptors.drop_last().len()
                implies descriptors.drop_last()[x].receipt@.height
                    == descriptors.drop_last()[y].receipt@.height by {}
        }
        assert(descriptors.drop_last()[i] == descriptors[i]);
        descriptor_forest_contents_value(
            descriptors.drop_last(),
            i,
            key,
        );
        PivotBranchRefinement::lemma_interpretation_subset_of_all_keys(
            descriptors[i].receipt@.pivot,
        );
        assert(Key::lte(
            key,
            descriptors[i].receipt@.last_key,
        ));
        assert(Key::lt(
            key,
            descriptors.last().first_key,
        )) by {


        }
        PivotBranchRefinement::lemma_interpretation_subset_of_all_keys(
            descriptors.last().receipt@.pivot,
        );
        assert(!descriptors.last().receipt@.pivot.i().map
            .contains_key(key)) by {
            if descriptors.last().receipt@.pivot.i().map
                .contains_key(key)
            {
                assert(Key::lte(descriptors.last().first_key, key));

                assert(false);
            }
        }

    }
}

proof fn descriptor_key_routes_to_child(
    descriptors: Seq<BranchChildDescriptor>,
    pivot: PivotNode,
    i: int,
    key: Key,
)
    requires
        descriptor_forest_wf(descriptors),
        pivot == (PivotNode::Index {
            pivots: descriptor_pivots(descriptors),
            children: descriptor_pivot_children(descriptors),
        }),
        pivot.wf(),
        0 <= i < descriptors.len(),
        descriptors[i].receipt@.pivot.i().map.contains_key(key),
    ensures
        pivot.route(key) + 1 == i,
{
    let pivots = descriptor_pivots(descriptors);
    PivotBranchRefinement::lemma_interpretation_subset_of_all_keys(
        descriptors[i].receipt@.pivot,
    );
    assert(descriptors[i].receipt@.pivot.all_keys().contains(key));
    assert(Key::lte(descriptors[i].first_key, key));
    assert(Key::lte(key, descriptors[i].receipt@.last_key));
    Key::strictly_sorted_implies_sorted(pivots);
    if i == 0 {
        if pivots.len() > 0 {
            assert(pivots[0] == descriptors[1].first_key);
            assert(descriptors[0].receipt@.last_key.0
                < descriptors[1].first_key.0);
            assert(Key::lt(key, pivots[0])) by {


            }
        }
        Key::largest_lte_is_lemma(pivots, key, -1);
    } else {
        assert(pivots[i - 1] == descriptors[i].first_key);
        if i < descriptors.len() - 1 {
            assert(pivots[i] == descriptors[i + 1].first_key);
            assert(descriptors[i].receipt@.last_key.0
                < descriptors[i + 1].first_key.0);
            assert(Key::lt(key, pivots[i])) by {


            }
        }
        assert(i - 1 == pivots.len() - 1
            || Key::lt(key, pivots[i]));
        Key::largest_lte_is_lemma(pivots, key, i - 1);
    }
    assert(pivot.route(key) == Key::largest_lte(pivots, key));
}

proof fn descriptor_parent_contents(
    descriptors: Seq<BranchChildDescriptor>,
    pivot: PivotNode,
)
    requires
        descriptor_forest_wf(descriptors),
        pivot == (PivotNode::Index {
            pivots: descriptor_pivots(descriptors),
            children: descriptor_pivot_children(descriptors),
        }),
        pivot.wf(),
    ensures
        pivot.i().map == descriptor_forest_contents(descriptors),
{
    PivotBranchRefinement::lemma_i_unfoldable(pivot);
    assert(pivot is Index);
    assert_maps_equal!(
        pivot.i().map,
        descriptor_forest_contents(descriptors),
        key => {
            if pivot.i().map.contains_key(key) {
                PivotBranchRefinement::lemma_index_i_routes(pivot, key);
                PivotBranchRefinement::lemma_i_contains_implies_routed_child_contains(
                    pivot,
                    key,
                );
                let i = pivot.route(key) + 1;
                assert(0 <= i < descriptors.len());
                assert(pivot->children[i]
                    == descriptors[i].receipt@.pivot);
                descriptor_forest_contents_value(descriptors, i, key);
                assert(pivot.i().map[key]
                    == pivot->children[pivot.route(key) + 1]
                        .i().map[key]);
                assert(pivot.route(key) + 1 == i);
                assert(pivot.i().map[key]
                    == pivot->children[i].i().map[key]);
            }
            if descriptor_forest_contents(descriptors)
                .contains_key(key)
            {
                descriptor_forest_contents_contains_iff(
                    descriptors,
                    key,
                );
                let i = choose |i: int| 0 <= i < descriptors.len()
                    && #[trigger] descriptors[i].receipt@.pivot.i().map
                        .contains_key(key);
                descriptor_key_routes_to_child(
                    descriptors,
                    pivot,
                    i,
                    key,
                );
                assert(pivot->children[i]
                    == descriptors[i].receipt@.pivot);
                assert(pivot.route(key) + 1 == i);
                PivotBranchRefinement::lemma_index_i_routes(pivot, key);
                assert(pivot.i().map.contains_key(key));
                descriptor_forest_contents_value(descriptors, i, key);
                assert(pivot.i().map[key]
                    == pivot->children[i].i().map[key]);
            }
        }
    );
}

proof fn message_map_union_prefer_right_assoc(
    left: Map<Key, Message>,
    middle: Map<Key, Message>,
    right: Map<Key, Message>,
)
    ensures
        left.union_prefer_right(middle).union_prefer_right(right)
            == left.union_prefer_right(
                middle.union_prefer_right(right),
            ),
{
    assert_maps_equal!(
        left.union_prefer_right(middle).union_prefer_right(right),
        left.union_prefer_right(middle.union_prefer_right(right)),
        key => {}
    );
}

proof fn descriptor_forest_contents_concat(
    left: Seq<BranchChildDescriptor>,
    right: Seq<BranchChildDescriptor>,
)
    ensures
        descriptor_forest_contents(left + right)
            == descriptor_forest_contents(left).union_prefer_right(
                descriptor_forest_contents(right),
            ),
    decreases right.len(),
{
    if right.len() == 0 {
        assert(left + right == left);

    } else {
        descriptor_forest_contents_concat(left, right.drop_last());
        assert((left + right).drop_last()
            == left + right.drop_last());
        assert((left + right).last() == right.last());

        message_map_union_prefer_right_assoc(
            descriptor_forest_contents(left),
            descriptor_forest_contents(right.drop_last()),
            right.last().receipt@.pivot.i().map,
        );
    }
}

proof fn descriptor_content_stage_preserves_total(
    input: Seq<BranchChildDescriptor>,
    old_output: Seq<BranchChildDescriptor>,
    descriptor: BranchChildDescriptor,
    start: int,
    count: int,
)
    requires
        0 <= start,
        0 < count,
        start + count <= input.len(),
        descriptor.receipt@.pivot.i().map
            == descriptor_forest_contents(
                input.subrange(start, start + count),
            ),
    ensures
        descriptor_forest_contents(old_output.push(descriptor))
            .union_prefer_right(descriptor_forest_contents(
                input.skip(start + count),
            ))
            == descriptor_forest_contents(old_output)
                .union_prefer_right(descriptor_forest_contents(
                    input.skip(start),
                )),
{
    let children = input.subrange(start, start + count);
    let tail = input.skip(start + count);
    assert(input.skip(start) == children + tail) by {
        assert_seqs_equal!(
            input.skip(start),
            children + tail,
            i => {
                if i < children.len() {
                    assert((children + tail)[i] == children[i]);
                } else {
                    assert((children + tail)[i]
                        == tail[i - children.len()]);
                }
            }
        );
    }
    descriptor_forest_contents_concat(children, tail);
    assert(old_output.push(descriptor).len() > 0);
    assert(old_output.push(descriptor).drop_last() == old_output);
    assert(old_output.push(descriptor).last() == descriptor);

    assert(descriptor_forest_contents(old_output.push(descriptor))
        == descriptor_forest_contents(old_output).union_prefer_right(
            descriptor.receipt@.pivot.i().map,
        ));
    message_map_union_prefer_right_assoc(
        descriptor_forest_contents(old_output),
        descriptor.receipt@.pivot.i().map,
        descriptor_forest_contents(tail),
    );
}

proof fn descriptor_forest_contains_receipt(
    descriptors: Seq<BranchChildDescriptor>,
    i: int,
)
    requires
        descriptor_forest_wf(descriptors),
        0 <= i < descriptors.len(),
    ensures
        descriptors[i].receipt@.nodes
            <= descriptor_forest_nodes(descriptors),
        descriptors[i].receipt@.ranking
            <= descriptor_forest_ranking(descriptors),
    decreases descriptors.len(),
{
    if descriptors.len() > 0 {
        let last = descriptors.len() - 1;
        if i < last {
            assert(descriptor_forest_wf(descriptors.drop_last())) by {
                assert(descriptor_sequence_wf(descriptors.drop_last())) by {
                assert forall |x: int| 0 <= x < descriptors.drop_last().len()
                    implies (#[trigger] descriptors.drop_last()[x]).wf() by {}
                assert forall |x: int, y: int|
                    0 <= x < y < descriptors.drop_last().len()
                    implies {
                        &&& descriptors.drop_last()[x].receipt@.nodes.dom()
                            .disjoint(
                                descriptors.drop_last()[y].receipt@.nodes.dom(),
                            )
                        &&& descriptors.drop_last()[x].receipt@.last_key.0
                            < descriptors.drop_last()[y].first_key.0
                        &&& descriptors.drop_last()[x].receipt@.height
                            == descriptors.drop_last()[y].receipt@.height
                    } by {}
                }
            }
            descriptor_forest_contains_receipt(
                descriptors.drop_last(),
                i,
            );
            assert(descriptors.drop_last()[i] == descriptors[i]);
            assert forall |addr: Address|
                #[trigger] descriptors[i].receipt@.nodes.contains_key(addr)
                implies descriptor_forest_nodes(descriptors)[addr]
                    == descriptors[i].receipt@.nodes[addr] by {
                assert(descriptor_forest_nodes(descriptors.drop_last())
                    .contains_key(addr));
                assert(!descriptors[last].receipt@.nodes
                    .contains_key(addr)) by {
                    assert(descriptors[i].receipt@.nodes.dom().disjoint(
                        descriptors[last].receipt@.nodes.dom(),
                    ));
                }
            }
            assert forall |addr: Address|
                #[trigger] descriptors[i].receipt@.ranking.contains_key(addr)
                implies descriptor_forest_ranking(descriptors)[addr]
                    == descriptors[i].receipt@.ranking[addr] by {
                assert(descriptor_forest_ranking(descriptors.drop_last())
                    .contains_key(addr));
                assert(!descriptors[last].receipt@.ranking
                    .contains_key(addr)) by {
                    assert(descriptors[i].receipt@.ranking.dom()
                        == descriptors[i].receipt@.nodes.dom());
                    assert(descriptors[last].receipt@.ranking.dom()
                        == descriptors[last].receipt@.nodes.dom());
                    assert(descriptors[i].receipt@.nodes.dom().disjoint(
                        descriptors[last].receipt@.nodes.dom(),
                    ));
                }
            }
        } else {
            assert(i == last);
        }
    }
}

proof fn descriptor_subrange_forest_wf(
    descriptors: Seq<BranchChildDescriptor>,
    start: int,
    end: int,
)
    requires
        descriptor_forest_wf(descriptors),
        0 <= start < end <= descriptors.len(),
    ensures
        descriptor_forest_wf(descriptors.subrange(start, end)),
{
    let sub = descriptors.subrange(start, end);
    assert(sub.len() > 0);
    assert(descriptor_sequence_wf(sub)) by {
        assert forall |i: int| 0 <= i < sub.len()
            implies (#[trigger] sub[i]).wf() by {}
        assert forall |i: int, j: int| 0 <= i < j < sub.len()
            implies {
                &&& #[trigger] sub[i].receipt@.nodes.dom().disjoint(
                    sub[j].receipt@.nodes.dom(),
                )
                &&& sub[i].receipt@.last_key.0 < sub[j].first_key.0
                &&& sub[i].receipt@.height == sub[j].receipt@.height
            } by {}
    }
}

proof fn descriptor_stage_partition(
    input: Seq<BranchChildDescriptor>,
    old_output: Seq<BranchChildDescriptor>,
    descriptor: BranchChildDescriptor,
    start: int,
    count: int,
    addr: Address,
    node: BranchNode,
    old_staged: LoadedBranch,
)
    requires
        descriptor_forest_wf(input),
        descriptor_sequence_wf(old_output),
        0 <= start,
        0 < count,
        start + count <= input.len(),
        descriptor.receipt@.nodes
            == descriptor_forest_nodes(input.subrange(
                start,
                start + count,
            )).insert(addr, node),
        !old_staged.contains_key(addr),
        descriptor_forest_nodes(input) <= old_staged,
        descriptor_forest_nodes(old_output) <= old_staged,
        descriptor_forest_nodes(old_output).dom()
            + descriptor_forest_nodes(input.skip(start)).dom()
            == old_staged.dom(),
    ensures
        descriptor_forest_nodes(old_output.push(descriptor))
            <= old_staged.insert(addr, node),
        descriptor_forest_nodes(input)
            <= old_staged.insert(addr, node),
        descriptor_forest_nodes(old_output.push(descriptor)).dom()
            + descriptor_forest_nodes(input.skip(start + count)).dom()
            == old_staged.insert(addr, node).dom(),
        start + count == input.len() ==>
            descriptor_forest_nodes(old_output.push(descriptor))
                == old_staged.insert(addr, node),
{
    let children = input.subrange(start, start + count);
    let new_output = old_output.push(descriptor);
    let new_staged = old_staged.insert(addr, node);
    assert(new_output.drop_last() == old_output);
    assert(new_output.last() == descriptor);

    descriptor_subrange_forest_wf(
        input,
        start,
        start + count,
    );
    assert(descriptor_forest_nodes(new_output)
        == descriptor_forest_nodes(old_output)
            .union_prefer_right(descriptor.receipt@.nodes));
    assert(descriptor.receipt@.nodes <= new_staged) by {
        assert forall |candidate: Address|
            #[trigger] descriptor.receipt@.nodes.contains_key(candidate)
            implies new_staged.contains_key(candidate)
                && descriptor.receipt@.nodes[candidate]
                    == new_staged[candidate] by {
            if candidate == addr {
            } else {
                assert(descriptor_forest_nodes(children)
                    .contains_key(candidate));
                descriptor_forest_contains_iff(children, candidate);
                let child_i = choose |child_i: int|
                    0 <= child_i < children.len()
                    && #[trigger] children[child_i].receipt@.nodes
                        .contains_key(candidate);
                let source_i = start + child_i;
                assert(input[source_i] == children[child_i]);
                descriptor_forest_contains_receipt(input, source_i);
                descriptor_forest_contains_receipt(children, child_i);
                assert(input[source_i].receipt@.nodes <= old_staged) by {
                    assert(input[source_i].receipt@.nodes
                        <= descriptor_forest_nodes(input));
                    vstd::map_lib::lemma_submap_of_trans(
                        input[source_i].receipt@.nodes,
                        descriptor_forest_nodes(input),
                        old_staged,
                    );
                }
                assert(descriptor_forest_nodes(children)[candidate]
                    == children[child_i].receipt@.nodes[candidate]);
                assert(old_staged.contains_pair(
                    candidate,
                    input[source_i].receipt@.nodes[candidate],
                ));
            }
        }
    }
    assert(descriptor_forest_nodes(new_output) <= new_staged) by {
        assert forall |candidate: Address|
            #[trigger] descriptor_forest_nodes(new_output)
                .contains_key(candidate)
            implies new_staged.contains_key(candidate)
                && descriptor_forest_nodes(new_output)[candidate]
                    == new_staged[candidate] by {
            if descriptor.receipt@.nodes.contains_key(candidate) {
            } else {
                assert(descriptor_forest_nodes(old_output)
                    .contains_key(candidate));
                assert(old_staged.contains_key(candidate));
                assert(descriptor_forest_nodes(old_output)[candidate]
                    == old_staged[candidate]);
            }
        }
    }
    assert(descriptor_forest_nodes(input) <= new_staged) by {
        assert forall |candidate: Address|
            #[trigger] descriptor_forest_nodes(input).contains_key(candidate)
            implies new_staged.contains_key(candidate)
                && descriptor_forest_nodes(input)[candidate]
                    == new_staged[candidate] by {
            assert(old_staged.contains_key(candidate));
        }
    }
    assert_sets_equal!(
        descriptor_forest_nodes(new_output).dom()
            + descriptor_forest_nodes(input.skip(start + count)).dom(),
        new_staged.dom(),
        candidate => {
            if descriptor_forest_nodes(new_output)
                .contains_key(candidate)
            {
                assert(new_staged.contains_key(candidate));
            }
            if descriptor_forest_nodes(input.skip(start + count))
                .contains_key(candidate)
            {
                descriptor_forest_contains_iff(
                    input.skip(start + count),
                    candidate,
                );
                let remaining_i = choose |remaining_i: int|
                    0 <= remaining_i < input.skip(start + count).len()
                    && #[trigger] input.skip(start + count)[remaining_i]
                        .receipt@.nodes.contains_key(candidate);
                let source_i = start + count + remaining_i;
                descriptor_forest_contains_receipt(input, source_i);
                assert(input[source_i]
                    == input.skip(start + count)[remaining_i]);
                assert(descriptor_forest_nodes(input)
                    .contains_key(candidate));
                assert(new_staged.contains_key(candidate));
            }
            if new_staged.contains_key(candidate) {
                if candidate == addr {
                    assert(descriptor.receipt@.nodes.contains_key(candidate));
                    assert(descriptor_forest_nodes(new_output)
                        .contains_key(candidate));
                } else {
                    assert(old_staged.contains_key(candidate));
                    if descriptor_forest_nodes(old_output)
                        .contains_key(candidate)
                    {
                        assert(descriptor_forest_nodes(new_output)
                            .contains_key(candidate));
                    } else {
                        assert(descriptor_forest_nodes(input.skip(start))
                            .contains_key(candidate));
                        descriptor_forest_contains_iff(
                            input.skip(start),
                            candidate,
                        );
                        let relative = choose |relative: int|
                            0 <= relative < input.skip(start).len()
                            && #[trigger] input.skip(start)[relative]
                                .receipt@.nodes.contains_key(candidate);
                        let source_i = start + relative;
                        if source_i < start + count {
                            let child_i = source_i - start;
                            assert(children[child_i] == input[source_i]);
                            descriptor_forest_contains_receipt(
                                children,
                                child_i,
                            );
                            assert(descriptor.receipt@.nodes
                                .contains_key(candidate));
                            assert(descriptor_forest_nodes(new_output)
                                .contains_key(candidate));
                        } else {
                            let remaining_i = source_i - (start + count);
                            assert(input.skip(start + count)[remaining_i]
                                == input[source_i]);
                            descriptor_subrange_forest_wf(
                                input,
                                start + count,
                                input.len() as int,
                            );
                            assert(descriptor_forest_nodes(
                                input.skip(start + count),
                            ).contains_key(candidate)) by {
                                descriptor_forest_contains_receipt(
                                    input.skip(start + count),
                                    remaining_i,
                                );
                            }
                        }
                    }
                }
            }
        }
    );
    if start + count == input.len() {
        assert(descriptor_forest_nodes(input.skip(start + count))
            == Map::<Address, BranchNode>::empty());
        assert(descriptor_forest_nodes(new_output).dom()
            == new_staged.dom());
        assert(descriptor_forest_nodes(new_output) == new_staged) by {
            assert_maps_equal!(
                descriptor_forest_nodes(new_output),
                new_staged,
                candidate => {}
            );
        }
    }
}

pub proof fn make_leaf_receipt(
    addr: Address,
    node: BranchNode,
) -> (receipt: BranchSubtreeReceipt)
    requires
        addr.wf(),
        node.wf(),
        node is Leaf,
        node.keys_strictly_sorted(),
    ensures
        receipt.wf(),
        receipt.root == addr,
        receipt.nodes == map![addr => node],
        receipt.first_key == node->keys.first(),
        receipt.last_key == node->keys.last(),
        receipt.height == 0,
        receipt.pivot == (PivotNode::Leaf {
            keys: node->keys,
            msgs: node->msgs,
        }),
{
    let nodes = map![addr => node];
    let ranking = map![addr => 0nat];
    let branch = LinkedBranch {
        root: addr,
        disk_view: BranchDiskView { entries: nodes },
    };
    let pivot = PivotNode::Leaf {
        keys: node->keys,
        msgs: node->msgs,
    };
    let receipt = BranchSubtreeReceipt {
        root: addr,
        nodes,
        ranking,
        pivot,
        first_key: node->keys.first(),
        last_key: node->keys.last(),
        height: 0,
    };
    assert(branch.disk_view.wf()) by {
        assert(branch.disk_view.entries_wf());
        assert(branch.disk_view.no_dangling_address()) by {
            assert forall |candidate: Address|
                #[trigger] branch.disk_view.entries.contains_key(candidate)
                implies branch.disk_view.node_has_valid_child_address(
                    branch.disk_view.entries[candidate],
                ) by {
                assert(candidate == addr);
                assert(branch.disk_view.entries[candidate] is Leaf);
            }
        }
    }
    assert(branch.wf());
    assert(branch.valid_ranking(ranking)) by {
        assert(branch.disk_view.valid_ranking(ranking)) by {
            assert forall |candidate: Address|
                #[trigger] ranking.contains_key(candidate)
                && branch.disk_view.entries.contains_key(candidate)
                implies branch.disk_view.node_children_respects_rank(
                    ranking,
                    candidate,
                ) by {
                assert(candidate == addr);
                assert(branch.disk_view.entries[candidate] is Leaf);
            }
        }
    }
    assert(branch.reachable_addrs_using_ranking(ranking)
        == set![addr]);
    assert(nodes.dom() == set![addr]);
    assert(branch.i_internal(ranking) == pivot);
    assert(pivot.wf());
    assert forall |key: Key|
        #[trigger] pivot.all_keys().contains(key)
        implies {
            &&& Key::lte(node->keys.first(), key)
            &&& Key::lte(key, node->keys.last())
        } by {
        assert(node->keys.contains(key));
        let idx = choose |i: int| 0 <= i < node->keys.len()
            && #[trigger] node->keys[i] == key;
        Key::strictly_sorted_implies_sorted(node->keys);
        if idx > 0 {
            assert(Key::lte(node->keys[0], node->keys[idx]));
        }
        if idx < node->keys.len() - 1 {
            assert(Key::lte(
                node->keys[idx],
                node->keys[node->keys.len() - 1],
            ));
        }
    }
    assert(pivot.all_keys().contains(node->keys.first()));
    assert(pivot.all_keys().contains(node->keys.last()));
    assert(receipt.wf());
    receipt
}

pub proof fn leaf_entries_contents(
    entries: Seq<MemtableEntry>,
    node: BranchNode,
)
    requires
        entries.len() > 0,
        MemtableBucket::unique_keys(entries),
        MemtableBucket::strictly_sorted(entries),
        node == (BranchNode::Leaf {
            keys: entries.map(
                |i: int, entry: MemtableEntry| entry.key,
            ),
            msgs: entries.map(
                |i: int, entry: MemtableEntry| entry.message,
            ),
        }),
    ensures
        (PivotNode::Leaf {
            keys: node->keys,
            msgs: node->msgs,
        }).i().map == MemtableBucket::entries_map(entries),
{
    let pivot = PivotNode::Leaf {
        keys: node->keys,
        msgs: node->msgs,
    };
    assert(pivot.wf()) by {
        assert(Key::is_strictly_sorted(pivot->keys)) by {
            assert forall |i: int, j: int|
                0 <= i < j < pivot->keys.len()
                implies Key::lt(pivot->keys[i], pivot->keys[j]) by {


            }
        }
    }
    assert_maps_equal!(
        pivot.i().map,
        MemtableBucket::entries_map(entries),
        key => {
            let present = pivot.contains(key);
            PivotBranchRefinement::contains_refines(pivot, key, present);
            if MemtableBucket::entries_map(entries).contains_key(key) {
                let i = MemtableBucket::entries_map_index_for_key(
                    entries,
                    key,
                );
                assert(pivot->keys[i] == key);
                assert(pivot.contains(key));
            }
            if pivot.i().map.contains_key(key) {
                assert(pivot.contains(key));
                assert(pivot->keys.contains(key));
                let i = pivot->keys.index_of(key);
                assert(0 <= i < entries.len());
                assert(entries[i].key == key);
                MemtableBucket::entries_map_index(entries, i);
                Key::largest_lte_is_lemma(pivot->keys, key, i);
                let msg = pivot.query(key);
                let lbl = PivotBranchRefinement::QueryLabel { key, msg };
                PivotBranchRefinement::query_refines(pivot, lbl);
                assert(pivot.i().query(key) == pivot.i().map[key]);
                assert(msg == pivot->msgs[i]);
                assert(pivot->msgs[i] == entries[i].message);
            }
        }
    );
}

pub proof fn make_index_receipt(
    descriptors: Seq<BranchChildDescriptor>,
    addr: Address,
    node: BranchNode,
) -> (receipt: BranchSubtreeReceipt)
    requires
        descriptor_forest_wf(descriptors),
        addr.wf(),
        !descriptor_forest_nodes(descriptors).contains_key(addr),
        node == (BranchNode::Index {
            pivots: descriptor_pivots(descriptors),
            children: descriptors.map(
                |i: int, descriptor: BranchChildDescriptor|
                    descriptor.addr@,
            ),
            aux_ptr: None,
        }),
    ensures
        receipt.wf(),
        receipt.root == addr,
        receipt.nodes == descriptor_forest_nodes(descriptors)
            .insert(addr, node),
        receipt.first_key == descriptors.first().first_key,
        receipt.last_key == descriptors.last().receipt@.last_key,
        receipt.height == descriptors.first().receipt@.height + 1,
        receipt.pivot == (PivotNode::Index {
            pivots: descriptor_pivots(descriptors),
            children: descriptor_pivot_children(descriptors),
        }),
        receipt.pivot.i().map
            == descriptor_forest_contents(descriptors),
{
    let forest_nodes = descriptor_forest_nodes(descriptors);
    let forest_ranking = descriptor_forest_ranking(descriptors);
    let nodes = forest_nodes.insert(addr, node);
    let height = descriptors.first().receipt@.height + 1;
    let ranking = forest_ranking.insert(addr, height);
    let pivot = PivotNode::Index {
        pivots: descriptor_pivots(descriptors),
        children: descriptor_pivot_children(descriptors),
    };
    let branch = LinkedBranch {
        root: addr,
        disk_view: BranchDiskView { entries: nodes },
    };
    let receipt = BranchSubtreeReceipt {
        root: addr,
        nodes,
        ranking,
        pivot,
        first_key: descriptors.first().first_key,
        last_key: descriptors.last().receipt@.last_key,
        height,
    };

    assert(descriptor_pivots(descriptors).len()
        == descriptors.len() - 1);
    assert(descriptor_pivot_children(descriptors).len()
        == descriptors.len());
    assert(node.wf());
    assert(branch.disk_view.entries_wf()) by {
        assert forall |candidate: Address|
            #[trigger] nodes.contains_key(candidate)
            implies nodes[candidate].wf() by {
            if candidate == addr {
                assert(nodes[candidate] == node);
            } else {
                assert(forest_nodes.contains_key(candidate));
                descriptor_forest_contains_iff(descriptors, candidate);
                let i = choose |i: int| 0 <= i < descriptors.len()
                    && #[trigger] descriptors[i].receipt@.nodes
                        .contains_key(candidate);
                descriptor_forest_contains_receipt(descriptors, i);
                assert(nodes[candidate]
                    == descriptors[i].receipt@.nodes[candidate]);
            }
        }
    }
    assert(branch.disk_view.no_dangling_address()) by {
        assert forall |candidate: Address|
            #[trigger] nodes.contains_key(candidate)
            implies branch.disk_view.node_has_valid_child_address(
                nodes[candidate],
            ) by {
            if candidate == addr {
                assert forall |child_idx: int|
                    0 <= child_idx < node->children.len()
                    implies nodes.contains_key(
                        #[trigger] node->children[child_idx],
                    ) && !(nodes[node->children[child_idx]] is Auxiliary) by {
                    let child_addr = descriptors[child_idx].addr@;
                    assert(node->children[child_idx] == child_addr);
                    assert(descriptors[child_idx].receipt@.nodes
                        .contains_key(child_addr));
                    descriptor_forest_contains_receipt(
                        descriptors,
                        child_idx,
                    );
                    assert(forest_nodes.contains_key(child_addr));
                    assert(nodes[child_addr]
                        == descriptors[child_idx].receipt@.nodes[child_addr]);
                    assert(!(descriptors[child_idx].receipt@.nodes[child_addr]
                        is Auxiliary));
                }
            } else {
                descriptor_forest_contains_iff(descriptors, candidate);
                let i = choose |i: int| 0 <= i < descriptors.len()
                    && #[trigger] descriptors[i].receipt@.nodes
                        .contains_key(candidate);
                descriptor_forest_contains_receipt(descriptors, i);
                let child_branch = descriptors[i].receipt@.branch();
                assert(child_branch.disk_view.node_has_valid_child_address(
                    child_branch.disk_view.entries[candidate],
                ));
                assert forall |child_idx: int|
                    #[trigger] child_branch.disk_view.entries[candidate]
                        .valid_child_index(child_idx)
                    implies nodes.contains_key(#[trigger]
                        child_branch.disk_view.entries[candidate]
                            .arrow_Index_children()[child_idx]) by {
                    let child_addr = child_branch.disk_view.entries[candidate]
                        .arrow_Index_children()[child_idx];
                    assert(child_branch.disk_view.valid_address(child_addr));
                    assert(descriptors[i].receipt@.nodes
                        .contains_key(child_addr));
                    assert(forest_nodes.contains_key(child_addr));
                }
            }
        }
    }
    assert(branch.disk_view.wf());
    assert(branch.wf());

    assert(ranking.dom() == nodes.dom()) by {
        assert(forest_ranking.dom() == forest_nodes.dom()) by {
            assert_sets_equal!(
                forest_ranking.dom(),
                forest_nodes.dom(),
                candidate => {
                    descriptor_forest_contains_iff(
                        descriptors,
                        candidate,
                    );
                    if forest_ranking.contains_key(candidate) {
                        let i = choose |i: int| 0 <= i < descriptors.len()
                            && #[trigger] descriptors[i].receipt@.ranking
                                .contains_key(candidate);
                        assert(descriptors[i].receipt@.ranking.dom()
                            == descriptors[i].receipt@.nodes.dom());
                    }
                    if forest_nodes.contains_key(candidate) {
                        let i = choose |i: int| 0 <= i < descriptors.len()
                            && #[trigger] descriptors[i].receipt@.nodes
                                .contains_key(candidate);
                        assert(descriptors[i].receipt@.ranking.dom()
                            == descriptors[i].receipt@.nodes.dom());
                    }
                }
            );
        }
        assert_maps_equal!(
            ranking,
            ranking,
            candidate => {}
        );
    }
    assert(branch.disk_view.valid_ranking(ranking)) by {
        assert forall |candidate: Address|
            #[trigger] ranking.contains_key(candidate)
            && nodes.contains_key(candidate)
            implies branch.disk_view.node_children_respects_rank(
                ranking,
                candidate,
            ) by {
            if candidate == addr {
                assert forall |child_idx: int|
                    #[trigger] node.valid_child_index(child_idx)
                    implies {
                        &&& ranking.contains_key(node->children[child_idx])
                        &&& ranking[node->children[child_idx]]
                            < ranking[addr]
                    } by {
                    let child_addr = descriptors[child_idx].addr@;
                    descriptor_forest_contains_receipt(
                        descriptors,
                        child_idx,
                    );
                    assert(forest_ranking[child_addr]
                        == descriptors[child_idx].receipt@.ranking[child_addr]);
                    assert(descriptors[child_idx].receipt@.ranking[child_addr]
                        == descriptors[child_idx].receipt@.height);
                    if child_idx > 0 {
                        assert(descriptors[0].receipt@.nodes.dom().disjoint(
                            descriptors[child_idx].receipt@.nodes.dom(),
                        ));
                        assert(descriptors[child_idx].receipt@.height
                            == descriptors[0].receipt@.height);
                    }
                }
            } else {
                descriptor_forest_contains_iff(descriptors, candidate);
                let i = choose |i: int| 0 <= i < descriptors.len()
                    && #[trigger] descriptors[i].receipt@.ranking
                        .contains_key(candidate);
                descriptor_forest_contains_receipt(descriptors, i);
                assert(nodes[candidate]
                    == descriptors[i].receipt@.nodes[candidate]);
                assert forall |child_idx: int|
                    #[trigger] nodes[candidate].valid_child_index(child_idx)
                    implies {
                        &&& ranking.contains_key(
                            nodes[candidate]->children[child_idx],
                        )
                        &&& ranking[nodes[candidate]->children[child_idx]]
                            < ranking[candidate]
                    } by {
                    let child_addr = nodes[candidate]->children[child_idx];
                    assert(descriptors[i].receipt@.ranking
                        .contains_key(child_addr));
                    assert(descriptors[i].receipt@.ranking[child_addr]
                        < descriptors[i].receipt@.ranking[candidate]);
                    assert(forest_ranking[child_addr]
                        == descriptors[i].receipt@.ranking[child_addr]);
                    assert(forest_ranking[candidate]
                        == descriptors[i].receipt@.ranking[candidate]);
                }
            }
        }
    }
    assert(branch.valid_ranking(ranking));

    assert forall |i: int| 0 <= i < descriptors.len()
        implies branch.child_at_idx(i).i_internal(ranking)
            == descriptors[i].receipt@.pivot
            && branch.child_at_idx(i)
                .reachable_addrs_using_ranking(ranking)
                == descriptors[i].receipt@.nodes.dom() by {
        let small = descriptors[i].receipt@.branch();
        let big = branch.child_at_idx(i);
        let except = nodes.dom() - descriptors[i].receipt@.nodes.dom();
        descriptor_forest_contains_receipt(descriptors, i);
        assert(small.disk_view.same_except(big.disk_view, except)) by {
            assert_maps_equal!(
                small.disk_view.entries.remove_keys(except),
                big.disk_view.entries.remove_keys(except),
                candidate => {}
            );
        }
        assert(small.reachable_addrs_using_ranking(
            descriptors[i].receipt@.ranking,
        ).disjoint(except));
        LinkedBranchRefinement::lemma_reachable_unchanged_implies_same_i_internal(
            small,
            descriptors[i].receipt@.ranking,
            big,
            ranking,
            except,
        );
    }
    assert(branch.i_internal(ranking) == pivot) by {
        assert(branch.i_internal(ranking)->children
            =~= descriptor_pivot_children(descriptors));
    }
    assert(branch.reachable_addrs_using_ranking(ranking)
        == nodes.dom()) by {
        let child_sets = descriptors.map(
                |i: int, descriptor: BranchChildDescriptor|
                    descriptor.receipt@.nodes.dom(),
            );
        assert(branch.children_reachable_addrs_using_ranking(ranking)
            =~= child_sets);
        assert_sets_equal!(
            branch.reachable_addrs_using_ranking(ranking),
            nodes.dom(),
            candidate => {
                if branch.reachable_addrs_using_ranking(ranking)
                    .contains(candidate)
                    && candidate != addr
                {
                    assert(union_seq_of_sets(child_sets).contains(candidate));
                    lemma_union_seq_of_sets_contains(child_sets, candidate);
                    let i = choose |i: int| 0 <= i < child_sets.len()
                        && #[trigger] child_sets[i].contains(candidate);
                    descriptor_forest_contains_receipt(descriptors, i);
                    assert(forest_nodes.contains_key(candidate));
                }
                if nodes.contains_key(candidate) && candidate != addr {
                    assert(forest_nodes.contains_key(candidate));
                    descriptor_forest_contains_iff(
                        descriptors,
                        candidate,
                    );
                    let i = choose |i: int| 0 <= i < descriptors.len()
                        && #[trigger] descriptors[i].receipt@.nodes
                            .contains_key(candidate);
                    assert(child_sets[i].contains(candidate));
                    lemma_set_subset_of_union_seq_of_sets(
                        child_sets,
                        candidate,
                    );
                }
            }
        );
    }

    assert(pivot.wf()) by {
        assert forall |i: int| 0 <= i < pivot->children.len()
            implies (#[trigger] pivot->children[i]).wf() by {
            assert(pivot->children[i]
                == descriptors[i].receipt@.pivot);
        }
        assert(Key::is_strictly_sorted(pivot->pivots)) by {
            assert forall |i: int, j: int|
                0 <= i < j < pivot->pivots.len()
                implies Key::lt(pivot->pivots[i], pivot->pivots[j]) by {


                assert(descriptors[i + 1].receipt@.nodes.dom().disjoint(
                    descriptors[j + 1].receipt@.nodes.dom(),
                ));
                assert(Key::lte(
                    descriptors[i + 1].first_key,
                    descriptors[i + 1].receipt@.last_key,
                ));
                assert(descriptors[i + 1].first_key.0
                    < descriptors[j + 1].first_key.0);
            }
        }
        assert forall |i: int| 0 <= i < pivot->children.len() - 1
            implies pivot.all_keys_below_bound(i) by {
            assert forall |key: Key|
                pivot->children[i].all_keys().contains(key)
                implies #[trigger] Key::lt(key, pivot->pivots[i]) by {
                assert(Key::lte(
                    key,
                    descriptors[i].receipt@.last_key,
                ));
                assert(descriptors[i].receipt@.nodes.dom().disjoint(
                    descriptors[i + 1].receipt@.nodes.dom(),
                ));
                assert(descriptors[i].receipt@.last_key.0
                    < descriptors[i + 1].first_key.0);


            }
        }
        assert forall |i: int| 0 < i < pivot->children.len()
            implies pivot.all_keys_above_bound(i) by {
            assert forall |key: Key|
                pivot->children[i].all_keys().contains(key)
                implies #[trigger] Key::lte(pivot->pivots[i - 1], key) by {
                assert(pivot->pivots[i - 1]
                    == descriptors[i].first_key);
            }
        }
    }
    assert(pivot.all_keys().contains(
        descriptors.first().first_key,
    )) by {
        assert(pivot->children[0].all_keys().contains(
            descriptors.first().first_key,
        ));
        assert(pivot.children_keys().contains(
            descriptors.first().first_key,
        ));
    }
    assert(pivot.all_keys().contains(
        descriptors.last().receipt@.last_key,
    )) by {
        let last = descriptors.len() - 1;
        assert(pivot->children[last].all_keys().contains(
            descriptors.last().receipt@.last_key,
        ));
        assert(pivot.children_keys().contains(
            descriptors.last().receipt@.last_key,
        ));
    }
    assert forall |key: Key|
        #[trigger] pivot.all_keys().contains(key)
        implies {
            &&& Key::lte(descriptors.first().first_key, key)
            &&& Key::lte(key, descriptors.last().receipt@.last_key)
        } by {
        if pivot->pivots.to_set().contains(key) {
            let i = choose |i: int| 0 <= i < pivot->pivots.len()
                && #[trigger] pivot->pivots[i] == key;
            assert(key == descriptors[i + 1].first_key);
            if i + 1 > 0 {
                assert(descriptors[0].receipt@.nodes.dom().disjoint(
                    descriptors[i + 1].receipt@.nodes.dom(),
                ));
                assert(Key::lte(
                    descriptors[0].first_key,
                    descriptors[0].receipt@.last_key,
                ));
            }
            if i + 1 < descriptors.len() - 1 {
                assert(descriptors[i + 1].receipt@.nodes.dom().disjoint(
                    descriptors.last().receipt@.nodes.dom(),
                ));
            }
            assert(Key::lte(descriptors.first().first_key, key)) by {

            }
            assert(Key::lte(
                key,
                descriptors.last().receipt@.last_key,
            )) by {

            }
        } else {
            assert(pivot.children_keys().contains(key));
            let i = choose |i: int| 0 <= i < pivot->children.len()
                && (#[trigger] pivot->children[i]).all_keys()
                    .contains(key);
            assert(Key::lte(descriptors[i].first_key, key));
            assert(Key::lte(key, descriptors[i].receipt@.last_key));
            if i > 0 {
                assert(descriptors[0].receipt@.nodes.dom().disjoint(
                    descriptors[i].receipt@.nodes.dom(),
                ));
                assert(descriptors[0].receipt@.last_key.0
                    < descriptors[i].first_key.0);
            }
            if i < descriptors.len() - 1 {
                assert(descriptors[i].receipt@.nodes.dom().disjoint(
                    descriptors.last().receipt@.nodes.dom(),
                ));
                assert(descriptors[i].receipt@.last_key.0
                    < descriptors.last().first_key.0);
            }

        }
    }
    descriptor_parent_contents(descriptors, pivot);
    assert(receipt.wf());
    receipt
}

pub proof fn finalize_leaf_seal(
    receipt: BranchSubtreeReceipt,
) -> (branch: LinkedBranch<Summary>)
    requires
        receipt.wf(),
        receipt.nodes[receipt.root] is Leaf,
    ensures
        branch == receipt.branch(),
        branch.valid_sealed_branch(),
        branch.tight_disk_view_with_summary(),
        branch.get_summary() == set![receipt.root.au],
        branch.i().i().map == receipt.pivot.i().map,
{
    let branch = receipt.branch();
    receipt.finalize();
    assert(branch.root() is Leaf);
    assert(branch.sealed_root());
    assert(branch.full_repr() == branch.representation());
    assert(branch.get_summary() == set![receipt.root.au]);
    assert(addrs_closed(branch.full_repr(), branch.get_summary())) by {
        assert forall |addr: Address|
            #[trigger] branch.full_repr().contains(addr)
            implies branch.get_summary().contains(addr.au) by {
            assert(branch.representation() == receipt.nodes.dom());
            assert(receipt.nodes == map![receipt.root => receipt.nodes[receipt.root]]);
            assert(addr == receipt.root);
        }
    }
    assert(restrict_domain_au(
        branch.disk_view.entries,
        branch.get_summary(),
    ) == branch.full_repr()) by {
        assert_sets_equal!(
            restrict_domain_au(
                branch.disk_view.entries,
                branch.get_summary(),
            ),
            branch.full_repr(),
            addr => {}
        );
    }
    assert(branch.valid_sealed_branch());
    assert(branch.tight_disk_view_with_summary());
    branch
}

pub proof fn finalize_index_seal(
    receipt: BranchSubtreeReceipt,
    aux: Address,
    summary: Summary,
) -> (post: LinkedBranch<Summary>)
    requires
        receipt.wf(),
        receipt.nodes[receipt.root] is Index,
        receipt.nodes[receipt.root]->aux_ptr is None,
        aux.wf(),
        !receipt.nodes.contains_key(aux),
        addrs_closed(receipt.nodes.dom().insert(aux), summary),
    ensures
        post == receipt.branch().seal(aux, summary),
        post.valid_sealed_branch(),
        post.tight_disk_view_with_summary(),
        post.get_summary() == summary,
        post.i().i().map == receipt.pivot.i().map,
        post.disk_view.entries == receipt.nodes
            .insert(receipt.root, BranchNode::Index {
                pivots: receipt.nodes[receipt.root]->pivots,
                children: receipt.nodes[receipt.root]->children,
                aux_ptr: Some(aux),
            })
            .insert(aux, BranchNode::Auxiliary(summary)),
{
    let pre = receipt.branch();
    let post = pre.seal(aux, summary);
    let ranking = receipt.ranking;
    let except = set![receipt.root] + set![aux];
    receipt.finalize();

    assert(post.disk_view.entries == receipt.nodes
        .insert(receipt.root, BranchNode::Index {
            pivots: receipt.nodes[receipt.root]->pivots,
            children: receipt.nodes[receipt.root]->children,
            aux_ptr: Some(aux),
        })
        .insert(aux, BranchNode::Auxiliary(summary)));
    assert(post.disk_view.entries_wf()) by {
        assert forall |addr: Address|
            #[trigger] post.disk_view.entries.contains_key(addr)
            implies post.disk_view.entries[addr].wf() by {
            if addr == aux {
                assert(post.disk_view.entries[addr]
                    == BranchNode::Auxiliary(summary));
            } else if addr == receipt.root {
                assert(post.disk_view.entries[addr] is Index);
            } else {
                assert(receipt.nodes.contains_key(addr));
            }
        }
    }
    assert(post.disk_view.no_dangling_address()) by {
        assert forall |addr: Address|
            #[trigger] post.disk_view.entries.contains_key(addr)
            implies post.disk_view.node_has_valid_child_address(
                post.disk_view.entries[addr],
            ) by {
            if addr == aux {
                assert(post.disk_view.entries[addr] is Auxiliary);
            } else if addr == receipt.root {
                assert forall |i: int|
                    #[trigger] post.disk_view.entries[addr]
                        .valid_child_index(i)
                    implies post.disk_view.entries.contains_key(
                        post.disk_view.entries[addr]->children[i],
                    ) && !(post.disk_view.entries[
                        post.disk_view.entries[addr]->children[i]
                    ] is Auxiliary) by {
                    assert(pre.root().valid_child_index(i));
                    assert(pre.disk_view.node_has_valid_child_address(
                        pre.root(),
                    ));
                    assert(pre.disk_view.entries.contains_key(
                        pre.root()->children[i],
                    ));
                }
            } else {
                assert(receipt.nodes.contains_key(addr));
                assert(pre.disk_view.node_has_valid_child_address(
                    pre.disk_view.entries[addr],
                ));
                assert forall |i: int|
                    #[trigger] post.disk_view.entries[addr]
                        .valid_child_index(i)
                    implies post.disk_view.entries.contains_key(
                        post.disk_view.entries[addr]->children[i],
                    ) && !(post.disk_view.entries[
                        post.disk_view.entries[addr]->children[i]
                    ] is Auxiliary) by {
                    assert(post.disk_view.entries[addr]
                        == pre.disk_view.entries[addr]);
                    assert(pre.disk_view.entries.contains_key(
                        pre.disk_view.entries[addr]->children[i],
                    ));
                }
            }
        }
    }
    assert(post.disk_view.wf());
    assert(post.wf());
    assert(post.valid_ranking(ranking)) by {
        assert forall |addr: Address|
            #[trigger] ranking.contains_key(addr)
            && post.disk_view.entries.contains_key(addr)
            implies post.disk_view.node_children_respects_rank(
                ranking,
                addr,
            ) by {
            if addr == receipt.root {
                assert(post.root()->children == pre.root()->children);
                assert(pre.disk_view.node_children_respects_rank(
                    ranking,
                    addr,
                ));
                assert forall |i: int|
                    #[trigger] post.root().valid_child_index(i)
                    implies {
                        &&& ranking.contains_key(post.root()->children[i])
                        &&& ranking[post.root()->children[i]]
                            < ranking[addr]
                    } by {
                    assert(pre.root().valid_child_index(i));
                }
            } else {
                assert(addr != aux) by {
                    assert(!ranking.contains_key(aux));
                }
                assert(post.disk_view.entries[addr]
                    == pre.disk_view.entries[addr]);
                assert(pre.disk_view.node_children_respects_rank(
                    ranking,
                    addr,
                ));
                assert forall |i: int|
                    #[trigger] post.disk_view.entries[addr]
                        .valid_child_index(i)
                    implies {
                        &&& ranking.contains_key(
                            post.disk_view.entries[addr]->children[i],
                        )
                        &&& ranking[
                            post.disk_view.entries[addr]->children[i]
                        ] < ranking[addr]
                    } by {
                }
            }
        }
    }
    assert(post.acyclic()) by {
        assert(exists |candidate: Ranking|
            post.valid_ranking(candidate)) by {
            assert(post.valid_ranking(ranking));
        }
    }
    assert(post.disk_view.entries.remove_keys(except)
        == pre.disk_view.entries.remove_keys(except));
    assert forall |i: int| #[trigger] post.root().valid_child_index(i)
        implies pre.root().valid_child_index(i) by {
    }
    assert forall |i: int| 0 <= i < post.root()->children.len()
        implies {
            &&& post.child_at_idx(i).i_internal(ranking)
                == pre.child_at_idx(i).i_internal(ranking)
            &&& post.child_at_idx(i)
                    .reachable_addrs_using_ranking(ranking)
                == pre.child_at_idx(i)
                    .reachable_addrs_using_ranking(ranking)
        } by {
        let pre_child = pre.child_at_idx(i);
        let post_child = post.child_at_idx(i);
        assert(pre_child.reachable_addrs_using_ranking(ranking)
            .disjoint(except)) by {
            if pre_child.reachable_addrs_using_ranking(ranking)
                .contains(receipt.root)
            {
                let child_sets = pre.children_reachable_addrs_using_ranking(
                    ranking,
                );
                assert(child_sets[i].contains(receipt.root));
                lemma_set_subset_of_union_seq_of_sets(
                    child_sets,
                    receipt.root,
                );
                LinkedBranchRefinement::lemma_reachable_child_has_smaller_rank(
                    pre,
                    ranking,
                    receipt.root,
                );
                assert(false);
            }
            if pre_child.reachable_addrs_using_ranking(ranking)
                .contains(aux)
            {
                LinkedBranchRefinement::lemma_reachable_implies_valid_address(
                    pre_child,
                    ranking,
                    aux,
                );
            }
        }
        LinkedBranchRefinement::lemma_reachable_unchanged_implies_same_i_internal(
            pre_child,
            ranking,
            post_child,
            ranking,
            except,
        );
    }
    assert(post.i_internal(ranking) == receipt.pivot) by {
        assert(post.i_internal(ranking)->children
            =~= receipt.pivot->children);
    }
    LinkedBranchRefinement::lemma_i_wf_implies_inv(post, ranking);
    assert(post.inv_internal(ranking));
    assert(post.acyclic());
    let canonical = post.the_ranking();
    LinkedBranchRefinement::lemma_reachable_unchanged_implies_same_i_internal(
        post,
        ranking,
        post,
        canonical,
        Set::empty(),
    );
    LinkedBranchRefinement::lemma_i_wf_implies_inv(post, canonical);
    assert(post.inv());
    assert(post.representation() == pre.representation()) by {
        assert(post.children_reachable_addrs_using_ranking(ranking)
            =~= pre.children_reachable_addrs_using_ranking(ranking));
    }
    assert(post.sealed_root());
    assert(post.get_summary() == summary);
    assert(post.full_repr() == post.representation().insert(aux));
    assert(post.disk_view.entries.dom()
        == receipt.nodes.dom().insert(aux));
    assert(post.tight_disk_view_with_summary());
    assert(addrs_closed(post.full_repr(), post.get_summary())) by {
        assert(post.full_repr() == receipt.nodes.dom().insert(aux));
    }
    assert(restrict_domain_au(
        post.disk_view.entries,
        post.get_summary(),
    ) == post.full_repr()) by {
        assert_sets_equal!(
            restrict_domain_au(
                post.disk_view.entries,
                post.get_summary(),
            ),
            post.full_repr(),
            addr => {}
        );
    }
    assert(post.valid_sealed_branch());
    assert(post.i() == receipt.pivot);
    post
}

fn collect_sorted_entries(
    cursor: &mut MemtableSortedCursor,
    memtable: &MemtableImpl,
    count: usize,
) -> (out: Vec<MemtableEntry>)
    requires
        old(cursor).wf(memtable),
        count > 0,
        count as nat <= old(cursor).count(memtable),
    ensures
        cursor.wf(memtable),
        out@.len() == count,
        MemtableBucket::unique_keys(out@),
        MemtableBucket::strictly_sorted(out@),
        cursor.count(memtable) + count
            == old(cursor).count(memtable),
        MemtableBucket::entries_map(out@).dom().disjoint(cursor@.dom()),
        MemtableBucket::entries_map(out@).union_prefer_right(cursor@)
            == old(cursor)@,
        forall |i: int| 0 <= i < out@.len() ==> {
            &&& old(cursor)@.contains_key(#[trigger] out@[i].key)
            &&& old(cursor)@[out@[i].key] == out@[i].message
        },
        forall |i: int, key: Key|
            0 <= i < out@.len()
            && cursor@.contains_key(key)
            ==> out@[i].key.0 < key.0,
{
    let ghost original = cursor@;
    let ghost original_count = cursor.count(memtable);
    let mut out = Vec::new();
    let mut index = 0usize;
    while index < count
        invariant
            cursor.wf(memtable),
            index <= count,
            count as nat - index as nat <= cursor.count(memtable),
            cursor.count(memtable) + index as nat == original_count,
            out@.len() == index,
            MemtableBucket::unique_keys(out@),
            MemtableBucket::strictly_sorted(out@),
            forall |i: int| 0 <= i < out@.len() ==> {
                &&& original.contains_key(#[trigger] out@[i].key)
                &&& original[out@[i].key] == out@[i].message
            },
            cursor@ <= original,
            MemtableBucket::entries_map(out@).dom()
                .disjoint(cursor@.dom()),
            MemtableBucket::entries_map(out@)
                .union_prefer_right(cursor@) == original,
            forall |i: int, key: Key|
                0 <= i < out@.len()
                && cursor@.contains_key(key)
                ==> out@[i].key.0 < key.0,
        decreases count - index,
    {
        let ghost before = cursor@;
        let ghost old_out = out@;
        let next = cursor.next(memtable);
        let entry_ref = match next {
            Some(entry) => entry,
            None => {
                proof { assert(false); }
                return out;
            },
        };
        let entry = *entry_ref;
        proof {
            assert(before.contains_key(entry.key));
            assert(before[entry.key] == entry.message);
            if out@.len() > 0 {
                assert(out@[out@.len() - 1].key.0 < entry.key.0);
            }
        }
        out.push(entry);
        proof {
            assert(!MemtableBucket::entries_map(old_out)
                .contains_key(entry.key)) by {
                if MemtableBucket::entries_map(old_out)
                    .contains_key(entry.key)
                {
                    assert(before.contains_key(entry.key));
                    assert(false);
                }
            }
            MemtableBucket::entries_map_after_push(old_out, entry);
            assert(MemtableBucket::strictly_sorted(out@)) by {
                assert forall |i: int, j: int|
                    0 <= i < j < out@.len()
                    implies out@[i].key.0 < out@[j].key.0 by {
                    if j == out@.len() - 1 {
                        assert(before.contains_key(out@[j].key));
                    }
                }
            }
            assert forall |i: int, key: Key|
                0 <= i < out@.len()
                && cursor@.contains_key(key)
                implies out@[i].key.0 < key.0 by {
                if i == out@.len() - 1 {
                    assert(out@[i] == entry);
                } else {
                    assert(before.contains_key(key));
                }
            }
            assert(original.contains_key(entry.key)) by {
                assert(before.contains_key(entry.key));
            }
            assert(original[entry.key] == entry.message);
            assert(cursor@ <= before) by {
                assert forall |key: Key| cursor@.contains_key(key)
                    implies #[trigger] before.contains_key(key)
                        && cursor@[key] == before[key] by {}
            }
            assert(cursor@ <= original);
            assert(MemtableBucket::entries_map(out@).dom()
                .disjoint(cursor@.dom())) by {
                assert forall |key: Key|
                    MemtableBucket::entries_map(out@).contains_key(key)
                    implies !cursor@.contains_key(key) by {
                    if key == entry.key {
                        assert(!cursor@.contains_key(entry.key));
                    } else {
                        assert(MemtableBucket::entries_map(old_out)
                            .contains_key(key));
                    }
                }
            }
            assert_maps_equal!(
                MemtableBucket::entries_map(out@)
                    .union_prefer_right(cursor@),
                original,
                key => {
                    if key == entry.key {
                        assert(before.contains_key(key));
                        assert(original.contains_key(key));
                    } else if cursor@.contains_key(key) {
                        assert(before.contains_key(key));
                    } else if MemtableBucket::entries_map(old_out)
                        .contains_key(key)
                    {
                    } else if original.contains_key(key) {
                        assert(before.contains_key(key));
                        assert(key == entry.key);
                    }
                }
            );
        }
        index += 1;
    }
    out
}

pub fn leaf_from_entries(entries: Vec<MemtableEntry>) -> (node: IBranchNode)
    requires
        entries@.len() > 0,
        MemtableBucket::strictly_sorted(entries@),
    ensures
        node.wf(),
        node is Leaf,
        node->keys@ == entries@.map(
            |i: int, entry: MemtableEntry| entry.key,
        ),
        node->msgs@ == entries@.map(
            |i: int, entry: MemtableEntry| entry.message,
        ),
        node@.wf(),
        node@.keys_strictly_sorted(),
{
    let mut keys = Vec::new();
    let mut msgs = Vec::new();
    let mut index = 0usize;
    while index < entries.len()
        invariant
            index <= entries.len(),
            keys@ == entries@.subrange(0, index as int).map(
                |i: int, entry: MemtableEntry| entry.key,
            ),
            msgs@ == entries@.subrange(0, index as int).map(
                |i: int, entry: MemtableEntry| entry.message,
            ),
        decreases entries.len() - index,
    {
        keys.push(entries[index].key);
        msgs.push(entries[index].message);
        index += 1;
    }
    let node = IBranchNode::Leaf { keys, msgs };
    proof {
        assert(node.wf());
        assert(Key::is_strictly_sorted(node->keys@)) by {
            assert forall |i: int, j: int| 0 <= i < j < node->keys@.len()
                implies Key::lt(node->keys@[i], node->keys@[j]) by {


            }
        }
        assert(node@.wf());
        assert(node@.keys_strictly_sorted());
    }
    node
}

pub fn index_from_descriptors(
    descriptors: &Vec<BranchChildDescriptor>,
    start: usize,
    count: usize,
    aux_ptr: Option<IAddress>,
) -> (node: IBranchNode)
    requires
        count > 0,
        start <= descriptors.len(),
        count <= descriptors.len() - start,
        forall |i: int| 0 <= i < descriptors@.len()
            ==> descriptors@[i].wf(),
        forall |i: int, j: int|
            start as int <= i < j < (start + count) as int
            ==> descriptors@[i].first_key.0
                < descriptors@[j].first_key.0,
    ensures
        node.wf(),
        node is Index,
        node->children@ == descriptors@.subrange(
            start as int,
            (start + count) as int,
        ).map(|i: int, desc: BranchChildDescriptor| desc.addr),
        node->pivots@ == descriptors@.subrange(
            start as int + 1,
            (start + count) as int,
        ).map(|i: int, desc: BranchChildDescriptor| desc.first_key),
        node->aux_ptr == aux_ptr,
        node@.wf(),
        node@.keys_strictly_sorted(),
{
    let mut pivots = Vec::new();
    let mut children = Vec::new();
    let mut index = 0usize;
    while index < count
        invariant
            index <= count,
            children@ == descriptors@.subrange(
                start as int,
                (start + index) as int,
            ).map(|i: int, desc: BranchChildDescriptor| desc.addr),
            pivots@ == if index == 0 {
                Seq::empty()
            } else {
                descriptors@.subrange(
                    start as int + 1,
                    (start + index) as int,
                ).map(|i: int, desc: BranchChildDescriptor| desc.first_key)
            },
        decreases count - index,
    {
        children.push(descriptors[start + index].addr);
        if index > 0 {
            pivots.push(descriptors[start + index].first_key);
        }
        index += 1;
    }
    let node = IBranchNode::Index { pivots, children, aux_ptr };
    proof {
        assert(node.wf());
        assert(Key::is_strictly_sorted(node->pivots@)) by {
            assert forall |i: int, j: int| 0 <= i < j < node->pivots@.len()
                implies Key::lt(node->pivots@[i], node->pivots@[j]) by {


            }
        }
        assert(node@.wf());
        assert(node@.keys_strictly_sorted());
    }
    node
}

pub proof fn staged_nodes_insert_preserves_wf(
    nodes: LoadedBranch,
    addr: Address,
    node: crate::allocation_layer::BranchTypes_v::BranchNode,
)
    requires
        BranchBulkBuilder::staged_nodes_wf(nodes),
        !nodes.contains_key(addr),
        addr.wf(),
        node.wf(),
        node.keys_strictly_sorted(),
        !(node is Auxiliary),
    ensures
        BranchBulkBuilder::staged_nodes_wf(nodes.insert(addr, node)),
{
    assert forall |candidate: Address|
        #[trigger] nodes.insert(addr, node).contains_key(candidate)
        implies {
            &&& candidate.wf()
            &&& nodes.insert(addr, node)[candidate].wf()
            &&& nodes.insert(addr, node)[candidate].keys_strictly_sorted()
            &&& !(nodes.insert(addr, node)[candidate] is Auxiliary)
        } by {
        if candidate == addr {
            assert(nodes.insert(addr, node)[candidate] == node);
        } else {
            assert(nodes.contains_key(candidate));
            assert(nodes.insert(addr, node)[candidate] == nodes[candidate]);
        }
    }
}

pub proof fn descriptors_push_preserves_wf_and_sorted(
    descriptors: Seq<BranchChildDescriptor>,
    descriptor: BranchChildDescriptor,
)
    requires
        BranchBulkBuilder::descriptors_wf(descriptors),
        BranchBulkBuilder::descriptors_sorted(descriptors),
        descriptor.wf(),
        forall |i: int| 0 <= i < descriptors.len()
            ==> descriptors[i].first_key.0 < descriptor.first_key.0,
        descriptor_sequence_wf(descriptors),
        forall |i: int| 0 <= i < descriptors.len() ==> {
            &&& descriptors[i].receipt@.nodes.dom().disjoint(
                descriptor.receipt@.nodes.dom(),
            )
            &&& descriptors[i].receipt@.last_key.0
                < descriptor.first_key.0
            &&& descriptors[i].receipt@.height
                == descriptor.receipt@.height
        },
    ensures
        BranchBulkBuilder::descriptors_wf(descriptors.push(descriptor)),
        BranchBulkBuilder::descriptors_sorted(descriptors.push(descriptor)),
        descriptor_sequence_wf(descriptors.push(descriptor)),
{
    assert forall |i: int| 0 <= i < descriptors.push(descriptor).len()
        implies (#[trigger] descriptors.push(descriptor)[i]).wf() by {
        if i == descriptors.len() {
            assert(descriptors.push(descriptor)[i] == descriptor);
        }
    }
    assert forall |i: int, j: int|
        0 <= i < j < descriptors.push(descriptor).len()
        implies descriptors.push(descriptor)[i].first_key.0
            < descriptors.push(descriptor)[j].first_key.0 by {
        if j == descriptors.len() {
            assert(descriptors.push(descriptor)[j] == descriptor);
            assert(descriptors.push(descriptor)[i] == descriptors[i]);
        }
    }
    assert(descriptor_sequence_wf(descriptors.push(descriptor))) by {
        assert forall |i: int| 0 <= i < descriptors.push(descriptor).len()
            implies (#[trigger] descriptors.push(descriptor)[i]).wf() by {
            if i == descriptors.len() {
                assert(descriptors.push(descriptor)[i] == descriptor);
            }
        }
        assert forall |i: int, j: int|
            0 <= i < j < descriptors.push(descriptor).len()
            implies #[trigger]
                descriptors.push(descriptor)[i].receipt@.nodes.dom().disjoint(
                        descriptors.push(descriptor)[j]
                            .receipt@.nodes.dom(),
                    ) by {
            if j == descriptors.len() {
                assert(descriptors.push(descriptor)[j] == descriptor);
                assert(descriptors.push(descriptor)[i] == descriptors[i]);
            }
        }
        assert forall |i: int, j: int|
            #![trigger descriptors.push(descriptor)[i],
                descriptors.push(descriptor)[j]]
            0 <= i < j < descriptors.push(descriptor).len()
            implies
                descriptors.push(descriptor)[i].receipt@.last_key.0
                    < descriptors.push(descriptor)[j].first_key.0 by {
            if j == descriptors.len() {
                assert(descriptors.push(descriptor)[j] == descriptor);
                assert(descriptors.push(descriptor)[i] == descriptors[i]);
            }
        }
        assert forall |i: int, j: int|
            #![trigger descriptors.push(descriptor)[i],
                descriptors.push(descriptor)[j]]
            0 <= i < j < descriptors.push(descriptor).len()
            implies
                descriptors.push(descriptor)[i].receipt@.height
                    == descriptors.push(descriptor)[j].receipt@.height by {
            if j == descriptors.len() {
                assert(descriptors.push(descriptor)[j] == descriptor);
                assert(descriptors.push(descriptor)[i] == descriptors[i]);
            }
        }
    }
}

impl BranchBulkBuilder {
    pub open spec fn descriptors_wf(
        descriptors: Seq<BranchChildDescriptor>,
    ) -> bool {
        forall |i: int| 0 <= i < descriptors.len()
            ==> (#[trigger] descriptors[i]).wf()
    }

    pub open spec fn descriptors_sorted(
        descriptors: Seq<BranchChildDescriptor>,
    ) -> bool {
        forall |i: int, j: int| 0 <= i < j < descriptors.len()
            ==> descriptors[i].first_key.0
                < descriptors[j].first_key.0
    }

    pub open spec fn staged_nodes_wf(nodes: LoadedBranch) -> bool {
        forall |addr: Address| #[trigger] nodes.contains_key(addr) ==> {
            &&& addr.wf()
            &&& nodes[addr].wf()
            &&& nodes[addr].keys_strictly_sorted()
            &&& !(nodes[addr] is Auxiliary)
        }
    }

    pub open spec fn wf(&self, memtable: &MemtableImpl) -> bool {
        &&& memtable.wf()
        &&& self.cursor.wf(memtable)
        &&& self.source@ == memtable@.buffer.map
        &&& self.index_fanout > 1
        &&& self.index_fanout as int
            == branch_index_capacity_spec() + 1
        &&& self.leaf_partition.wf()
        &&& self.leaf_partition.capacity as int
            == crate::implementation::BranchPageImpl_v::branch_leaf_capacity_spec()
        &&& Self::descriptors_wf(self.leaf_output@)
        &&& Self::descriptors_sorted(self.leaf_output@)
        &&& descriptor_sequence_wf(self.leaf_output@)
        &&& Self::descriptors_wf(self.root_children@)
        &&& Self::descriptors_sorted(self.root_children@)
        &&& descriptor_sequence_wf(self.root_children@)
        &&& Self::staged_nodes_wf(self.staged_nodes@)
        &&& match self.level {
            Some(ref level) => {
                &&& level.partition.wf()
                &&& level.partition.capacity > 1
                &&& level.partition.capacity == self.index_fanout
                &&& level.partition.total == level.input.len()
                &&& level.partition.emitted < level.partition.node_count
                &&& level.partition.node_count > 1
                &&& level.next_input <= level.input.len()
                &&& level.next_input as int
                    == level.partition.prefix_size(
                        level.partition.emitted as int,
                    )
                &&& level.output.len() == level.partition.emitted
                &&& Self::descriptors_wf(level.input@)
                &&& Self::descriptors_sorted(level.input@)
                &&& descriptor_forest_wf(level.input@)
                &&& Self::descriptors_wf(level.output@)
                &&& Self::descriptors_sorted(level.output@)
                &&& descriptor_sequence_wf(level.output@)
                &&& descriptor_forest_nodes(level.input@)
                    <= self.staged_nodes@
                &&& descriptor_forest_nodes(level.output@)
                    <= self.staged_nodes@
                &&& forall |i: int, j: int|
                    0 <= i < level.output@.len()
                    && level.next_input as int <= j < level.input@.len()
                    ==> level.output@[i].first_key.0
                        < level.input@[j].first_key.0
                &&& forall |i: int, j: int|
                    0 <= i < level.output@.len()
                    && level.next_input as int <= j < level.input@.len()
                    ==> level.output@[i].receipt@.nodes.dom().disjoint(
                            level.input@[j].receipt@.nodes.dom(),
                        )
                &&& forall |i: int, j: int|
                    0 <= i < level.output@.len()
                    && level.next_input as int <= j < level.input@.len()
                    ==> level.output@[i].receipt@.last_key.0
                            < level.input@[j].first_key.0
                &&& forall |i: int, j: int|
                    0 <= i < level.output@.len()
                    && level.next_input as int <= j < level.input@.len()
                    ==> level.output@[i].receipt@.height
                            == level.input@[j].receipt@.height + 1
            },
            None => true,
        }
        &&& match self.phase {
            BranchBulkPhase::Leaves => {
                &&& self.level is None
                &&& self.root_leaf.len() == 0
                &&& self.root_children.len() == 0
                &&& self.leaf_partition.emitted
                    < self.leaf_partition.node_count
                &&& self.leaf_partition.node_count > 1
                &&& self.leaf_output.len()
                    == self.leaf_partition.emitted
                &&& descriptor_forest_nodes(self.leaf_output@)
                    == self.staged_nodes@
                &&& descriptor_forest_contents(self.leaf_output@)
                    .union_prefer_right(self.cursor@) == self.source@
                &&& self.cursor.count(memtable) as int
                    + self.leaf_partition.prefix_size(
                        self.leaf_partition.emitted as int,
                    ) == self.leaf_partition.total as int
                &&& forall |i: int, key: Key|
                    0 <= i < self.leaf_output@.len()
                    && self.cursor@.contains_key(key)
                    ==> self.leaf_output@[i].receipt@.last_key.0 < key.0
                &&& forall |i: int| 0 <= i < self.leaf_output@.len()
                    ==> self.leaf_output@[i].receipt@.height == 0
            },
            BranchBulkPhase::Index => {
                &&& self.level is Some
                &&& self.root_leaf.len() == 0
                &&& self.root_children.len() == 0
                &&& self.leaf_output.len() == 0
                &&& self.cursor@ == Map::<Key, Message>::empty()
                &&& descriptor_forest_nodes(
                    self.level->0.output@,
                ).dom() + descriptor_forest_nodes(
                    self.level->0.input@.skip(
                        self.level->0.next_input as int,
                    ),
                ).dom() == self.staged_nodes@.dom()
                &&& descriptor_forest_contents(
                    self.level->0.output@,
                ).union_prefer_right(descriptor_forest_contents(
                    self.level->0.input@.skip(
                        self.level->0.next_input as int,
                    ),
                )) == self.source@
            },
            BranchBulkPhase::ReadyLeafRoot => {
                &&& self.level is None
                &&& self.leaf_output.len() == 0
                &&& self.root_children.len() == 0
                &&& self.staged_nodes@ == LoadedBranch::empty()
                &&& self.root_leaf.len() > 0
                &&& self.leaf_partition.node_count == 1
                &&& self.root_leaf.len() == self.leaf_partition.total
                &&& MemtableBucket::unique_keys(self.root_leaf@)
                &&& MemtableBucket::strictly_sorted(self.root_leaf@)
                &&& self.cursor@ == Map::<Key, Message>::empty()
                &&& MemtableBucket::entries_map(self.root_leaf@)
                    == self.source@
            },
            BranchBulkPhase::ReadyIndexRoot => {
                &&& self.level is None
                &&& self.leaf_output.len() == 0
                &&& self.root_leaf.len() == 0
                &&& self.root_children.len() > 1
                &&& self.root_children.len() <= self.index_fanout
                &&& self.cursor@ == Map::<Key, Message>::empty()
                &&& descriptor_forest_wf(self.root_children@)
                &&& descriptor_forest_nodes(self.root_children@)
                    <= self.staged_nodes@
                &&& descriptor_forest_nodes(self.root_children@).dom()
                    == self.staged_nodes@.dom()
                &&& descriptor_forest_contents(self.root_children@)
                    == self.source@
            },
            BranchBulkPhase::Sealed => {
                self.cursor@ == Map::<Key, Message>::empty()
            },
        }
    }

    pub fn start(memtable: &MemtableImpl) -> (result: BranchBulkStartResult)
        requires
            memtable.wf(),
        ensures
            match result {
                BranchBulkStartResult::Started { builder } => {
                    &&& builder.wf(memtable)
                    &&& builder.source@ == memtable@.buffer.map
                    &&& !builder.source@.is_empty()
                    &&& builder.staged_nodes@ == LoadedBranch::empty()
                },
                BranchBulkStartResult::Empty => memtable@.is_empty(),
                BranchBulkStartResult::Overflow => true,
                BranchBulkStartResult::InvalidCapacity => true,
            },
    {
        let mut cursor = memtable.sorted_scan();
        let total = match cursor.remaining_len_checked(memtable) {
            Some(total) => total,
            None => return BranchBulkStartResult::Overflow,
        };
        if total == 0 {
            proof {
                cursor.count_zero_implies_empty(memtable);
                assert(cursor@ == Map::<Key, Message>::empty());
                assert(memtable@.buffer.map == Map::<Key, Message>::empty());
            }
            return BranchBulkStartResult::Empty;
        }
        proof {
            cursor.count_positive_implies_nonempty(memtable);
            assert(memtable@.buffer.map
                != Map::<Key, Message>::empty());
            assert(!memtable@.buffer.map.is_empty()) by {
                if memtable@.buffer.map.is_empty() {
                    assert_maps_equal!(
                        memtable@.buffer.map,
                        Map::<Key, Message>::empty(),
                        key => {}
                    );
                }
            }
        }
        let leaf_capacity = branch_leaf_capacity();
        let index_pivots = branch_index_capacity();
        if leaf_capacity == 0 || index_pivots == 0
            || index_pivots == usize::MAX
        {
            return BranchBulkStartResult::InvalidCapacity;
        }
        let index_fanout = index_pivots + 1;
        let leaf_partition = match BalancedPartition::new(
            total,
            leaf_capacity,
        ) {
            Some(partition) => partition,
            None => {
                proof { assert(false); }
                return BranchBulkStartResult::InvalidCapacity;
            },
        };
        let ghost source = memtable@.buffer.map;
        let ghost staged_nodes = LoadedBranch::empty();
        if total <= leaf_capacity {
            let root_leaf = collect_sorted_entries(
                &mut cursor,
                memtable,
                total,
            );
            let builder = Self {
                cursor,
                phase: BranchBulkPhase::ReadyLeafRoot,
                index_fanout,
                leaf_partition,
                leaf_output: Vec::new(),
                level: None,
                root_leaf,
                root_children: Vec::new(),
                staged_nodes: Ghost(staged_nodes),
                source: Ghost(source),
            };
            proof {
                assert(((total as nat - 1) as nat) < leaf_capacity as nat);
                lemma_basic_div(
                    total as int - 1,
                    leaf_capacity as int,
                );
                assert((total as int - 1) / (leaf_capacity as int) == 0);
                assert(((total as nat - 1) as nat)
                    / (leaf_capacity as nat) == 0nat);
                assert(builder.leaf_partition.node_count == 1);
                assert(builder.cursor.count(memtable) == 0);
                builder.cursor.count_zero_implies_empty(memtable);
                assert(builder.cursor@ == Map::<Key, Message>::empty()) by {
                    assert_maps_equal!(
                        builder.cursor@,
                        Map::<Key, Message>::empty(),
                        key => {}
                    );
                }
                assert(MemtableBucket::entries_map(builder.root_leaf@)
                    == builder.source@) by {
                    assert(MemtableBucket::entries_map(builder.root_leaf@)
                        .union_prefer_right(builder.cursor@)
                            == builder.source@);
                    assert_maps_equal!(
                        MemtableBucket::entries_map(builder.root_leaf@),
                        builder.source@,
                        key => {}
                    );
                }
                assert(!builder.source@.is_empty());
                assert(builder.wf(memtable));
            }
            BranchBulkStartResult::Started { builder }
        } else {
            let builder = Self {
                cursor,
                phase: BranchBulkPhase::Leaves,
                index_fanout,
                leaf_partition,
                leaf_output: Vec::new(),
                level: None,
                root_leaf: Vec::new(),
                root_children: Vec::new(),
                staged_nodes: Ghost(staged_nodes),
                source: Ghost(source),
            };
            proof {
                assert(leaf_partition.node_count > 1) by {
                    if leaf_partition.node_count == 1 {
                        assert(leaf_partition.total == total);
                        assert(leaf_partition.capacity == leaf_capacity);
                        assert(leaf_partition.node_count as int == 1);
                        assert(leaf_partition.capacity as int
                            == leaf_capacity as int);
                        assert(leaf_partition.total as int
                            <= leaf_partition.node_count as int
                                * leaf_partition.capacity as int);
                        assert(leaf_partition.node_count as int
                            * leaf_partition.capacity as int
                                == 1int * leaf_partition.capacity as int);
                        lemma_mul_basics(leaf_partition.capacity as int);
                        assert(1int * leaf_partition.capacity as int
                            == leaf_partition.capacity as int);
                        assert(leaf_partition.node_count as int
                            * leaf_partition.capacity as int
                                == leaf_capacity as int);
                        assert(total as int <= leaf_capacity as int);
                        assert(false);
                    }
                }
                assert(descriptor_forest_contents(builder.leaf_output@)
                    == Map::<Key, Message>::empty()) by {

                }
                assert(descriptor_forest_contents(builder.leaf_output@)
                    .union_prefer_right(builder.cursor@)
                        == builder.source@) by {
                    assert(builder.cursor@ == builder.source@);
                    assert_maps_equal!(
                        descriptor_forest_contents(builder.leaf_output@)
                            .union_prefer_right(builder.cursor@),
                        builder.source@,
                        key => {}
                    );
                }
                assert(!builder.source@.is_empty());
                assert(builder.wf(memtable));
            }
            BranchBulkStartResult::Started { builder }
        }
    }

    pub fn needs_staged_page(&self) -> (out: bool)
        ensures
            out == (self.phase is Leaves || self.phase is Index),
    {
        match self.phase {
            BranchBulkPhase::Leaves | BranchBulkPhase::Index => true,
            _ => false,
        }
    }

    pub fn ready_to_seal(&self) -> (out: bool)
        ensures
            out == (self.phase is ReadyLeafRoot
                || self.phase is ReadyIndexRoot),
    {
        match self.phase {
            BranchBulkPhase::ReadyLeafRoot
            | BranchBulkPhase::ReadyIndexRoot => true,
            _ => false,
        }
    }

    fn enter_index_or_root(
        &mut self,
        descriptors: Vec<BranchChildDescriptor>,
        fanout: usize,
    )
        requires
            fanout > 1,
            descriptors@.len() > 1,
            Self::descriptors_wf(descriptors@),
            Self::descriptors_sorted(descriptors@),
            descriptor_forest_wf(descriptors@),
            descriptor_forest_nodes(descriptors@)
                == old(self).staged_nodes@,
            descriptor_forest_contents(descriptors@)
                == old(self).source@,
        ensures
            self.cursor == old(self).cursor,
            self.index_fanout == old(self).index_fanout,
            self.leaf_partition == old(self).leaf_partition,
            self.leaf_output@ == old(self).leaf_output@,
            self.root_leaf@ == old(self).root_leaf@,
            self.staged_nodes@ == old(self).staged_nodes@,
            self.source@ == old(self).source@,
            Self::descriptors_wf(self.root_children@),
            Self::descriptors_sorted(self.root_children@),
            descriptor_sequence_wf(self.root_children@),
            match self.phase {
                BranchBulkPhase::ReadyIndexRoot => {
                    &&& self.level is None
                    &&& self.root_children@ == descriptors@
                    &&& self.root_children.len() <= fanout
                    &&& descriptor_forest_nodes(self.root_children@)
                        == self.staged_nodes@
                    &&& descriptor_forest_contents(self.root_children@)
                        == self.source@
                },
                BranchBulkPhase::Index => {
                    &&& self.level is Some
                    &&& self.level->0.input@ == descriptors@
                    &&& self.level->0.partition.capacity == fanout
                    &&& self.level->0.partition.wf()
                    &&& self.level->0.partition.total
                        == descriptors.len()
                    &&& self.level->0.partition.emitted == 0
                    &&& self.level->0.partition.node_count > 1
                    &&& self.level->0.next_input == 0
                    &&& self.level->0.next_input as int
                        == self.level->0.partition.prefix_size(
                            self.level->0.partition.emitted as int,
                        )
                    &&& self.level->0.output.len() == 0
                    &&& Self::descriptors_wf(self.level->0.input@)
                    &&& Self::descriptors_sorted(self.level->0.input@)
                    &&& self.root_children.len() == 0
                    &&& descriptor_forest_nodes(self.level->0.input@)
                        == self.staged_nodes@
                    &&& descriptor_forest_nodes(self.level->0.output@)
                        .dom() + descriptor_forest_nodes(
                            self.level->0.input@.skip(
                                self.level->0.next_input as int,
                            ),
                        ).dom() == self.staged_nodes@.dom()
                    &&& descriptor_forest_contents(
                        self.level->0.output@,
                    ).union_prefer_right(descriptor_forest_contents(
                        self.level->0.input@.skip(
                            self.level->0.next_input as int,
                        ),
                    )) == self.source@
                },
                _ => false,
            },
    {
        if descriptors.len() <= fanout {
            self.root_children = descriptors;
            self.level = None;
            self.phase = BranchBulkPhase::ReadyIndexRoot;
        } else {
            let partition = match BalancedPartition::new(
                descriptors.len(),
                fanout,
            ) {
                Some(partition) => partition,
                None => {
                    proof { assert(false); }
                    return;
                },
            };
            self.level = Some(BranchBuildLevel {
                input: descriptors,
                next_input: 0,
                partition,
                output: Vec::new(),
            });
            self.root_children = Vec::new();
            self.phase = BranchBulkPhase::Index;
            proof {
                assert(self.level->0.partition.node_count > 1) by {
                    if self.level->0.partition.node_count == 1 {
                        assert(self.level->0.partition.total
                            == self.level->0.input.len());
                        assert(self.level->0.partition.capacity == fanout);
                        assert(self.level->0.partition.node_count as int == 1);
                        assert(self.level->0.partition.total as int
                            <= self.level->0.partition.node_count as int
                                * self.level->0.partition.capacity as int);
                        assert(self.level->0.partition.node_count as int
                            * self.level->0.partition.capacity as int
                                == 1int * self.level->0.partition.capacity as int);
                        lemma_mul_basics(
                            self.level->0.partition.capacity as int,
                        );
                        assert(1int * self.level->0.partition.capacity as int
                            == self.level->0.partition.capacity as int);
                        assert(self.level->0.partition.total as int
                            <= fanout as int);
                        assert(false);
                    }
                }
                assert(self.level->0.partition.prefix_size(0) == 0);
                assert(self.level->0.next_input as int
                    == self.level->0.partition.prefix_size(
                        self.level->0.partition.emitted as int,
                    ));
                assert(self.level->0.input@.skip(0)
                    == self.level->0.input@);
                assert(descriptor_forest_nodes(
                    self.level->0.output@,
                ) == Map::<Address, BranchNode>::empty());
                assert(descriptor_forest_contents(
                    self.level->0.output@,
                ) == Map::<Key, Message>::empty()) by {

                }
                assert(descriptor_forest_nodes(
                    self.level->0.output@,
                ).dom() + descriptor_forest_nodes(
                    self.level->0.input@.skip(
                        self.level->0.next_input as int,
                    ),
                ).dom() == self.staged_nodes@.dom());
                assert(descriptor_forest_contents(
                    self.level->0.output@,
                ).union_prefer_right(descriptor_forest_contents(
                    self.level->0.input@.skip(
                        self.level->0.next_input as int,
                    ),
                )) == self.source@) by {
                    assert(self.level->0.input@.skip(0)
                        == self.level->0.input@);
                    assert_maps_equal!(
                        descriptor_forest_contents(
                            self.level->0.output@,
                        ).union_prefer_right(descriptor_forest_contents(
                            self.level->0.input@,
                        )),
                        self.source@,
                        key => {}
                    );
                }
            }
        }
    }

    #[verifier::rlimit(32)]
    pub fn stage_next(
        &mut self,
        memtable: &MemtableImpl,
        addr: IAddress,
    ) -> (result: BranchBulkNodeResult)
        requires
            old(self).wf(memtable),
            addr@.wf(),
            !old(self).staged_nodes@.contains_key(addr@),
        ensures
            self.wf(memtable),
            (old(self).phase is Leaves || old(self).phase is Index)
                ==> result is Page,
            match result {
                BranchBulkNodeResult::Page { node, descriptor } => {
                    &&& (old(self).phase is Leaves
                        || old(self).phase is Index)
                    &&& node.wf()
                    &&& node@.wf()
                    &&& node@.keys_strictly_sorted()
                    &&& !(node is Auxiliary)
                    &&& node is Leaf ==> {
                        &&& node->keys@.len()
                            <= crate::implementation::BranchPageImpl_v::branch_leaf_capacity_spec()
                        &&& node->keys@.len() <= u8::MAX as int
                    }
                    &&& node is Index ==> {
                        &&& node->pivots@.len()
                            <= branch_index_capacity_spec()
                        &&& node->pivots@.len() <= u8::MAX as int
                    }
                    &&& descriptor.addr == addr
                    &&& descriptor.wf()
                    &&& self.staged_nodes@
                        == old(self).staged_nodes@.insert(addr@, node@)
                },
                BranchBulkNodeResult::NotReady => *self == *old(self),
            },
    {
        match self.phase {
            BranchBulkPhase::Leaves => {
                let ghost old_partition = self.leaf_partition;
                let ghost old_cursor = self.cursor@;
                let ghost old_output = self.leaf_output@;
                let ghost old_staged = self.staged_nodes@;
                let size = match self.leaf_partition.next_size() {
                    Some(size) => size,
                    None => {
                        proof { assert(false); }
                        return BranchBulkNodeResult::NotReady;
                    },
                };
                proof {
                    assert(size as int
                        <= old(self).cursor.count(memtable) as int) by {
                        assert(old_partition.prefix_size(
                            old_partition.emitted as int,
                        ) + size as int
                            <= old_partition.total as int);
                    }
                }
                let entries = collect_sorted_entries(
                    &mut self.cursor,
                    memtable,
                    size,
                );
                let ghost entry_seq = entries@;
                let first_key = entries[0].key;
                let node = leaf_from_entries(entries);
                let ghost receipt = make_leaf_receipt(addr@, node@);
                let descriptor = BranchChildDescriptor {
                    first_key,
                    addr,
                    receipt: Ghost(receipt),
                };
                proof {
                    leaf_entries_contents(entry_seq, node@);
                    assert(receipt.pivot.i().map
                        == MemtableBucket::entries_map(entry_seq));
                    assert(descriptor_sequence_wf(old_output));
                    assert forall |i: int| 0 <= i < old_output.len()
                        implies old_output[i].first_key.0
                            < descriptor.first_key.0 by {
                        assert(old_cursor.contains_key(first_key));
                    }
                    assert forall |i: int| 0 <= i < old_output.len()
                        implies {
                            &&& old_output[i].receipt@.nodes.dom().disjoint(
                                descriptor.receipt@.nodes.dom(),
                            )
                            &&& old_output[i].receipt@.last_key.0
                                < descriptor.first_key.0
                            &&& old_output[i].receipt@.height
                                == descriptor.receipt@.height
                        } by {
                        assert(old_cursor.contains_key(first_key));
                        assert(old_output[i].receipt@.last_key.0
                            < first_key.0);
                        assert(old_output[i].receipt@.height == 0);
                        assert(descriptor.receipt@.height == 0);
                        assert(descriptor.receipt@.nodes.dom()
                            == set![addr@]);
                        if old_output.len() > 0 {
                            assert(descriptor_forest_wf(old_output));
                            descriptor_forest_contains_receipt(
                                old_output,
                                i,
                            );
                            assert(old_output[i].receipt@.nodes
                                <= old_staged);
                        }
                        assert(!old_staged.contains_key(addr@));
                    }
                    descriptors_push_preserves_wf_and_sorted(
                        old_output,
                        descriptor,
                    );
                    staged_nodes_insert_preserves_wf(
                        old_staged,
                        addr@,
                        node@,
                    );
                }
                self.leaf_output.push(descriptor);
                self.staged_nodes = Ghost(
                    old_staged.insert(addr@, node@),
                );
                proof {
                    assert(Self::descriptors_wf(self.leaf_output@));
                    assert(Self::descriptors_sorted(self.leaf_output@));
                    assert(descriptor_sequence_wf(self.leaf_output@));
                    assert(descriptor_forest_nodes(self.leaf_output@)
                        == self.staged_nodes@) by {
                        assert(self.leaf_output@
                            == old_output.push(descriptor));
                        assert(self.leaf_output@.len() > 0);
                        assert(self.leaf_output@.drop_last() == old_output);
                        assert(self.leaf_output@.last() == descriptor);

                        assert(descriptor_forest_nodes(self.leaf_output@)
                            == descriptor_forest_nodes(old_output)
                                .union_prefer_right(
                                    descriptor.receipt@.nodes,
                                ));
                        assert(descriptor_forest_nodes(old_output)
                            == old_staged);
                        assert(descriptor.receipt@.nodes
                            == map![addr@ => node@]);
                        assert_maps_equal!(
                            descriptor_forest_nodes(self.leaf_output@),
                            self.staged_nodes@,
                            candidate => {}
                        );
                    }
                    assert(descriptor_forest_contents(self.leaf_output@)
                        == descriptor_forest_contents(old_output)
                            .union_prefer_right(
                                descriptor.receipt@.pivot.i().map,
                            )) by {
                        assert(self.leaf_output@
                            == old_output.push(descriptor));
                        assert(self.leaf_output@.drop_last() == old_output);
                        assert(self.leaf_output@.last() == descriptor);

                    }
                    message_map_union_prefer_right_assoc(
                        descriptor_forest_contents(old_output),
                        descriptor.receipt@.pivot.i().map,
                        self.cursor@,
                    );
                    assert(descriptor_forest_contents(self.leaf_output@)
                        .union_prefer_right(self.cursor@)
                            == self.source@) by {
                        assert(MemtableBucket::entries_map(entry_seq)
                            .union_prefer_right(self.cursor@)
                                == old_cursor);
                        assert(descriptor_forest_contents(old_output)
                            .union_prefer_right(old_cursor)
                                == self.source@);
                    }
                    assert(Self::staged_nodes_wf(self.staged_nodes@));
                }
                if self.leaf_partition.complete() {
                    proof {
                        self.cursor.count_zero_implies_empty(memtable);
                        assert(self.cursor@
                            == Map::<Key, Message>::empty());
                        assert(self.leaf_output.len()
                            == self.leaf_partition.node_count);
                        assert(self.leaf_output.len() > 1);
                        assert(descriptor_forest_wf(self.leaf_output@));
                        assert(descriptor_forest_contents(
                            self.leaf_output@,
                        ) == self.source@) by {
                            assert_maps_equal!(
                                descriptor_forest_contents(
                                    self.leaf_output@,
                                ),
                                self.source@,
                                key => {}
                            );
                        }
                    }
                    let descriptors = self.leaf_output.clone();
                    self.leaf_output.clear();
                    let fanout = self.index_fanout;
                    self.enter_index_or_root(descriptors, fanout);
                }
                proof {
                    assert(descriptor.wf());
                    assert(node->keys@.len() == size);
                    assert(node->keys@.len()
                        <= crate::implementation::BranchPageImpl_v::branch_leaf_capacity_spec());
                    assert(node->keys@.len() <= u8::MAX as int) by {

                    }
                    assert(self.wf(memtable));
                }
                BranchBulkNodeResult::Page { node, descriptor }
            },
            BranchBulkPhase::Index => {
                let ghost pre_level = self.level;
                let ghost old_staged = self.staged_nodes@;
                let level_opt = self.level.take();
                let mut level = level_opt.unwrap();
                let ghost old_level_input = level.input@;
                let ghost old_level_output = level.output@;
                let ghost old_level_partition = level.partition;
                let ghost old_next_input = level.next_input;
                let size = match level.partition.next_size() {
                    Some(size) => size,
                    None => {
                        proof { assert(false); }
                        return BranchBulkNodeResult::NotReady;
                    },
                };
                let start = level.next_input;
                proof {
                    assert(start == old_next_input);
                    assert(start as int + size as int
                        == level.partition.prefix_size(
                            level.partition.emitted as int,
                        ));
                    assert(start + size <= level.input.len());
                    assert((start + size) as int
                        == start as int + size as int);
                }
                let node = index_from_descriptors(
                    &level.input,
                    start,
                    size,
                    None,
                );
                let ghost children = old_level_input.subrange(
                    start as int,
                    (start + size) as int,
                );
                proof {
                    assert(children.len() == size);
                    assert(descriptor_forest_wf(children)) by {
                        assert(descriptor_sequence_wf(children)) by {
                            assert forall |i: int| 0 <= i < children.len()
                                implies (#[trigger] children[i]).wf() by {}
                            assert forall |i: int, j: int|
                                0 <= i < j < children.len()
                                implies {
                                    &&& children[i].receipt@.nodes.dom()
                                        .disjoint(
                                            children[j].receipt@.nodes.dom(),
                                        )
                                    &&& children[i].receipt@.last_key.0
                                        < children[j].first_key.0
                                    &&& children[i].receipt@.height
                                        == children[j].receipt@.height
                                } by {}
                        }
                    }
                    assert(!descriptor_forest_nodes(children)
                        .contains_key(addr@)) by {
                        if descriptor_forest_nodes(children)
                            .contains_key(addr@)
                        {
                            descriptor_forest_contains_iff(children, addr@);
                            let i = choose |i: int| 0 <= i < children.len()
                                && #[trigger] children[i].receipt@.nodes
                                    .contains_key(addr@);
                            let source_i = start as int + i;
                            descriptor_forest_contains_receipt(
                                old_level_input,
                                source_i,
                            );
                            assert(old_level_input[source_i] == children[i]);
                            assert(old_level_input[source_i].receipt@.nodes
                                <= old_staged) by {
                                assert(old_level_input[source_i].receipt@.nodes
                                    <= descriptor_forest_nodes(
                                        old_level_input,
                                    ));
                                vstd::map_lib::lemma_submap_of_trans(
                                    old_level_input[source_i]
                                        .receipt@.nodes,
                                    descriptor_forest_nodes(old_level_input),
                                    old_staged,
                                );
                            }
                            assert(old_staged.contains_key(addr@));
                            assert(false);
                        }
                    }
                    assert(descriptor_pivots(children)
                        == node@->pivots) by {
                        assert_seqs_equal!(
                            descriptor_pivots(children),
                            node@->pivots,
                            i => {}
                        );
                    }
                    assert(children.map(
                        |i: int, descriptor: BranchChildDescriptor|
                            descriptor.addr@,
                    ) == node@->children) by {
                        assert_seqs_equal!(
                            children.map(
                                |i: int, descriptor: BranchChildDescriptor|
                                    descriptor.addr@,
                            ),
                            node@->children,
                            i => {}
                        );
                    }
                    assert(node@ == (BranchNode::Index {
                        pivots: descriptor_pivots(children),
                        children: children.map(
                            |i: int, descriptor: BranchChildDescriptor|
                                descriptor.addr@,
                        ),
                        aux_ptr: None,
                    }));
                }
                let ghost receipt = make_index_receipt(
                    children,
                    addr@,
                    node@,
                );
                let first_key = level.input[start].first_key;
                let descriptor = BranchChildDescriptor {
                    first_key,
                    addr,
                    receipt: Ghost(receipt),
                };
                proof {
                    assert(descriptor.wf());
                    assert(descriptor_sequence_wf(old_level_output));
                    assert forall |i: int| 0 <= i < old_level_output.len()
                        implies old_level_output[i].first_key.0
                            < descriptor.first_key.0 by {
                        assert(old_level_input[start as int].first_key
                            == descriptor.first_key);
                    }
                    assert forall |i: int| 0 <= i < old_level_output.len()
                        implies {
                            &&& old_level_output[i].receipt@.nodes.dom()
                                .disjoint(descriptor.receipt@.nodes.dom())
                            &&& old_level_output[i].receipt@.last_key.0
                                < descriptor.first_key.0
                            &&& old_level_output[i].receipt@.height
                                == descriptor.receipt@.height
                        } by {
                        assert(old_level_output[i].receipt@.nodes.dom()
                            .disjoint(
                                old_level_input[start as int]
                                    .receipt@.nodes.dom(),
                            ));
                        assert(old_level_output[i].receipt@.last_key.0
                            < old_level_input[start as int].first_key.0);
                        assert(old_level_output[i].receipt@.height
                            == old_level_input[start as int]
                                .receipt@.height + 1);
                        assert(descriptor.receipt@.height
                            == children.first().receipt@.height + 1);
                        assert(children.first()
                            == old_level_input[start as int]);
                        assert(old_level_output[i].receipt@.nodes
                            <= old_staged) by {
                            if old_level_output.len() > 0 {
                                assert(descriptor_forest_wf(
                                    old_level_output,
                                ));
                                descriptor_forest_contains_receipt(
                                    old_level_output,
                                    i,
                                );
                                assert(descriptor_forest_nodes(
                                    old_level_output,
                                ) <= old_staged);
                            }
                        }
                        assert(old_level_output[i].receipt@.nodes.dom()
                            .disjoint(descriptor.receipt@.nodes.dom())) by {
                            assert forall |candidate: Address|
                                old_level_output[i].receipt@.nodes
                                    .contains_key(candidate)
                                implies !descriptor.receipt@.nodes
                                    .contains_key(candidate) by {
                                if candidate == addr@ {
                                    assert(!old_staged.contains_key(addr@));
                                } else if descriptor_forest_nodes(children)
                                    .contains_key(candidate)
                                {
                                    descriptor_forest_contains_iff(
                                        children,
                                        candidate,
                                    );
                                    let child_i = choose |child_i: int|
                                        0 <= child_i < children.len()
                                        && #[trigger] children[child_i]
                                            .receipt@.nodes
                                            .contains_key(candidate);
                                    let source_i = start as int + child_i;
                                    assert(old_level_output[i].receipt@.nodes
                                        .dom().disjoint(
                                            old_level_input[source_i]
                                                .receipt@.nodes.dom(),
                                        ));
                                    assert(old_level_input[source_i]
                                        == children[child_i]);
                                }
                            }
                        }
                    }
                    descriptors_push_preserves_wf_and_sorted(
                        old_level_output,
                        descriptor,
                    );
                    staged_nodes_insert_preserves_wf(
                        old_staged,
                        addr@,
                        node@,
                    );
                }
                level.next_input = start + size;
                level.output.push(descriptor);
                proof {
                    descriptor_content_stage_preserves_total(
                        old_level_input,
                        old_level_output,
                        descriptor,
                        start as int,
                        size as int,
                    );
                    assert(descriptor_forest_contents(level.output@)
                        .union_prefer_right(descriptor_forest_contents(
                            level.input@.skip(level.next_input as int),
                        )) == self.source@) by {
                        assert(level.input@ == old_level_input);
                        assert(level.output@
                            == old_level_output.push(descriptor));
                        assert(descriptor_forest_contents(old_level_output)
                            .union_prefer_right(descriptor_forest_contents(
                                old_level_input.skip(start as int),
                            )) == self.source@);
                    }
                    assert(level.next_input as int
                        == level.partition.prefix_size(
                            level.partition.emitted as int,
                        ));
                    assert(Self::descriptors_wf(level.output@));
                    assert(Self::descriptors_sorted(level.output@));
                    assert(descriptor_sequence_wf(level.output@));
                    assert forall |i: int, j: int|
                        #![trigger level.output@[i], level.input@[j]]
                        0 <= i < level.output@.len()
                        && level.next_input as int <= j < level.input@.len()
                        implies level.output@[i].first_key.0
                            < level.input@[j].first_key.0 by {
                        if i == old_level_output.len() {
                            assert(level.output@[i] == descriptor);
                            assert((start as int) < j);
                        }
                    }
                    assert forall |i: int, j: int|
                        #![trigger level.output@[i], level.input@[j]]
                        0 <= i < level.output@.len()
                        && level.next_input as int <= j < level.input@.len()
                        implies
                            level.output@[i].receipt@.nodes.dom().disjoint(
                                level.input@[j].receipt@.nodes.dom(),
                            ) by {
                        if i < old_level_output.len() {
                            assert(old_level_output[i]
                                == level.output@[i]);
                            assert(old_level_input[j] == level.input@[j]);
                        } else {
                            assert(i == old_level_output.len());
                            assert(level.output@[i] == descriptor);
                            assert(descriptor.receipt@.last_key
                                == children.last().receipt@.last_key);
                            assert(children.last()
                                == old_level_input[(start + size - 1) as int]);
                            assert(old_level_input[(start + size - 1) as int]
                                .receipt@.nodes.dom().disjoint(
                                    old_level_input[j].receipt@.nodes.dom(),
                                ));
                            assert(descriptor.receipt@.nodes.dom().disjoint(
                                level.input@[j].receipt@.nodes.dom(),
                            )) by {
                                assert forall |candidate: Address|
                                    descriptor.receipt@.nodes
                                        .contains_key(candidate)
                                    implies !level.input@[j].receipt@.nodes
                                        .contains_key(candidate) by {
                                    if candidate == addr@ {
                                        descriptor_forest_contains_receipt(
                                            old_level_input,
                                            j,
                                        );
                                        assert(old_level_input[j].receipt@.nodes
                                            <= old_staged) by {
                                            assert(old_level_input[j]
                                                .receipt@.nodes
                                                <= descriptor_forest_nodes(
                                                    old_level_input,
                                                ));
                                            vstd::map_lib::lemma_submap_of_trans(
                                                old_level_input[j]
                                                    .receipt@.nodes,
                                                descriptor_forest_nodes(
                                                    old_level_input,
                                                ),
                                                old_staged,
                                            );
                                        }
                                        assert(!old_staged.contains_key(addr@));
                                    } else if descriptor_forest_nodes(children)
                                        .contains_key(candidate)
                                    {
                                        descriptor_forest_contains_iff(
                                            children,
                                            candidate,
                                        );
                                        let child_i = choose |child_i: int|
                                            0 <= child_i < children.len()
                                            && #[trigger] children[child_i]
                                                .receipt@.nodes
                                                .contains_key(candidate);
                                        let source_i = start as int + child_i;
                                        assert(old_level_input[source_i]
                                            .receipt@.nodes.dom().disjoint(
                                                old_level_input[j]
                                                    .receipt@.nodes.dom(),
                                            ));
                                    }
                                }
                            }
                        }
                    }
                    assert forall |i: int, j: int|
                        #![trigger level.output@[i], level.input@[j]]
                        0 <= i < level.output@.len()
                        && level.next_input as int <= j < level.input@.len()
                        implies
                            level.output@[i].receipt@.last_key.0
                                < level.input@[j].first_key.0 by {
                        if i < old_level_output.len() {
                            assert(old_level_output[i] == level.output@[i]);
                            assert(old_level_input[j] == level.input@[j]);
                        } else {
                            assert(i == old_level_output.len());
                            assert(level.output@[i] == descriptor);
                            assert(descriptor.receipt@.last_key
                                == children.last().receipt@.last_key);
                            assert(children.last()
                                == old_level_input[(start + size - 1) as int]);
                            assert(old_level_input[(start + size - 1) as int]
                                .receipt@.last_key.0
                                < old_level_input[j].first_key.0);
                        }
                    }
                    assert forall |i: int, j: int|
                        #![trigger level.output@[i], level.input@[j]]
                        0 <= i < level.output@.len()
                        && level.next_input as int <= j < level.input@.len()
                        implies
                            level.output@[i].receipt@.height
                                == level.input@[j].receipt@.height + 1 by {
                        if i < old_level_output.len() {
                            assert(old_level_output[i] == level.output@[i]);
                            assert(old_level_input[j] == level.input@[j]);
                        } else {
                            assert(i == old_level_output.len());
                            assert(level.output@[i] == descriptor);
                            assert(descriptor.receipt@.height
                                == children.first().receipt@.height + 1);
                            assert(children.first()
                                == old_level_input[start as int]);
                            assert(old_level_input[start as int]
                                .receipt@.nodes.dom().disjoint(
                                    old_level_input[j]
                                        .receipt@.nodes.dom(),
                                ));
                            assert(old_level_input[start as int]
                                .receipt@.height
                                == old_level_input[j].receipt@.height);
                        }
                    }
                }
                let complete = level.partition.complete();
                let output = if complete {
                    Some(level.output.clone())
                } else {
                    None
                };
                self.level = Some(level);
                self.staged_nodes = Ghost(
                    old_staged.insert(addr@, node@),
                );
                proof {
                    descriptor_stage_partition(
                        old_level_input,
                        old_level_output,
                        descriptor,
                        start as int,
                        size as int,
                        addr@,
                        node@,
                        old_staged,
                    );
                    assert(descriptor_forest_nodes(
                        self.level->0.output@,
                    ) <= self.staged_nodes@);
                    assert(descriptor_forest_nodes(
                        self.level->0.input@,
                    ) <= self.staged_nodes@);
                    assert(descriptor_forest_nodes(
                        self.level->0.output@,
                    ).dom() + descriptor_forest_nodes(
                        self.level->0.input@.skip(
                            self.level->0.next_input as int,
                        ),
                    ).dom() == self.staged_nodes@.dom());
                    assert(descriptor_forest_contents(
                        self.level->0.output@,
                    ).union_prefer_right(descriptor_forest_contents(
                        self.level->0.input@.skip(
                            self.level->0.next_input as int,
                        ),
                    )) == self.source@);
                }
                match output {
                    Some(descriptors) => {
                        proof {
                            assert(descriptors.len()
                                == self.level->0.partition.node_count);
                            assert(descriptors.len() > 1);
                            assert(self.level->0.next_input
                                == self.level->0.input.len());
                            assert(descriptor_forest_wf(descriptors@));
                            assert(descriptor_forest_nodes(descriptors@)
                                == self.staged_nodes@);
                            assert(descriptor_forest_contents(descriptors@)
                                == self.source@) by {
                                assert(self.level->0.input@.skip(
                                    self.level->0.next_input as int,
                                ).len() == 0);
                                assert(descriptor_forest_contents(
                                    self.level->0.input@.skip(
                                        self.level->0.next_input as int,
                                    ),
                                ) == Map::<Key, Message>::empty()) by {

                                }
                                assert_maps_equal!(
                                    descriptor_forest_contents(
                                        descriptors@,
                                    ),
                                    self.source@,
                                    key => {}
                                );
                            }
                        }
                        self.level = None;
                        let fanout = self.index_fanout;
                        self.enter_index_or_root(descriptors, fanout);
                    },
                    None => {},
                }
                proof {
                    assert(descriptor.wf());
                    assert(node->pivots@.len() + 1 == size);
                    assert(size <= level.partition.capacity);
                    assert(level.partition.capacity == self.index_fanout);
                    assert(node->pivots@.len()
                        <= branch_index_capacity_spec());
                    assert(node->pivots@.len() <= u8::MAX as int) by {

                    }
                    assert(Self::staged_nodes_wf(self.staged_nodes@));
                    assert(self.wf(memtable));
                }
                BranchBulkNodeResult::Page { node, descriptor }
            },
            _ => BranchBulkNodeResult::NotReady,
        }
    }

    pub fn root_node(
        &self,
        aux_ptr: Option<IAddress>,
    ) -> (result: Option<IBranchNode>)
        requires
            self.phase is ReadyLeafRoot
                || self.phase is ReadyIndexRoot,
            self.phase is ReadyLeafRoot ==> aux_ptr is None,
            self.phase is ReadyIndexRoot ==> aux_ptr is Some,
            self.phase is ReadyLeafRoot ==> {
                &&& self.root_leaf@.len() > 0
                &&& MemtableBucket::strictly_sorted(self.root_leaf@)
            },
            self.phase is ReadyIndexRoot ==> {
                &&& self.root_children@.len() > 1
            },
            Self::descriptors_wf(self.root_children@),
            Self::descriptors_sorted(self.root_children@),
        ensures
            result is Some,
            result.unwrap().wf(),
            result.unwrap()@.wf(),
            result.unwrap()@.keys_strictly_sorted(),
            !(result.unwrap() is Auxiliary),
            self.phase is ReadyLeafRoot ==> result.unwrap() is Leaf,
            self.phase is ReadyIndexRoot ==> result.unwrap() is Index,
            self.phase is ReadyLeafRoot ==> result.unwrap()@
                == (BranchNode::Leaf {
                    keys: self.root_leaf@.map(
                        |i: int, entry: MemtableEntry| entry.key,
                    ),
                    msgs: self.root_leaf@.map(
                        |i: int, entry: MemtableEntry| entry.message,
                    ),
                }),
            self.phase is ReadyIndexRoot ==> result.unwrap()@
                == (BranchNode::Index {
                    pivots: descriptor_pivots(self.root_children@),
                    children: self.root_children@.map(
                        |i: int, descriptor: BranchChildDescriptor|
                            descriptor.addr@,
                    ),
                    aux_ptr: iopt_addr(aux_ptr),
                }),
    {
        match self.phase {
            BranchBulkPhase::ReadyLeafRoot => {
                let entries = self.root_leaf.clone();
                Some(leaf_from_entries(entries))
            },
            BranchBulkPhase::ReadyIndexRoot => {
                let node = index_from_descriptors(
                    &self.root_children,
                    0,
                    self.root_children.len(),
                    aux_ptr,
                );
                proof {
                    assert(node@->pivots
                        == descriptor_pivots(self.root_children@)) by {
                        assert_seqs_equal!(
                            node@->pivots,
                            descriptor_pivots(self.root_children@),
                            i => {}
                        );
                    }
                    assert(node@->children
                        == self.root_children@.map(
                            |i: int, descriptor: BranchChildDescriptor|
                                descriptor.addr@,
                        )) by {
                        assert_seqs_equal!(
                            node@->children,
                            self.root_children@.map(
                                |i: int, descriptor: BranchChildDescriptor|
                                    descriptor.addr@,
                            ),
                            i => {}
                        );
                    }
                    assert(node@ == (BranchNode::Index {
                        pivots: descriptor_pivots(self.root_children@),
                        children: self.root_children@.map(
                            |i: int, descriptor: BranchChildDescriptor|
                                descriptor.addr@,
                        ),
                        aux_ptr: iopt_addr(aux_ptr),
                    }));
                }
                Some(node)
            },
            _ => None,
        }
    }

    pub proof fn sealed_branch_receipt(
        &self,
        memtable: &MemtableImpl,
        root: Address,
        root_node: BranchNode,
        aux: Option<Address>,
        summary: Summary,
    ) -> (branch: LinkedBranch<Summary>)
        requires
            self.wf(memtable),
            self.phase is ReadyLeafRoot
                || self.phase is ReadyIndexRoot,
            root.wf(),
            root_node.wf(),
            !self.staged_nodes@.contains_key(root),
            self.phase is ReadyLeafRoot ==> {
                &&& aux is None
                &&& summary == set![root.au]
                &&& root_node == (BranchNode::Leaf {
                    keys: self.root_leaf@.map(
                        |i: int, entry: MemtableEntry| entry.key,
                    ),
                    msgs: self.root_leaf@.map(
                        |i: int, entry: MemtableEntry| entry.message,
                    ),
                })
            },
            self.phase is ReadyIndexRoot ==> {
                &&& aux is Some
                &&& aux.unwrap().wf()
                &&& aux.unwrap() != root
                &&& !self.staged_nodes@.contains_key(aux.unwrap())
                &&& root_node == (BranchNode::Index {
                    pivots: descriptor_pivots(self.root_children@),
                    children: self.root_children@.map(
                        |i: int, descriptor: BranchChildDescriptor|
                            descriptor.addr@,
                    ),
                    aux_ptr: Some(aux.unwrap()),
                })
            },
            addrs_closed(
                if aux is Some {
                    self.staged_nodes@.dom().insert(root)
                        .insert(aux.unwrap())
                } else {
                    self.staged_nodes@.dom().insert(root)
                },
                summary,
            ),
        ensures
            branch.root == root,
            branch.valid_sealed_branch(),
            branch.tight_disk_view_with_summary(),
            branch.get_summary() == summary,
            branch.i().i().map == self.source@,
            branch.disk_view.entries == if aux is Some {
                self.staged_nodes@.insert(root, root_node).insert(
                    aux.unwrap(),
                    BranchNode::Auxiliary(summary),
                )
            } else {
                self.staged_nodes@.insert(root, root_node)
            },
    {
        match self.phase {
            BranchBulkPhase::ReadyLeafRoot => {
                let receipt = make_leaf_receipt(root, root_node);
                leaf_entries_contents(self.root_leaf@, root_node);
                assert(receipt.pivot.i().map == self.source@);
                assert(receipt.nodes
                    == self.staged_nodes@.insert(root, root_node));
                let branch = finalize_leaf_seal(receipt);
                assert(branch.get_summary() == summary);
                branch
            },
            BranchBulkPhase::ReadyIndexRoot => {
                let unsealed = BranchNode::Index {
                    pivots: descriptor_pivots(self.root_children@),
                    children: self.root_children@.map(
                        |i: int, descriptor: BranchChildDescriptor|
                            descriptor.addr@,
                    ),
                    aux_ptr: None,
                };
                let receipt = make_index_receipt(
                    self.root_children@,
                    root,
                    unsealed,
                );
                assert(receipt.nodes
                    == self.staged_nodes@.insert(root, unsealed));
                assert(receipt.pivot.i().map == self.source@);
                let branch = finalize_index_seal(
                    receipt,
                    aux.unwrap(),
                    summary,
                );
                assert(branch.disk_view.entries
                    == self.staged_nodes@.insert(root, root_node).insert(
                        aux.unwrap(),
                        BranchNode::Auxiliary(summary),
                    ));
                branch
            },
            _ => {
                assert(false);
                arbitrary()
            },
        }
    }

    pub fn record_bulk_seal(
        &mut self,
        root: IAddress,
        root_node: Ghost<crate::allocation_layer::BranchTypes_v::BranchNode>,
        aux: Option<IAddress>,
        aux_node: Ghost<Option<crate::allocation_layer::BranchTypes_v::BranchNode>>,
    )
        requires
            old(self).phase is ReadyLeafRoot
                || old(self).phase is ReadyIndexRoot,
            root@.wf(),
            root_node@.wf(),
            !old(self).staged_nodes@.contains_key(root@),
            aux is Some <==> aux_node@ is Some,
            aux is Some ==> {
                &&& aux.unwrap()@.wf()
                &&& aux.unwrap() != root
                &&& aux_node@.unwrap() is Auxiliary
                &&& !old(self).staged_nodes@.contains_key(aux.unwrap()@)
            },
        ensures
            self.phase is Sealed,
            self.staged_nodes@ == if aux is Some {
                old(self).staged_nodes@
                    .insert(root@, root_node@)
                    .insert(aux.unwrap()@, aux_node@.unwrap())
            } else {
                old(self).staged_nodes@.insert(root@, root_node@)
            },
    {
        let ghost nodes = if aux is Some {
            self.staged_nodes@
                .insert(root@, root_node@)
                .insert(aux.unwrap()@, aux_node@.unwrap())
        } else {
            self.staged_nodes@.insert(root@, root_node@)
        };
        self.staged_nodes = Ghost(nodes);
        self.phase = BranchBulkPhase::Sealed;
    }
}

#[allow(dead_code)]
fn verify_balanced_partition_cases() {
    let one = BalancedPartition::new(1, 4);
    match one {
        Some(mut partition) => {
            let first = partition.next_size();
            let done = partition.next_size();
            proof {
                assert(done is None);
                assert(first is Some);
                assert(first.unwrap() <= 4);
            }
        },
        None => { proof { assert(false); } },
    }

    let uneven = BalancedPartition::new(9, 4);
    match uneven {
        Some(mut partition) => {
            let first = partition.next_size();
            let second = partition.next_size();
            let third = partition.next_size();
            proof {
                assert(first is Some);
                assert(second is Some);
                assert(third is Some);
                assert(first.unwrap() <= 4);
                assert(second.unwrap() <= 4);
                assert(third.unwrap() <= 4);
            }
        },
        None => { proof { assert(false); } },
    }
}

} // verus!
