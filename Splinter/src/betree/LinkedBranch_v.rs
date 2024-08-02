// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;

use builtin_macros::*;

use vstd::prelude::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::disk::GenericDisk_v::*;
use crate::betree::Utils_v::*;

// Refinement is a submodule of LinkedBranch so that it can access all internal details
// of LinkedBranch.
pub mod Refinement_v;

// A LinkedBranch represents a B+ tree where each node is stored at a different disk address.
// LinkedBranch refines to PivotBranch.
verus! {

pub enum SplitArg {
    SplitIndex{pivot: Key, pivot_index: int},
    SplitLeaf{pivot: Key}
}

impl SplitArg {
    pub open spec(checked) fn wf<N: BranchNode>(self, split_branch: LinkedBranch<N>) -> bool
        recommends split_branch.has_root()
    {
        let root = split_branch.root();
        match self {
            Self::SplitLeaf{pivot} => {
                &&& !root.is_index()
                &&& root.keys().len() == root.msgs().len()
                &&& 0 < Key::largest_lt(root.keys(), pivot) + 1 < root.keys().len()
            }
            Self::SplitIndex{pivot, pivot_index} => {
                &&& root.is_index()
                &&& root.children().len() == root.pivots().len() + 1
                &&& 0 <= pivot_index < root.pivots().len()
                &&& root.pivots()[pivot_index] == pivot
            }
        }
    }

    pub open spec(checked) fn get_pivot(self) -> Key
    {
        if self is SplitLeaf {
            self.arrow_SplitLeaf_pivot()
        } else {
            self.arrow_SplitIndex_pivot()
        }
    }
}

/// A LinkedBranch node. See PivotBranch_v::Node for more details.
/// A LinkedBranch node stores addresses of child nodes rather than recursively storing the child
/// nodes themselves as PivotBranch does.
pub enum Node {
    Leaf{keys: Seq<Key>, msgs: Seq<Message>},
    Index{pivots: Seq<Key>, children: Seq<Address>},
}

impl BranchNode for Node {
    open spec(checked) fn wf(&self) -> bool
    {
        match self {
            Self::Leaf{keys, msgs} => {
                &&& keys.len() > 0
                &&& keys.len() == msgs.len()
            }
            Self::Index{pivots, children} => {
                &&& pivots.len() == children.len() - 1
            }
        }
    }

    open spec(checked) fn is_index(&self) -> bool
    {
        self is Index
    }

    open spec(checked) fn keys(&self) -> Seq<Key>
    {
        self->keys
    }

    open spec(checked) fn msgs(&self) -> Seq<Message>
    {
        self->msgs
    }

    open spec(checked) fn pivots(&self) -> Seq<Key>
    {
        self->pivots
    }

    open spec(checked) fn children(&self) -> Seq<Address>
    {
        self->children
    }
}

/// A DiskView is, well, a view of the disk. We view the disk as a mapping from Addresses to LinkedBranch
/// nodes. For LinkedBranch we assume all addresses map to LinkedBranch nodes.
#[verifier::ext_equal]
pub struct DiskView<N> {
    pub entries: Map<Address, N>
}

impl<N: BranchNode> DiskView<N> {
    /// Ensures that all LinkedBranch nodes in the disk are well formed, and that
    /// all Addresses pointed to by all nodes are themselves valid addresses.
    pub open spec(checked) fn wf(self) -> bool
    {
        &&& self.entries_wf()
        &&& self.no_dangling_address()
    }

    /// Returns true iff all Nodes mapped by this DiskView are well formed.
    pub open spec(checked) fn entries_wf(self) -> bool
    {
        forall |addr| #[trigger] self.entries.contains_key(addr) ==> self.entries[addr].wf()
    }

    pub open spec(checked) fn valid_address(self, addr: Address) -> bool
    {
        self.entries.contains_key(addr)
    }

    pub open spec(checked) fn node_has_valid_child_address(self, node: N) -> bool
    {
        node.is_index() ==>
            forall |idx| 0 <= idx < node.children().len() ==> self.valid_address(#[trigger] node.children()[idx])
    }

    // disk is closed wrt to all the address in the nodes on disk
    pub open spec(checked) fn no_dangling_address(self) -> bool
    {
        forall |addr| #[trigger] self.entries.contains_key(addr) ==> self.node_has_valid_child_address(self.entries[addr])
    }

    pub open spec(checked) fn get(self, addr: Address) -> N
        recommends self.valid_address(addr)
    {
        self.entries[addr]
    }

    pub open spec(checked) fn representation(self) -> Set<Address>
    {
        self.entries.dom()
    }

    pub open spec(checked) fn agrees_with_disk(self, other: Self) -> bool
    {
        self.entries.agrees(other.entries)
    }

    pub open spec(checked) fn is_subset_of(self, other: Self) -> bool
    {
        self.entries <= other.entries
    }

    // The node at this address has child pointers that respect ranking
    pub open spec(checked) fn node_children_respects_rank(self, ranking: Ranking, addr: Address) -> bool
        recommends
            self.wf(),
            self.entries.contains_key(addr),
            ranking.contains_key(addr)
    {
        let node = self.entries[addr];
        forall |child_idx: int| #[trigger] node.valid_child_index(child_idx) ==> {
            &&& ranking.contains_key(node.children()[child_idx]) // ranking is closed
            &&& ranking[node.children()[child_idx]] < ranking[addr]
        }
    }

    // Together with NodeChildrenRespectsRank, this says that ranking is closed
    pub open spec(checked) fn valid_ranking(self, ranking: Ranking) -> bool
        recommends self.wf()
    {
        forall |addr| #[trigger] ranking.contains_key(addr) && self.entries.contains_key(addr) ==>
            self.node_children_respects_rank(ranking, addr)
    }

    pub open spec(checked) fn is_fresh(self, addrs: Set<Address>) -> bool
    {
        addrs.disjoint(self.entries.dom())
    }

    pub closed spec(checked) fn merge_disk(self, other: Self) -> Self
    {
        Self{entries: self.entries.union_prefer_right(other.entries)}
    }

    pub closed spec(checked) fn remove_disk(self, other: Self) -> Self
    {
        Self{entries: self.entries.remove_keys(other.entries.dom())}
    }

    pub open spec(checked) fn modify_disk(self, addr: Address, item: N) -> Self
    {
        Self{entries: self.entries.insert(addr, item)}
    }

    pub open spec(checked) fn same_except(self, other: Self, except: Set<Address>) -> bool
    {
        self.entries.remove_keys(except) == other.entries.remove_keys(except)
    }
}

pub open spec(checked) fn empty_disk() -> DiskView<Node>
{
    DiskView{entries: map!{}}
}

// A B+ tree represented by a disk that maps addresses to nodes and the address of its root node.
#[verifier::ext_equal]
pub struct LinkedBranch<N> {
    pub root: Address,
    pub disk_view: DiskView<N>
}

// The "public" facing interface of LinkedBranch is meant to be just limited to
// to the following functions: query, insert, grow, append, split.
// However due to how we put every file into its own module and how
// in this project we split out refinement proofs into separate files, this means we
// can't keep just these functions public, and instead need to make all LinkedBranch
// methods public so that the refinement proof module is able to access and reason about
// all spec fn's listed here.
impl LinkedBranch<Node> {
    pub open spec/*XXX (checked)*/ fn insert(self, key: Key, msg: Message, path: Path<Node>) -> Self
        recommends
            path.valid(),
            path.branch == self,
            path.key == key,
            path.target().root() is Leaf,
    {
        // Need path.valid() ==> path.target().has_root() && path.target().wf() to restore checked
        path.substitute(path.target().insert_leaf(key, msg))
    }

    pub open spec/*XXX (checked)*/ fn insert_leaf(self, key: Key, msg: Message) -> Self
        recommends
            self.wf(),
            self.root() is Leaf,
    {
        // Need largest_lte ensures to restore checked
        let node = self.root();
        let llte = Key::largest_lte(node->keys, key);
        let new_node =
            if 0 <= llte && node->keys[llte] == key {
                Node::Leaf{keys: node->keys, msgs: node->msgs.update(llte, msg)}
            } else {
                Node::Leaf{keys: node->keys.insert(llte+1, key), msgs: node->msgs.insert(llte+1, msg)}
            };
        Self{root: self.root, disk_view: self.disk_view.modify_disk(self.root, new_node)}
    }

    pub open spec(checked) fn grow(self, addr: Address) -> Self
        recommends
            self.wf(),
            self.disk_view.is_fresh(set!{addr})
    {
        let new_root = Node::Index{pivots: seq![], children: seq![self.root]};
        let new_disk_view = self.disk_view.modify_disk(addr, new_root);
        Self{root: addr, disk_view: new_disk_view}
    }

    pub open spec/*XXX (checked)*/ fn append(self, keys: Seq<Key>, msgs: Seq<Message>, path: Path<Node>) -> Self
        recommends
            path.valid(),
            path.branch == self,
            keys.len() > 0,
            keys.len() == msgs.len(),
            Key::is_strictly_sorted(keys),
            path.target().root() is Leaf,
            Key::lt(path.target().root()->keys.last(), keys[0]),
            path.key == keys[0],
            path.path_equiv(keys.last()),
    {
        // Need path.valid() ==> path.target().wf() to restore checked
        path.substitute(path.target().append_leaf(keys, msgs))
    }

    pub open spec(checked) fn append_leaf(self, new_keys: Seq<Key>, new_msgs: Seq<Message>) -> Self
        recommends
            self.wf(),
            self.root() is Leaf,
            new_keys.len() > 0,
            new_keys.len() == new_msgs.len(),
            Key::is_strictly_sorted(new_keys),
            Key::lt(self.root()->keys.last(), new_keys[0]),
    {
        let new_node = Node::Leaf{ keys: self.root()->keys + new_keys, msgs: self.root()->msgs + new_msgs };
        let new_disk_view = self.disk_view.modify_disk(self.root, new_node);
        Self{root: self.root, disk_view: new_disk_view}
    }

    pub open spec(checked) fn split(self, addr: Address, path: Path<Node>, split_arg: SplitArg) -> Self
        recommends
            path.valid(),
            path.branch == self,
            path.key == split_arg.get_pivot(),
            path.target().can_split_child_of_index(split_arg, addr),
            self.disk_view.is_fresh(set!{addr})
    {
        path.substitute(path.target().split_child_of_index(split_arg, addr))
    }

    pub open spec/*XXX (checked)*/ fn split_child_of_index(self, split_arg: SplitArg, new_child_addr: Address) -> Self
        recommends self.can_split_child_of_index(split_arg, new_child_addr)
    {
        // Need route ensures to restore checked
        let pivot = split_arg.get_pivot();
        let child_idx = self.root().route(pivot) + 1;
        let (left_branch, right_branch) = self.child_at_idx(child_idx).split_node(split_arg, new_child_addr);
        let new_root = Node::Index{
            pivots: self.root()->pivots.insert(child_idx, pivot),
            children: self.root()->children.insert(child_idx + 1, new_child_addr)
        };
        let new_disk_view = self.disk_view
            .merge_disk(left_branch.disk_view)
            .modify_disk(self.root, new_root);
        Self{root: self.root, disk_view: new_disk_view}
    }

    pub open spec(checked) fn split_node(self, split_arg: SplitArg, right_root_addr: Address) -> (Self, Self)
        recommends
            self.has_root(),
            split_arg.wf(self),
            self.disk_view.is_fresh(set!{right_root_addr})
    {
        if (self.root() is Leaf) {
            self.split_leaf(split_arg, right_root_addr)
        } else {
            self.split_index(split_arg, right_root_addr)
        }
    }

    pub open spec(checked) fn split_leaf(self, split_arg: SplitArg, right_root_addr: Address) -> (Self, Self)
        recommends
            self.has_root(),
            split_arg.wf(self),
            self.disk_view.is_fresh(set!{right_root_addr})
    {
        let pivot = split_arg.get_pivot();
        let split_index = Key::largest_lt(self.root()->keys, pivot) + 1;
        let left_root = Node::Leaf{
            keys: self.root()->keys.take(split_index),
            msgs: self.root()->msgs.take(split_index)
        };
        let right_root = Node::Leaf{
            keys: self.root()->keys.skip(split_index),
            msgs: self.root()->msgs.skip(split_index)
        };
        let new_disk_view = self.disk_view
            .modify_disk(self.root, left_root)
            .modify_disk(right_root_addr, right_root);
        let left_leaf = Self{root: self.root, disk_view: new_disk_view};
        let right_leaf = Self{root: right_root_addr, disk_view: new_disk_view};
        (left_leaf, right_leaf)
    }

    pub open spec/*XXX (checked)*/ fn split_index(self, split_arg: SplitArg, right_root_addr: Address) -> (Self, Self)
        recommends
            self.has_root(),
            split_arg.wf(self),
            self.disk_view.is_fresh(set!{right_root_addr})
    {
        // Possibly lexical match failure for sub_index recommends
        let pivot_index = split_arg->pivot_index;
        let left_root = self.sub_index(0, pivot_index + 1);
        let right_root = self.sub_index(pivot_index + 1, self.root()->children.len() as int);
        let new_disk_view = self.disk_view
            .modify_disk(self.root, left_root)
            .modify_disk(right_root_addr, right_root);
        let left_index = Self{root: self.root, disk_view: new_disk_view};
        let right_index = Self{root: right_root_addr, disk_view: new_disk_view};
        (left_index, right_index)
    }

    pub open spec(checked) fn sub_index(self, from: int, to: int) -> Node
        recommends
            self.has_root(),
            self.root() is Index,
            self.root()->children.len() == self.root()->pivots.len() + 1,
            0 <= from < to <= self.root()->children.len()
    {
        Node::Index{
            pivots: self.root()->pivots.subrange(from, to-1),
            children: self.root()->children.subrange(from, to)
        }
    }
}

impl<N: BranchNode> LinkedBranch<N> {
    pub closed spec/*XXX (checked)*/ fn query(self, key: Key) -> Message
    {
        // Need route ensures to satisfy query_internal when to restore checked
        if self.acyclic() {
            self.query_internal(key, self.the_ranking())
        } else {
            Message::Update{delta: nop_delta()}
        }
    }

    pub open spec(checked) fn wf(self) -> bool
    {
        &&& self.disk_view.wf()
        &&& self.has_root()
    }

    pub open spec(checked) fn has_root(self) -> bool
    {
        self.disk_view.valid_address(self.root)
    }

    pub open spec(checked) fn root(self) -> N
        recommends self.has_root()
    {
        self.disk_view.get(self.root)
    }

    pub open spec(checked) fn get_rank(self, ranking: Ranking) -> nat
        recommends self.wf()
    {
        if ranking.contains_key(self.root) { ranking[self.root] + 1 } else { 0 }
    }

    pub open spec(checked) fn valid_ranking(self, ranking: Ranking) -> bool
        recommends self.wf()
    {
        &&& self.disk_view.valid_ranking(ranking)
        &&& ranking.contains_key(self.root) // ranking covers tree from this root
    }

    pub open spec(checked) fn the_ranking(self) -> Ranking
        recommends self.acyclic()
    {
        let ranking = choose |ranking| self.valid_ranking(ranking);
        ranking
    }

    pub open spec(checked) fn acyclic(self) -> bool
    {
        &&& self.wf()
        &&& exists |ranking| self.valid_ranking(ranking)
    }

    pub open spec(checked) fn keys_strictly_sorted_internal(self, ranking: Ranking) -> bool
        recommends
            self.wf(),
            self.valid_ranking(ranking),
        decreases self.get_rank(ranking),
        when self.wf() && self.valid_ranking(ranking)
    {
        self.root().keys_strictly_sorted()
        && (self.root().is_index() ==> (
            forall |i| #[trigger] self.root().valid_child_index(i)
                ==> self.child_at_idx(i).keys_strictly_sorted_internal(ranking)
        ))
    }

    pub open spec(checked) fn all_keys_in_range(self) -> bool
        recommends self.acyclic()
    {
        self.all_keys_in_range_internal(self.the_ranking())
    }

    pub open spec(checked) fn all_keys_in_range_internal(self, ranking: Ranking) -> bool
        recommends
            self.wf(),
            self.valid_ranking(ranking),
        decreases self.get_rank(ranking)//, 1int
        when self.wf() && self.valid_ranking(ranking)
    {
        self.root().is_index() ==> {
            &&& (forall |i| #[trigger] self.root().valid_child_index(i) ==> self.child_at_idx(i).all_keys_in_range_internal(ranking))
            &&& (forall |i| 0 <= i < self.root().children().len() - 1 ==> self.all_keys_below_bound(i, ranking))
            &&& (forall |i| 0 < i < self.root().children().len() ==> self.all_keys_above_bound(i, ranking))
        }
    }

    pub open spec(checked) fn map_all_keys(self, ranking: Ranking) -> Seq<Set<Key>>
        recommends
            self.wf(),
            self.valid_ranking(ranking),
            self.root().is_index(),
        decreases
            self.get_rank(ranking),
            0int,
        when {
            &&& self.wf()
            &&& self.valid_ranking(ranking)
        }
    {
        self.root().children().map(|i: int, addr: Address|
            if self.root().valid_child_index(i) {
                self.child_at_idx(i).all_keys(ranking)
            } else {
                set!{} // dummy value 
            })
    }

    // Union of sets of all keys of children[i..]
    pub open spec(checked) fn children_keys(self, ranking: Ranking) -> Set<Key>
        recommends
            self.wf(),
            self.valid_ranking(ranking),
            self.root().is_index(),
        decreases
            self.get_rank(ranking),
            1int,
    {
        union_seq_of_sets(self.map_all_keys(ranking))
    }

    pub open spec(checked) fn all_keys(self, ranking: Ranking) -> Set<Key>
        recommends
            self.wf(),
            self.valid_ranking(ranking)
        decreases self.get_rank(ranking), 2int
    {
        // TODO(x9du): the match doesn't satisfy the self.root() is Index recommends
        // but the if does?
        if !self.root().is_index() {
            self.root().keys().to_set()
        } else {
            let pivot_keys = self.root().pivots().to_set();
            let index_keys = self.children_keys(ranking);
            pivot_keys + index_keys
        }
        // match self.root() {
        //     Node::Leaf{keys, msgs} => {
        //         keys.to_set()
        //     }
        //     Node::Index{pivots, children} => {
        //         let pivot_keys = pivots.to_set();
        //         let index_keys = self.children_keys(ranking);
        //         pivot_keys + index_keys
        //     }
        // }
    }

    pub open spec/*XXX (checked)*/ fn all_keys_below_bound(self, i: int, ranking: Ranking) -> bool
        recommends
            self.wf(),
            self.valid_ranking(ranking),
            self.root().is_index(),
            0 <= i < self.root().pivots().len()
        decreases self.get_rank(ranking)
    {
        // Need valid ranking implies child has valid ranking to restore checked
        forall |key| self.child_at_idx(i).all_keys(ranking).contains(key) ==> Key::lt(key, self.root().pivots()[i])
    }

    pub open spec/*XXX (checked)*/ fn all_keys_above_bound(self, i: int, ranking: Ranking) -> bool
        recommends
            self.wf(),
            self.valid_ranking(ranking),
            self.root().is_index(),
            0 <= i - 1 < self.root().pivots().len()
        decreases self.get_rank(ranking)
    {
        // Need valid ranking implies child has valid ranking to restore checked
        forall |key| self.child_at_idx(i).all_keys(ranking).contains(key) ==> #[trigger] Key::lte(self.root().pivots()[i-1], key)
    }

    pub open spec(checked) fn child_at_idx(self, i: int) -> Self
        recommends
            self.has_root(),
            self.root().valid_child_index(i)
    {
        Self{root: self.root().children()[i], disk_view: self.disk_view}
    }

    pub open spec(checked) fn representation(self) -> Set<Address>
        recommends self.acyclic()
    {
        self.reachable_addrs_using_ranking(self.the_ranking())
    }

    pub open spec(checked) fn reachable_addrs_using_ranking(self, ranking: Ranking) -> Set<Address>
        recommends
            self.wf(),
            self.valid_ranking(ranking)
        decreases self.get_rank(ranking), 2int
    {
        if !self.has_root() {
            set!{}
        } else if !self.root().is_index() {
            set!{self.root}
        } else {
            let subtree_addrs = self.children_reachable_addrs_using_ranking(ranking);
            union_seq_of_sets(subtree_addrs).insert(self.root)
        }
    }

    pub open spec(checked) fn children_reachable_addrs_using_ranking(self, ranking: Ranking) -> Seq<Set<Address>>
        recommends
            self.wf(),
            self.valid_ranking(ranking),
            self.root().is_index(),
        decreases self.get_rank(ranking), 1int
    {
        Seq::new(self.root().children().len(), |i: int| self.child_reachable_addrs_using_ranking(ranking, i))
    }

    pub open spec(checked) fn child_reachable_addrs_using_ranking(self, ranking: Ranking, i: int) -> Set<Address>
        recommends
            self.wf(),
            self.valid_ranking(ranking),
            self.root().is_index(),
            0 <= i < self.root().children().len()
        decreases self.get_rank(ranking), 0int
        when {
            &&& self.wf()
            &&& self.valid_ranking(ranking)
            &&& self.root().valid_child_index(i)
        }
    {
        self.child_at_idx(i).reachable_addrs_using_ranking(ranking)
    }

    pub open spec(checked) fn tight_disk_view(self) -> bool
    {
        self.acyclic() ==> self.representation() == self.disk_view.representation()
    }

    pub open spec/*XXX (checked)*/ fn query_internal(self, key: Key, ranking: Ranking) -> Message
        recommends
            self.wf(),
            self.valid_ranking(ranking),
        decreases self.get_rank(ranking)
        when {
            self.root().is_index() ==> {
                let r = self.root().route(key);
                &&& self.wf()
                &&& self.valid_ranking(ranking)
                &&& self.root().valid_child_index(r + 1)
            }
        }
    {
        // Need route and child_at_idx ensures to restore checked
        let node = self.root();
        let r = node.route(key);
        if !node.is_index() {
            if r >= 0 && node.keys()[r] == key {
                node.msgs()[r]
            } else {
                Message::Update{delta: nop_delta()}
            }
        } else {
            self.child_at_idx(r+1).query_internal(key, ranking)
        }
    }

    pub open spec/*XXX (checked)*/ fn can_split_child_of_index(self, split_arg: SplitArg, new_child_addr: Address) -> bool
    {
        // Need route ensures to restore checked
        &&& self.has_root()
        &&& self.root().is_index()
        &&& self.root().wf()
        &&& {
            let child_idx = self.root().route(split_arg.get_pivot()) + 1;
            &&& self.child_at_idx(child_idx).has_root()
            &&& split_arg.wf(self.child_at_idx(child_idx))
            &&& self.child_at_idx(child_idx).disk_view.is_fresh(set!{new_child_addr})
            }
    }
}

pub open spec(checked) fn empty_linked_branch(root: Address) -> LinkedBranch<Node>
{
    LinkedBranch{root: root, disk_view: empty_disk().modify_disk(root, Node::Leaf{keys: seq![], msgs: seq![]})}
}

#[verifier::ext_equal]
pub struct Path<N> {
    pub branch: LinkedBranch<N>,
    pub key: Key,
    pub depth: nat
}

impl<N: BranchNode> Path<N> {
    pub open spec/*XXX (checked)*/ fn subpath(self) -> Self
        recommends
            0 < self.depth,
            self.branch.wf(),
            self.branch.root().is_index(),
    {
        // Need route ensures to restore checked
        let r = self.branch.root().route(self.key) + 1;
        Self{branch: self.branch.child_at_idx(r), key: self.key, depth: (self.depth - 1) as nat}
    }

    pub open spec(checked) fn valid(self) -> bool
        decreases self.depth
    {
        &&& self.branch.wf()
        &&& 0 < self.depth ==> self.branch.root().is_index()
        &&& 0 < self.depth ==> self.subpath().valid()
    }

    pub open spec(checked) fn target(self) -> LinkedBranch<N>
        recommends self.valid()
        decreases self.depth
    {
        if 0 == self.depth {
            self.branch
        } else {
            self.subpath().target()
        }
    }

    pub open spec(checked) fn substitute(self, replacement: LinkedBranch<N>) -> LinkedBranch<N>
        recommends self.valid()
    {
        LinkedBranch{root: self.branch.root, disk_view: replacement.disk_view}
    }

    pub open spec(checked) fn path_equiv(self, other_key: Key) -> bool
        recommends self.valid()
        decreases self.depth, 1int
    {
        &&& self.branch.root().route(self.key) == self.branch.root().route(other_key)
        &&& 0 < self.depth ==> self.subpath().path_equiv(other_key)
    }
}

}