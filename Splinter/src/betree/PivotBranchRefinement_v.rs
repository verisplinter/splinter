// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::prelude::*;
//use vstd::prelude_macros::*;

use vstd::prelude::*;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::Message;
use crate::betree::Buffer_v::{Buffer, SimpleBuffer, all_keys};
use crate::betree::Utils_v::{lemma_set_subset_of_union_seq_of_sets, lemma_union_seq_of_sets_contains, lemma_union_seq_of_sets_finite, union_seq_of_sets};
use crate::betree::PivotBranch_v::{Node, Path, SplitArg};

verus! {

broadcast use Node::route_ensures;

impl Node {
    // Takes in a btree node and returns the buffer abstraction
    pub open spec(checked) fn i(self) -> SimpleBuffer
        recommends self.wf()
        decreases self
        // TODO(x9du): this when condition is kind of annoying to prove
        // Usually route_ensures & assert(self.wf()) works
        when self is Index ==> forall |key| 0 <= #[trigger] self.route(key) + 1 < self->children.len()
    {
        match self {
            Node::Leaf{keys, msgs} => {
                SimpleBuffer{map: Map::new(|key| keys.contains(key), |key| msgs[self.route(key)])}
            }
            Node::Index{pivots, children} => {
                SimpleBuffer{map: Map::new(
                    // TODO(x9du): adding triggers in here causes ungraceful dump
                    |key| children[self.route(key) + 1].i().map.contains_key(key),
                    |key| children[self.route(key) + 1].i().map[key]
                )}
            }
        }
    }

    pub open spec(checked) fn append_via_insert(self, keys: Seq<Key>, msgs: Seq<Message>, path: Path) -> Node
        recommends
            path.valid(),
            path.node == self,
            keys.len() > 0,
            keys.len() == msgs.len(),
            Key::is_strictly_sorted(keys),
            path.target() is Leaf,
            path.target().wf(), // comes from path.valid(), but not having this here causes recommendation not met
            Key::lt(path.target()->keys.last(), keys[0]),
            path.key == keys[0],
            path.path_equiv(keys.last()),
    {
        keys.zip_with(msgs).fold_left_alt(self, |node: Node, pair: (Key, Message)|
            node.insert(pair.0, pair.1, Path{node: node, key: pair.0, depth: path.depth}))
    }
}

pub proof fn lemma_route_to_end(node: Node, key: Key)
    requires
        node.wf(),
        Key::lte(node.get_keys_or_pivots().last(), key),
    ensures
        node.route(key) == node.get_keys_or_pivots().len() - 1,
{
    let r = node.route(key);
    let s = node.get_keys_or_pivots();
    if r < s.len() - 1 {
    }
}

pub proof fn lemma_key_lte_implies_route_lte(node: Node, key1: Key, key2: Key)
    requires
        node.wf(),
        Key::lte(key1, key2),
    ensures
        node.route(key1) <= node.route(key2)
{
    let s = if node is Leaf { node->keys } else { node->pivots };
    Key::strictly_sorted_implies_sorted(s);
    Key::largest_lte_ensures(s, key1, Key::largest_lte(s, key1));
    Key::largest_lte_ensures(s, key2, Key::largest_lte(s, key2));
    // Proof by contradiction
    if (Key::largest_lte(s, key1) > Key::largest_lte(s, key2)) {
        assert(Key::lt(key2, s[Key::largest_lte(s, key1)])); // trigger
    }
}

pub open spec(checked) fn map_all_keys(children: Seq<Node>) -> Seq<Set<Key>>
{
    children.map(|i, child: Node| child.all_keys())
}

pub open spec(checked) fn union_all_keys(children: Seq<Node>) -> Set<Key>
{
    union_seq_of_sets(map_all_keys(children))
}

pub proof fn lemma_union_all_keys_finite(children: Seq<Node>)
    requires forall |i| 0 <= i < children.len() ==> (#[trigger] children[i]).all_keys().finite()
    ensures union_all_keys(children).finite()
{
    lemma_union_seq_of_sets_finite(map_all_keys(children));
}

pub proof fn lemma_children_keys_equivalence(node: Node)
    requires node is Index
    ensures node.children_keys() == union_all_keys(node->children)
{
    let children = node->children;

    assert forall |key| #[trigger] node.children_keys().contains(key)
    implies union_all_keys(children).contains(key) by
    {
        let i = choose |i| 0 <= i < children.len()
            && (#[trigger] children[i]).all_keys().contains(key);
        assert(map_all_keys(children)[i].contains(key)); // trigger
        lemma_set_subset_of_union_seq_of_sets(map_all_keys(children), key);
    }

    assert forall |key| union_all_keys(children).contains(key)
    implies #[trigger] node.children_keys().contains(key) by
    {
        lemma_union_seq_of_sets_contains(map_all_keys(children), key);
    }

}

pub proof fn lemma_wf_implies_all_keys_finite_and_not_empty(node: Node)
    requires
        node.wf(),
    ensures
        node.all_keys().finite(),
        !node.all_keys().is_empty(),
    decreases node,
{
    if node is Leaf {
        assert(node.all_keys().contains(node->keys[0])); // trigger
    } else {
        let pivot_keys = node->pivots.to_set();
        lemma_children_keys_equivalence(node);
        assert forall |i| 0 <= i < node->children.len()
        implies (#[trigger] node->children[i].all_keys()).finite() by {
            lemma_wf_implies_all_keys_finite_and_not_empty(node->children[i]);
        }
        lemma_union_all_keys_finite(node->children);

        lemma_wf_implies_all_keys_finite_and_not_empty(node->children[0]);
        let key = choose |key| node->children[0].all_keys().contains(key);
    }
}

// Proves that insert() on a leaf node refines (as well as other useful and
// guaranteed properties).
pub proof fn lemma_insert_leaf_is_correct(node: Node, key: Key, msg: Message)
    requires
        node is Leaf,
        node.wf()
    ensures
        node.insert_leaf(key, msg).i() == (SimpleBuffer{map: node.i().map.insert(key, msg)}),
        node.insert_leaf(key, msg).all_keys() == node.all_keys().insert(key)
{
    let post = node.insert_leaf(key, msg);
    let r_key = node.route(key);
    assert(post.wf());
    assert(-1 <= r_key < node->keys.len());

    if 0 <= r_key && node->keys[r_key] == key {
        assert(post.i().map =~~= node.i().map.insert(key, msg));
        assert(post.all_keys() =~~= node.all_keys().insert(key));
    } else {
        assert forall |k| node.i().map.insert(key, msg).contains_key(k)
        implies #[trigger] post.i().map.contains_key(k) by {
            if k == key {
                assert(0 <= r_key + 1 < post->keys.len());
                assert(post->keys[r_key+1] == k);
            } else {
                let i = node->keys.index_of(k);
                assert(0 <= i < post->keys.len());
                assert(0 <= i+1 < post->keys.len());
                if i < r_key + 1 {
                    assert(post->keys[i] == k);
                } else if i >= r_key + 1 {
                    assert(post->keys[i+1] == k);
                }
            }
        }

        // TODO(x9du): create a lemma for post_r == r / post_r == r+1 proofs cuz this is getting repetitive...

        assert forall |k| post.i().map.contains_key(k)
        implies #[trigger] post.i().map[k] == node.i().map.insert(key, msg)[k] by {
            assert(node.i().map.insert(key, msg).contains_key(k));

            if k != key {
                let r = node.route(k);
                let post_r = post.route(k);
                assert(0 <= post_r < post->msgs.len());
                assert(0 <= r + 1 < post->msgs.len());
                assert(0 <= r < node->msgs.len());
                assert(post->keys.len() == post->msgs.len());
                assert(node.i().map.contains_key(k));
                Key::strictly_sorted_implies_sorted(post->keys);
                if r <= r_key {
                    assert(post->msgs[r] == node->msgs[r]);
                    assert(post_r == r) by {
                        if (r >= 0) {
                            assert(Key::lte(node->keys[r], k));
                            assert(node->keys[r] == post->keys[r]);
                        }
                        if (r < post->keys.len() - 1) {
                            assert(Key::lt(k, post->keys[r+1])) by {
                                if (r < r_key) {
                                    assert(Key::lt(k, node->keys[r+1]));
                                    assert(node->keys[r+1] == post->keys[r+1]);
                                } else {
                                    assert(Key::lte(node->keys[r], key));
                                    assert(node->keys[r] == k);
                                    assert(key == post->keys[r+1]);
                                }
                            }
                        }
                        Key::largest_lte_is_lemma(post->keys, k, r);
                    }
                    assert(post->msgs[post_r] == node->msgs[r]);
                } else {
                    assert(post->msgs[r+1] == node->msgs[r]);
                    assert(post_r == r + 1) by {
                        if (r+1 >= 0) {
                            assert(Key::lte(node->keys[r], k));
                            assert(node->keys[r] == post->keys[r+1]);
                        }
                        if (r+1 < post->keys.len() - 1) {
                            assert(Key::lt(k, node->keys[r+1]));
                            assert(node->keys[r+1] == post->keys[r+2]);
                        }
                        Key::largest_lte_is_lemma(post->keys, k, r+1);
                    }
                    assert(post->msgs[post_r] == node->msgs[r]);
                }
            }
        }

        assert(post.i().map =~~= node.i().map.insert(key, msg));
        assert(post.all_keys() =~~= node.all_keys().insert(key));
    }
}

pub proof fn lemma_sub_index_preserves_wf(node: Node, from: int, to: int)
    requires
        node.wf(),
        node is Index,
        0 <= from < to <= node->children.len()
    ensures node.sub_index(from, to).wf()
{
    let sub = node.sub_index(from, to);

    assert(forall |i| 0 <= i < sub->children.len() ==>
        0 <= from + i < node->children.len() && sub->children[i] == node->children[from + i]);
    assert(forall |i| 0 <= i < sub->pivots.len() ==>
        0 <= from + i < node->pivots.len() && sub->pivots[i] == node->pivots[from + i]);

    assert forall |i| 0 <= i < sub->children.len() - 1 implies sub.all_keys_below_bound(i) by {
        assert(node.all_keys_below_bound(from + i)); // trigger
    }

    assert forall |i| 0 < i < sub->children.len() implies sub.all_keys_above_bound(i) by {
        assert(node.all_keys_above_bound(from + i)); // trigger
        assert(sub->pivots[i-1] == node->pivots[from + i - 1]); // trigger
    }
}

pub proof fn lemma_split_node_preserves_wf(node: Node, split_arg: SplitArg)
    requires
        node.wf(),
        split_arg.wf(node)
    ensures ({
        let (left_node, right_node) = node.split_node(split_arg);
        &&& left_node.wf()
        &&& right_node.wf()
    })
{
    if node is Index {
        let pivot_index = split_arg->pivot_index;
        lemma_sub_index_preserves_wf(node, 0, pivot_index + 1);
        lemma_sub_index_preserves_wf(node, pivot_index + 1, node->children.len() as int);
    }
}

pub proof fn lemma_split_leaf_interpretation(old_leaf: Node, split_arg: SplitArg)
    requires
        old_leaf.wf(),
        old_leaf is Leaf,
        split_arg.wf(old_leaf)
    ensures ({
        let (left_leaf, right_leaf) = old_leaf.split_leaf(split_arg);
        &&& left_leaf.wf()
        &&& right_leaf.wf()
        &&& old_leaf.i().map == Key::map_pivoted_union(left_leaf.i().map, split_arg.get_pivot(), right_leaf.i().map)
    })
{
    let (left_leaf, right_leaf) = old_leaf.split_leaf(split_arg);
    lemma_split_node_preserves_wf(old_leaf, split_arg);
    assert(left_leaf.wf() && right_leaf.wf());
    let union_map = Key::map_pivoted_union(left_leaf.i().map, split_arg.get_pivot(), right_leaf.i().map);
    let pivot = split_arg.get_pivot();
    let split_index = Key::largest_lt(old_leaf->keys, pivot) + 1;

    assert forall |key| #[trigger] old_leaf.i().map.contains_key(key)
    implies union_map.contains_key(key) && old_leaf.i().map[key] == union_map[key] by {
        assert(old_leaf->keys.contains(key));
        let i = old_leaf->keys.index_of(key);
        let new_leaf = if i < split_index { left_leaf } else { right_leaf };
        let i_new = if i < split_index { i } else { i - split_index };
        assert(0 <= i_new < new_leaf->keys.len() == new_leaf->msgs.len());

        Key::strictly_sorted_implies_sorted(old_leaf->keys);
        Key::largest_lt_ensures(old_leaf->keys, pivot, split_index - 1);
        if i < split_index {
            assert(Key::lt(key, pivot));
        } else {
            assert(Key::lte(pivot, key));
        }

        assert(old_leaf->keys[i] == new_leaf->keys[i_new]);

        // Subgoal 1
        assert(union_map.contains_key(key));

        let r = old_leaf.route(key);
        assert(0 <= r < old_leaf->keys.len());
        assert(old_leaf->keys[r] == key);
        Key::strictly_sorted_implies_unique(old_leaf->keys);
        assert(r == i);

        let r_new = new_leaf.route(key);
        assert(0 <= r_new < new_leaf->keys.len());
        assert(new_leaf->keys[r_new] == key);
        Key::strictly_sorted_implies_unique(new_leaf->keys);
        assert(r_new == i_new);
        assert(old_leaf->msgs[i] == new_leaf->msgs[i_new]);
        assert(old_leaf.i().map[key] == new_leaf.i().map[key]);
        assert(union_map[key] == new_leaf.i().map[key]);
    }

    assert(old_leaf.i().map =~~= union_map);
}

pub proof fn lemma_split_index_interpretation(old_index: Node, split_arg: SplitArg)
    requires
        old_index.wf(),
        old_index is Index,
        split_arg.wf(old_index),
        ({
            let (left_index, right_index) = old_index.split_index(split_arg);
            &&& left_index.wf()
            &&& right_index.wf()
        })
    ensures ({
        let (left_index, right_index) = old_index.split_index(split_arg);
        old_index.i().map == Key::map_pivoted_union(left_index.i().map, split_arg.get_pivot(), right_index.i().map)
    })
{
    let (left_index, right_index) = old_index.split_index(split_arg);
    lemma_split_node_preserves_wf(old_index, split_arg);
    assert(left_index.wf() && right_index.wf());
    let pivot = split_arg.get_pivot();
    let union_map = Key::map_pivoted_union(left_index.i().map, pivot, right_index.i().map);
    let pivot_index = split_arg->pivot_index;

    assert forall |key|
    (#[trigger] old_index.i().map.dom().contains(key) ==>
        union_map.dom().contains(key) && old_index.i().map[key] == union_map[key])
    && (union_map.dom().contains(key) ==> old_index.i().map.dom().contains(key)) by {

        let r = old_index.route(key);
        assert(0 <= r+1 < old_index->children.len());
        assert(old_index->children[r+1].wf());
        Key::strictly_sorted_implies_sorted(old_index->pivots);
        if r+1 <= pivot_index {
            assert(0 <= r+1 < left_index->children.len());
            assert(left_index->children[r+1] == old_index->children[r+1]);
            let left_r = left_index.route(key);
            Key::largest_lte_subrange(old_index->pivots, key, r, 0, pivot_index, left_r);
            assert(left_r == r);
        } else {
            assert(0 <= r + 1 - (pivot_index + 1) < right_index->children.len());
            assert(right_index->children[r + 1 - (pivot_index + 1)] == old_index->children[r+1]);
            let right_r = right_index.route(key);
            Key::largest_lte_subrange(old_index->pivots, key, r,
                pivot_index + 1, old_index->children.len() as int - 1, right_r);
            assert(right_r == r - (pivot_index + 1));
        }

        if old_index.i().map.dom().contains(key) {
            assert(old_index->children[r+1].i().map.contains_key(key));
            if r+1 <= pivot_index {
                assert(left_index.i().map.contains_key(key));
                assert(Key::lt(key, pivot));
            } else {
                assert(right_index.i().map.contains_key(key));
                assert(Key::lte(pivot, key));
            }
            assert(union_map.dom().contains(key));
            assert(old_index.i().map[key] == union_map[key]);
        }

        if union_map.dom().contains(key) {
            if Key::lt(key, pivot) {
                assert(r < pivot_index) by {
                    if r >= pivot_index {
                        assert(Key::lte(pivot, key));
                    }
                }
                assert(left_index.i().map.contains_key(key));
            } else {
                assert(r+1 > pivot_index);
                assert(right_index.i().map.contains_key(key));
            }
            assert(old_index->children[r+1].i().map.contains_key(key));
            assert(old_index.i().map.dom().contains(key));
        }
    }

    assert(old_index.i().map =~~= union_map);
}

pub proof fn lemma_split_node_interpretation(old_node: Node, split_arg: SplitArg)
    requires
        old_node.wf(),
        split_arg.wf(old_node),
        ({
            let (left_node, right_node) = old_node.split_node(split_arg);
            &&& left_node.wf()
            &&& right_node.wf()
        })
    ensures ({
        let (left_node, right_node) = old_node.split_node(split_arg);
        old_node.i().map == Key::map_pivoted_union(left_node.i().map, split_arg.get_pivot(), right_node.i().map)
    })
{
    if (old_node is Leaf) {
        lemma_split_leaf_interpretation(old_node, split_arg);
    } else {
        lemma_split_index_interpretation(old_node, split_arg);
    }
}

pub proof fn lemma_split_leaf_all_keys(old_leaf: Node, split_arg: SplitArg)
    requires
        old_leaf.wf(),
        old_leaf is Leaf,
        split_arg.wf(old_leaf),
        ({
            let (left_leaf, right_leaf) = old_leaf.split_leaf(split_arg);
            &&& left_leaf.wf()
            &&& right_leaf.wf()
        })
    ensures ({
        let (left_leaf, right_leaf) = old_leaf.split_leaf(split_arg);
        &&& old_leaf.all_keys() == left_leaf.all_keys() + right_leaf.all_keys()
        &&& forall |key| left_leaf.all_keys().contains(key)
            <==> (Key::lt(key, split_arg.get_pivot()) && old_leaf.all_keys().contains(key))
        &&& forall |key| right_leaf.all_keys().contains(key)
            <==> (Key::lte(split_arg.get_pivot(), key) && old_leaf.all_keys().contains(key))
    })
{
    let (left_leaf, right_leaf) = old_leaf.split_leaf(split_arg);
    let pivot = split_arg.get_pivot();

    assert(old_leaf->keys == left_leaf->keys + right_leaf->keys);
    assert(old_leaf.all_keys() == left_leaf.all_keys() + right_leaf.all_keys());

    let split_index = Key::largest_lt(old_leaf->keys, pivot) + 1;
    Key::strictly_sorted_implies_sorted(old_leaf->keys);
    Key::largest_lt_ensures(old_leaf->keys, pivot, split_index - 1);
}

/// Prove that the `all_keys` of the left and right child after splitting an index node 
/// maintain certain wf properties.
pub proof fn lemma_split_index_all_keys(old_index: Node, split_arg: SplitArg)
    requires
        old_index.wf(),
        old_index is Index,
        split_arg.wf(old_index),
        ({
            let (left_index, right_index) = old_index.split_index(split_arg);
            &&& left_index.wf()
            &&& right_index.wf()
        })
    ensures ({
        let (left_index, right_index) = old_index.split_index(split_arg);
        &&& old_index.all_keys() == left_index.all_keys() + right_index.all_keys() + set![split_arg.get_pivot()]
        &&& forall |key| left_index.all_keys().contains(key)
            <==> (Key::lt(key, split_arg.get_pivot()) && old_index.all_keys().contains(key))
        &&& forall |key| (right_index.all_keys().contains(key) || key == split_arg.get_pivot())
            <==> (Key::lte(split_arg.get_pivot(), key) && old_index.all_keys().contains(key))
    })
{
    let (left_index, right_index) = old_index.split_index(split_arg);
    let pivot = split_arg.get_pivot();
    let pivot_index = split_arg->pivot_index;
    
    assert(left_index.wf());
    assert(right_index.wf());
    
    // Assert that old index's pivots and children are related to left and right indices by concatenation.
    // It's surprising (in a good way) that Verus is able to get these facts just through assertion (probably
    // through triggering seq axioms).
    assert(old_index->pivots == left_index->pivots + seq![pivot] + right_index->pivots);
    assert(old_index->children == left_index->children + right_index->children);

    // Ensures GOAL 1
    assert(old_index.all_keys() =~~= left_index.all_keys() + right_index.all_keys() + set![pivot]);

    assert(left_index->pivots == old_index->pivots.subrange(0, pivot_index));
    assert(left_index->children == old_index->children.subrange(0, pivot_index + 1));
    assert(right_index->pivots == old_index->pivots.subrange(pivot_index + 1, old_index->pivots.len() as int));
    assert(right_index->children == old_index->children.subrange(pivot_index + 1, old_index->children.len() as int));

    // Ensures Goal 2
    assert forall |key| left_index.all_keys().contains(key)
    implies #[trigger] Key::lt(key, pivot) && old_index.all_keys().contains(key) by {
        if (!left_index->pivots.contains(key)) {
            assert(left_index.children_keys().contains(key));
            let i = choose |i| 0 <= i < left_index->children.len()
                && (#[trigger] left_index->children[i]).all_keys().contains(key);
            assert(left_index->children[i] == old_index->children[i]);
            assert(old_index.all_keys_below_bound(i));
            assert(Key::lt(key, old_index->pivots[i]));
            if (i < left_index->children.len() - 1) {
                assert(Key::lt(old_index->pivots[i], pivot));
            } else {
                assert(old_index->pivots[i] == pivot);
            }
            assert(Key::lt(key, pivot));
        }
    }

    assert forall |key| #[trigger] Key::lt(key, pivot) && old_index.all_keys().contains(key)
    implies left_index.all_keys().contains(key) by {
        if (old_index->pivots.contains(key)) {
            let i = old_index->pivots.index_of(key);
            if (i >= pivot_index) { // proof by contradiction
                assert(Key::lt(pivot, key));
            }
            assert(i < pivot_index == left_index->pivots.len());
            assert(left_index->pivots.contains(key));
        } else {
            let i = choose |i| 0 <= i < old_index->children.len()
                && (#[trigger] old_index->children[i]).all_keys().contains(key);
            if (i >= pivot_index + 1) { // proof by contradiction
                assert(old_index.all_keys_above_bound(i));
                assert(Key::lte(old_index->pivots[i-1], key));
                Key::strictly_sorted_implies_sorted(old_index->pivots);
                assert(Key::lte(pivot, old_index->pivots[i-1]));
            }
            assert(i < pivot_index + 1 == left_index->children.len());
            assert(left_index->children[i].all_keys().contains(key));
        }
    }

    assert forall |key| (right_index.all_keys().contains(key) || key == pivot)
    implies #[trigger] Key::lte(pivot, key) && old_index.all_keys().contains(key) by {
        if (key == pivot) {
        } else if (right_index->pivots.contains(key)) {
            assert(Key::lt(pivot, key));
        } else {
            assert(right_index.children_keys().contains(key));
            let i = choose |i| 0 <= i < right_index->children.len()
                && (#[trigger] right_index->children[i]).all_keys().contains(key);
            assert(right_index->children[i] == old_index->children[i + pivot_index + 1]);
            assert(old_index.all_keys_above_bound(i + pivot_index + 1));
            assert(Key::lte(old_index->pivots[i + pivot_index + 1 - 1], key));
            if (0 < i) {
                assert(Key::lt(pivot, old_index->pivots[i + pivot_index]));
            } else {
                assert(old_index->pivots[i + pivot_index] == pivot);
            }
            Key::lte(pivot, key);
        }
    }

    assert forall |key| #[trigger] Key::lte(pivot, key) && old_index.all_keys().contains(key)
    implies (right_index.all_keys().contains(key) || key == pivot) by {
        if (old_index->pivots.contains(key)) {
            let i = old_index->pivots.index_of(key);
            if (i == pivot_index) {
                assert(key == pivot);
            } else if (i < pivot_index) { // proof by contradiction
                assert(Key::lt(key, pivot));
            } else {
                assert(pivot_index < i);
                assert(right_index->pivots.contains(key));
            }
        } else {
            let i = choose |i| 0 <= i < old_index->children.len()
                && (#[trigger] old_index->children[i]).all_keys().contains(key);
            if (i < pivot_index + 1) { // proof by contradiction
                assert(old_index.all_keys_below_bound(i));
                assert(Key::lt(key, old_index->pivots[i]));
                Key::strictly_sorted_implies_sorted(old_index->pivots);
                assert(Key::lte(old_index->pivots[i], pivot));
            }
            assert(pivot_index + 1 <= i);
            assert(right_index->children[i - (pivot_index + 1)].all_keys().contains(key));
        }
    }
}

pub proof fn lemma_split_node_all_keys(old_node: Node, split_arg: SplitArg)
    requires
        old_node.wf(),
        split_arg.wf(old_node),
        ({
            let (left_node, right_node) = old_node.split_node(split_arg);
            &&& left_node.wf()
            &&& right_node.wf()
        })
    ensures ({
        let (left_node, right_node) = old_node.split_node(split_arg);
        &&& if (old_node is Leaf) {
                &&& old_node.all_keys() == left_node.all_keys() + right_node.all_keys()
                &&& forall |key| right_node.all_keys().contains(key)
                    <==> (Key::lte(split_arg.get_pivot(), key) && old_node.all_keys().contains(key))
            } else {
                &&& old_node.all_keys() == left_node.all_keys() + right_node.all_keys() + set![split_arg.get_pivot()]
                &&& forall |key| (right_node.all_keys().contains(key) || key == split_arg.get_pivot())
                    <==> (Key::lte(split_arg.get_pivot(), key) && old_node.all_keys().contains(key))
            }
        &&& forall |key| left_node.all_keys().contains(key)
            <==> (Key::lt(key, split_arg.get_pivot()) && old_node.all_keys().contains(key))
    })
{
    if (old_node is Leaf) {
        lemma_split_leaf_all_keys(old_node, split_arg);
    } else {
        lemma_split_index_all_keys(old_node, split_arg);
    }
}

pub proof fn lemma_interpretation_subset_of_all_keys(node: Node)
    requires
        node.wf(),
    ensures
        node.i().map.dom().subset_of(node.all_keys()),
    decreases node,
{
    if node is Leaf {
        let keys = node->keys;
        assert forall |key: Key|
            #[trigger] node.i().map.contains_key(key)
            implies node.all_keys().contains(key)
        by {
            assert(keys.contains(key));
        };
    } else {
        let children = node->children;
        let pivots = node->pivots;
        lemma_i_unfoldable(node);
        assert forall |key: Key|
            #[trigger] node.i().map.contains_key(key)
            implies node.all_keys().contains(key)
        by {
            let r = node.route(key);
            Node::route_ensures(node, key);
            assert(0 <= r + 1 < children.len());
            lemma_i_contains_implies_routed_child_contains(node, key);
            lemma_interpretation_subset_of_all_keys(children[r+1]);
            assert(children[r+1].all_keys().contains(key));
            assert(node.children_keys().contains(key)) by {
                assert(exists |i| 0 <= i < children.len()
                    && (#[trigger] children[i]).all_keys().contains(key));
            };
            assert(node.all_keys().contains(key));
        };
    }
}

#[verifier::ext_equal]
pub struct QueryLabel {
    pub key: Key,
    pub msg: Message,
}

#[verifier::ext_equal]
pub struct InsertLabel {
    pub key: Key,
    pub msg: Message,
    pub path: Path,
}

#[verifier::ext_equal]
pub struct AppendLabel {
    pub keys: Seq<Key>,
    pub msgs: Seq<Message>,
    pub path: Path,
}

#[verifier::ext_equal]
pub struct InternalLabel {}

// ============ ============
// ============ TRANSITION REFINEMENTS ============
// ============ ============

pub proof fn query_refines(pre: Node, lbl: QueryLabel)
    requires
        pre.wf(),
        pre.query(lbl.key) == lbl.msg
    ensures
        pre.i().query(lbl.key) == lbl.msg
    decreases pre
{
    let r = pre.route(lbl.key);
    if pre is Index {
        let pivots = pre->pivots;
        let children = pre->children;


        query_refines(children[r+1], lbl);

    }
}

pub proof fn query_refines_to_routed_child(pre: Node, lbl: QueryLabel)
    requires
        pre.wf(),
        pre is Index,
        pre.query(lbl.key) == lbl.msg,
    ensures
        pre->children[pre.route(lbl.key) + 1].i().query(lbl.key) == lbl.msg,
    decreases pre,
{
    let r = pre.route(lbl.key);
    if pre is Index {
        let pivots = pre->pivots;
        let children = pre->children;
        assert(children[r+1].wf());
        assert(children[r+1].query(lbl.key) == lbl.msg);
        query_refines(children[r+1], lbl);
    }
}

pub proof fn lemma_i_unfoldable(node: Node)
    requires
        node.wf(),
        node is Index,
    ensures
        forall |key: Key| 0 <= #[trigger] node.route(key) + 1 < node->children.len(),
{
    let children = node->children;
    assert forall |key: Key| 0 <= #[trigger] node.route(key) + 1 < children.len() by {
        Node::route_ensures(node, key);
    };
}

pub proof fn lemma_i_contains_implies_routed_child_contains(node: Node, key: Key)
    requires
        node.wf(),
        node is Index,
        node.i().map.contains_key(key),
    ensures
        node->children[node.route(key) + 1].i().map.contains_key(key),
{
    let children = node->children;
    let pivots = node->pivots;
    let r = node.route(key);
    Node::route_ensures(node, key);
    Key::strictly_sorted_implies_sorted(pivots);
    assert(0 <= r + 1 < children.len());
    assert(children[r+1].wf());
}

pub proof fn contains_refines_to_routed_child(pre: Node, key: Key, result: bool)
    requires
        pre.wf(),
        pre is Index,
        pre.contains(key) == result,
    ensures
        pre->children[pre.route(key) + 1].contains(key) == result,
    decreases pre,
{
    let children = pre->children;
    let r = pre.route(key);
    Node::route_ensures(pre, key);
    assert(0 <= r + 1 < children.len());
    if children[r+1] is Index {
        assert(children[r+1].wf());
        contains_refines_to_routed_child(children[r+1], key, result);
    }
}

pub proof fn contains_refines(pre: Node, key: Key, result: bool)
    requires
        pre.wf(),
        pre.contains(key) == result
    ensures
        pre.i().map.contains_key(key) == result
    decreases pre
{
    let r = pre.route(key);
    if pre is Leaf {
        let keys = pre->keys;
        Node::route_ensures(pre, key);
        assert(pre.i().map.contains_key(key) == keys.contains(key));
        if result {
            assert(0 <= r && keys[r] == key);
            assert(keys.contains(key));
        } else {
            assert(!(0 <= r && keys[r] == key));
            if keys.contains(key) {
                let i = keys.index_of(key);
                assert(0 <= i < keys.len());
                assert(keys[i] == key);
                Key::largest_lte_is_lemma(keys, key, i);
                assert(r == i);
                assert(0 <= r && keys[r] == key);
            }
            assert(!keys.contains(key));
        }
    } else {
        let children = pre->children;
        Node::route_ensures(pre, key);
        lemma_i_unfoldable(pre);
        assert(0 <= r + 1 < children.len());
        contains_refines_to_routed_child(pre, key, result);
        assert(children[r+1].contains(key) == result);
        contains_refines(children[r+1], key, result);
        if result {
            assert(children[r+1].i().map.contains_key(key));
            assert(pre.i().map.contains_key(key));
        } else {
            assert(!children[r+1].i().map.contains_key(key));
            if pre.i().map.contains_key(key) {
                lemma_i_contains_implies_routed_child_contains(pre, key);
                assert(false);
            }
        }
    }
}

pub proof fn lemma_insert_inserts_to_all_keys(node: Node, key: Key, msg: Message, path: Path)
    requires
        node.wf(),
        path.valid(),
        path.node == node,
        path.key == key,
        path.target() is Leaf,
    ensures
        node.insert(key, msg, path).all_keys() == node.all_keys().insert(key)
    decreases node,
{
    match node {
        Node::Leaf{keys, msgs} => {
            lemma_insert_leaf_is_correct(node, key, msg);
        },
        Node::Index{pivots, children} => {
            let post = node.insert(key, msg, path);
            let r = node.route(key);

            // Recursively call the lemma on the changed child: the child we inserted into.
            lemma_insert_inserts_to_all_keys(children[r+1], key, msg, path.subpath());
            // This implies that the changed child's all_keys is the same as before except with the
            // new key inserted.
            assert(post->children[r+1].all_keys() == children[r+1].all_keys().insert(key)); // trigger

            // Now let's just assert that each of the post state's children all_keys
            // are the same as the pre (besides the changed child).
            assert(forall |i| 0 <= i < post->children.len() && i != (r+1)
                ==> post->children[i] =~~= #[trigger] children[i]);

            // GOAL
        },
    }
}

pub proof fn lemma_insert_preserves_wf(node: Node, key: Key, msg: Message, path: Path)
    requires
        node.wf(),
        path.valid(),
        path.node == node,
        path.key == key,
        path.target() is Leaf,
    ensures
        node.insert(key, msg, path).wf(),
    decreases node
{
    match node {
        Node::Leaf{keys, msgs} => {},
        Node::Index{pivots, children} => {
            let post = node.insert(key, msg, path);

            let r = node.route(key);
            lemma_insert_preserves_wf(children[r+1], key, msg, path.subpath());

            // For recommends

            // Subgoal 1, needed for asserting that unchanged keys in children[r+1].all_keys() still satisfy bounds
            lemma_insert_inserts_to_all_keys(children[r+1], key, msg, path.subpath());

            // Subgoal 2: the only changed child, r+1, satisfies all keys bounds

            if (r+1 < children.len() - 1) {
                assert(node.all_keys_below_bound(r+1)); // trigger
            }

            if (0 <= r) {
                assert(node.all_keys_above_bound(r+1)); // trigger
            }

            // Subgoal 3: the unchanged children still satisfy all keys bounds

            assert forall |i| 0 <= i < post->children.len() - 1 && i != r+1
                implies post.all_keys_below_bound(i) by
            {
                assert(node.all_keys_below_bound(i)); // trigger
            }

            assert forall |i| 0 < i < post->children.len() && i != r+1
                implies post.all_keys_above_bound(i) by
            {
                assert(node.all_keys_above_bound(i)); // trigger
            }
        },
    }
}

pub proof fn lemma_path_target_is_wf(path: Path)
    requires
        path.valid(),
    ensures
        path.target().wf(),
    decreases
        path.depth
{
    if path.depth > 0 {
        lemma_path_target_is_wf(path.subpath());
    }
}

// Proves that inserting into a node and then refining is the same
// as refining then inserting into the refinement.
pub proof fn insert_refines(pre: Node, lbl: InsertLabel)
    requires
        pre.wf(),
        lbl.path.valid(),
        lbl.path.node == pre,
        lbl.path.key == lbl.key,
        lbl.path.target() is Leaf,
    ensures
        pre.insert(lbl.key, lbl.msg, lbl.path).wf(),
        pre.insert(lbl.key, lbl.msg, lbl.path).i() == pre.i().insert(lbl.key, lbl.msg),
    decreases
        pre
{
    lemma_path_target_is_wf(lbl.path);
    lemma_insert_leaf_is_correct(lbl.path.target(), lbl.key, lbl.msg);

    // Goal 1 - After insertion the node is still well formed.
    lemma_insert_preserves_wf(pre, lbl.key, lbl.msg, lbl.path);
    
    // Goal 2 - Inserting into node then abstracting to Map,
    // is the same as abstracting to map, then inserting to map.

    match pre {
        Node::Leaf{keys, msgs} => {}, // Given by lemma_insert_leaf_is_correct!
        Node::Index{pivots, children} => {
            let post = pre.insert(lbl.key, lbl.msg, lbl.path);
            let r = pre.route(lbl.key);
            
            // Suppress recommendation
            assert(forall |i| 0 <= i < children.len() ==> (#[trigger] children[i]).wf()); // trigger

            // Assert that the changed child has original keys plus the new key-value pair.
            let child_label = InsertLabel{ key: lbl.key, msg: lbl.msg, path: lbl.path.subpath() };
            insert_refines(children[r+1], child_label);

        },
    }
}

pub proof fn grow_refines(pre: Node, lbl: InternalLabel)
    requires
        pre.wf(),
    ensures
        pre.grow().wf(),
        pre.grow().i() == pre.i()
{
    let post = pre.grow();
}

/// Proves that if the first and last key in a sorted seq of keys are path
/// equiv (i.e.: would map to the same node), then *all* keys in seq must
/// be path equiv.
pub proof fn lemma_append_keys_are_path_equiv(keys: Seq<Key>, path: Path)
    requires
        path.valid(),
        keys.len() > 0,
        Key::is_strictly_sorted(keys),
        path.key == keys[0],
        path.path_equiv(keys.last())
    ensures
        forall |key| keys.contains(key) ==> path.path_equiv(key)
    decreases path.depth
{
    if 0 < path.depth {
        lemma_append_keys_are_path_equiv(keys, path.subpath());
    }
    Key::strictly_sorted_implies_sorted(keys);

    assert forall |key| keys.contains(key) implies path.path_equiv(key) by {
        let node = path.node;
        lemma_key_lte_implies_route_lte(node, keys[0], key);
        lemma_key_lte_implies_route_lte(node, key, keys.last());
    }
}

pub proof fn lemma_append_via_insert_path(path: Path, new_keys: Seq<Key>, new_msgs: Seq<Message>)
    requires
        path.valid(),
        new_keys.len() > 1,
        new_keys.len() == new_msgs.len(),
        Key::is_strictly_sorted(new_keys),
        path.target() is Leaf,
        Key::lt(path.target()->keys.last(), new_keys[0]),
        path.key == new_keys[0],
        path.path_equiv(new_keys.last()),
    ensures ({
            let path1 = Path{node: path.node.insert(new_keys[0], new_msgs[0], path), key: new_keys[1], depth: path.depth};
            &&& path1.valid()
            &&& path1.target() == path.target().insert_leaf(new_keys[0], new_msgs[0])
            &&& path1.path_equiv(new_keys.last())
        })
    decreases path.depth,
{
    let post = path.node.insert(new_keys[0], new_msgs[0], path);
    let path1 = Path{node: post, key: new_keys[1], depth: path.depth};
    lemma_insert_preserves_wf(path.node, new_keys[0], new_msgs[0], path);
    lemma_append_keys_are_path_equiv(new_keys, path);
    assert(path.path_equiv(new_keys[1]));

    if path.depth == 0 {
        lemma_route_to_end(path.target(), new_keys[0]);
        assert(path1.node->keys.last() == new_keys[0]);

        let r1_key1 = path1.node.route(new_keys[1]);
        assert(r1_key1 == path1.node->keys.len() - 1) by {
            assert(Key::lt(new_keys[0], new_keys[1]));
            if r1_key1 < path1.node->keys.len() - 1 {
                assert(Key::lt(new_keys[1], path1.node->keys.last()));
            }
        }
        let r1_key2 = path1.node.route(new_keys.last());
        assert(r1_key2 == path1.node->keys.len() - 1) by {
            assert(Key::lt(new_keys[0], new_keys.last()));
            if r1_key2 < path1.node->keys.len() - 1 {
                assert(Key::lt(new_keys.last(), path1.node->keys.last()));
            }
        }
        assert(r1_key1 == r1_key2);
    } else {
        lemma_append_via_insert_path(path.subpath(), new_keys, new_msgs);
    }
}

pub proof fn lemma_append_via_insert_preserves_wf(pre: Node, keys: Seq<Key>, msgs: Seq<Message>, path: Path)
    requires
        path.valid(),
        path.node == pre,
        keys.len() > 0,
        keys.len() == msgs.len(),
        Key::is_strictly_sorted(keys),
        path.target() is Leaf,
        Key::lt(path.target()->keys.last(), keys[0]),
        path.key == keys[0],
        path.path_equiv(keys.last()),
    ensures
        pre.append_via_insert(keys, msgs, path).wf(),
    decreases keys.len(),
{
    let post = pre.append_via_insert(keys, msgs, path);
    let insert0 = pre.insert(keys[0], msgs[0], path);
    let keys_msgs = keys.zip_with(msgs);
    if keys_msgs.len() == 1 {
        reveal_with_fuel(vstd::prelude::Seq::fold_left_alt, 2);
        lemma_insert_preserves_wf(pre, keys[0], msgs[0], path);
    } else {
        let path1 = Path{node: insert0, key: keys[1], depth: path.depth};
        lemma_append_via_insert_path(path, keys, msgs);
        lemma_path_target_is_wf(path);
        lemma_route_to_end(path.target(), keys[0]);
        lemma_append_via_insert_preserves_wf(insert0, keys.skip(1), msgs.skip(1), path1);
        assert(keys_msgs.skip(1) == keys.skip(1).zip_with(msgs.skip(1))); // trigger
    }
}

pub proof fn lemma_append_incremental(new_keys: Seq<Key>, new_msgs: Seq<Message>, path: Path, path1: Path)
    requires
        path.valid(),
        new_keys.len() > 1,
        new_keys.len() == new_msgs.len(),
        Key::is_strictly_sorted(new_keys),
        path.target() is Leaf,
        Key::lt(path.target()->keys.last(), new_keys[0]),
        path.key == new_keys[0],
        path.path_equiv(new_keys.last()),
        path1 == (Path{node: path.node.append(new_keys.take(1), new_msgs.take(1), path),
            key: new_keys[1], depth: path.depth}),
    ensures
        path.node.append(new_keys, new_msgs, path)
            == path1.node.append(new_keys.skip(1), new_msgs.skip(1), path1),
    decreases path.depth,
{
    let post = path.node.append(new_keys, new_msgs, path);
    let post1 = path1.node.append(new_keys.skip(1), new_msgs.skip(1), path1);
    if path.depth == 0 {
        assert(path.node->keys + new_keys == path.node->keys + new_keys.take(1) + new_keys.skip(1));
        assert(path.node->msgs + new_msgs == path.node->msgs + new_msgs.take(1) + new_msgs.skip(1));
    } else {
        let r1 = path1.node.route(new_keys[1]);
        let r = path.node.route(new_keys[0]);
        lemma_append_keys_are_path_equiv(new_keys, path);
        assert(path.path_equiv(new_keys[1]));
        assert(r == path.node.route(new_keys[1]));
        assert(r == r1);
        assert(path1.subpath().node == path1.node->children[r+1]);
        assert(path1.subpath().node == path.node->children[r+1].append(new_keys.take(1), new_msgs.take(1), path.subpath()));
        lemma_append_incremental(new_keys, new_msgs, path.subpath(), path1.subpath());
        // changed children equal
        assert(post->children[r+1]
            == path.subpath().node.append(new_keys, new_msgs, path.subpath()));
        assert(post1->children[r+1]
            == path1.subpath().node.append(new_keys.skip(1), new_msgs.skip(1), path1.subpath()));
        
        // unchanged children equal
        assert(post->children.len() == path.node->children.len() == post1->children.len());
        assert(forall |i| 0 <= i < post->children.len() && i != r+1
            ==> #[trigger] post->children[i] == path.node->children[i] && post1->children[i] == path.node->children[i]);

        assert(post->children =~~= post1->children);
    }
}

pub proof fn lemma_append_via_insert_equiv(node: Node, new_keys: Seq<Key>, new_msgs: Seq<Message>, path: Path)
    requires
        path.valid(),
        path.node == node,
        new_keys.len() > 0,
        new_keys.len() == new_msgs.len(),
        Key::is_strictly_sorted(new_keys),
        path.target() is Leaf,
        Key::lt(path.target()->keys.last(), new_keys[0]),
        path.key == new_keys[0],
        path.path_equiv(new_keys.last()),
    ensures
        node.append(new_keys, new_msgs, path) == node.append_via_insert(new_keys, new_msgs, path),
    decreases new_keys.len(),
{
    lemma_path_target_is_wf(path);
    let post = node.append(new_keys, new_msgs, path);
    let via_insert = node.append_via_insert(new_keys, new_msgs, path);
    let keys_msgs = new_keys.zip_with(new_msgs);
    let insert0 = node.insert(new_keys[0], new_msgs[0], path);
    let r = path.target().route(new_keys[0]);
    lemma_route_to_end(path.target(), new_keys[0]);
    assert(path.target()->keys.insert(r+1, new_keys[0]) == path.target()->keys + new_keys.take(1)); // trigger
    assert(path.target()->msgs.insert(r+1, new_msgs[0]) == path.target()->msgs + new_msgs.take(1)); // trigger

    if new_keys.len() == 1 {
        reveal_with_fuel(vstd::prelude::Seq::fold_left_alt, 2);
        assert(new_keys.take(1) == new_keys); // trigger
        assert(new_msgs.take(1) == new_msgs); // trigger
    } else {
        let path1 = Path{node: insert0, key: new_keys[1], depth: path.depth};
        lemma_append_via_insert_path(path, new_keys, new_msgs);

        lemma_append_via_insert_equiv(insert0, new_keys.skip(1), new_msgs.skip(1), path1);

        lemma_append_incremental(new_keys, new_msgs, path, path1);

        assert(keys_msgs.skip(1) == new_keys.skip(1).zip_with(new_msgs.skip(1))); // trigger

    }
}

pub proof fn lemma_append_via_insert_refines(pre: Node, keys: Seq<Key>, msgs: Seq<Message>, path: Path)
    requires
        path.valid(),
        path.node == pre,
        keys.len() > 0,
        keys.len() == msgs.len(),
        Key::is_strictly_sorted(keys),
        path.target() is Leaf,
        Key::lt(path.target()->keys.last(), keys[0]),
        path.key == keys[0],
        path.path_equiv(keys.last()),
    ensures
        pre.append_via_insert(keys, msgs, path).wf(),
        pre.append_via_insert(keys, msgs, path).i() == (
            SimpleBuffer{map: pre.i().map.union_prefer_right(Map::new(
                |key| keys.contains(key),
                // TODO(x9du): use Key::largest_lte instead?
                |key| msgs[(Node::Leaf{ keys: keys, msgs: msgs }).route(key)]))}),
    decreases keys.len(),
{
    lemma_append_via_insert_preserves_wf(pre, keys, msgs, path);

    let keys_msgs = keys.zip_with(msgs);
    let post = pre.append_via_insert(keys, msgs, path);
    let append_leaf = Node::Leaf{ keys: keys, msgs: msgs };
    let append_map = Map::new(
        |key| keys.contains(key),
        |key| msgs[append_leaf.route(key)]);
    let i_then_append = SimpleBuffer{map: pre.i().map.union_prefer_right(append_map)};
    let insert0 = pre.insert(keys[0], msgs[0], path);
    insert_refines(pre, InsertLabel{key: keys[0], msg: msgs[0], path: path});
    assert(insert0.i() == pre.i().insert(keys[0], msgs[0]));
    if keys_msgs.len() == 1 {
        reveal_with_fuel(vstd::prelude::Seq::fold_left_alt, 2);
        assert(post == insert0);
        assert(append_map =~~= map![keys[0] => msgs[0]]);
        assert(i_then_append =~~= pre.i().insert(keys[0], msgs[0]));
        assert(post.i() == i_then_append);
    } else {
        let path1 = Path{node: insert0, key: keys[1], depth: path.depth};
        lemma_append_via_insert_path(path, keys, msgs);
        lemma_path_target_is_wf(path);
        lemma_route_to_end(path.target(), keys[0]);
        assert(path1.target()->keys.last() == keys[0]);
        assert(keys.skip(1)[0] == keys[1]);
        assert(Key::lt(keys[0], keys[1]));
        lemma_append_via_insert_refines(insert0, keys.skip(1), msgs.skip(1), path1);
        assert(keys_msgs.skip(1) == keys.skip(1).zip_with(msgs.skip(1)));
        assert(post == insert0.append_via_insert(keys.skip(1), msgs.skip(1), path1));
        let append_map1 = Map::new(
            |key| keys.skip(1).contains(key),
            |key| msgs.skip(1)[(Node::Leaf{ keys: keys.skip(1), msgs: msgs.skip(1) }).route(key)]);
        assert(post.i().map == pre.i().insert(keys[0], msgs[0]).map.union_prefer_right(append_map1));

        assert forall |key| #[trigger] post.i().map.contains_key(key)
        implies i_then_append.map.contains_key(key) by {
            if !pre.i().map.contains_key(key) {
                assert(append_map.contains_key(key));
            }
        }

        assert forall |key| i_then_append.map.contains_key(key)
        implies #[trigger] post.i().map.contains_key(key) by {
            if !pre.i().map.contains_key(key) {
                assert(keys.contains(key));
                let i = keys.index_of(key);
                if i > 0 {
                    assert(keys.skip(1)[i - 1] == key);
                }
            }
        }

        assert forall |key| #[trigger] post.i().map.contains_key(key)
        implies post.i().map[key] == i_then_append.map[key] by {
            Key::strictly_sorted_implies_unique(keys);
            if keys.contains(key) {
                let i = keys.index_of(key);
                assert(post.i().map[key] == msgs[i]) by {
                    if i > 0 {
                        assert(keys.skip(1)[i-1] == key);
                        assert(msgs.skip(1)[i-1] == msgs[i]);
                    }
                }
                assert(i_then_append.map[key] == msgs[i]);
            }
        }

        assert(post.i().map =~~= i_then_append.map);
    }
}

pub proof fn append_refines(pre: Node, lbl: AppendLabel)
    requires
        lbl.path.valid(),
        lbl.path.node == pre,
        lbl.keys.len() > 0,
        lbl.keys.len() == lbl.msgs.len(),
        Key::is_strictly_sorted(lbl.keys),
        lbl.path.target() is Leaf,
        Key::lt(lbl.path.target()->keys.last(), lbl.keys[0]),
        lbl.path.key == lbl.keys[0],
        lbl.path.path_equiv(lbl.keys.last()),
    ensures
        pre.append(lbl.keys, lbl.msgs, lbl.path).wf(),
        pre.append(lbl.keys, lbl.msgs, lbl.path).i() == (
            SimpleBuffer{map: pre.i().map.union_prefer_right(Map::new(
                |key| lbl.keys.contains(key),
                |key| lbl.msgs[(Node::Leaf{ keys: lbl.keys, msgs: lbl.msgs }).route(key)]))}),
{
    lemma_append_via_insert_equiv(pre, lbl.keys, lbl.msgs, lbl.path);
    lemma_append_via_insert_refines(pre, lbl.keys, lbl.msgs, lbl.path);
}

pub proof fn lemma_split_child_of_index_preserves_wf(pre: Node, split_arg: SplitArg)
requires
    pre.can_split_child_of_index(split_arg),
ensures
    pre.split_child_of_index(split_arg).wf(),
{
    let children = pre->children;
    let pivots = pre->pivots;
    let pivot = split_arg.get_pivot();
    let r = pre.route(pivot);
    let post = pre.split_child_of_index(split_arg);

    // Suppress recommends
    assert(pre is Index); // trigger
    assert(post is Index); // trigger
    assert(0 <= r + 1 < children.len()); // trigger

    // Suppress recommends
    assert(post->pivots.len() == pivots.len() + 1); // trigger
    assert(post->pivots[r+1] == pivot); // trigger

    lemma_split_node_preserves_wf(children[r+1], split_arg);


    // Assert pivots to the left of where new pivot was inserted are still sorted.

    // Assert pivots to the right of where new pivot was inserted are still sorted.

    // post->pivots[r] < pivot < post->pivots[r+2] (when r, r+2 exist)
    // TODO(x9du): might be some duplication of this proof in split_preserves_wf
    if (r >= 0) {
        assert(Key::lt(post->pivots[r], post->pivots[r+1])) by {

            if (children[r+1] is Leaf) {
                // If the split child is Leaf, then the targeted key that's
                // being split can NOT be one of the end indices of the child's keys,
                // because otherwise one of the partitions would be empty, and that
                // contradicts the split_arg wf() precondition.

                // The index that child will be split on is index of where split_arg.pivot
                // would be inserted into child's keys.
                let c_keys = children[r+1]->keys;
                let split_index = Key::largest_lt(c_keys, pivot) + 1;


                // By definition of Key::largest_lt, we know that:

                assert(pre.all_keys_above_bound(r+1)); // trigger
                // Needs this weird r+1-1 in order to trigger the postcondition of
                // all_keys_above_bound (because quantified `i` appears as `i-1` in trigger).
                assert(Key::lte(pivots[r+1-1], c_keys[0]));

                // And then combined with transitivity we should get:
            } else {
                let pivot_index = split_arg->pivot_index;
                lemma_wf_implies_all_keys_finite_and_not_empty(children[r+1]->children[pivot_index]);
                let key = children[r+1]->children[pivot_index].all_keys().choose();
                assert(Key::lt(key, pivot)) by {
                    assert(children[r+1].all_keys_below_bound(pivot_index)); // trigger
                }
                assert(Key::lte(pivots[r+1-1], key)) by {
                    assert(pre.all_keys_above_bound(r+1)); // trigger
                }
            }
        }
    }

    if (r+2 < post->pivots.len()) {
        assert(Key::lt(post->pivots[r+1], post->pivots[r+2])) by {


            assert(pre.all_keys_below_bound(r+1)); // trigger

            if (children[r+1] is Leaf) {
                let c_keys = children[r+1]->keys;
                let split_index = Key::largest_lt(c_keys, pivot) + 1;
                assert(children[r+1].wf());
                assert(Key::is_strictly_sorted(c_keys));
                Key::strictly_sorted_implies_sorted(c_keys);
                Key::largest_lt_ensures(c_keys, pivot, Key::largest_lt(c_keys, pivot));

                // by all_keys_below_bound

            } else {
                // by all_keys_below_bound
            }
        }
    }

    // Stitch the two ends together.
    assert forall |i, j| 0 <= i < j < post->pivots.len()
        implies Key::lt(post->pivots[i], post->pivots[j]) by
    {
        if (j < r+1) {
            // Untouched section to the left of insert is still sorted.
        } else if (i > r+1) {
            // Untouched section to the right of insert is still sorted.
        } else {
            if (i < r) {
            }
            if (r+2 < j) {
            }
        }
    }

    // Goal 1


    assert forall |i| 0 <= i < r+1 implies post.all_keys_below_bound(i) by {
        assert(pre.all_keys_below_bound(i)); // trigger
    }
    assert forall |i| 0 < i < r+1 implies post.all_keys_above_bound(i) by {
        assert(pre.all_keys_above_bound(i)); // trigger
    }

    assert forall |i: int| r+2 < i < post->children.len() - 1
    implies post.all_keys_below_bound(i) by {
        assert(pre.all_keys_below_bound(i - 1)); // trigger
    }
    assert forall |i: int| r+2 < i < post->children.len()
    implies post.all_keys_above_bound(i) by {
        assert(pre.all_keys_above_bound(i - 1)); // trigger
        assert(post->pivots[i-1] == pre->pivots[i-1-1]); // trigger
    }

    let (left_node, right_node) = children[r+1].split_node(split_arg);
    lemma_split_node_all_keys(children[r+1], split_arg);


    if (r+2 < post->children.len() - 1) {
        assert forall |key| post->children[r+2].all_keys().contains(key)
        implies #[trigger] Key::lt(key, post->pivots[r+2]) by {
            assert(pre.all_keys_below_bound(r+1)); // trigger
        }
    }

    if (0 < r+1) {
        assert forall |key| post->children[r+1].all_keys().contains(key)
        implies #[trigger] Key::lte(post->pivots[r+1-1], key) by {
            assert(pre.all_keys_above_bound(r+1)); // trigger
        }
    }

    // Goal 2
    // Goal 3
}

pub proof fn lemma_split_child_of_index_all_keys(pre: Node, split_arg: SplitArg)
requires
    pre.can_split_child_of_index(split_arg),
ensures
    if split_arg is SplitLeaf {
        pre.split_child_of_index(split_arg).all_keys() == pre.all_keys().insert(split_arg.get_pivot())
    } else {
        pre.split_child_of_index(split_arg).all_keys() == pre.all_keys()
    },
{
    // TODO(x9du): clean this proof up
    assert(pre is Index);
    let children = pre->children;
    let pivots = pre->pivots;
    let pivot = split_arg.get_pivot();
    let r = pre.route(pivot);
    let post = pre.split_child_of_index(split_arg);
    assert(post is Index);

    // Suppress recommends
    assert(0 <= r + 1 < children.len());
    assert(split_arg.wf(children[r+1]));
    assert(post->pivots.len() == pivots.len() + 1);
    assert(post->children.len() == children.len() + 1);
    assert(0 <= r + 2 <= post->pivots.len());
    assert(post->pivots[r+1] == pivot);

    lemma_split_node_preserves_wf(children[r+1], split_arg);
    lemma_split_node_all_keys(children[r+1], split_arg);

    assert(forall |i| 0 <= i < r+1 ==> #[trigger] children[i] == post->children[i]);
    assert(forall |i: int| r+2 < i < post->children.len() ==> children[i-1] == post->children[i]);

    assert(post->pivots == pivots.insert(r+1, pivot));

    assert forall |key| pre.all_keys().contains(key) implies post.all_keys().contains(key) by {
        if (pivots.contains(key)) {
            let i = pivots.index_of(key);
            if (i < r+1) {
                assert(pivots.insert(r+1, pivot)[i] == key);
            } else {
                assert(pivots.insert(r+1, pivot)[i+1] == key);
            }
            assert(pivots.insert(r+1, pivot).contains(key));
            assert(post->pivots.contains(key));
            assert(post.all_keys().contains(key));
        } else {
            assert(!pivots.to_set().contains(key));
            let i = choose |i| 0 <= i < children.len() 
                && (#[trigger] children[i]).all_keys().contains(key);
            if (i < r+1) {
                assert(post->children[i].all_keys().contains(key));
            } else if (i == r+1) {
                assert({
                    ||| post->children[r+1].all_keys().contains(key)
                    ||| post->children[r+2].all_keys().contains(key)
                    ||| key == pivot
                });
            } else {
                assert(post->children[i+1].all_keys().contains(key));
            }
            assert(post.all_keys().contains(key));
        }
    }

    if (split_arg is SplitLeaf) {
        assert(post.all_keys() == pre.all_keys().insert(split_arg.get_pivot()));
    } else {
        let pivot_index = split_arg->pivot_index;
        assert(0 <= pivot_index < children[r+1]->pivots.len());
        /*assert(old_index->pivots == left_index->pivots + seq![pivot] + right_index->pivots);
        assert(old_index->children == left_index->children + right_index->children); */
        assert forall |key| post.all_keys().contains(key) implies pre.all_keys().contains(key) by {
            if (post->pivots.contains(key)) {
                if (key == pivot) {
                    assert(pivot == children[r+1]->pivots[pivot_index]);
                    assert(children[r+1]->pivots.to_set().contains(key));
                } else {
                    assert(pivots.contains(key));
                }
            } else {
                assert(pre.all_keys().contains(key));
            }
            assert(pre.all_keys().contains(key));
        }

        assert(post.all_keys() == pre.all_keys());
    }
}

pub proof fn lemma_split_all_keys(pre: Node, path: Path, split_arg: SplitArg)
requires
    pre.wf(),
    path.valid(),
    path.node == pre,
    path.key == split_arg.get_pivot(),
    path.target().can_split_child_of_index(split_arg),
ensures
    if split_arg is SplitLeaf {
        pre.split(path, split_arg).all_keys() == pre.all_keys().insert(split_arg.get_pivot())
    } else {
        pre.split(path, split_arg).all_keys() == pre.all_keys()
    },
decreases
    path.depth,
{
    let children = pre->children;
    let pivots = pre->pivots;
    let pivot = split_arg.get_pivot();
    let r = pre.route(pivot);
    let post = pre.split(path, split_arg);

    // Suppress recommends
    assert(pre is Index);
    assert(post is Index);
    assert(0 <= r + 1 < children.len());

    if (path.depth == 0) {
        lemma_split_child_of_index_all_keys(pre, split_arg);
    } else {
        lemma_split_all_keys(children[r+1], path.subpath(), split_arg);
        assert(post->pivots == pivots);
        assert(post->pivots.to_set() == pivots.to_set());
        assert(post->children.len() == children.len());
        if split_arg is SplitLeaf {
            assert(forall |i| 0 <= i < post->children.len() && i != r+1 ==> post->children[i].all_keys() == (#[trigger] children[i]).all_keys());
            assert(post->children[r+1].all_keys() == children[r+1].all_keys().insert(split_arg.get_pivot()));
            assert(post.all_keys() == pre.all_keys().insert(split_arg.get_pivot()));
        } else {
            assert(forall |i| 0 <= i < post->children.len() ==> post->children[i].all_keys() == (#[trigger] children[i]).all_keys());
            assert(post.all_keys() == pre.all_keys());
        }
    }
}

pub proof fn lemma_target_all_keys(pre: Node, path: Path, key: Key)
    requires
        pre.wf(),
        path.valid(),
        path.node == pre,
    ensures
        path.target().all_keys().contains(key) ==> pre.all_keys().contains(key),
    decreases
        path.depth,
{
    if (path.depth == 0) {
    } else {
        let r = pre.route(path.key);
        lemma_target_all_keys(pre->children[r+1], path.subpath(), key);
    }
}

pub proof fn lemma_split_preserves_wf(pre: Node, path: Path, split_arg: SplitArg)
requires
    pre.wf(),
    path.valid(),
    path.node == pre,
    path.key == split_arg.get_pivot(),
    // Asserts `split_arg.wf()`
    path.target().can_split_child_of_index(split_arg),
ensures
    pre.split(path, split_arg).wf(),
decreases
    path.depth
{
    let children = pre->children;
    let pivots = pre->pivots;
    let pivot = split_arg.get_pivot();
    let r = pre.route(pivot);
    let post = pre.split(path, split_arg);

    // Suppress recommends

    if (path.depth == 0) {
        lemma_split_child_of_index_preserves_wf(pre, split_arg);
    } else {
        lemma_split_preserves_wf(children[r+1], path.subpath(), split_arg);

        lemma_split_all_keys(children[r+1], path.subpath(), split_arg);

        // In the split child is leaf case, children[r+1] all_keys also contains the pivot.
        // Shared asserts for proving pivot < pivots[r+1] and pivots[r] < pivot.
        let r2 = path.target().route(pivot);

        if (split_arg is SplitLeaf) {
            let split_keys = path.target()->children[r2+1]->keys;

            assert(path.target()->children[r2+1].wf()); // trigger
            Key::strictly_sorted_implies_sorted(split_keys);
            Key::largest_lt_ensures(split_keys, pivot, Key::largest_lt(split_keys, pivot));
        }

        if (r+1 < post->children.len() - 1) {
            assert(post.all_keys_below_bound(r+1)) by {
                assert(pre.all_keys_below_bound(r+1)); // trigger

                // pivot < pivots[r+1] idea:
                // - pivot <= last key in split child
                // - This key is also in children[r+1], so it's < pivots[r+1] by all_keys_below_bound
                if (split_arg is SplitLeaf) {
                    let split_keys = path.target()->children[r2+1]->keys;
                    let last_key = split_keys.last();

                    assert(path.target()->children[r2+1].all_keys().contains(last_key)); // trigger
                    assert(path.target().all_keys().contains(last_key)); // trigger
                    lemma_target_all_keys(children[r+1], path.subpath(), last_key);

                }
            }
        }

        if (0 < r+1 < post->children.len()) {
            // pivots[r] <= pivot idea:
            // - First key in split child < pivot
            // - This key is also in children[r+1], so it's >= pivots[r] by all_keys_above_bound
            // We need this fact for the last assert so took it out of the assert by.
            if (split_arg is SplitLeaf) {
                let split_keys = path.target()->children[r2+1]->keys;
                let key = split_keys.first();

                lemma_target_all_keys(children[r+1], path.subpath(), key);
                assert(Key::lte(pivots[r+1-1], key)) by {
                    assert(pre.all_keys_above_bound(r+1)); // trigger
                }

            }

            assert(post.all_keys_above_bound(r+1)) by {
                assert(pre.all_keys_above_bound(r+1)); // trigger
            }
        }

        assert forall |i| 0 <= i < post->children.len() - 1 && i != r+1
        implies post.all_keys_below_bound(i) by {
            assert(pre.all_keys_below_bound(i)); // trigger
        }

        assert forall |i| 0 < i < post->children.len() && i != r+1
        implies post.all_keys_above_bound(i) by {
            assert(pre.all_keys_above_bound(i)); // trigger
        }
    }
}

pub proof fn lemma_split_child_of_index_interpretation(pre: Node, split_arg: SplitArg)
requires
    pre.wf(),
    pre.can_split_child_of_index(split_arg),
ensures
    pre.i() == pre.split_child_of_index(split_arg).i(),
{
    let pivots = pre->pivots;
    let children = pre->children;
    let post = pre.split_child_of_index(split_arg);
    let pivot = split_arg.get_pivot();

    lemma_split_child_of_index_preserves_wf(pre, split_arg);

    let r = pre.route(pivot);

    assert(post->pivots[r+1] == pivot); // trigger


    lemma_split_node_preserves_wf(children[r+1], split_arg);
    lemma_split_node_interpretation(children[r+1], split_arg);

    assert forall |k| pre.i().map.contains_key(k) implies post.i().map.contains_key(k) by {
        let r2 = pre.route(k);
        let post_r2 = post.route(k);


        Key::strictly_sorted_implies_sorted(post->pivots);

        if (r2 < r || (r2 == r && Key::lt(k, pivot))) {
            assert(r2 == post_r2) by {
                if (r2 >= 0) {
                }
                if (r2 < post->pivots.len() - 1) {
                    assert(Key::lt(k, post->pivots[r2+1])) by {
                        if (r2 < r) {
                        }
                    }
                }
                Key::largest_lte_is_lemma(post->pivots, k, r2);
            }
        } else if (r2 > r || (r2 == r && Key::lte(pivot, k))) {
            assert(r2+1 == post_r2) by {
                if (r2+1 >= 0) {
                    assert(Key::lte(post->pivots[r2+1], k)) by {
                        if (r2 > r) {
                        }
                    }
                }
                if (r2+1 < post->pivots.len() - 1) {
                }
                Key::largest_lte_is_lemma(post->pivots, k, r2+1);
            }
        }

        if (r2 == r) {
            if (Key::lt(k, pivot)) {
            } else {
            }
        } else if r2 < r {
        } else {
        }
    }

    assert forall |k| #[trigger] post.i().map.contains_key(k)
    implies pre.i().map.contains_key(k) && post.i().map[k] == pre.i().map[k] by {
        let r2 = pre.route(k);
        let post_r2 = post.route(k);

        lemma_interpretation_subset_of_all_keys(post->children[post_r2+1]);

        Key::strictly_sorted_implies_sorted(pivots);

        if (post_r2 <= r) {
            assert(r2 == post_r2) by {
                if (post_r2 >= 0) {
                    assert(Key::lte(post->pivots[post_r2], k)); // trigger
                }
                if (post_r2 < pivots.len() - 1) {
                    assert(Key::lte(post->pivots[post_r2+1], pivots[post_r2+1])) by {
                        if (post_r2 < r) {
                        } else if (post_r2 == r) {
                        }
                    }
                }
                Key::largest_lte_is_lemma(pivots, k, post_r2);
            }
        } else if (post_r2 >= r+1) {
            assert(r2 == post_r2-1) by {
                if (post_r2-1 >= 0) {
                    assert(Key::lte(pivots[post_r2-1], k)) by {
                        if (post_r2 > r+1) {
                            assert(Key::lte(post->pivots[post_r2], k)); // trigger
                        } else if (post_r2 == r+1) {
                        }
                    }
                }
                if (post_r2-1 < pivots.len() - 1) {
                    assert(Key::lt(k, post->pivots[post_r2+1])); // trigger
                }
                Key::largest_lte_is_lemma(pivots, k, post_r2-1);
            }
        }
        
        if (post_r2 == r) {
            assert(Key::lt(k, pivot)) by {
            }
        } else if (post_r2 == r+1) {
            assert(Key::lte(pivot, k)) by {
            }
        } else if (post_r2 < r) {
        } else {
        }
    }

    // GOAL 1

    // OVERALL GOAL
}

// Prove that splitting a node is equivalent to a no-op in the interpreted space.
pub proof fn split_refines(pre: Node, path: Path, split_arg: SplitArg)
requires
    pre.wf(),
    path.valid(),
    path.node == pre,
    path.key == split_arg.get_pivot(),
    path.target().can_split_child_of_index(split_arg),
ensures
    pre.split(path, split_arg).wf(),
    pre.i() == pre.split(path, split_arg).i(),
decreases
    path.depth,
{
    let pivots = pre->pivots;
    let children = pre->children;
    let post = pre.split(path, split_arg);
    let pivot = split_arg.get_pivot();

    lemma_split_preserves_wf(pre, path, split_arg);

    let r = pre.route(pivot);

    if (path.depth == 0) {
        lemma_split_child_of_index_interpretation(pre, split_arg);
    } else {
        assert(path.subpath().valid()); // trigger
        split_refines(children[r+1], path.subpath(), split_arg);
    }
}

}
