// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::{map::*, set::*};

use crate::allocation_layer::AllocationBranch_v::BranchNode as AllocationBranchNode;
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::LinkedBranch_v::SplitArg;
use crate::disk::GenericDisk_v::{AU, Address, Pointer};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Message, nop_delta};

verus! {

pub type LoadedBranch = Map<Address, AllocationBranchNode>;

pub open spec fn covers(available: Set<Address>, needed: Set<Address>) -> bool
{
    needed <= available
}

pub open spec fn root_needed(root: Pointer) -> Set<Address>
{
    if root is Some {
        set! { root.unwrap() }
    } else {
        Set::<Address>::empty()
    }
}

pub open spec fn loaded_child_addr(root: Address, loaded: LoadedBranch, key: Key) -> Address
    recommends
        loaded.contains_key(root),
        loaded[root].wf(),
        loaded[root] is Index,
{
    let child_idx = loaded[root].route(key) + 1;
    loaded[root]->children[child_idx]
}

pub open spec fn split_arg_matches_child(child: AllocationBranchNode, split_arg: SplitArg) -> bool
{
    match split_arg {
        SplitArg::SplitLeaf{pivot} => {
            &&& child is Leaf
            &&& 0 < Key::largest_lt(child->keys, pivot) + 1
            &&& Key::largest_lt(child->keys, pivot) + 1 < child->keys.len()
        }
        SplitArg::SplitIndex{pivot, pivot_index} => {
            &&& child is Index
            &&& child->children.len() == child->pivots.len() + 1
            &&& 0 <= pivot_index < child->pivots.len()
            &&& child->pivots[pivot_index] == pivot
        }
    }
}

pub open spec fn loaded_has_route_at_depth(root: Address, loaded: LoadedBranch, key: Key, depth: nat) -> bool
    decreases depth
{
    &&& loaded.contains_key(root)
    &&& loaded[root].wf()
    &&& !(loaded[root] is Auxiliary)
    &&& loaded[root].keys_strictly_sorted()
    &&& if depth == 0 {
        loaded[root] is Leaf
    } else {
        &&& loaded[root] is Index
        &&& loaded_has_route_at_depth(loaded_child_addr(root, loaded, key), loaded, key, (depth - 1) as nat)
    }
}

pub open spec fn loaded_path_addrs_at_depth(root: Address, loaded: LoadedBranch, key: Key, depth: nat) -> Set<Address>
    recommends loaded_has_route_at_depth(root, loaded, key, depth)
    decreases depth
{
    if depth == 0 {
        set! { root }
    } else {
        loaded_path_addrs_at_depth(loaded_child_addr(root, loaded, key), loaded, key, (depth - 1) as nat).insert(root)
    }
}

pub open spec fn loaded_target_addr_at_depth(root: Address, loaded: LoadedBranch, key: Key, depth: nat) -> Address
    recommends loaded_has_route_at_depth(root, loaded, key, depth)
    decreases depth
{
    if depth == 0 {
        root
    } else {
        loaded_target_addr_at_depth(loaded_child_addr(root, loaded, key), loaded, key, (depth - 1) as nat)
    }
}

pub open spec fn loaded_target_at_depth(root: Address, loaded: LoadedBranch, key: Key, depth: nat) -> AllocationBranchNode
    recommends loaded_has_route_at_depth(root, loaded, key, depth)
{
    loaded[loaded_target_addr_at_depth(root, loaded, key, depth)]
}

pub open spec fn loaded_path_equiv_at_depth(root: Address, loaded: LoadedBranch, key: Key, other_key: Key, depth: nat) -> bool
    recommends loaded_has_route_at_depth(root, loaded, key, depth)
    decreases depth
{
    if depth == 0 {
        true
    } else {
        &&& loaded[root].route(key) == loaded[root].route(other_key)
        &&& loaded_path_equiv_at_depth(loaded_child_addr(root, loaded, key), loaded, key, other_key, (depth - 1) as nat)
    }
}

pub open spec fn loaded_query_ready_at_depth(root: Address, loaded: LoadedBranch, key: Key, depth: nat) -> bool
{
    loaded_has_route_at_depth(root, loaded, key, depth)
}

pub open spec fn loaded_query_result_at_depth(root: Address, loaded: LoadedBranch, key: Key, depth: nat) -> Message
    recommends loaded_query_ready_at_depth(root, loaded, key, depth)
    decreases depth
{
    if depth == 0 {
        let leaf = loaded[root];
        let idx = leaf.route(key);
        if 0 <= idx && leaf->keys[idx] == key {
            leaf->msgs[idx]
        } else {
            Message::Update{delta: nop_delta()}
        }
    } else {
        loaded_query_result_at_depth(loaded_child_addr(root, loaded, key), loaded, key, (depth - 1) as nat)
    }
}

pub open spec(checked) fn loaded_append_ready_at_depth(root: Address, loaded: LoadedBranch, keys: Seq<Key>, msgs: Seq<Message>, depth: nat) -> bool
    recommends keys.len() > 0,
{
    let first_key = keys[0];
    let last_key = keys.last();
    &&& keys.len() == msgs.len()
    &&& Key::is_strictly_sorted(keys)
    &&& loaded_query_ready_at_depth(root, loaded, first_key, depth)
    &&& loaded_target_at_depth(root, loaded, first_key, depth)->keys.len() > 0
    &&& Key::lt(loaded_target_at_depth(root, loaded, first_key, depth)->keys.last(), first_key)
    &&& loaded_path_equiv_at_depth(root, loaded, first_key, last_key, depth)
}

pub open spec fn loaded_append_write_nodes_at_depth(root: Address, loaded: LoadedBranch, keys: Seq<Key>, msgs: Seq<Message>, depth: nat) -> LoadedBranch
    recommends loaded_append_ready_at_depth(root, loaded, keys, msgs, depth)
{
    let leaf_addr = loaded_target_addr_at_depth(root, loaded, keys[0], depth);
    let leaf = loaded[leaf_addr];
    map! {
        leaf_addr => AllocationBranchNode::Leaf{
            keys: leaf->keys + keys,
            msgs: leaf->msgs + msgs,
        }
    }
}

pub open spec fn loaded_split_child_addr_at_depth(root: Address, loaded: LoadedBranch, key: Key, depth: nat) -> Address
    recommends
        loaded_has_route_at_depth(root, loaded, key, depth),
        loaded_target_at_depth(root, loaded, key, depth) is Index,
{
    let target = loaded_target_at_depth(root, loaded, key, depth);
    let child_idx = target.route(key) + 1;
    target->children[child_idx]
}

pub open spec fn loaded_split_ready_at_depth(root: Address, loaded: LoadedBranch, pivot: Key, depth: nat, split_arg: SplitArg) -> bool
{
    &&& loaded_has_route_at_depth(root, loaded, pivot, depth)
    &&& loaded_target_at_depth(root, loaded, pivot, depth) is Index
    &&& split_arg.get_pivot() == pivot
    &&& loaded.contains_key(loaded_split_child_addr_at_depth(root, loaded, pivot, depth))
    &&& loaded[loaded_split_child_addr_at_depth(root, loaded, pivot, depth)].wf()
    &&& !(loaded[loaded_split_child_addr_at_depth(root, loaded, pivot, depth)] is Auxiliary)
    &&& loaded[loaded_split_child_addr_at_depth(root, loaded, pivot, depth)].keys_strictly_sorted()
    &&& split_arg_matches_child(loaded[loaded_split_child_addr_at_depth(root, loaded, pivot, depth)], split_arg)
}

pub open spec fn loaded_split_write_nodes_at_depth(root: Address, loaded: LoadedBranch, pivot: Key, depth: nat, split_arg: SplitArg, new_child_addr: Address) -> LoadedBranch
    recommends loaded_split_ready_at_depth(root, loaded, pivot, depth, split_arg)
{
    let parent_addr = loaded_target_addr_at_depth(root, loaded, pivot, depth);
    let parent = loaded[parent_addr];
    let child_addr = loaded_split_child_addr_at_depth(root, loaded, pivot, depth);
    let child = loaded[child_addr];
    let child_idx = parent.route(pivot) + 1;
    let new_parent = AllocationBranchNode::Index{
        pivots: parent->pivots.insert(child_idx, pivot),
        children: parent->children.insert(child_idx + 1, new_child_addr),
        aux_ptr: parent->aux_ptr,
    };
    let (new_left_child, new_right_child) = match split_arg {
        SplitArg::SplitLeaf{pivot} => {
            let split_index = Key::largest_lt(child->keys, pivot) + 1;
            (
                AllocationBranchNode::Leaf{
                    keys: child->keys.take(split_index),
                    msgs: child->msgs.take(split_index),
                },
                AllocationBranchNode::Leaf{
                    keys: child->keys.skip(split_index),
                    msgs: child->msgs.skip(split_index),
                },
            )
        }
        SplitArg::SplitIndex{pivot, pivot_index} => {
            (
                AllocationBranchNode::Index{
                    pivots: child->pivots.subrange(0, pivot_index),
                    children: child->children.subrange(0, pivot_index + 1),
                    aux_ptr: None,
                },
                AllocationBranchNode::Index{
                    pivots: child->pivots.subrange(pivot_index + 1, child->pivots.len() as int),
                    children: child->children.subrange(pivot_index + 1, child->children.len() as int),
                    aux_ptr: None,
                },
            )
        }
    };
    map! {
        parent_addr => new_parent,
        child_addr => new_left_child,
        new_child_addr => new_right_child,
    }
}

pub open spec fn loaded_grow_write_nodes(root: Address, new_root_addr: Address) -> LoadedBranch
{
    map! {
        new_root_addr => AllocationBranchNode::Index{
            pivots: seq![],
            children: seq![root],
            aux_ptr: None,
        }
    }
}

pub open spec fn loaded_seal_write_nodes(root: Address, loaded: LoadedBranch, aux_ptr: Pointer, summary: Set<AU>) -> LoadedBranch
    recommends
        loaded.contains_key(root),
        loaded[root].wf(),
        !(loaded[root] is Auxiliary),
        aux_ptr is Some <==> loaded[root] is Index,
{
    if aux_ptr is Some {
        let root_node = loaded[root];
        map! {
            root => AllocationBranchNode::Index{
                pivots: root_node->pivots,
                children: root_node->children,
                aux_ptr,
            },
            aux_ptr.unwrap() => AllocationBranchNode::Auxiliary(summary),
        }
    } else {
        map! {}
    }
}

pub struct CachedBranch {
    pub sealed: bool,
    pub root: Pointer,
    pub seq_end: nat,
}

pub open spec fn init_mini_allocator(aus: Set<AU>) -> MiniAllocator
{
    MiniAllocator::empty().add_aus(aus)
}

impl CachedBranch {
    pub open spec fn wf(self) -> bool
    {
        &&& self.sealed ==> self.root is Some
    }

    pub open spec fn valid_allocator(self, mini_allocator: MiniAllocator) -> bool
    {
        &&& !self.sealed && self.root is Some ==> mini_allocator.all_aus().contains(self.root.unwrap().au)
    }

    pub open spec fn valid_init(self, init_aus: Set<AU>) -> bool
    {
        &&& self.wf()
        &&& (self.sealed ==> self.root is Some)
        &&& (!self.sealed ==> self.root is None)
        &&& if self.sealed {
            &&& self.root is Some
            &&& init_aus == Set::<AU>::empty()
        } else {
            &&& self.seq_end == 0
            &&& init_mini_allocator(init_aus).all_aus() == init_aus
        }
    }

    pub open spec fn can_query(self, mini_allocator: MiniAllocator, key: Key, depth: nat, read_nodes: LoadedBranch, needed: Set<Address>) -> bool
    {
        &&& self.wf()
        &&& self.valid_allocator(mini_allocator)
        &&& self.root is Some
        &&& loaded_query_ready_at_depth(self.root.unwrap(), read_nodes, key, depth)
        &&& needed == loaded_path_addrs_at_depth(self.root.unwrap(), read_nodes, key, depth)
        &&& covers(read_nodes.dom(), needed)
    }

    pub open spec fn query_result(self, key: Key, depth: nat, read_nodes: LoadedBranch) -> Message
        recommends
            self.wf(),
            self.root is Some,
            loaded_query_ready_at_depth(self.root.unwrap(), read_nodes, key, depth),
    {
        loaded_query_result_at_depth(self.root.unwrap(), read_nodes, key, depth)
    }

    pub open spec fn can_append(
        self,
        mini_allocator: MiniAllocator,
        keys: Seq<Key>,
        msgs: Seq<Message>,
        depth: nat,
        read_nodes: LoadedBranch,
        write_nodes: LoadedBranch,
        needed: Set<Address>,
    ) -> bool
    {
        &&& self.wf()
        &&& self.valid_allocator(mini_allocator)
        &&& !self.sealed
        &&& self.root is Some
        &&& keys.len() > 0
        &&& loaded_append_ready_at_depth(self.root.unwrap(), read_nodes, keys, msgs, depth)
        &&& write_nodes == loaded_append_write_nodes_at_depth(self.root.unwrap(), read_nodes, keys, msgs, depth)
        &&& needed == loaded_path_addrs_at_depth(self.root.unwrap(), read_nodes, keys[0], depth)
        &&& covers(read_nodes.dom(), needed)
    }

    pub open spec fn append(
        self,
        keys: Seq<Key>,
        msgs: Seq<Message>,
        depth: nat,
        read_nodes: LoadedBranch,
        write_nodes: LoadedBranch,
        needed: Set<Address>,
    ) -> Self
        recommends
            self.wf(),
    {
        Self {
            seq_end: self.seq_end + keys.len(),
            ..self
        }
    }

    pub open spec fn can_grow(
        self,
        mini_allocator: MiniAllocator,
        new_root_addr: Address,
        read_nodes: LoadedBranch,
        write_nodes: LoadedBranch,
    ) -> bool
    {
        &&& self.wf()
        &&& self.valid_allocator(mini_allocator)
        &&& !self.sealed
        &&& self.root is Some
        &&& read_nodes.contains_key(self.root.unwrap())
        &&& read_nodes[self.root.unwrap()].wf()
        &&& !(read_nodes[self.root.unwrap()] is Auxiliary)
        &&& write_nodes == loaded_grow_write_nodes(self.root.unwrap(), new_root_addr)
        &&& covers(read_nodes.dom(), root_needed(self.root))
        &&& mini_allocator.wf()
        &&& mini_allocator.can_allocate(new_root_addr)
    }

    pub open spec fn grow(
        self,
        mini_allocator: MiniAllocator,
        new_root_addr: Address,
        read_nodes: LoadedBranch,
        write_nodes: LoadedBranch,
    ) -> Self
        recommends
            self.can_grow(mini_allocator, new_root_addr, read_nodes, write_nodes),
    {
        Self {
            root: Some(new_root_addr),
            ..self
        }
    }

    pub open spec fn can_split(
        self,
        mini_allocator: MiniAllocator,
        new_child_addr: Address,
        pivot: Key,
        depth: nat,
        split_arg: SplitArg,
        read_nodes: LoadedBranch,
        write_nodes: LoadedBranch,
        needed: Set<Address>,
    ) -> bool
    {
        &&& self.wf()
        &&& self.valid_allocator(mini_allocator)
        &&& !self.sealed
        &&& self.root is Some
        &&& loaded_split_ready_at_depth(self.root.unwrap(), read_nodes, pivot, depth, split_arg)
        &&& write_nodes == loaded_split_write_nodes_at_depth(self.root.unwrap(), read_nodes, pivot, depth, split_arg, new_child_addr)
        &&& needed == loaded_path_addrs_at_depth(self.root.unwrap(), read_nodes, pivot, depth)
            .insert(loaded_split_child_addr_at_depth(self.root.unwrap(), read_nodes, pivot, depth))
        &&& covers(read_nodes.dom(), needed)
        &&& mini_allocator.wf()
        &&& mini_allocator.can_allocate(new_child_addr)
    }

    pub open spec fn split(
        self,
        mini_allocator: MiniAllocator,
        new_child_addr: Address,
        pivot: Key,
        depth: nat,
        split_arg: SplitArg,
        read_nodes: LoadedBranch,
        write_nodes: LoadedBranch,
        needed: Set<Address>,
    ) -> Self
        recommends
            self.can_split(mini_allocator, new_child_addr, pivot, depth, split_arg, read_nodes, write_nodes, needed),
    {
        Self {
            ..self
        }
    }

    pub open spec fn can_seal(
        self,
        mini_allocator: MiniAllocator,
        aux_ptr: Pointer,
        read_nodes: LoadedBranch,
        write_nodes: LoadedBranch,
    ) -> bool
    {
        &&& self.wf()
        &&& self.valid_allocator(mini_allocator)
        &&& !self.sealed
        &&& self.root is Some
        &&& read_nodes.contains_key(self.root.unwrap())
        &&& read_nodes[self.root.unwrap()].wf()
        &&& !(read_nodes[self.root.unwrap()] is Auxiliary)
        &&& covers(read_nodes.dom(), root_needed(self.root))
        &&& (aux_ptr is Some <==> read_nodes[self.root.unwrap()] is Index)
        &&& mini_allocator.wf()
        &&& (aux_ptr is Some ==> mini_allocator.can_allocate(aux_ptr.unwrap()))
        &&& write_nodes == loaded_seal_write_nodes(self.root.unwrap(), read_nodes, aux_ptr, mini_allocator.reserved_aus())
    }

    pub open spec fn seal(
        self,
        mini_allocator: MiniAllocator,
        aux_ptr: Pointer,
        read_nodes: LoadedBranch,
        write_nodes: LoadedBranch,
    ) -> Self
        recommends
            self.can_seal(mini_allocator, aux_ptr, read_nodes, write_nodes),
    {
        Self {
            sealed: true,
            ..self
        }
    }
}

} // verus!
