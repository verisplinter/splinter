// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::{map::*, set::*};

use verus_state_machines_macros::state_machine;

use crate::allocation_layer::AllocationBranch_v::{BranchNode as AllocationBranchNode, Summary};
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::LinkedBranch_v::SplitArg;
use crate::disk::GenericDisk_v::{AU, Address, Pointer};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Message, nop_delta};

verus! {

pub type LoadedBranch = Map<Address, AllocationBranchNode>;

pub open spec fn loaded_child_addr(root: Address, loaded: LoadedBranch, key: Key) -> Address
    recommends
        loaded_line_wf(loaded, root),
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

pub struct LoadedPathReceiptLine {
    pub addr: Address,
    pub node: AllocationBranchNode,
}

impl LoadedPathReceiptLine {
    pub open spec fn wf(self) -> bool
    {
        &&& self.node.wf()
        &&& !(self.node is Auxiliary)
        &&& self.node.keys_strictly_sorted()
    }
}

pub open spec fn loaded_line_wf(loaded: LoadedBranch, addr: Address) -> bool
{
    if loaded.contains_key(addr) {
        LoadedPathReceiptLine{addr, node: loaded[addr]}.wf()
    } else {
        false
    }
}

pub struct LoadedPathReceipt {
    pub key: Key,
    pub root: Address,
    pub lines: Seq<LoadedPathReceiptLine>,
}

impl LoadedPathReceipt {
    pub open spec fn wf(self) -> bool
    {
        &&& self.lines.len() > 0
        &&& self.lines[0].addr == self.root
        &&& forall |i: int| #![auto]
            0 <= i < self.lines.len() - 1
            ==> self.lines[i].node is Index
        &&& forall |i: int|
            0 <= i < self.lines.len()
            ==> #[trigger] self.lines[i].wf()
        &&& forall |i: int|
            0 <= i < self.lines.len() - 1
            ==> {
                let line = self.lines[i];
                let child_idx = line.node.route(self.key) + 1;
                &&& line.node->children[child_idx] == #[trigger] self.lines[i + 1].addr
            }
    }

    pub open spec fn valid_for(self, root: Address, loaded: LoadedBranch) -> bool
    {
        &&& self.wf()
        &&& self.root == root
        &&& self.needed_addrs() <= loaded.dom()
        &&& forall |i: int|
            0 <= i < self.lines.len()
            ==> {
                &&& loaded.contains_key(self.lines[i].addr)
                &&& #[trigger] loaded[self.lines[i].addr] == self.lines[i].node
            }
    }

    pub open spec fn depth(self) -> nat
        recommends self.lines.len() > 0
    {
        (self.lines.len() - 1) as nat
    }

    pub open spec fn needed_addrs(self) -> Set<Address>
    {
        Set::new(|addr: Address| exists |i: int|
            0 <= i < self.lines.len() && #[trigger] self.lines[i].addr == addr)
    }

    pub open spec fn target(self) -> LoadedPathReceiptLine
        recommends self.lines.len() > 0
    {
        self.lines.last()
    }

    pub open spec fn child_addr(self) -> Address
        recommends
            self.lines.len() > 0,
            self.target().node is Index,
    {
        let target = self.target().node;
        let child_idx = target.route(self.key) + 1;
        target->children[child_idx]
    }

    pub open spec fn tail(self) -> LoadedPathReceipt
        recommends self.lines.len() > 1
    {
        LoadedPathReceipt{
            key: self.key,
            root: self.lines[1].addr,
            lines: self.lines.skip(1),
        }
    }

    pub open spec fn path_equiv(self, other_key: Key) -> bool
    {
        forall |i: int|
            0 <= i < self.lines.len() - 1
            ==> self.lines[i].node.route(self.key) == #[trigger] self.lines[i].node.route(other_key)
    }

    pub open spec fn result(self) -> Message
        recommends
            self.lines.len() > 0,
            self.target().node is Leaf,
    {
        let leaf = self.target().node;
        let idx = leaf.route(self.key);
        if 0 <= idx && leaf->keys[idx] == self.key {
            leaf->msgs[idx]
        } else {
            Message::Update{delta: nop_delta()}
        }
    }
}

pub open spec fn root_summary_read_valid(root: Address, read_nodes: LoadedBranch) -> bool
{
    &&& read_nodes.contains_key(root)
    &&& if read_nodes[root] is Index {
        let aux_ptr = read_nodes[root]->aux_ptr;
        &&& aux_ptr is Some
        &&& read_nodes.contains_key(aux_ptr.unwrap())
        &&& read_nodes[aux_ptr.unwrap()] is Auxiliary
    } else {
        read_nodes[root] is Leaf
    }
}

pub open spec fn root_summary_from_read(root: Address, read_nodes: LoadedBranch) -> Summary
    recommends root_summary_read_valid(root, read_nodes)
{
    if read_nodes[root] is Index {
        let aux_ptr = read_nodes[root]->aux_ptr.unwrap();
        read_nodes[aux_ptr]->0
    } else {
        set![root.au]
    }
}

pub proof fn receipt_valid_implies_tail_valid(receipt: LoadedPathReceipt, loaded: LoadedBranch)
    requires
        receipt.valid_for(receipt.root, loaded),
        receipt.depth() > 0,
    ensures
        receipt.tail().valid_for(receipt.tail().root, loaded),
{
    let child_receipt = receipt.tail();
    assert(child_receipt.wf()) by {
        assert(child_receipt.lines.len() > 0);
        assert(child_receipt.lines.len() == receipt.lines.len() - 1);
        assert(child_receipt.lines[0].addr == child_receipt.root);
        assert forall |i: int| #![auto]
            0 <= i < child_receipt.lines.len() - 1
            implies child_receipt.lines[i].node is Index
        by {
            assert(child_receipt.lines[i] == receipt.lines[i + 1]);
            assert(receipt.lines[i + 1].node is Index);
        };
        assert forall |i: int|
            0 <= i < child_receipt.lines.len()
            implies #[trigger] child_receipt.lines[i].wf()
        by {
            assert(child_receipt.lines[i] == receipt.lines[i + 1]);
            assert(receipt.lines[i + 1].wf());
        };
        assert forall |i: int|
            0 <= i < child_receipt.lines.len() - 1
            implies {
                let line = child_receipt.lines[i];
                let child_idx = line.node.route(child_receipt.key) + 1;
                &&& line.node->children[child_idx] == #[trigger] child_receipt.lines[i + 1].addr
            }
        by {
            assert(child_receipt.lines[i] == receipt.lines[i + 1]);
            assert(child_receipt.lines[i + 1] == receipt.lines[i + 2]);
            assert(i + 1 < receipt.lines.len() - 1);
            assert(receipt.lines[i + 1].node is Index);
            assert(receipt.lines[i + 1].node->children[receipt.lines[i + 1].node.route(receipt.key) + 1]
                == receipt.lines[i + 2].addr);
        };
    }
    assert forall |i: int|
        0 <= i < child_receipt.lines.len()
        implies {
            &&& loaded.contains_key(child_receipt.lines[i].addr)
            &&& #[trigger] loaded[child_receipt.lines[i].addr] == child_receipt.lines[i].node
        }
    by {
        assert(child_receipt.lines[i] == receipt.lines[i + 1]);
    };
}

pub open spec fn loaded_has_route_at_depth(root: Address, loaded: LoadedBranch, key: Key, depth: nat) -> bool
    decreases depth
{
    &&& loaded_line_wf(loaded, root)
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

pub open spec(checked) fn loaded_append_ready(receipt: LoadedPathReceipt, loaded: LoadedBranch, keys: Seq<Key>, msgs: Seq<Message>) -> bool
    recommends keys.len() > 0,
{
    let first_key = keys[0];
    let last_key = keys.last();
    &&& receipt.key == first_key
    &&& keys.len() == msgs.len()
    &&& Key::is_strictly_sorted(keys)
    &&& receipt.valid_for(receipt.root, loaded)
    &&& receipt.target().node is Leaf
    &&& receipt.target().node->keys.len() > 0
    &&& Key::lt(receipt.target().node->keys.last(), first_key)
    &&& receipt.path_equiv(last_key)
}

pub open spec fn loaded_append_write_nodes(receipt: LoadedPathReceipt, keys: Seq<Key>, msgs: Seq<Message>) -> LoadedBranch
    recommends
        receipt.lines.len() > 0,
        receipt.target().node is Leaf,
{
    let leaf_addr = receipt.target().addr;
    let leaf = receipt.target().node;
    map! {
        leaf_addr => AllocationBranchNode::Leaf{
            keys: leaf->keys + keys,
            msgs: leaf->msgs + msgs,
        }
    }
}

pub open spec fn loaded_initialize_write_nodes(init_root: Address, keys: Seq<Key>, msgs: Seq<Message>) -> LoadedBranch
{
    map! {
        init_root => AllocationBranchNode::Leaf{keys, msgs}
    }
}

pub open spec fn loaded_has_index_route_at_depth(root: Address, loaded: LoadedBranch, key: Key, depth: nat) -> bool
    decreases depth
{
    &&& loaded_line_wf(loaded, root)
    &&& if depth == 0 {
        loaded[root] is Index
    } else {
        &&& loaded[root] is Index
        &&& loaded_has_index_route_at_depth(loaded_child_addr(root, loaded, key), loaded, key, (depth - 1) as nat)
    }
}

pub open spec fn loaded_index_path_addrs_at_depth(root: Address, loaded: LoadedBranch, key: Key, depth: nat) -> Set<Address>
    recommends loaded_has_index_route_at_depth(root, loaded, key, depth)
    decreases depth
{
    if depth == 0 {
        set! { root }
    } else {
        loaded_index_path_addrs_at_depth(loaded_child_addr(root, loaded, key), loaded, key, (depth - 1) as nat).insert(root)
    }
}

pub open spec fn loaded_index_target_addr_at_depth(root: Address, loaded: LoadedBranch, key: Key, depth: nat) -> Address
    recommends loaded_has_index_route_at_depth(root, loaded, key, depth)
    decreases depth
{
    if depth == 0 {
        root
    } else {
        loaded_index_target_addr_at_depth(loaded_child_addr(root, loaded, key), loaded, key, (depth - 1) as nat)
    }
}

pub open spec fn loaded_index_target_at_depth(root: Address, loaded: LoadedBranch, key: Key, depth: nat) -> AllocationBranchNode
    recommends loaded_has_index_route_at_depth(root, loaded, key, depth)
{
    loaded[loaded_index_target_addr_at_depth(root, loaded, key, depth)]
}

pub open spec fn loaded_split_ready(receipt: LoadedPathReceipt, loaded: LoadedBranch, split_arg: SplitArg) -> bool
{
    &&& receipt.key == split_arg.get_pivot()
    &&& receipt.valid_for(receipt.root, loaded)
    &&& receipt.target().node is Index
    &&& split_arg.get_pivot() == receipt.key
    &&& receipt.target().addr != receipt.child_addr()
    &&& loaded_line_wf(loaded, receipt.child_addr())
    &&& split_arg_matches_child(loaded[receipt.child_addr()], split_arg)
}

pub open spec fn loaded_split_write_nodes(receipt: LoadedPathReceipt, loaded: LoadedBranch, split_arg: SplitArg, new_child_addr: Address) -> LoadedBranch
    recommends loaded_split_ready(receipt, loaded, split_arg)
{
    let parent_addr = receipt.target().addr;
    let parent = receipt.target().node;
    let child_addr = receipt.child_addr();
    let child = loaded[child_addr];
    let child_idx = parent.route(receipt.key) + 1;
    let new_parent = AllocationBranchNode::Index{
        pivots: parent->pivots.insert(child_idx, receipt.key),
        children: parent->children.insert(child_idx + 1, new_child_addr),
        aux_ptr: None,
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
        loaded_line_wf(loaded, root),
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

state_machine!{ CachedBranch {
    fields {
        pub root: Pointer,
    }

    pub enum Label {
        Query{
            mini_allocator: MiniAllocator,
            receipt: LoadedPathReceipt,
            read_nodes: LoadedBranch,
            msg: Message,
        },
        Append{
            mini_allocator: MiniAllocator,
            receipt: LoadedPathReceipt,
            keys: Seq<Key>,
            msgs: Seq<Message>,
            read_nodes: LoadedBranch,
            write_nodes: LoadedBranch,
        },
        Initialize{
            mini_allocator: MiniAllocator,
            init_root: Address,
            keys: Seq<Key>,
            msgs: Seq<Message>,
            write_nodes: LoadedBranch,
        },
        Grow{
            mini_allocator: MiniAllocator,
            new_root_addr: Address,
            read_nodes: LoadedBranch,
            write_nodes: LoadedBranch,
        },
        Split{
            mini_allocator: MiniAllocator,
            new_child_addr: Address,
            receipt: LoadedPathReceipt,
            split_arg: SplitArg,
            read_nodes: LoadedBranch,
            write_nodes: LoadedBranch,
        },
        Seal{
            mini_allocator: MiniAllocator,
            aux_ptr: Pointer,
            read_nodes: LoadedBranch,
            write_nodes: LoadedBranch,
        },
        ResetEmpty,
        Internal,
    }

    init!{ init_state(root: Pointer) {
        init root = root;
    }}

    transition!{ query(lbl: Label) {
        require let Label::Query{mini_allocator, receipt, read_nodes, msg} = lbl;
        require pre.can_query(mini_allocator, receipt, read_nodes);
        require msg == pre.query_result(receipt, read_nodes);
    }}

    transition!{ append_step(lbl: Label) {
        require let Label::Append{mini_allocator, receipt, keys, msgs, read_nodes, write_nodes} = lbl;
        require pre.can_append(mini_allocator, receipt, keys, msgs, read_nodes, write_nodes);
    }}

    transition!{ initialize_branch(lbl: Label) {
        require let Label::Initialize{mini_allocator, init_root, keys, msgs, write_nodes} = lbl;
        require pre.can_initialize(mini_allocator, init_root, keys, msgs, write_nodes);
        update root = Some(init_root);
    }}

    transition!{ grow_step(lbl: Label) {
        require let Label::Grow{mini_allocator, new_root_addr, read_nodes, write_nodes} = lbl;
        require pre.can_grow(mini_allocator, new_root_addr, read_nodes, write_nodes);
        update root = Some(new_root_addr);
    }}

    transition!{ split_step(lbl: Label) {
        require let Label::Split{mini_allocator, new_child_addr, receipt, split_arg, read_nodes, write_nodes} = lbl;
        require pre.can_split(mini_allocator, new_child_addr, receipt, split_arg, read_nodes, write_nodes);
    }}

    transition!{ seal_step(lbl: Label) {
        require let Label::Seal{mini_allocator, aux_ptr, read_nodes, write_nodes} = lbl;
        require pre.can_seal(mini_allocator, aux_ptr, read_nodes, write_nodes);
    }}

    transition!{ reset_empty(lbl: Label) {
        require lbl is ResetEmpty;
        update root = None;
    }}

    transition!{ internal(lbl: Label) {
        require lbl is Internal;
    }}

    #[invariant]
    pub open spec fn inv(self) -> bool
    {
        self.wf()
    }

    #[inductive(init_state)]
    fn init_state_inductive(post: Self, root: Pointer) { }

    #[inductive(query)]
    fn query_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(append_step)]
    fn append_step_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(initialize_branch)]
    fn initialize_branch_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(grow_step)]
    fn grow_step_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(split_step)]
    fn split_step_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(seal_step)]
    fn seal_step_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(reset_empty)]
    fn reset_empty_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(internal)]
    fn internal_inductive(pre: Self, post: Self, lbl: Label) { }
}}

pub open spec fn init_mini_allocator(aus: Set<AU>) -> MiniAllocator
{
    MiniAllocator::empty().add_aus(aus)
}

impl CachedBranch::State {
    pub open spec fn empty_active() -> Self
    {
        Self { root: None }
    }

    pub open spec fn is_empty_active(self) -> bool
    {
        self == Self::empty_active()
    }

    pub open spec fn wf(self) -> bool
    {
        true
    }

    pub open spec fn valid_allocator(self, mini_allocator: MiniAllocator) -> bool
    {
        self.root is Some ==> mini_allocator.all_aus().contains(self.root.unwrap().au)
    }

    pub open spec fn ready_for_operation(self, mini_allocator: MiniAllocator) -> bool
    {
        &&& self.wf()
        &&& self.valid_allocator(mini_allocator)
        &&& self.root is Some
    }

    pub open spec fn ready_for_mutation(self, mini_allocator: MiniAllocator) -> bool
    {
        self.ready_for_operation(mini_allocator)
    }

    pub open spec fn can_query(self, mini_allocator: MiniAllocator, receipt: LoadedPathReceipt, read_nodes: LoadedBranch) -> bool
    {
        &&& self.ready_for_operation(mini_allocator)
        &&& receipt.valid_for(self.root.unwrap(), read_nodes)
        &&& receipt.target().node is Leaf
    }

    pub open spec fn query_result(self, receipt: LoadedPathReceipt, read_nodes: LoadedBranch) -> Message
        recommends
            self.wf(),
            self.root is Some,
            receipt.valid_for(self.root.unwrap(), read_nodes),
            receipt.target().node is Leaf,
    {
        receipt.result()
    }

    pub open spec fn can_append(
        self,
        mini_allocator: MiniAllocator,
        receipt: LoadedPathReceipt,
        keys: Seq<Key>,
        msgs: Seq<Message>,
        read_nodes: LoadedBranch,
        write_nodes: LoadedBranch,
    ) -> bool
    {
        &&& self.ready_for_mutation(mini_allocator)
        &&& keys.len() > 0
        &&& receipt.valid_for(self.root.unwrap(), read_nodes)
        &&& loaded_append_ready(receipt, read_nodes, keys, msgs)
        &&& write_nodes == loaded_append_write_nodes(receipt, keys, msgs)
    }

    pub open spec fn can_initialize(
        self,
        mini_allocator: MiniAllocator,
        init_root: Address,
        keys: Seq<Key>,
        msgs: Seq<Message>,
        write_nodes: LoadedBranch,
    ) -> bool
    {
        &&& self.is_empty_active()
        &&& mini_allocator.wf()
        &&& mini_allocator.allocated_aus() == Set::<AU>::empty()
        &&& mini_allocator.can_allocate(init_root)
        &&& keys.len() > 0
        &&& keys.len() == msgs.len()
        &&& Key::is_strictly_sorted(keys)
        &&& write_nodes == loaded_initialize_write_nodes(init_root, keys, msgs)
    }

    pub open spec fn initialize(
        self,
        init_root: Address,
        keys: Seq<Key>,
        msgs: Seq<Message>,
        write_nodes: LoadedBranch,
    ) -> Self
        recommends
            self.wf(),
    {
        Self { root: Some(init_root) }
    }

    pub open spec fn append(
        self,
        receipt: LoadedPathReceipt,
        keys: Seq<Key>,
        msgs: Seq<Message>,
        read_nodes: LoadedBranch,
        write_nodes: LoadedBranch,
    ) -> Self
        recommends
            self.wf(),
    {
        self
    }

    pub open spec fn can_grow(
        self,
        mini_allocator: MiniAllocator,
        new_root_addr: Address,
        read_nodes: LoadedBranch,
        write_nodes: LoadedBranch,
    ) -> bool
    {
        &&& self.ready_for_mutation(mini_allocator)
        &&& loaded_line_wf(read_nodes, self.root.unwrap())
        &&& write_nodes == loaded_grow_write_nodes(self.root.unwrap(), new_root_addr)
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
        receipt: LoadedPathReceipt,
        split_arg: SplitArg,
        read_nodes: LoadedBranch,
        write_nodes: LoadedBranch,
    ) -> bool
    {
        &&& self.ready_for_mutation(mini_allocator)
        &&& receipt.valid_for(self.root.unwrap(), read_nodes)
        &&& loaded_split_ready(receipt, read_nodes, split_arg)
        &&& write_nodes == loaded_split_write_nodes(receipt, read_nodes, split_arg, new_child_addr)
        &&& mini_allocator.wf()
        &&& mini_allocator.can_allocate(new_child_addr)
    }

    pub open spec fn split(
        self,
        mini_allocator: MiniAllocator,
        new_child_addr: Address,
        receipt: LoadedPathReceipt,
        split_arg: SplitArg,
        read_nodes: LoadedBranch,
        write_nodes: LoadedBranch,
    ) -> Self
        recommends
            self.can_split(mini_allocator, new_child_addr, receipt, split_arg, read_nodes, write_nodes),
    {
        self
    }

    pub open spec fn can_seal(
        self,
        mini_allocator: MiniAllocator,
        aux_ptr: Pointer,
        read_nodes: LoadedBranch,
        write_nodes: LoadedBranch,
    ) -> bool
    {
        &&& self.ready_for_mutation(mini_allocator)
        &&& loaded_line_wf(read_nodes, self.root.unwrap())
        &&& (aux_ptr is Some <==> read_nodes[self.root.unwrap()] is Index)
        &&& mini_allocator.wf()
        &&& (aux_ptr is Some ==> mini_allocator.can_allocate(aux_ptr.unwrap()))
        &&& (aux_ptr is Some ==> mini_allocator.allocated_aus().contains(aux_ptr.unwrap().au))
        &&& write_nodes == loaded_seal_write_nodes(self.root.unwrap(), read_nodes, aux_ptr, mini_allocator.allocated_aus())
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
        self
    }
}

pub proof fn receipt_valid_implies_loaded_path_at_depth(receipt: LoadedPathReceipt, loaded: LoadedBranch)
    requires
        receipt.valid_for(receipt.root, loaded),
        receipt.target().node is Leaf,
    ensures
        loaded_has_route_at_depth(receipt.root, loaded, receipt.key, receipt.depth()),
        loaded_path_addrs_at_depth(receipt.root, loaded, receipt.key, receipt.depth()) == receipt.needed_addrs(),
        loaded_target_addr_at_depth(receipt.root, loaded, receipt.key, receipt.depth()) == receipt.target().addr,
        loaded_target_at_depth(receipt.root, loaded, receipt.key, receipt.depth()) == receipt.target().node,
    decreases receipt.depth(),
{
    let depth = receipt.depth();
    if depth == 0 {
        assert(receipt.lines.len() == 1);
        assert(receipt.lines[0].node is Leaf);
        assert(receipt.target().addr == receipt.root);
        assert(receipt.target().node == loaded[receipt.root]);
        assert(loaded[receipt.root] == receipt.lines[0].node);
        assert(receipt.lines[0].wf());
        assert(loaded.contains_key(receipt.root));
        assert(loaded[receipt.root].wf());
        assert(!(loaded[receipt.root] is Auxiliary));
        assert(loaded[receipt.root].keys_strictly_sorted());
        assert(loaded[receipt.root] is Leaf);
        assert(loaded_has_route_at_depth(receipt.root, loaded, receipt.key, depth));
        assert(receipt.needed_addrs() == set!{receipt.root}) by {
            assert forall |addr: Address| #[trigger] receipt.needed_addrs().contains(addr) implies set!{receipt.root}.contains(addr) by {
                let i = choose |i: int| 0 <= i < receipt.lines.len() && #[trigger] receipt.lines[i].addr == addr;
                assert(i == 0);
            };
            assert forall |addr: Address| #[trigger] set!{receipt.root}.contains(addr) implies receipt.needed_addrs().contains(addr) by {
                assert(receipt.lines[0].addr == receipt.root);
            };
        };
    } else {
        let child_receipt = receipt.tail();
        assert(child_receipt.target().node is Leaf);
        receipt_valid_implies_tail_valid(receipt, loaded);
        receipt_valid_implies_loaded_path_at_depth(child_receipt, loaded);
        assert(loaded[receipt.root] == receipt.lines[0].node);
        assert(receipt.lines[0].wf());
        assert(loaded.contains_key(receipt.root));
        assert(loaded[receipt.root].wf());
        assert(!(loaded[receipt.root] is Auxiliary));
        assert(loaded[receipt.root].keys_strictly_sorted());
        assert(loaded[receipt.root] is Index);
        let child_addr = loaded_child_addr(receipt.root, loaded, receipt.key);
        assert(child_addr == child_receipt.root);
        assert(loaded_has_route_at_depth(receipt.root, loaded, receipt.key, depth));
        assert(loaded_target_addr_at_depth(receipt.root, loaded, receipt.key, depth)
            == loaded_target_addr_at_depth(child_receipt.root, loaded, receipt.key, (depth - 1) as nat));
        assert(loaded_target_at_depth(receipt.root, loaded, receipt.key, depth)
            == loaded_target_at_depth(child_receipt.root, loaded, receipt.key, (depth - 1) as nat));
        assert(receipt.target().addr == child_receipt.target().addr);
        assert(receipt.target().node == child_receipt.target().node);
        assert(receipt.needed_addrs() == child_receipt.needed_addrs().insert(receipt.root)) by {
            assert forall |addr: Address|
                #[trigger] receipt.needed_addrs().contains(addr)
                implies child_receipt.needed_addrs().insert(receipt.root).contains(addr)
            by {
                let i = choose |i: int| 0 <= i < receipt.lines.len() && #[trigger] receipt.lines[i].addr == addr;
                if i == 0 {
                } else {
                    assert(child_receipt.lines[i - 1] == receipt.lines[i]);
                    assert(child_receipt.needed_addrs().contains(addr));
                }
            };
            assert forall |addr: Address|
                #[trigger] child_receipt.needed_addrs().insert(receipt.root).contains(addr)
                implies receipt.needed_addrs().contains(addr)
            by {
                if addr == receipt.root {
                    assert(receipt.lines[0].addr == receipt.root);
                } else {
                    assert(child_receipt.needed_addrs().contains(addr));
                    let i = choose |i: int| 0 <= i < child_receipt.lines.len() && #[trigger] child_receipt.lines[i].addr == addr;
                    assert(receipt.lines[i + 1] == child_receipt.lines[i]);
                }
            };
        };
    }
}

pub proof fn receipt_valid_implies_loaded_index_path_at_depth(receipt: LoadedPathReceipt, loaded: LoadedBranch)
    requires
        receipt.valid_for(receipt.root, loaded),
        receipt.target().node is Index,
    ensures
        loaded_has_index_route_at_depth(receipt.root, loaded, receipt.key, receipt.depth()),
        loaded_index_path_addrs_at_depth(receipt.root, loaded, receipt.key, receipt.depth()) == receipt.needed_addrs(),
        loaded_index_target_addr_at_depth(receipt.root, loaded, receipt.key, receipt.depth()) == receipt.target().addr,
        loaded_index_target_at_depth(receipt.root, loaded, receipt.key, receipt.depth()) == receipt.target().node,
    decreases receipt.depth(),
{
    let depth = receipt.depth();
    if depth == 0 {
        assert(receipt.lines.len() == 1);
        assert(receipt.lines[0].node is Index);
        assert(receipt.target().addr == receipt.root);
        assert(receipt.target().node == loaded[receipt.root]);
        assert(loaded[receipt.root] == receipt.lines[0].node);
        assert(receipt.lines[0].wf());
        assert(loaded.contains_key(receipt.root));
        assert(loaded[receipt.root].wf());
        assert(!(loaded[receipt.root] is Auxiliary));
        assert(loaded[receipt.root].keys_strictly_sorted());
        assert(loaded[receipt.root] is Index);
        assert(loaded_has_index_route_at_depth(receipt.root, loaded, receipt.key, depth));
        assert(receipt.needed_addrs() == set!{receipt.root}) by {
            assert forall |addr: Address| #[trigger] receipt.needed_addrs().contains(addr) implies set!{receipt.root}.contains(addr) by {
                let i = choose |i: int| 0 <= i < receipt.lines.len() && #[trigger] receipt.lines[i].addr == addr;
                assert(i == 0);
            };
            assert forall |addr: Address| #[trigger] set!{receipt.root}.contains(addr) implies receipt.needed_addrs().contains(addr) by {
                assert(receipt.lines[0].addr == receipt.root);
            };
        };
    } else {
        let child_receipt = receipt.tail();
        assert(child_receipt.target().node is Index);
        receipt_valid_implies_tail_valid(receipt, loaded);
        receipt_valid_implies_loaded_index_path_at_depth(child_receipt, loaded);
        assert(loaded[receipt.root] == receipt.lines[0].node);
        assert(receipt.lines[0].wf());
        assert(loaded.contains_key(receipt.root));
        assert(loaded[receipt.root].wf());
        assert(!(loaded[receipt.root] is Auxiliary));
        assert(loaded[receipt.root].keys_strictly_sorted());
        assert(loaded[receipt.root] is Index);
        let child_addr = loaded_child_addr(receipt.root, loaded, receipt.key);
        assert(child_addr == child_receipt.root);
        assert(loaded_has_index_route_at_depth(receipt.root, loaded, receipt.key, depth));
        assert(loaded_index_target_addr_at_depth(receipt.root, loaded, receipt.key, depth)
            == loaded_index_target_addr_at_depth(child_receipt.root, loaded, receipt.key, (depth - 1) as nat));
        assert(loaded_index_target_at_depth(receipt.root, loaded, receipt.key, depth)
            == loaded_index_target_at_depth(child_receipt.root, loaded, receipt.key, (depth - 1) as nat));
        assert(receipt.target().addr == child_receipt.target().addr);
        assert(receipt.target().node == child_receipt.target().node);
        assert(receipt.needed_addrs() == child_receipt.needed_addrs().insert(receipt.root)) by {
            assert forall |addr: Address|
                #[trigger] receipt.needed_addrs().contains(addr)
                implies child_receipt.needed_addrs().insert(receipt.root).contains(addr)
            by {
                let i = choose |i: int| 0 <= i < receipt.lines.len() && #[trigger] receipt.lines[i].addr == addr;
                if i == 0 {
                } else {
                    assert(child_receipt.lines[i - 1] == receipt.lines[i]);
                    assert(child_receipt.needed_addrs().contains(addr));
                }
            };
            assert forall |addr: Address|
                #[trigger] child_receipt.needed_addrs().insert(receipt.root).contains(addr)
                implies receipt.needed_addrs().contains(addr)
            by {
                if addr == receipt.root {
                    assert(receipt.lines[0].addr == receipt.root);
                } else {
                    assert(child_receipt.needed_addrs().contains(addr));
                    let i = choose |i: int| 0 <= i < child_receipt.lines.len() && #[trigger] child_receipt.lines[i].addr == addr;
                    assert(receipt.lines[i + 1] == child_receipt.lines[i]);
                }
            };
        };
    }
}

pub proof fn receipt_query_matches_loaded_query_result_at_depth(receipt: LoadedPathReceipt, loaded: LoadedBranch)
    requires
        receipt.valid_for(receipt.root, loaded),
        receipt.target().node is Leaf,
    ensures
        loaded_query_ready_at_depth(receipt.root, loaded, receipt.key, receipt.depth()),
        loaded_query_result_at_depth(receipt.root, loaded, receipt.key, receipt.depth()) == receipt.result(),
    decreases receipt.depth(),
{
    receipt_valid_implies_loaded_path_at_depth(receipt, loaded);
    let depth = receipt.depth();
    if depth == 0 {
        let leaf = loaded[receipt.root];
        let idx = leaf.route(receipt.key);
        assert(receipt.target().node == leaf);
    } else {
        let child_receipt = receipt.tail();
        receipt_valid_implies_tail_valid(receipt, loaded);
        receipt_query_matches_loaded_query_result_at_depth(child_receipt, loaded);
        let child_addr = loaded_child_addr(receipt.root, loaded, receipt.key);
        assert(child_addr == child_receipt.root);
        assert(receipt.result() == child_receipt.result());
    }
}

} // verus!
