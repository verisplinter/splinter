// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::map::*;
use vstd::assert_maps_equal;

use crate::allocation_layer::AllocationBranch_v::Summary;
use crate::betree::LinkedBranch_v::{DiskView as SpecDiskView, LinkedBranch as SpecLinkedBranch, Node as SpecNode, Path as SpecPath, SplitArg};
use crate::disk::GenericDisk_v::{AU, Address};
pub use crate::implementation::IBranchNode_v::IBranchNode as BranchNode;
use crate::implementation::MiniAllocatorImpl_v::MiniAllocatorImpl;
use crate::implementation::PageAllocator_v::PageAllocator;
use crate::spec::ImplDisk_t::{IAddress, IAU};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Delta, Message};

verus! {

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BranchError {
    MissingRoot,
    MissingNode,
    RootIsAuxiliary,
    ChildIsAuxiliary,
    InvalidLeaf,
    InvalidIndex,
    InvalidSummary,
    InvalidAppend,
    InvalidSplit,
    InvalidSeal,
    InvalidCommit,
    AlreadySealed,
    AlreadyInitialized,
    Uninitialized,
    AddressInUse,
    RootMustBeIndex,
    CycleDetected,
    UnexpectedAuxiliaryPointer,
    AllocatorUnavailable,
    SmokeCheckFailed,
}

pub trait BranchStore {
    fn contains(&self, addr: &IAddress) -> bool;
    fn read(&self, addr: &IAddress) -> Option<BranchNode>;
    fn insert_fresh(&mut self, addr: IAddress, node: BranchNode) -> Result<(), BranchError>;
    fn overwrite(&mut self, addr: IAddress, node: BranchNode) -> Result<(), BranchError>;
}

pub struct MemBranchStore {
    pub entries: Vec<(IAddress, BranchNode)>,
}

#[derive(Clone, Copy, Debug)]
pub struct BranchPathFrame {
    pub addr: IAddress,
    pub child_idx: usize,
}

#[derive(Clone, Copy, Debug)]
struct SplitTarget {
    parent_addr: IAddress,
    child_idx: usize,
    child_addr: IAddress,
}

#[derive(Clone, Copy, Debug)]
pub struct BranchImpl {
    pub root: IAddress,
}

fn same_iaddr(left: &IAddress, right: &IAddress) -> (out: bool)
    ensures
        out ==> left@ == right@,
        !out ==> left@ != right@,
{
    let out = left.au == right.au && left.page == right.page;
    if out {
        assert(left.au as nat == right.au as nat);
        assert(left.page as nat == right.page as nat);
    } else {
        assert(left.au != right.au || left.page != right.page);
    }
    out
}

fn find_store_index(entries: &Vec<(IAddress, BranchNode)>, addr: &IAddress) -> (out: Option<usize>)
    ensures
        out is Some ==> out.unwrap() < entries.len(),
        out is Some ==> entries[out.unwrap() as int].0@ == addr@,
        out is None ==> forall |i: int| 0 <= i < entries@.len() ==> entries@[i].0@ != addr@,
{
    let mut idx = 0usize;
    while idx < entries.len()
        invariant
            idx <= entries.len(),
            forall |i: int| 0 <= i < idx ==> entries@[i].0@ != addr@,
        decreases entries.len() - idx,
    {
        if same_iaddr(&entries[idx].0, addr) {
            return Some(idx);
        }
        proof {
            assert(entries@[idx as int].0@ != addr@);
        }
        idx += 1;
    }
    None
}

fn key_lt(left: Key, right: Key) -> bool {
    left.0 < right.0
}

fn key_lte(left: Key, right: Key) -> bool {
    left.0 <= right.0
}

fn keys_strictly_sorted(keys: &Vec<Key>) -> bool {
    if keys.len() == 0 {
        return true;
    }
    let mut idx = 1usize;
    while idx < keys.len()
        invariant
            1 <= idx <= keys.len(),
        decreases keys.len() - idx,
    {
        if !key_lt(keys[idx - 1], keys[idx]) {
            return false;
        }
        idx += 1;
    }
    true
}

fn summary_sorted_unique(summary_aus: &Vec<IAU>) -> bool {
    if summary_aus.len() == 0 {
        return true;
    }
    let mut idx = 1usize;
    while idx < summary_aus.len()
        invariant
            1 <= idx <= summary_aus.len(),
        decreases summary_aus.len() - idx,
    {
        if summary_aus[idx - 1] >= summary_aus[idx] {
            return false;
        }
        idx += 1;
    }
    true
}

fn route_index(pivots: &Vec<Key>, key: Key) -> (out: usize)
    ensures
        out <= pivots.len(),
{
    let mut idx = 0usize;
    while idx < pivots.len() && key_lte(pivots[idx], key)
        invariant
            idx <= pivots.len(),
        decreases pivots.len() - idx,
    {
        idx += 1;
    }
    idx
}

fn find_exact_key(keys: &Vec<Key>, key: Key) -> (out: Option<usize>)
    ensures
        out is Some ==> out.unwrap() < keys.len(),
{
    let mut idx = 0usize;
    while idx < keys.len()
        invariant
            idx <= keys.len(),
        decreases keys.len() - idx,
    {
        if keys[idx].0 == key.0 {
            return Some(idx);
        }
        idx += 1;
    }
    None
}

fn split_leaf_index(keys: &Vec<Key>, pivot: Key) -> (out: usize)
    ensures
        out <= keys.len(),
{
    let mut idx = 0usize;
    while idx < keys.len() && key_lt(keys[idx], pivot)
        invariant
            idx <= keys.len(),
        decreases keys.len() - idx,
    {
        idx += 1;
    }
    idx
}

fn clone_key_range(keys: &Vec<Key>, start: usize, end: usize) -> Vec<Key>
    requires
        start <= end,
        end <= keys.len(),
{
    let mut out = Vec::new();
    let mut idx = start;
    while idx < end
        invariant
            start <= idx <= end,
            end <= keys.len(),
        decreases end - idx,
    {
        out.push(keys[idx]);
        idx += 1;
    }
    out
}

fn clone_msg_range(msgs: &Vec<Message>, start: usize, end: usize) -> Vec<Message>
    requires
        start <= end,
        end <= msgs.len(),
{
    let mut out = Vec::new();
    let mut idx = start;
    while idx < end
        invariant
            start <= idx <= end,
            end <= msgs.len(),
        decreases end - idx,
    {
        out.push(msgs[idx]);
        idx += 1;
    }
    out
}

fn clone_addr_range(addrs: &Vec<IAddress>, start: usize, end: usize) -> Vec<IAddress>
    requires
        start <= end,
        end <= addrs.len(),
{
    let mut out = Vec::new();
    let mut idx = start;
    while idx < end
        invariant
            start <= idx <= end,
            end <= addrs.len(),
        decreases end - idx,
    {
        out.push(addrs[idx]);
        idx += 1;
    }
    out
}

fn vec_contains_addr(addrs: &Vec<IAddress>, needle: &IAddress) -> bool {
    let mut idx = 0usize;
    while idx < addrs.len()
        invariant
            idx <= addrs.len(),
        decreases addrs.len() - idx,
    {
        if same_iaddr(&addrs[idx], needle) {
            return true;
        }
        idx += 1;
    }
    false
}

pub fn allocate_fresh_addr(allocator: &mut PageAllocator) -> IAddress {
    let addr = allocator.peek_next_addr();
    allocator.advance_next_addr();
    addr
}

pub fn allocate_fresh_addr_from_mini(
    allocator: &mut MiniAllocatorImpl,
) -> (result: Result<IAddress, BranchError>)
    requires
        old(allocator).wf(),
    ensures
        allocator.wf(),
        result is Ok ==> old(allocator).allocation_ready(),
        result is Err ==> *allocator == *old(allocator),
{
    match allocator.allocate_fresh_addr() {
        Some(addr) => Ok(addr),
        None => Err(BranchError::AllocatorUnavailable),
    }
}

impl MemBranchStore {
    pub fn new() -> (out: Self)
        ensures
            out.wf(),
            out@.entries == Map::<Address, SpecNode<Summary>>::empty(),
    {
        let out = Self { entries: Vec::new() };
        proof {
            assert_maps_equal!(
                out@.entries,
                Map::<Address, SpecNode<Summary>>::empty(),
                addr => {
                    if out@.entries.contains_key(addr) {
                        let idx = choose |i: int| 0 <= i < out.entries@.len()
                            && #[trigger] out.entries@[i].0@ == addr;
                        assert(false);
                    }
                }
            );
        }
        out
    }

    pub open spec fn unique_addrs(entries: Seq<(IAddress, BranchNode)>) -> bool
    {
        forall |i: int, j: int|
            0 <= i < entries.len() && 0 <= j < entries.len() && entries[i].0@ == entries[j].0@
            ==> i == j
    }

    pub open spec fn wf(self) -> bool
    {
        Self::unique_addrs(self.entries@)
    }

    pub fn insert_fresh(&mut self, addr: IAddress, node: BranchNode) -> (result: Result<(), BranchError>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            result is Ok ==> self@.entries == old(self)@.entries.insert(addr@, node@),
            result is Err ==> self@ == old(self)@,
            !old(self)@.entries.contains_key(addr@) ==> result is Ok,
    {
        let ghost pre_entries = self.entries@;
        if find_store_index(&self.entries, &addr).is_some() {
            proof {
                assert(self@ == old(self)@);
            }
            return Err(BranchError::AddressInUse);
        }
        self.entries.push((addr, node));
        proof {
            assert(self.entries@ == pre_entries.push((addr, node)));
            assert forall |i: int, j: int|
                0 <= i < self.entries@.len()
                && 0 <= j < self.entries@.len()
                && self.entries@[i].0@ == self.entries@[j].0@
                implies i == j by {
                if i < pre_entries.len() && j < pre_entries.len() {
                    assert(pre_entries[i].0@ == pre_entries[j].0@);
                    assert(old(self).wf());
                } else if i == pre_entries.len() && j == pre_entries.len() {
                } else if i == pre_entries.len() {
                    assert(self.entries@[i].0@ == addr@);
                    assert(self.entries@[j].0@ == pre_entries[j].0@);
                    assert(pre_entries[j].0@ != addr@);
                } else {
                    assert(j == pre_entries.len());
                    assert(self.entries@[j].0@ == addr@);
                    assert(self.entries@[i].0@ == pre_entries[i].0@);
                    assert(pre_entries[i].0@ != addr@);
                }
            }
            assert(self@.entries =~= old(self)@.entries.insert(addr@, node@)) by {
                assert forall |a: Address| #[trigger] self@.entries.contains_key(a)
                    == old(self)@.entries.insert(addr@, node@).contains_key(a) by {
                    if self@.entries.contains_key(a) {
                        let k = choose |k: int| 0 <= k < self.entries@.len()
                            && self.entries@[k].0@ == a;
                        if k == pre_entries.len() {
                            assert(a == addr@);
                        } else {
                            assert(pre_entries[k].0@ == a);
                            assert(old(self)@.entries.contains_key(a));
                        }
                    }
                    if old(self)@.entries.insert(addr@, node@).contains_key(a) {
                        if a == addr@ {
                            assert(self.entries@[pre_entries.len() as int].0@ == a);
                            assert(self@.entries.contains_key(a));
                        } else {
                            assert(old(self)@.entries.contains_key(a));
                            let k = choose |k: int| 0 <= k < pre_entries.len()
                                && pre_entries[k].0@ == a;
                            assert(self.entries@[k].0@ == a);
                            assert(self@.entries.contains_key(a));
                        }
                    }
                }
                assert forall |a: Address| self@.entries.contains_key(a) implies
                    #[trigger] self@.entries[a]
                        == old(self)@.entries.insert(addr@, node@)[a] by {
                    if a == addr@ {
                        let k = choose |k: int| 0 <= k < self.entries@.len()
                            && self.entries@[k].0@ == a;
                        assert(k == pre_entries.len() as int);
                    } else {
                        let k = choose |k: int| 0 <= k < self.entries@.len()
                            && self.entries@[k].0@ == a;
                        assert(k != pre_entries.len());
                        assert(self.entries@[k] == pre_entries[k]);
                        let old_k = choose |old_k: int| 0 <= old_k < pre_entries.len()
                            && pre_entries[old_k].0@ == a;
                        assert(old_k == k);
                    }
                }
            }
        }
        Ok(())
    }

    pub fn overwrite(&mut self, addr: IAddress, node: BranchNode) -> (result: Result<(), BranchError>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            result is Ok ==> self@.entries == old(self)@.entries.insert(addr@, node@),
            result is Err ==> self@ == old(self)@,
            old(self)@.entries.contains_key(addr@) ==> result is Ok,
    {
        let ghost pre_entries = self.entries@;
        match find_store_index(&self.entries, &addr) {
            Some(idx) => {
                self.entries[idx] = (addr, node);
                proof {
                    assert(pre_entries[idx as int].0@ == addr@);
                    assert(self.entries@ == pre_entries.update(idx as int, (addr, node)));
                    assert forall |i: int, j: int|
                        0 <= i < self.entries@.len()
                        && 0 <= j < self.entries@.len()
                        && self.entries@[i].0@ == self.entries@[j].0@
                        implies i == j by {
                        assert(self.entries@[i].0@ == pre_entries[i].0@);
                        assert(self.entries@[j].0@ == pre_entries[j].0@);
                        assert(old(self).wf());
                    }
                    assert(self@.entries =~= old(self)@.entries.insert(addr@, node@)) by {
                        assert forall |a: Address| #[trigger] self@.entries.contains_key(a)
                            == old(self)@.entries.insert(addr@, node@).contains_key(a) by {
                            if self@.entries.contains_key(a) {
                                let k = choose |k: int| 0 <= k < self.entries@.len()
                                    && self.entries@[k].0@ == a;
                                if k == idx as int {
                                    assert(a == addr@);
                                } else {
                                    assert(pre_entries[k].0@ == a);
                                    assert(old(self)@.entries.contains_key(a));
                                }
                            }
                            if old(self)@.entries.insert(addr@, node@).contains_key(a) {
                                if a == addr@ {
                                    assert(self.entries@[idx as int].0@ == a);
                                    assert(self@.entries.contains_key(a));
                                } else {
                                    assert(old(self)@.entries.contains_key(a));
                                    let k = choose |k: int| 0 <= k < pre_entries.len()
                                        && pre_entries[k].0@ == a;
                                    assert(k != idx as int);
                                    assert(self.entries@[k].0@ == a);
                                    assert(self@.entries.contains_key(a));
                                }
                            }
                        }
                        assert forall |a: Address| self@.entries.contains_key(a) implies
                            #[trigger] self@.entries[a]
                                == old(self)@.entries.insert(addr@, node@)[a] by {
                            if a == addr@ {
                                let k = choose |k: int| 0 <= k < self.entries@.len()
                                    && self.entries@[k].0@ == a;
                                assert(self.entries@[k].0@ == self.entries@[idx as int].0@);
                                assert(k == idx as int);
                            } else {
                                let k = choose |k: int| 0 <= k < self.entries@.len()
                                    && self.entries@[k].0@ == a;
                                assert(k != idx as int);
                                assert(self.entries@[k] == pre_entries[k]);
                                let old_k = choose |old_k: int| 0 <= old_k < pre_entries.len()
                                    && pre_entries[old_k].0@ == a;
                                assert(pre_entries[old_k].0@ == pre_entries[k].0@);
                                assert(old_k == k);
                            }
                        }
                    }
                }
                Ok(())
            }
            None => {
                proof {
                    assert(self@ == old(self)@);
                }
                Err(BranchError::MissingNode)
            },
        }
    }

    pub fn read_checked(&self, addr: &IAddress) -> (out: Option<BranchNode>)
        requires
            self.wf(),
        ensures
            out is Some ==> {
                &&& self@.entries.contains_key(addr@)
                &&& out.unwrap()@ == self@.entries[addr@]
            },
            out is None ==> !self@.entries.contains_key(addr@),
    {
        match find_store_index(&self.entries, addr) {
            Some(idx) => {
                let node = self.entries[idx].1.clone_checked();
                proof {
                    assert(self.entries@[idx as int].0@ == addr@);
                    assert(self@.entries.contains_key(addr@));
                    assert(self@.entries[addr@] == self.entries@[idx as int].1@) by {
                        let chosen = choose |i: int| 0 <= i < self.entries@.len()
                            && self.entries@[i].0@ == addr@;
                        assert(self.entries@[chosen].0@ == self.entries@[idx as int].0@);
                        assert(chosen == idx as int);
                    }
                    assert(node@ == self.entries@[idx as int].1@);
                }
                Some(node)
            },
            None => {
                proof {
                    assert(!self@.entries.contains_key(addr@)) by {
                        if self@.entries.contains_key(addr@) {
                            let idx = choose |i: int| 0 <= i < self.entries@.len()
                                && self.entries@[i].0@ == addr@;
                            assert(false);
                        }
                    }
                }
                None
            },
        }
    }
}

impl View for MemBranchStore {
    type V = SpecDiskView<Summary>;

    open spec fn view(&self) -> Self::V
    {
        SpecDiskView {
            entries: Map::new(
                |addr: Address| exists |i: int| 0 <= i < self.entries@.len() && self.entries@[i].0@ == addr,
                |addr: Address| {
                    let i = choose |i: int| 0 <= i < self.entries@.len() && self.entries@[i].0@ == addr;
                    self.entries@[i].1@
                },
            ),
        }
    }
}

impl BranchStore for MemBranchStore {
    fn contains(&self, addr: &IAddress) -> bool {
        find_store_index(&self.entries, addr).is_some()
    }

    fn read(&self, addr: &IAddress) -> Option<BranchNode> {
        match find_store_index(&self.entries, addr) {
            Some(idx) => Some(self.entries[idx].1.clone()),
            None => None,
        }
    }

    fn insert_fresh(&mut self, addr: IAddress, node: BranchNode) -> Result<(), BranchError> {
        if find_store_index(&self.entries, &addr).is_some() {
            return Err(BranchError::AddressInUse);
        }
        self.entries.push((addr, node));
        Ok(())
    }

    fn overwrite(&mut self, addr: IAddress, node: BranchNode) -> Result<(), BranchError> {
        match find_store_index(&self.entries, &addr) {
            Some(idx) => {
                self.entries[idx] = (addr, node);
                Ok(())
            }
            None => Err(BranchError::MissingNode),
        }
    }
}

impl BranchImpl {
    pub open spec fn i(self, store: &MemBranchStore) -> SpecLinkedBranch<Summary>
    {
        SpecLinkedBranch { root: self.root@, disk_view: store@ }
    }

    pub open spec fn inv(self, store: &MemBranchStore) -> bool
    {
        &&& store.wf()
        &&& self.i(store).inv()
        &&& self.i(store).tight_disk_view()
    }

    pub open spec fn sealed_inv(self, store: &MemBranchStore) -> bool
    {
        &&& store.wf()
        &&& self.i(store).valid_sealed_branch()
        &&& self.i(store).tight_disk_view_with_summary()
    }

    pub open spec fn invariants(self, store: &MemBranchStore) -> bool
    {
        ||| self.inv(store)
        ||| self.sealed_inv(store)
    }

    pub fn new(root: IAddress) -> (out: Self)
        ensures
            out.root == root,
            out.root@ == root@,
    {
        Self { root }
    }

    fn read_node(&self, store: &MemBranchStore, addr: &IAddress) -> Result<BranchNode, BranchError> {
        match store.read(addr) {
            Some(node) => Ok(node),
            None => {
                if same_iaddr(addr, &self.root) {
                    Err(BranchError::MissingRoot)
                } else {
                    Err(BranchError::MissingNode)
                }
            }
        }
    }

    fn ensure_root_unsealed(&self, store: &MemBranchStore) -> Result<(), BranchError> {
        match self.read_node(store, &self.root)? {
            BranchNode::Leaf { .. } => Ok(()),
            BranchNode::Index { aux_ptr, .. } => {
                if aux_ptr.is_some() {
                    Err(BranchError::AlreadySealed)
                } else {
                    Ok(())
                }
            }
            BranchNode::Auxiliary { .. } => Err(BranchError::RootIsAuxiliary),
        }
    }

    pub fn root_aux_ptr(&self, store: &MemBranchStore) -> Result<Option<IAddress>, BranchError> {
        match self.read_node(store, &self.root)? {
            BranchNode::Leaf { .. } => Ok(None),
            BranchNode::Index { aux_ptr, .. } => Ok(aux_ptr),
            BranchNode::Auxiliary { .. } => Err(BranchError::RootIsAuxiliary),
        }
    }

    fn find_leaf(&self, store: &MemBranchStore, key: Key) -> Result<IAddress, BranchError>
        requires
            self.invariants(store),
    {
        let mut current = self.root;
        let mut remaining = store.entries.len();

        while remaining > 0
            invariant
                remaining <= store.entries.len(),
            decreases remaining,
        {
            remaining -= 1;
            match self.read_node(store, &current)? {
                BranchNode::Leaf { .. } => return Ok(current),
                BranchNode::Index { pivots, children, .. } => {
                    let child_idx = route_index(&pivots, key);
                    if child_idx >= children.len() {
                        return Err(BranchError::InvalidIndex);
                    }
                    current = children[child_idx];
                }
                BranchNode::Auxiliary { .. } => return Err(BranchError::RootIsAuxiliary),
            }
        }

        Err(BranchError::CycleDetected)
    }

    pub fn find_leaf_for_key(&self, store: &MemBranchStore, key: Key) -> Result<IAddress, BranchError>
        requires
            self.invariants(store),
    {
        self.find_leaf(store, key)
    }

    fn find_split_target(&self, store: &MemBranchStore, pivot: Key) -> Result<SplitTarget, BranchError>
        requires
            self.inv(store),
    {
        let mut current = self.root;
        let mut remaining = store.entries.len();

        while remaining > 0
            invariant
                remaining <= store.entries.len(),
            decreases remaining,
        {
            remaining -= 1;
            let current_node = self.read_node(store, &current)?;
            let (pivots, children) = match current_node {
                BranchNode::Index { pivots, children, .. } => (pivots, children),
                BranchNode::Leaf { .. } => return Err(BranchError::RootMustBeIndex),
                BranchNode::Auxiliary { .. } => return Err(BranchError::RootIsAuxiliary),
            };

            let child_idx = route_index(&pivots, pivot);
            if child_idx >= children.len() {
                return Err(BranchError::InvalidIndex);
            }
            let child_addr = children[child_idx];
            match self.read_node(store, &child_addr)? {
                BranchNode::Leaf { .. } => {
                    return Ok(SplitTarget { parent_addr: current, child_idx, child_addr });
                }
                BranchNode::Index { pivots: child_pivots, .. } => {
                    if find_exact_key(&child_pivots, pivot).is_some() {
                        return Ok(SplitTarget { parent_addr: current, child_idx, child_addr });
                    }
                    current = child_addr;
                }
                BranchNode::Auxiliary { .. } => return Err(BranchError::ChildIsAuxiliary),
            }
        }

        Err(BranchError::CycleDetected)
    }

    pub fn query(&self, store: &MemBranchStore, key: Key) -> Result<Message, BranchError>
        requires
            self.invariants(store),
    {
        let leaf_addr = self.find_leaf(store, key)?;
        match self.read_node(store, &leaf_addr)? {
            BranchNode::Leaf { keys, msgs } => {
                match find_exact_key(&keys, key) {
                    Some(idx) => {
                        if idx >= msgs.len() {
                            return Err(BranchError::InvalidLeaf);
                        }
                        Ok(msgs[idx])
                    },
                    None => Ok(Message::Update { delta: Delta(0) }),
                }
            }
            _ => Err(BranchError::InvalidLeaf),
        }
    }

    pub fn append(&self, store: &mut MemBranchStore, keys: Vec<Key>, msgs: Vec<Message>) -> (result: Result<(), BranchError>)
        requires
            self.inv(old(store)),
        ensures
            result is Ok ==> store.wf(),
    {
        self.ensure_root_unsealed(store)?;

        if keys.is_empty() || keys.len() != msgs.len() || !keys_strictly_sorted(&keys) {
            return Err(BranchError::InvalidAppend);
        }

        let leaf_addr = self.find_leaf(store, keys[0])?;
        match self.read_node(store, &leaf_addr)? {
            BranchNode::Leaf { keys: mut existing_keys, msgs: mut existing_msgs } => {
                if existing_keys.is_empty() || existing_keys.len() != existing_msgs.len() {
                    return Err(BranchError::InvalidAppend);
                }
                if !key_lt(existing_keys[existing_keys.len() - 1], keys[0]) {
                    return Err(BranchError::InvalidAppend);
                }

                let mut idx = 0usize;
                while idx < keys.len()
                    invariant
                        idx <= keys.len(),
                        existing_keys.len() == existing_msgs.len(),
                    decreases keys.len() - idx,
                {
                    existing_keys.push(keys[idx]);
                    existing_msgs.push(msgs[idx]);
                    idx += 1;
                }

                store.overwrite(leaf_addr, BranchNode::Leaf { keys: existing_keys, msgs: existing_msgs })?;
                Ok(())
            }
            _ => Err(BranchError::InvalidAppend),
        }
    }

    pub fn grow(&mut self, store: &mut MemBranchStore, allocator: &mut MiniAllocatorImpl) -> (result: Result<(), BranchError>)
        requires
            old(self).inv(old(store)),
            old(allocator).wf(),
        ensures
            result is Ok ==> store.wf(),
            result is Ok ==> allocator.wf(),
    {
        self.ensure_root_unsealed(store)?;

        let new_root = allocate_fresh_addr_from_mini(allocator)?;
        store.insert_fresh(
            new_root,
            BranchNode::Index { pivots: Vec::new(), children: vec![self.root], aux_ptr: None },
        )?;
        self.root = new_root;
        Ok(())
    }

    pub fn split(&self, store: &mut MemBranchStore, pivot: Key, allocator: &mut MiniAllocatorImpl) -> (result: Result<(), BranchError>)
        requires
            self.inv(old(store)),
            old(allocator).wf(),
        ensures
            result is Ok ==> store.wf(),
            result is Ok ==> allocator.wf(),
    {
        self.ensure_root_unsealed(store)?;

        let target = self.find_split_target(store, pivot)?;
        let parent_node = self.read_node(store, &target.parent_addr)?;
        let (mut parent_pivots, mut parent_children, parent_aux_ptr) = match parent_node {
            BranchNode::Index { pivots, children, aux_ptr } => (pivots, children, aux_ptr),
            _ => return Err(BranchError::InvalidSplit),
        };

        let child_node = self.read_node(store, &target.child_addr)?;
        let new_child_addr = allocate_fresh_addr_from_mini(allocator)?;

        match child_node {
            BranchNode::Leaf { keys, msgs } => {
                if keys.len() != msgs.len() {
                    return Err(BranchError::InvalidLeaf);
                }
                let split_idx = split_leaf_index(&keys, pivot);
                if split_idx == 0 || split_idx >= keys.len() {
                    return Err(BranchError::InvalidSplit);
                }

                let left_keys = clone_key_range(&keys, 0, split_idx);
                let left_msgs = clone_msg_range(&msgs, 0, split_idx);
                let right_keys = clone_key_range(&keys, split_idx, keys.len());
                let right_msgs = clone_msg_range(&msgs, split_idx, msgs.len());

                store.overwrite(target.child_addr, BranchNode::Leaf { keys: left_keys, msgs: left_msgs })?;
                store.insert_fresh(new_child_addr, BranchNode::Leaf { keys: right_keys, msgs: right_msgs })?;
            }
            BranchNode::Index { pivots, children, aux_ptr } => {
                if aux_ptr.is_some() {
                    return Err(BranchError::InvalidSplit);
                }
                if children.len() == 0 || children.len() - 1 != pivots.len() {
                    return Err(BranchError::InvalidIndex);
                }

                let pivot_idx = match find_exact_key(&pivots, pivot) {
                    Some(idx) => idx,
                    None => return Err(BranchError::InvalidSplit),
                };
                if pivot_idx >= children.len() {
                    return Err(BranchError::InvalidIndex);
                }
                assert(pivot_idx < pivots.len());
                assert(children.len() == pivots.len() + 1);
                assert(pivot_idx + 1 <= children.len());

                let left_pivots = clone_key_range(&pivots, 0, pivot_idx);
                let left_children = clone_addr_range(&children, 0, pivot_idx + 1);
                let right_pivots = clone_key_range(&pivots, pivot_idx + 1, pivots.len());
                let right_children = clone_addr_range(&children, pivot_idx + 1, children.len());

                store.overwrite(
                    target.child_addr,
                    BranchNode::Index { pivots: left_pivots, children: left_children, aux_ptr: None },
                )?;
                store.insert_fresh(
                    new_child_addr,
                    BranchNode::Index { pivots: right_pivots, children: right_children, aux_ptr: None },
                )?;
            }
            BranchNode::Auxiliary { .. } => return Err(BranchError::InvalidSplit),
        }

        if parent_children.len() == 0 || parent_children.len() - 1 != parent_pivots.len() {
            return Err(BranchError::InvalidIndex);
        }
        if target.child_idx > parent_pivots.len() || target.child_idx >= parent_children.len() {
            return Err(BranchError::InvalidIndex);
        }
        assert(target.child_idx + 1 <= parent_children.len());
        parent_pivots.insert(target.child_idx, pivot);
        parent_children.insert(target.child_idx + 1, new_child_addr);
        store.overwrite(
            target.parent_addr,
            BranchNode::Index { pivots: parent_pivots, children: parent_children, aux_ptr: parent_aux_ptr },
        )?;

        Ok(())
    }

    pub fn seal(&self, store: &mut MemBranchStore, allocator: &mut MiniAllocatorImpl) -> (result: Result<(), BranchError>)
        requires
            self.inv(old(store)),
            old(allocator).wf(),
        ensures
            result is Ok ==> store.wf(),
            result is Ok ==> allocator.wf(),
    {
        match self.read_node(store, &self.root)? {
            BranchNode::Leaf { .. } => Ok(()),
            BranchNode::Index { pivots, children, aux_ptr } => {
                if aux_ptr.is_some() {
                    return Err(BranchError::AlreadySealed);
                }

                let aux_addr = allocate_fresh_addr_from_mini(allocator)?;
                let summary_aus = vec![aux_addr.au];

                store.insert_fresh(aux_addr, BranchNode::Auxiliary { summary_aus })?;
                store.overwrite(
                    self.root,
                    BranchNode::Index { pivots, children, aux_ptr: Some(aux_addr) },
                )?;
                Ok(())
            }
            BranchNode::Auxiliary { .. } => Err(BranchError::RootIsAuxiliary),
        }
    }
}

} // verus!
