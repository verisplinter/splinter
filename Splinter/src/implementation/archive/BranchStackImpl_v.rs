// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::map::*;
use vstd::assert_maps_equal;
use vstd::assert_sets_equal;
use vstd::pervasive::unreached;

use crate::allocation_layer::AllocationBranch_v::{
    BranchNode as SpecBranchNode, Summary,
};
use crate::allocation_layer::MiniAllocator_v::{
    MiniAllocator, PageAllocator as SpecMiniPageAllocator,
};
use crate::betree::LinkedBranch_v::{
    LinkedBranch as SpecLinkedBranch, Path as SpecPath, Refinement_v as LinkedBranchRefinement,
};
use crate::disk::GenericDisk_v::Ranking;
use crate::implementation::AtomicBranchState_v::{
    AtomicBranchImage, AtomicBranchState, empty_branch_image, query_from_receipts_up_to,
    query_receipts_read_addrs, query_receipts_valid, query_roots, to_branch_nodes,
};
use crate::implementation::AuPoolImpl_v::{iau_vec_set, AuAllocation};
use crate::implementation::BranchImpl_v::{
    allocate_fresh_addr_from_mini, BranchError, BranchImpl, BranchNode, BranchStore, MemBranchStore,
};
use crate::implementation::Cache_v::{Cache, Entry};
use crate::implementation::CachedBranch_v::{
    loaded_append_ready, loaded_append_write_nodes, loaded_grow_write_nodes, loaded_line_wf,
    loaded_initialize_write_nodes, loaded_seal_write_nodes, receipt_valid_implies_tail_valid, CachedBranch, LoadedBranch,
    LoadedPathReceipt, LoadedPathReceiptLine, root_summary_from_read, root_summary_read_valid,
};
use crate::implementation::CachingDiskBranch_v::{
    root_aus_up_to, root_aus_up_to_contains, root_aus_up_to_member_has_index,
};
use crate::implementation::FracCacheImpl_v::{
    FetchErrorCode, FracCacheImpl, MutHandle, ReserveWriteResult, PAGE_SIZE_BYTES,
};
use crate::implementation::IBranchNode_v::{iaddr_seq, iau_seq, iau_seq_set, iopt_addr};
use crate::implementation::MiniAllocatorImpl_v::MiniAllocatorImpl;
use crate::implementation::DiskLayout_v::{spec_superblock_addr, superblock_addr};
use crate::implementation::OverflowFiction_v::convert_overflow_into_liveness_failure;
use crate::disk::GenericDisk_v::AU;
use crate::marshalling::IBranchNodeFormat_v::{
    BranchNodePageFmt, leaf_entry_seq, raw_page_to_branch_node,
};
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::WF_v::WF;
use crate::spec::AsyncDisk_t::{Address, RawPage};
use crate::spec::ImplDisk_t::{IAddress, IAU, IPage};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Delta, Message, Value};

verus! {

pub const BRANCH_FREE_AU_THRESHOLD: IAU = 5;
pub const BRANCH_GROW_LEAF_THRESHOLD: usize = 4;

pub struct BranchImageImpl {
    pub sealed_roots: Vec<IAddress>,
    pub seq_end: usize,
}

impl BranchImageImpl {
    pub open spec fn wf(&self) -> bool
    {
        true
    }

    pub open spec fn roots_wf(&self) -> bool
    {
        forall |i: int| 0 <= i < self.sealed_roots@.len()
            ==> #[trigger] self.sealed_roots@[i]@.wf()
    }

    pub open spec fn roots_bounded(&self, total_aus: IAU) -> bool
    {
        forall |i: int| 0 <= i < self@.sealed_roots.len()
            ==> #[trigger] self@.sealed_roots[i].au < total_aus as nat
    }

    pub fn empty() -> (out: Self)
        ensures
            out.wf(),
            out@ == (AtomicBranchImage{sealed_roots: Seq::empty(), seq_end: 0}),
            out.sealed_roots@.len() == 0,
    {
        Self { sealed_roots: Vec::new(), seq_end: 0 }
    }

    pub fn from_parts(sealed_roots: Vec<IAddress>, seq_end: u64) -> (out: Self)
        requires
            forall |i: int| 0 <= i < sealed_roots@.len()
                ==> #[trigger] sealed_roots@[i]@.wf(),
        ensures
            out.wf(),
            out.roots_wf(),
            out@ == (AtomicBranchImage{
                sealed_roots: iaddr_seq(sealed_roots@),
                seq_end: seq_end as nat,
            }),
            out.sealed_roots@ == sealed_roots@,
            out.seq_end as nat == seq_end as nat,
    {
        if seq_end > usize::MAX as u64 {
            convert_overflow_into_liveness_failure();
        }
        Self { sealed_roots, seq_end: seq_end as usize }
    }
}

impl View for BranchImageImpl {
    type V = AtomicBranchImage;

    open spec fn view(&self) -> Self::V
    {
        AtomicBranchImage {
            sealed_roots: iaddr_seq(self.sealed_roots@),
            seq_end: self.seq_end as nat,
        }
    }
}

pub struct BranchSummaryImpl {
    pub entries: Vec<(IAU, Vec<IAU>)>,
}

impl BranchSummaryImpl {
    pub open spec fn wf(&self) -> bool
    {
        forall |i: int, j: int| 0 <= i < self.entries@.len() && 0 <= j < self.entries@.len()
            && #[trigger] self.entries@[i].0 == #[trigger] self.entries@[j].0
            ==> i == j
    }

    pub open spec fn i(&self) -> Map<nat, Summary>
    {
        let entries = self.entries@;
        Map::new(
            |au: nat| exists |idx: int| 0 <= idx < entries.len() && entries[idx].0 as nat == au,
            |au: nat| {
                let idx = choose |idx: int| 0 <= idx < entries.len() && entries[idx].0 as nat == au;
                iau_seq_set(entries[idx].1@)
            }
        )
    }

    pub fn new() -> (out: Self)
        ensures
            out.wf(),
            out.i() == Map::<nat, Summary>::empty(),
    {
        Self { entries: Vec::new() }
    }

    fn find_root_au(&self, root_au: IAU) -> (out: Option<usize>)
        ensures
            out is Some ==> out.unwrap() < self.entries.len(),
            out is Some ==> self.entries@[out.unwrap() as int].0 == root_au,
            out is None ==> forall |i: int| 0 <= i < self.entries@.len()
                ==> #[trigger] self.entries@[i].0 != root_au,
    {
        let mut idx: usize = 0;
        while idx < self.entries.len()
            invariant
                idx <= self.entries.len(),
                forall |i: int| 0 <= i < idx ==> #[trigger] self.entries@[i].0 != root_au,
            decreases self.entries.len() - idx,
        {
            if self.entries[idx].0 == root_au {
                return Some(idx);
            }
            idx = idx + 1;
        }
        None
    }

    pub fn contains_root_au(&self, root_au: IAU) -> (out: bool)
    {
        self.find_root_au(root_au).is_some()
    }

    pub fn insert_or_update(&mut self, root_au: IAU, discovered_aus: Vec<IAU>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self.i().dom().contains(root_au as nat),
            self.i()[root_au as nat] == iau_seq_set(discovered_aus@),
            self.i() == old(self).i().insert(root_au as nat, iau_seq_set(discovered_aus@)),
            self.i().dom() =~= old(self).i().dom().insert(root_au as nat),
    {
        match self.find_root_au(root_au) {
            Some(idx) => {
                let ghost old_entries = self.entries@;
                self.entries[idx] = (root_au, discovered_aus);
                proof {
                    assert(exists |i: int| 0 <= i < self.entries@.len()
                        && #[trigger] self.entries@[i].0 as nat == root_au as nat) by {
                        assert(self.entries@[idx as int].0 as nat == root_au as nat);
                    }
                    assert(self.i().dom().contains(root_au as nat));
                    assert(self.i()[root_au as nat] == iau_seq_set(discovered_aus@)) by {
                        let chosen = choose |i: int|
                            0 <= i < self.entries@.len()
                                && #[trigger] self.entries@[i].0 as nat == root_au as nat;
                        assert(chosen == idx as int) by {
                            assert(self.entries@[chosen].0 == root_au);
                            assert(self.entries@[idx as int].0 == root_au);
                            assert(self.wf());
                        }
                    }
                    assert forall |au: nat| #[trigger] self.i().dom().contains(au)
                        <==> old(self).i().dom().insert(root_au as nat).contains(au)
                    by {
                        if au == root_au as nat {
                        } else {
                            if self.i().dom().contains(au) {
                                let witness = choose |i: int|
                                    0 <= i < self.entries@.len()
                                        && #[trigger] self.entries@[i].0 as nat == au;
                                if witness == idx as int {
                                    assert(self.entries@[witness].0 == root_au);
                                    assert(false);
                                } else {
                                    assert(self.entries@[witness] == old_entries[witness]);
                                    assert(old(self).i().dom().contains(au));
                                }
                            }
                            if old(self).i().dom().insert(root_au as nat).contains(au) {
                                assert(au != root_au as nat);
                                assert(old(self).i().dom().contains(au));
                                let witness = choose |i: int|
                                    0 <= i < old_entries.len()
                                        && #[trigger] old_entries[i].0 as nat == au;
                                if witness == idx as int {
                                    assert(old_entries[witness].0 == root_au);
                                    assert(au == root_au as nat);
                                    assert(false);
                                } else {
                                    assert(self.entries@[witness] == old_entries[witness]);
                                    assert(self.i().dom().contains(au));
                                }
                            }
                        }
                    };
                    assert_maps_equal!(
                        self.i(),
                        old(self).i().insert(root_au as nat, iau_seq_set(discovered_aus@)),
                        au => {
                            if au == root_au as nat {
                                assert(self.i()[au] == iau_seq_set(discovered_aus@));
                            } else {
                                if self.i().contains_key(au) {
                                    let witness = choose |i: int|
                                        0 <= i < self.entries@.len()
                                            && #[trigger] self.entries@[i].0 as nat == au;
                                    assert(witness != idx as int);
                                    assert(self.entries@[witness] == old_entries[witness]);
                                    assert(old(self).i().contains_key(au));
                                    let old_chosen = choose |i: int|
                                        0 <= i < old_entries.len()
                                            && #[trigger] old_entries[i].0 as nat == au;
                                    assert(old_chosen == witness) by {
                                        assert(old_entries[old_chosen].0 == old_entries[witness].0);
                                        assert(old(self).wf());
                                    }
                                    let new_chosen = choose |i: int|
                                        0 <= i < self.entries@.len()
                                            && #[trigger] self.entries@[i].0 as nat == au;
                                    assert(new_chosen == witness) by {
                                        assert(self.entries@[new_chosen].0 == self.entries@[witness].0);
                                        assert(self.wf());
                                    }
                                    assert(self.i()[au] == old(self).i()[au]);
                                }
                            }
                        }
                    );
                }
            },
            None => {
                let ghost old_entries = self.entries@;
                self.entries.push((root_au, discovered_aus));
                proof {
                    assert(exists |i: int| 0 <= i < self.entries@.len()
                        && #[trigger] self.entries@[i].0 as nat == root_au as nat) by {
                        let last = old_entries.len();
                        assert(self.entries@[last as int].0 as nat == root_au as nat);
                    }
                    assert(self.i().dom().contains(root_au as nat));
                    assert(self.i()[root_au as nat] == iau_seq_set(discovered_aus@)) by {
                        let chosen = choose |i: int|
                            0 <= i < self.entries@.len()
                                && #[trigger] self.entries@[i].0 as nat == root_au as nat;
                        assert(chosen == old_entries.len()) by {
                            if chosen != old_entries.len() {
                                assert(0 <= chosen < old_entries.len());
                                assert(old_entries[chosen].0 == root_au);
                                assert(false);
                            }
                        }
                    }
                    assert forall |au: nat| #[trigger] self.i().dom().contains(au)
                        <==> old(self).i().dom().insert(root_au as nat).contains(au)
                    by {
                        let last = old_entries.len();
                        if self.i().dom().contains(au) {
                            let witness = choose |i: int|
                                0 <= i < self.entries@.len()
                                    && #[trigger] self.entries@[i].0 as nat == au;
                            if witness == last {
                                assert(au == root_au as nat);
                            } else {
                                assert(0 <= witness < old_entries.len());
                                assert(self.entries@[witness] == old_entries[witness]);
                                assert(old(self).i().dom().contains(au));
                            }
                        }
                        if old(self).i().dom().insert(root_au as nat).contains(au) {
                            if au == root_au as nat {
                            } else {
                                assert(old(self).i().dom().contains(au));
                                let witness = choose |i: int|
                                    0 <= i < old_entries.len()
                                        && #[trigger] old_entries[i].0 as nat == au;
                                assert(self.entries@[witness] == old_entries[witness]);
                                assert(self.i().dom().contains(au));
                            }
                        }
                    };
                    assert_maps_equal!(
                        self.i(),
                        old(self).i().insert(root_au as nat, iau_seq_set(discovered_aus@)),
                        au => {
                            if au == root_au as nat {
                                assert(self.i()[au] == iau_seq_set(discovered_aus@));
                            } else {
                                if self.i().contains_key(au) {
                                    let witness = choose |i: int|
                                        0 <= i < self.entries@.len()
                                            && #[trigger] self.entries@[i].0 as nat == au;
                                    assert(witness != old_entries.len());
                                    assert(0 <= witness < old_entries.len());
                                    assert(self.entries@[witness] == old_entries[witness]);
                                    assert(old(self).i().contains_key(au));
                                    let old_chosen = choose |i: int|
                                        0 <= i < old_entries.len()
                                            && #[trigger] old_entries[i].0 as nat == au;
                                    assert(old_chosen == witness) by {
                                        assert(old_entries[old_chosen].0 == old_entries[witness].0);
                                        assert(old(self).wf());
                                    }
                                    let new_chosen = choose |i: int|
                                        0 <= i < self.entries@.len()
                                            && #[trigger] self.entries@[i].0 as nat == au;
                                    assert(new_chosen == witness) by {
                                        assert(self.entries@[new_chosen].0 == self.entries@[witness].0);
                                        assert(self.wf());
                                    }
                                    assert(self.i()[au] == old(self).i()[au]);
                                }
                            }
                        }
                    );
                }
            }
        }
    }
}

pub enum CommitPhase {
    Idle,
    InFlight { prefix_len: usize, seq_end: usize, prepared: bool },
}

#[derive(Clone, Copy, Debug)]
pub enum BranchLoadState {
    AwaitingSuperblock,
    LoadingMetadata { next_root_idx: usize },
    MetadataLoaded,
}

#[derive(Clone, Copy, Debug)]
pub enum BranchMetadataReadKind {
    Root { root_idx: usize },
    Aux { root_idx: usize, root: IAddress, aux: IAddress },
}

pub enum BranchMetadataStepResult {
    NeedCacheLoad { addr: IAddress, handle: MutHandle, kind: BranchMetadataReadKind },
    RootComplete { root: IAddress, reads: Ghost<Map<Address, RawPage>>, discovered_aus: Vec<IAU> },
    AllComplete,
    Blocked,
}

pub enum BranchReplayAppendResult {
    Appended{
        prepared_cache: Ghost<Cache::State>,
        branch_reads: Ghost<Map<Address, RawPage>>,
        writes: Ghost<Map<Address, RawPage>>,
        receipt: Ghost<LoadedPathReceipt>,
        init_root: Ghost<Option<Address>>,
    },
    NeedCacheLoad{addr: IAddress, handle: MutHandle},
    NeedsAUs,
    CacheFull,
    Blocked,
}

pub enum BranchQueryResult {
    Hit{
        value: Value,
        msg: Ghost<Message>,
        reads: Ghost<Map<Address, RawPage>>,
        receipts: Ghost<Seq<LoadedPathReceipt>>,
    },
    NeedCacheLoad{addr: IAddress, handle: MutHandle},
    Blocked,
}

pub enum BranchPathLoadResult {
    Loaded{
        leaf: IAddress,
        reads: Ghost<Map<Address, RawPage>>,
        receipt: Ghost<LoadedPathReceipt>,
    },
    NeedCacheLoad{addr: IAddress, handle: MutHandle},
    CacheFull,
    Blocked,
}

pub enum BranchMaintenanceResult {
    Grew{
        new_root_addr: IAddress,
        reads: Ghost<Map<Address, RawPage>>,
        writes: Ghost<Map<Address, RawPage>>,
    },
    GrewAfterPrepare{
        new_root_addr: IAddress,
        reads: Ghost<Map<Address, RawPage>>,
        writes: Ghost<Map<Address, RawPage>>,
    },
    NeedsAUs,
    CacheFull,
    Noop,
    Blocked,
}

pub enum BranchSealResult {
    Sealed{
        root: IAddress,
        aux_ptr: Option<IAddress>,
        summary_aus: Vec<IAU>,
        reads: Ghost<Map<Address, RawPage>>,
        writes: Ghost<Map<Address, RawPage>>,
    },
    SealedAfterPrepare{
        root: IAddress,
        aux_ptr: Option<IAddress>,
        summary_aus: Vec<IAU>,
        reads: Ghost<Map<Address, RawPage>>,
        writes: Ghost<Map<Address, RawPage>>,
        prepared_cache: Ghost<Cache::State>,
    },
    NeedsAUs,
    CacheFull,
    Blocked,
}

fn same_message(left: &Message, right: &Message) -> (out: bool)
    ensures
        out ==> *left == *right,
{
    match (*left, *right) {
        (Message::Define{value: left_value}, Message::Define{value: right_value}) => {
            left_value.0 == right_value.0
        },
        (Message::Update{delta: left_delta}, Message::Update{delta: right_delta}) => {
            left_delta.0 == right_delta.0
        },
        _ => false,
    }
}

fn same_key_vec(left: &Vec<Key>, right: &Vec<Key>) -> (out: bool)
    ensures
        out ==> left@ == right@,
{
    if left.len() != right.len() {
        return false;
    }
    let mut idx = 0usize;
    while idx < left.len()
        invariant
            idx <= left.len(),
            left.len() == right.len(),
            forall |i: int| 0 <= i < idx ==> left@[i] == right@[i],
        decreases left.len() - idx,
    {
        if left[idx] != right[idx] {
            return false;
        }
        idx += 1;
    }
    proof {
        assert(left@ == right@);
    }
    true
}

fn same_message_vec(left: &Vec<Message>, right: &Vec<Message>) -> (out: bool)
    ensures
        out ==> left@ == right@,
{
    if left.len() != right.len() {
        return false;
    }
    let mut idx = 0usize;
    while idx < left.len()
        invariant
            idx <= left.len(),
            left.len() == right.len(),
            forall |i: int| 0 <= i < idx ==> left@[i] == right@[i],
        decreases left.len() - idx,
    {
        if !same_message(&left[idx], &right[idx]) {
            return false;
        }
        idx += 1;
    }
    proof {
        assert(left@ == right@);
    }
    true
}

fn same_iaddr_local(left: &IAddress, right: &IAddress) -> (out: bool)
    ensures
        out ==> left@ == right@,
        !out ==> left@ != right@,
{
    let out = left.au == right.au && left.page == right.page;
    if out {
        assert(left.au as nat == right.au as nat);
        assert(left.page as nat == right.page as nat);
    }
    out
}

proof fn bounded_index_branch_node_marshallable(node: &BranchNode)
    requires
        node.wf(),
        node is Index,
        node->pivots.len() <= BranchNodePageFmt::spec_new().index_routes_fmt.max_length,
        node->pivots.len() <= u8::MAX as int,
    ensures
        BranchNodePageFmt::spec_new().marshallable(node.parsedv()),
        BranchNodePageFmt::spec_new().impl_marshallable(*node),
        BranchNodePageFmt::spec_new().spec_size(node.parsedv()) == PAGE_SIZE_BYTES,
{
    let fmt = BranchNodePageFmt::spec_new();
    match node {
        BranchNode::Index{pivots, children, aux_ptr} => {
            let routes = crate::marshalling::IBranchNodeFormat_v::route_image_seq(
                pivots@,
                iaddr_seq(children@),
            );
            assert(children.len() == pivots.len() + 1);
            assert(routes.len() == pivots@.len());
            fmt.index_routes_fmt.eltf.uniform_size_matches_spec_size();
            assert forall |i: int| 0 <= i < routes.len()
                implies #[trigger] fmt.index_routes_fmt.marshallable_at(routes, i) by {
                assert(routes[i].pivot == pivots@[i]);
                assert(routes[i].child == children@[i + 1]@);
                assert(fmt.index_routes_fmt.eltf.marshallable(routes[i]));
                assert(fmt.index_routes_fmt.eltf.spec_size(routes[i])
                    == fmt.index_routes_fmt.eltf.uniform_size());
            }
            assert(routes.len() <= u8::MAX as int);
            assert(routes.len() <= fmt.index_routes_fmt.max_length);
            assert(fmt.index_routes_fmt.marshallable(routes));
            assert(fmt.index_meta_fmt.impl_marshallable(
                crate::marshalling::IBranchNodeFormat_v::IBranchIndexMeta{
                    first_child: children[0],
                    aux_ptr: *aux_ptr,
                },
            ));
            assert forall |i: int| 0 <= i < pivots.len()
                implies #[trigger] fmt.index_routes_fmt.eltf.impl_marshallable(
                    crate::marshalling::IBranchNodeFormat_v::IBranchIndexRoute{
                        pivot: pivots[i],
                        child: children[i + 1],
                    },
                ) by {
                assert(pivots[i].wf());
                assert(children[i + 1].wf());
            }
            assert(fmt.marshallable(node.parsedv()));
            assert(fmt.impl_marshallable(*node));
            assert(fmt.spec_size(node.parsedv()) == fmt.uniform_size());
            assert(fmt.uniform_size() == PAGE_SIZE_BYTES);
        },
        _ => {},
    }
}

fn same_iaddr_vec(left: &Vec<IAddress>, right: &Vec<IAddress>) -> (out: bool)
    ensures
        out ==> iaddr_seq(left@) == iaddr_seq(right@),
{
    if left.len() != right.len() {
        return false;
    }
    let mut idx = 0usize;
    while idx < left.len()
        invariant
            idx <= left.len(),
            left.len() == right.len(),
            forall |i: int| 0 <= i < idx ==> left@[i]@ == right@[i]@,
        decreases left.len() - idx,
    {
        if !same_iaddr_local(&left[idx], &right[idx]) {
            return false;
        }
        idx += 1;
    }
    proof {
        assert(iaddr_seq(left@) == iaddr_seq(right@));
    }
    true
}

fn same_iau_vec(left: &Vec<IAU>, right: &Vec<IAU>) -> (out: bool)
    ensures
        out ==> iau_seq(left@) == iau_seq(right@),
{
    if left.len() != right.len() {
        return false;
    }
    let mut idx = 0usize;
    while idx < left.len()
        invariant
            idx <= left.len(),
            left.len() == right.len(),
            forall |i: int| 0 <= i < idx ==> left@[i] as nat == right@[i] as nat,
        decreases left.len() - idx,
    {
        if left[idx] != right[idx] {
            return false;
        }
        idx += 1;
    }
    proof {
        assert(iau_seq(left@) == iau_seq(right@));
    }
    true
}

fn same_branch_node_view(left: &BranchNode, right: &BranchNode) -> (out: bool)
    ensures
        out ==> left@ == right@,
{
    match (left, right) {
        (
            BranchNode::Leaf{keys: left_keys, msgs: left_msgs},
            BranchNode::Leaf{keys: right_keys, msgs: right_msgs},
        ) => {
            if same_key_vec(left_keys, right_keys) && same_message_vec(left_msgs, right_msgs) {
                proof {
                    assert(left@ == right@);
                }
                true
            } else {
                false
            }
        },
        (
            BranchNode::Index{pivots: left_pivots, children: left_children, aux_ptr: left_aux},
            BranchNode::Index{pivots: right_pivots, children: right_children, aux_ptr: right_aux},
        ) => {
            let same_aux = match (*left_aux, *right_aux) {
                (None, None) => true,
                (Some(left_addr), Some(right_addr)) => same_iaddr_local(&left_addr, &right_addr),
                _ => false,
            };
            if same_key_vec(left_pivots, right_pivots)
                && same_iaddr_vec(left_children, right_children)
                && same_aux {
                proof {
                    assert(left@ == right@);
                }
                true
            } else {
                false
            }
        },
        (
            BranchNode::Auxiliary{summary_aus: left_aus},
            BranchNode::Auxiliary{summary_aus: right_aus},
        ) => {
            if same_iau_vec(left_aus, right_aus) {
                proof {
                    assert(left@ == right@);
                }
                true
            } else {
                false
            }
        },
        _ => false,
    }
}

fn marshall_branch_node_page(node: &BranchNode) -> (out: Vec<u8>)
    requires
        node.wf(),
        BranchNodePageFmt::spec_new().marshallable(node.parsedv()),
        BranchNodePageFmt::spec_new().impl_marshallable(*node),
        BranchNodePageFmt::spec_new().spec_size(node.parsedv()) == PAGE_SIZE_BYTES,
    ensures
        out.len() == PAGE_SIZE_BYTES,
        raw_page_to_branch_node(out@) == node@,
{
    let fmt = BranchNodePageFmt::new();
    let mut out = vec![0u8; PAGE_SIZE_BYTES];
    let end = fmt.exec_marshall(node, &mut out, 0);
    proof {
        assert(fmt == BranchNodePageFmt::spec_new());
        assert(end == PAGE_SIZE_BYTES);
        assert(out@.subrange(0, end as int) == out@);
        assert(fmt.parsable(out@));
        assert(fmt.parse(out@) == node.parsedv());
        assert(raw_page_to_branch_node(out@) == node@);
    }
    out
}

proof fn small_leaf_branch_node_marshallable(node: &BranchNode)
    requires
        node.wf(),
        node is Leaf,
        node->keys.len() <= BranchNodePageFmt::spec_new().leaf_fmt.max_length,
        node->keys.len() <= u8::MAX as int,
    ensures
        BranchNodePageFmt::spec_new().marshallable(node.parsedv()),
        BranchNodePageFmt::spec_new().impl_marshallable(*node),
        BranchNodePageFmt::spec_new().spec_size(node.parsedv()) == PAGE_SIZE_BYTES,
{
    let fmt = BranchNodePageFmt::spec_new();
    match node {
        BranchNode::Leaf{keys, msgs} => {
            let entries = leaf_entry_seq(keys@, msgs@);
            assert(keys.len() == msgs.len());
            assert(entries.len() == keys@.len());
            fmt.leaf_fmt.eltf.uniform_size_matches_spec_size();
            assert forall |i: int| 0 <= i < entries.len()
                implies #[trigger] fmt.leaf_fmt.marshallable_at(entries, i) by {
                assert(entries[i].key == keys@[i]);
                assert(entries[i].msg == msgs@[i]);
                assert(fmt.leaf_fmt.eltf.marshallable(entries[i]));
                assert(fmt.leaf_fmt.eltf.spec_size(entries[i])
                    == fmt.leaf_fmt.eltf.uniform_size());
            }
            assert(entries.len() <= u8::MAX as int);
            assert(entries.len() <= fmt.leaf_fmt.max_length);
            assert(fmt.leaf_fmt.marshallable(entries));
            assert(fmt.marshallable(node.parsedv()));
            assert(fmt.impl_marshallable(*node));
            assert(fmt.spec_size(node.parsedv()) == fmt.uniform_size());
            assert(fmt.uniform_size() == PAGE_SIZE_BYTES);
        },
        _ => {},
    }
}

proof fn grow_root_branch_node_marshallable(node: &BranchNode)
    requires
        node.wf(),
        node is Index,
        node->pivots.len() == 0,
        node->children.len() == 1,
    ensures
        BranchNodePageFmt::spec_new().marshallable(node.parsedv()),
        BranchNodePageFmt::spec_new().impl_marshallable(*node),
        BranchNodePageFmt::spec_new().spec_size(node.parsedv()) == PAGE_SIZE_BYTES,
{
    let fmt = BranchNodePageFmt::spec_new();
    match node {
        BranchNode::Index{pivots, children, aux_ptr} => {
            assert(children.len() == pivots.len() + 1);
            assert(pivots@.len() == 0);
            assert(children@.len() == 1);
            assert(fmt.index_routes_fmt.marshallable(seq![]));
            assert(fmt.index_meta_fmt.impl_marshallable(
                crate::marshalling::IBranchNodeFormat_v::IBranchIndexMeta{
                    first_child: children[0],
                    aux_ptr: *aux_ptr,
                },
            ));
            assert(fmt.index_routes_fmt.marshallable(
                crate::marshalling::IBranchNodeFormat_v::route_image_seq(
                    pivots@,
                    iaddr_seq(children@),
                ),
            ));
            assert forall |i: int| 0 <= i < pivots.len()
                implies #[trigger] fmt.index_routes_fmt.eltf.impl_marshallable(
                    crate::marshalling::IBranchNodeFormat_v::IBranchIndexRoute{
                        pivot: pivots[i],
                        child: children[i + 1],
                    },
                ) by {
                assert(false);
            }
            assert(fmt.marshallable(node.parsedv()));
            assert(fmt.impl_marshallable(*node));
            assert(fmt.spec_size(node.parsedv()) == fmt.uniform_size());
            assert(fmt.uniform_size() == PAGE_SIZE_BYTES);
        },
        _ => {},
    }
}

fn branch_stack_route_index(pivots: &Vec<Key>, key: Key) -> (out: usize)
    ensures
        out <= pivots.len(),
        Key::is_sorted(pivots@) ==> out as int == Key::largest_lte(pivots@, key) + 1,
{
    let mut idx = 0usize;
    while idx < pivots.len() && pivots[idx].0 <= key.0
        invariant
            idx <= pivots.len(),
            forall |i: int| 0 <= i < idx ==> Key::lte(#[trigger] pivots@[i], key),
        decreases pivots.len() - idx,
    {
        proof {
            assert(Key::lte(pivots@[idx as int], key));
        }
        idx += 1;
    }
    proof {
        if Key::is_sorted(pivots@) {
            let r = idx as int - 1;
            if idx < pivots.len() {
                assert(!(pivots@[idx as int].0 <= key.0));
                assert(key.0 < pivots@[idx as int].0);
                assert(Key::lt(key, pivots@[idx as int]));
            }
            if idx > 0 {
                assert(Key::lte(pivots@[idx as int - 1], key));
            }
            Key::largest_lte_is_lemma(pivots@, key, r);
            assert(Key::largest_lte(pivots@, key) == r);
        }
    }
    idx
}

pub open spec fn branch_stack_store_addrs_safe(store: &MemBranchStore) -> bool
{
    forall |addr: Address| #[trigger] store@.entries.contains_key(addr) ==> {
        &&& addr.wf()
        &&& addr != spec_superblock_addr()
    }
}

proof fn empty_branch_stack_store_addrs_safe(store: &MemBranchStore)
    requires
        store@.entries == Map::<Address, SpecBranchNode>::empty(),
    ensures
        branch_stack_store_addrs_safe(store),
{
    assert forall |addr: Address| #[trigger] store@.entries.contains_key(addr)
        implies {
            &&& addr.wf()
            &&& addr != spec_superblock_addr()
        } by {
        assert(false);
    }
}

proof fn branch_stack_store_addrs_safe_after_insert(
    old_store: &MemBranchStore,
    new_store: &MemBranchStore,
    addr: Address,
    node: SpecBranchNode,
)
    requires
        branch_stack_store_addrs_safe(old_store),
        new_store@.entries == old_store@.entries.insert(addr, node),
        addr.wf(),
        addr != spec_superblock_addr(),
    ensures
        branch_stack_store_addrs_safe(new_store),
{
    assert forall |read_addr: Address| #[trigger] new_store@.entries.contains_key(read_addr)
        implies {
            &&& read_addr.wf()
            &&& read_addr != spec_superblock_addr()
        } by {
        if read_addr == addr {
        } else {
            assert(old_store@.entries.contains_key(read_addr));
            assert(branch_stack_store_addrs_safe(old_store));
        }
    }
}

pub open spec fn branch_store_cache_read_aligned(store: &MemBranchStore, cache: Cache::State) -> bool
{
    forall |addr: Address, raw: RawPage|
        #[trigger] cache.valid_read(addr, raw) && store@.entries.contains_key(addr)
        ==> raw_page_to_branch_node(raw) == store@.entries[addr]
}

pub open spec fn branch_cursor_inv(branch: BranchImpl, store: &MemBranchStore, current: IAddress) -> bool
{
    let linked = branch.i(store);
    let ranking = linked.the_ranking();
    let cursor = SpecLinkedBranch{root: current@, disk_view: store@};
    &&& linked.inv()
    &&& cursor.wf()
    &&& cursor.valid_ranking(ranking)
    &&& cursor.keys_strictly_sorted_internal(ranking)
}

pub open spec fn branch_path_lines_wf(key: Key, root: Address, lines: Seq<LoadedPathReceiptLine>) -> bool
{
    &&& (lines.len() == 0 || lines[0].addr == root)
    &&& forall |i: int| 0 <= i < lines.len() - 1 ==> {
        #[trigger] lines[i].node is Index
    }
    &&& forall |i: int| 0 <= i < lines.len() ==> {
        #[trigger] lines[i].wf()
    }
    &&& forall |i: int| 0 <= i < lines.len() - 1 ==> {
        let line = lines[i];
        let child_idx = line.node.route(key) + 1;
        line.node->children[child_idx] == #[trigger] lines[i + 1].addr
    }
}

pub open spec fn branch_partial_path_wf(
    key: Key,
    root: Address,
    lines: Seq<LoadedPathReceiptLine>,
    current: Address,
) -> bool
{
    &&& branch_path_lines_wf(key, root, lines)
    &&& lines.len() == 0 ==> current == root
    &&& lines.len() > 0 ==> {
        let line = lines.last();
        let child_idx = line.node.route(key) + 1;
        &&& line.node is Index
        &&& line.node->children[child_idx] == current
    }
}

pub open spec fn branch_path_lines_equiv(
    key: Key,
    other_key: Key,
    lines: Seq<LoadedPathReceiptLine>,
) -> bool
{
    forall |i: int| 0 <= i < lines.len() && lines[i].node is Index ==> {
        #[trigger] lines[i].node.route(key) == lines[i].node.route(other_key)
    }
}

proof fn iau_seq_set_singleton(aus: Seq<IAU>, au: IAU)
    requires
        aus.len() == 1,
        aus[0] == au,
    ensures
        iau_seq_set(aus) == set![au as nat],
{
    let values = Map::new(|i: int| 0 <= i < aus.len(), |i: int| aus[i] as nat);
    assert(iau_seq_set(aus) == values.values());
    assert_sets_equal!(
        iau_seq_set(aus),
        set![au as nat],
        x => {
            if iau_seq_set(aus).contains(x) {
                assert(values.values().contains(x));
                let i = choose |i: int| values.contains_key(i) && #[trigger] values[i] == x;
                assert(0 <= i < aus.len());
                assert(i == 0);
                assert(x == au as nat);
            }
            if set![au as nat].contains(x) {
                assert(x == au as nat);
                assert(values.contains_key(0));
                assert(values[0] == x);
                assert(values.values().contains(x));
                assert(iau_seq_set(aus).contains(x));
            }
        }
    );
}

proof fn iau_seq_set_matches_to_set(aus: Seq<IAU>)
    ensures
        iau_seq_set(aus) == iau_seq(aus).to_set(),
{
    let values = Map::new(|i: int| 0 <= i < aus.len(), |i: int| aus[i] as nat);
    assert(iau_seq_set(aus) == values.values());
    assert_sets_equal!(
        iau_seq_set(aus),
        iau_seq(aus).to_set(),
        au => {
            if iau_seq_set(aus).contains(au) {
                assert(values.values().contains(au));
                let i = choose |i: int| values.contains_key(i) && #[trigger] values[i] == au;
                assert(0 <= i < aus.len());
                assert(iau_seq(aus)[i] == au);
                assert(iau_seq(aus).to_set().contains(au));
            }
            if iau_seq(aus).to_set().contains(au) {
                let i = choose |i: int| 0 <= i < iau_seq(aus).len()
                    && #[trigger] iau_seq(aus)[i] == au;
                assert(0 <= i < aus.len());
                assert(values.contains_key(i));
                assert(values[i] == au);
                assert(values.values().contains(au));
                assert(iau_seq_set(aus).contains(au));
            }
        }
    );
}

proof fn iau_seq_set_matches_vec_set(aus: Seq<IAU>)
    ensures
        iau_seq_set(aus) =~= iau_vec_set(aus),
{
    iau_seq_set_matches_to_set(aus);
    assert forall |au: AU| #[trigger] iau_seq_set(aus).contains(au)
        <==> iau_vec_set(aus).contains(au) by {
        if iau_seq_set(aus).contains(au) {
            assert(iau_seq(aus).to_set().contains(au));
            let i = choose |i: int| 0 <= i < iau_seq(aus).len()
                && #[trigger] iau_seq(aus)[i] == au;
            assert(aus[i] as nat == au);
        }
        if iau_vec_set(aus).contains(au) {
            let i = choose |i: int| 0 <= i < aus.len()
                && #[trigger] aus[i] as nat == au;
            assert(iau_seq(aus)[i] == au);
            assert(iau_seq(aus).to_set().contains(au));
        }
    }
}

pub open spec fn leaf_query_result(
    keys: Seq<Key>,
    msgs: Seq<Message>,
    key: Key,
) -> Message
{
    let leaf = SpecBranchNode::Leaf{keys, msgs};
    let idx = leaf.route(key);
    if 0 <= idx && leaf->keys[idx] == key {
        leaf->msgs[idx]
    } else {
        Message::Update{delta: Delta(0)}
    }
}

fn query_leaf_message(keys: &Vec<Key>, msgs: &Vec<Message>, key: Key) -> (msg: Message)
    requires
        keys@.len() == msgs@.len(),
        Key::is_strictly_sorted(keys@),
    ensures
        msg == leaf_query_result(keys@, msgs@, key),
{
    let mut idx = 0usize;
    while idx < keys.len()
        invariant
            idx <= keys.len(),
            keys@.len() == msgs@.len(),
            Key::is_strictly_sorted(keys@),
            forall |i: int| 0 <= i < idx ==> #[trigger] keys@[i] != key,
        decreases keys.len() - idx,
    {
        if keys[idx].0 == key.0 {
            let msg = msgs[idx];
            proof {
                assert(keys@[idx as int] == key);
                let route = Key::largest_lte(keys@, key);
                Key::strictly_sorted_implies_sorted(keys@);
                Key::largest_lte_ensures(keys@, key, route);
                assert(keys@.contains(key));
                assert(0 <= route < keys@.len());
                assert(keys@[route] == key);
                if route <= idx as int {
                    Key::strictly_sorted_implies_unique(keys@);
                    assert(route == idx as int);
                } else {
                    Key::strictly_sorted_implies_unique(keys@);
                    assert(idx as int <= route);
                    assert(route == idx as int);
                }
                assert(leaf_query_result(keys@, msgs@, key) == msg);
            }
            return msg;
        }
        proof {
            assert(keys@[idx as int] != key);
        }
        idx = idx + 1;
    }
    let msg = Message::Update{delta: Delta(0)};
    proof {
        assert forall |i: int| 0 <= i < keys@.len() implies #[trigger] keys@[i] != key by {
        }
        Key::strictly_sorted_implies_sorted(keys@);
        let route = Key::largest_lte(keys@, key);
        Key::largest_lte_ensures(keys@, key, route);
        if 0 <= route {
            assert(route < keys@.len());
            assert(keys@[route] != key);
        }
        assert(leaf_query_result(keys@, msgs@, key) == msg);
    }
    msg
}

fn branch_stack_key_lt(left: Key, right: Key) -> (out: bool)
    ensures
        out == Key::lt(left, right),
{
    left.0 < right.0
}

fn branch_stack_keys_strictly_sorted(keys: &Vec<Key>) -> (out: bool)
    ensures
        out == Key::is_strictly_sorted(keys@),
{
    if keys.len() == 0 {
        return true;
    }
    let mut idx = 1usize;
    while idx < keys.len()
        invariant
            1 <= idx <= keys.len(),
            forall |i: int, j: int| 0 <= i < j < idx ==> Key::lt(keys@[i], keys@[j]),
        decreases keys.len() - idx,
    {
        if !branch_stack_key_lt(keys[idx - 1], keys[idx]) {
            proof {
                assert(!Key::lt(keys@[(idx - 1) as int], keys@[idx as int]));
                assert(!Key::is_strictly_sorted(keys@)) by {
                    if Key::is_strictly_sorted(keys@) {
                        assert(Key::lt(keys@[(idx - 1) as int], keys@[idx as int]));
                    }
                }
            }
            return false;
        }
        proof {
            assert(Key::lt(keys@[(idx - 1) as int], keys@[idx as int]));
            assert forall |i: int, j: int| 0 <= i < j < idx + 1
                implies Key::lt(keys@[i], keys@[j]) by {
                if j == idx as int {
                    if i == idx as int - 1 {
                        assert(Key::lt(keys@[i], keys@[j]));
                    } else {
                        assert(i < idx as int - 1);
                        assert(Key::lt(keys@[i], keys@[(idx - 1) as int]));
                        assert(Key::lte(keys@[i], keys@[(idx - 1) as int]));
                        assert(Key::lte(keys@[(idx - 1) as int], keys@[j]));
                        Key::lte_transitive_forall();
                        assert(Key::lte(keys@[i], keys@[j]));
                        assert(keys@[i].0 < keys@[(idx - 1) as int].0);
                        assert(keys@[(idx - 1) as int].0 < keys@[j].0);
                        assert(keys@[i] != keys@[j]);
                        assert(Key::lt(keys@[i], keys@[j]));
                    }
                } else {
                    assert(j < idx as int);
                    assert(Key::lt(keys@[i], keys@[j]));
                }
            }
        }
        idx = idx + 1;
    }
    proof {
        assert(idx == keys.len());
    }
    true
}

fn branch_stack_combine_deltas(new_delta: Delta, old_delta: Delta) -> (out: Delta)
    ensures
        out == Message::combine_deltas(new_delta, old_delta),
{
    if new_delta.0 == 0 {
        proof {
            assert(new_delta == crate::spec::Messages_t::nop_delta());
        }
        old_delta
    } else if old_delta.0 == 0 {
        proof {
            assert(new_delta != crate::spec::Messages_t::nop_delta());
            assert(old_delta == crate::spec::Messages_t::nop_delta());
        }
        new_delta
    } else {
        proof {
            assert(new_delta != crate::spec::Messages_t::nop_delta());
            assert(old_delta != crate::spec::Messages_t::nop_delta());
        }
        new_delta
    }
}

fn branch_stack_merge_messages(older: Message, newer: Message) -> (out: Message)
    ensures
        out == older.merge(newer),
{
    match newer {
        Message::Define{value} => Message::Define{value},
        Message::Update{delta: new_delta} => {
            match older {
                Message::Define{value} => {
                    proof {
                        assert(Message::apply_delta(new_delta, value) == value);
                    }
                    Message::Define{value}
                },
                Message::Update{delta: old_delta} => {
                    let delta = branch_stack_combine_deltas(new_delta, old_delta);
                    Message::Update{delta}
                },
            }
        },
    }
}

fn branch_stack_normalize_value(msg: Message) -> (out: Value)
    ensures
        out == crate::implementation::AllocationBranchStack_v::normalize_value(msg),
{
    match msg {
        Message::Define{value} => value,
        Message::Update{..} => {
            proof {
                assert(Message::apply_delta(Delta(0), crate::spec::Messages_t::default_value())
                    == crate::spec::Messages_t::default_value());
            }
            Value(0)
        },
    }
}

pub open spec fn branch_query_prefix_receipts_valid(
    roots: Seq<Address>,
    receipts: Seq<LoadedPathReceipt>,
    read_nodes: LoadedBranch,
    key: Key,
) -> bool
{
    &&& receipts.len() <= roots.len()
    &&& forall |i: int| #![trigger receipts[i]] 0 <= i < receipts.len()
        ==> {
            let receipt = receipts[i];
            &&& receipt.key == key
            &&& receipt.valid_for(roots[i], read_nodes)
            &&& receipt.target().node is Leaf
        }
}

pub open spec fn branch_query_receipts_store_aligned(
    store: &MemBranchStore,
    receipts: Seq<LoadedPathReceipt>,
) -> bool
{
    forall |i: int, j: int|
        0 <= i < receipts.len() && 0 <= j < receipts[i].lines.len()
        ==> {
            let line = #[trigger] receipts[i].lines[j];
            &&& store@.entries.contains_key(line.addr)
            &&& line.node == store@.entries[line.addr]
        }
}

proof fn branch_query_full_prefix_receipts_valid(
    roots: Seq<Address>,
    receipts: Seq<LoadedPathReceipt>,
    read_nodes: LoadedBranch,
    key: Key,
)
    requires
        branch_query_prefix_receipts_valid(roots, receipts, read_nodes, key),
        receipts.len() == roots.len(),
    ensures
        query_receipts_valid(roots, receipts, read_nodes, key),
{
    assert forall |i: int| #![trigger receipts[i]] 0 <= i < receipts.len()
        implies {
            let receipt = receipts[i];
            let root_idx = roots.len() as int - receipts.len() as int + i;
            &&& receipt.key == key
            &&& receipt.valid_for(roots[root_idx], read_nodes)
            &&& receipt.target().node is Leaf
        } by {
        assert(roots.len() as int - receipts.len() as int + i == i);
    }
}

proof fn query_from_receipts_same_prefix(
    left: Seq<LoadedPathReceipt>,
    right: Seq<LoadedPathReceipt>,
    end: nat,
)
    requires
        end <= left.len(),
        end <= right.len(),
        forall |i: int| 0 <= i < end ==> #[trigger] left[i] == right[i],
    ensures
        query_from_receipts_up_to(left, end)
            == query_from_receipts_up_to(right, end),
    decreases end,
{
    if end > 0 {
        query_from_receipts_same_prefix(left, right, (end - 1) as nat);
        let idx = (end - 1) as int;
        assert(left[idx] == right[idx]);
    }
}

proof fn query_from_receipts_push(
    receipts: Seq<LoadedPathReceipt>,
    receipt: LoadedPathReceipt,
)
    ensures
        query_from_receipts_up_to(receipts.push(receipt), receipts.push(receipt).len() as nat)
            == query_from_receipts_up_to(receipts, receipts.len() as nat).merge(receipt.result()),
{
    let pushed = receipts.push(receipt);
    assert(pushed.len() == receipts.len() + 1);
    assert(pushed[(pushed.len() - 1) as int] == receipt);
    query_from_receipts_same_prefix(pushed, receipts, receipts.len() as nat);
}

proof fn query_receipts_read_addrs_same_prefix(
    left: Seq<LoadedPathReceipt>,
    right: Seq<LoadedPathReceipt>,
    end: nat,
)
    requires
        end <= left.len(),
        end <= right.len(),
        forall |i: int| 0 <= i < end ==> #[trigger] left[i] == right[i],
    ensures
        query_receipts_read_addrs(left, end) == query_receipts_read_addrs(right, end),
    decreases end,
{
    if end > 0 {
        query_receipts_read_addrs_same_prefix(left, right, (end - 1) as nat);
        let idx = (end - 1) as int;
        assert(left[idx] == right[idx]);
    }
}

proof fn query_receipts_read_addrs_push(
    receipts: Seq<LoadedPathReceipt>,
    receipt: LoadedPathReceipt,
)
    ensures
        query_receipts_read_addrs(receipts.push(receipt), receipts.push(receipt).len() as nat)
            == query_receipts_read_addrs(receipts, receipts.len() as nat) + receipt.needed_addrs(),
{
    let pushed = receipts.push(receipt);
    assert(pushed.len() == receipts.len() + 1);
    assert(pushed[(pushed.len() - 1) as int] == receipt);
    query_receipts_read_addrs_same_prefix(pushed, receipts, receipts.len() as nat);
}

proof fn branch_query_prefix_valid_after_reads_grow(
    roots: Seq<Address>,
    receipts: Seq<LoadedPathReceipt>,
    old_reads: Map<Address, RawPage>,
    new_reads: Map<Address, RawPage>,
    key: Key,
    store: &MemBranchStore,
)
    requires
        branch_query_prefix_receipts_valid(roots, receipts, to_branch_nodes(old_reads), key),
        branch_query_receipts_store_aligned(store, receipts),
        old_reads.dom() <= new_reads.dom(),
        forall |addr: Address| #[trigger] new_reads.contains_key(addr)
            && store@.entries.contains_key(addr)
            ==> raw_page_to_branch_node(new_reads[addr]) == store@.entries[addr],
    ensures
        branch_query_prefix_receipts_valid(roots, receipts, to_branch_nodes(new_reads), key),
{
    assert forall |i: int| #![trigger receipts[i]] 0 <= i < receipts.len()
        implies {
            let receipt = receipts[i];
            &&& receipt.key == key
            &&& receipt.valid_for(roots[i], to_branch_nodes(new_reads))
            &&& receipt.target().node is Leaf
        } by {
        let receipt = receipts[i];
        assert(receipt.valid_for(roots[i], to_branch_nodes(old_reads)));
        assert(receipt.wf());
        assert(receipt.root == roots[i]);
        assert(receipt.needed_addrs() <= to_branch_nodes(new_reads).dom()) by {
            assert forall |addr: Address| #[trigger] receipt.needed_addrs().contains(addr)
                implies to_branch_nodes(new_reads).dom().contains(addr) by {
                assert(to_branch_nodes(old_reads).dom().contains(addr));
                assert(old_reads.contains_key(addr));
                assert(new_reads.contains_key(addr));
            }
        }
        assert forall |j: int| 0 <= j < receipt.lines.len()
            implies {
                &&& to_branch_nodes(new_reads).contains_key(receipt.lines[j].addr)
                &&& #[trigger] to_branch_nodes(new_reads)[receipt.lines[j].addr]
                    == receipt.lines[j].node
            } by {
            let line = receipt.lines[j];
            assert(to_branch_nodes(old_reads).contains_key(line.addr));
            assert(old_reads.contains_key(line.addr));
            assert(new_reads.contains_key(line.addr));
            assert(store@.entries.contains_key(line.addr));
            assert(line.node == store@.entries[line.addr]);
            assert(raw_page_to_branch_node(new_reads[line.addr]) == store@.entries[line.addr]);
            assert(to_branch_nodes(new_reads)[line.addr] == line.node);
        }
    }
}

proof fn branch_query_prefix_valid_after_reads_preserve_lines(
    roots: Seq<Address>,
    receipts: Seq<LoadedPathReceipt>,
    old_reads: Map<Address, RawPage>,
    new_reads: Map<Address, RawPage>,
    key: Key,
)
    requires
        branch_query_prefix_receipts_valid(roots, receipts, to_branch_nodes(old_reads), key),
        old_reads.dom() <= new_reads.dom(),
        forall |i: int, j: int|
            0 <= i < receipts.len() && 0 <= j < receipts[i].lines.len()
            ==> #[trigger] new_reads[receipts[i].lines[j].addr]
                == old_reads[receipts[i].lines[j].addr],
    ensures
        branch_query_prefix_receipts_valid(roots, receipts, to_branch_nodes(new_reads), key),
{
    assert forall |i: int| #![trigger receipts[i]] 0 <= i < receipts.len()
        implies {
            let receipt = receipts[i];
            &&& receipt.key == key
            &&& receipt.valid_for(roots[i], to_branch_nodes(new_reads))
            &&& receipt.target().node is Leaf
        } by {
        let receipt = receipts[i];
        assert(receipt.valid_for(roots[i], to_branch_nodes(old_reads)));
        assert(receipt.wf());
        assert(receipt.root == roots[i]);
        assert(receipt.needed_addrs() <= to_branch_nodes(new_reads).dom()) by {
            assert forall |addr: Address| #[trigger] receipt.needed_addrs().contains(addr)
                implies to_branch_nodes(new_reads).dom().contains(addr) by {
                let j = choose |j: int| 0 <= j < receipt.lines.len()
                    && #[trigger] receipt.lines[j].addr == addr;
                assert(to_branch_nodes(old_reads).dom().contains(addr));
                assert(old_reads.contains_key(addr));
                assert(new_reads.contains_key(addr));
            }
        }
        assert forall |j: int| 0 <= j < receipt.lines.len()
            implies {
                &&& to_branch_nodes(new_reads).contains_key(receipt.lines[j].addr)
                &&& #[trigger] to_branch_nodes(new_reads)[receipt.lines[j].addr]
                    == receipt.lines[j].node
            } by {
            let line = receipt.lines[j];
            assert(to_branch_nodes(old_reads).contains_key(line.addr));
            assert(to_branch_nodes(old_reads)[line.addr] == line.node);
            assert(old_reads.contains_key(line.addr));
            assert(new_reads.contains_key(line.addr));
            assert(new_reads[line.addr] == old_reads[line.addr]);
            assert(to_branch_nodes(new_reads)[line.addr] == line.node);
        }
    }
}

proof fn branch_stack_child_inv_internal_from_parent(
    branch: SpecLinkedBranch<Summary>,
    ranking: Ranking,
    child_idx: int,
)
    requires
        branch.inv_internal(ranking),
        branch.root().valid_child_index(child_idx),
    ensures
        branch.child_at_idx(child_idx).inv_internal(ranking),
{
    assert(branch.child_at_idx(child_idx).valid_ranking(ranking)) by {
        assert(branch.disk_view.valid_ranking(ranking));
        assert(ranking.contains_key(branch.root));
        assert(branch.disk_view.node_children_respects_rank(ranking, branch.root));
        assert(ranking.contains_key(branch.root()->children[child_idx]));
    }
    assert(branch.child_at_idx(child_idx).keys_strictly_sorted_internal(ranking));
    assert(branch.child_at_idx(child_idx).all_keys_in_range_internal(ranking));
}

proof fn branch_stack_leaf_append_route_equiv(leaf: SpecBranchNode, keys: Seq<Key>)
    requires
        leaf is Leaf,
        leaf->keys.len() > 0,
        keys.len() > 0,
        Key::is_strictly_sorted(leaf->keys),
        Key::is_strictly_sorted(keys),
        Key::lt(leaf->keys.last(), keys[0]),
    ensures
        leaf.route(keys[0]) == leaf.route(keys.last()),
{
    let last_idx = leaf->keys.len() - 1;
    Key::strictly_sorted_implies_sorted(leaf->keys);
    Key::strictly_sorted_implies_sorted(keys);
    Key::lte_transitive_forall();
    assert(0 <= last_idx < leaf->keys.len());
    assert(Key::lte(leaf->keys[last_idx], keys[0]));
    Key::largest_lte_is_lemma(leaf->keys, keys[0], last_idx);
    assert(Key::lte(keys[0], keys.last()));
    assert(Key::lte(leaf->keys[last_idx], keys.last()));
    Key::largest_lte_is_lemma(leaf->keys, keys.last(), last_idx);
}

proof fn receipt_path_valid_for_branch_disk(
    branch: SpecLinkedBranch<Summary>,
    ranking: Ranking,
    receipt: LoadedPathReceipt,
    other_key: Key,
)
    requires
        branch.inv_internal(ranking),
        receipt.valid_for(branch.root, branch.disk_view.entries),
        receipt.path_equiv(other_key),
        receipt.target().node.route(receipt.key) == receipt.target().node.route(other_key),
    ensures
        ({
            let path = SpecPath{branch, key: receipt.key, depth: receipt.depth()};
            &&& path.valid()
            &&& path.target().has_root()
            &&& path.target().root == receipt.target().addr
            &&& path.target().root() == receipt.target().node
            &&& path.target().disk_view == branch.disk_view
            &&& path.path_equiv(other_key)
        }),
    decreases receipt.depth(),
{
    let path = SpecPath{branch, key: receipt.key, depth: receipt.depth()};
    assert(receipt.wf());
    assert(receipt.lines.len() > 0);
    assert(receipt.lines[0].addr == receipt.root);
    assert(receipt.root == branch.root);
    assert(branch.disk_view.entries.contains_key(branch.root));
    assert(branch.root() == receipt.lines[0].node);
    if receipt.depth() == 0 {
        assert(receipt.lines.len() == 1);
        assert(path.valid());
        assert(path.target() == branch);
        assert(path.target().root == receipt.target().addr);
        assert(path.target().root() == receipt.target().node);
        assert(path.target().disk_view == branch.disk_view);
        assert(branch.root().route(receipt.key) == branch.root().route(other_key));
        assert(path.path_equiv(other_key));
    } else {
        assert(receipt.lines.len() > 1);
        assert(branch.root() is Index);
        let child_idx = branch.root().route(receipt.key) + 1;
        LinkedBranchRefinement::lemma_route_ensures(branch.root(), receipt.key);
        assert(branch.root().valid_child_index(child_idx));
        let line0 = receipt.lines[0];
        assert(branch.root() == line0.node);
        assert(child_idx == line0.node.route(receipt.key) + 1);
        assert(0 <= 0 < receipt.lines.len() - 1);
        assert(receipt.lines[0int + 1].addr == receipt.lines[1].addr);
        assert({
            let line = receipt.lines[0];
            let idx = line.node.route(receipt.key) + 1;
            line.node->children[idx] == receipt.lines[0int + 1].addr
        });
        assert(line0.node->children[child_idx] == receipt.lines[1].addr);
        assert(branch.root()->children[child_idx] == receipt.lines[1].addr);
        let child_branch = branch.child_at_idx(child_idx);
        let child_receipt = receipt.tail();
        receipt_valid_implies_tail_valid(receipt, branch.disk_view.entries);
        assert(child_receipt.root == receipt.lines[1].addr);
        assert(child_receipt.root == child_branch.root);
        assert(child_branch.disk_view == branch.disk_view);
        branch_stack_child_inv_internal_from_parent(branch, ranking, child_idx);
        assert(child_receipt.target().node == receipt.target().node);
        receipt_path_valid_for_branch_disk(child_branch, ranking, child_receipt, other_key);
        assert(path.subpath() == SpecPath{
            branch: child_branch,
            key: receipt.key,
            depth: child_receipt.depth(),
        });
        assert(path.valid());
        assert(path.target() == path.subpath().target());
        assert(path.target().root == receipt.target().addr);
        assert(path.target().root() == receipt.target().node);
        assert(path.target().disk_view == branch.disk_view);
        assert(branch.root().route(receipt.key) == branch.root().route(other_key));
        assert(path.subpath().path_equiv(other_key));
        assert(path.path_equiv(other_key));
    }
}

proof fn one_line_leaf_receipt_facts(
    key: Key,
    root: Address,
    keys: Seq<Key>,
    msgs: Seq<Message>,
    read_nodes: LoadedBranch,
)
    requires
        keys.len() > 0,
        keys.len() == msgs.len(),
        Key::is_strictly_sorted(keys),
        read_nodes.contains_key(root),
        read_nodes[root] == (SpecBranchNode::Leaf{keys, msgs}),
    ensures
        ({
            let node = SpecBranchNode::Leaf{keys, msgs};
            let line = LoadedPathReceiptLine{addr: root, node};
            let receipt = LoadedPathReceipt{key, root, lines: seq![line]};
            &&& receipt.valid_for(root, read_nodes)
            &&& receipt.target().node is Leaf
            &&& receipt.result() == leaf_query_result(keys, msgs, key)
        }),
{
    let node = SpecBranchNode::Leaf{keys, msgs};
    let line = LoadedPathReceiptLine{addr: root, node};
    let receipt = LoadedPathReceipt{key, root, lines: seq![line]};
    assert(node.wf());
    assert(node.keys_strictly_sorted());
    assert(line.wf());
    assert(receipt.wf()) by {
        assert(receipt.lines.len() == 1);
        assert(receipt.lines[0] == line);
    }
    assert(receipt.needed_addrs() == set![root]) by {
        assert forall |addr: Address| #[trigger] receipt.needed_addrs().contains(addr)
            implies set![root].contains(addr) by {
            let idx = choose |i: int| 0 <= i < receipt.lines.len()
                && #[trigger] receipt.lines[i].addr == addr;
            assert(idx == 0);
            assert(addr == root);
        }
        assert forall |addr: Address| #[trigger] set![root].contains(addr)
            implies receipt.needed_addrs().contains(addr) by {
            assert(receipt.lines[0].addr == addr);
        }
    }
    assert(receipt.needed_addrs() <= read_nodes.dom());
    assert forall |i: int| 0 <= i < receipt.lines.len()
        implies {
            &&& read_nodes.contains_key(receipt.lines[i].addr)
            &&& #[trigger] read_nodes[receipt.lines[i].addr] == receipt.lines[i].node
        } by {
        assert(i == 0);
        assert(receipt.lines[i].addr == root);
        assert(receipt.lines[i].node == node);
    }
    assert(receipt.valid_for(root, read_nodes));
    assert(receipt.target().node == node);
    assert(receipt.result() == leaf_query_result(keys, msgs, key));
}

proof fn receipt_result_matches_leaf_query(
    receipt: LoadedPathReceipt,
    keys: Seq<Key>,
    msgs: Seq<Message>,
)
    requires
        receipt.lines.len() > 0,
        receipt.target().node == (SpecBranchNode::Leaf{keys, msgs}),
    ensures
        receipt.result() == leaf_query_result(keys, msgs, receipt.key),
{
    assert(receipt.target().node is Leaf);
    assert(receipt.result() == leaf_query_result(keys, msgs, receipt.key));
}

proof fn au_allocation_vec_set_matches(allocation: AuAllocation, total_aus: IAU)
    requires
        allocation.wf(total_aus),
    ensures
        iau_vec_set(allocation.aus@) =~= allocation.as_set(),
{
    assert forall |au: AU| #[trigger] iau_vec_set(allocation.aus@).contains(au)
        implies allocation.as_set().contains(au) by {
        let idx = choose |i: int| 0 <= i < allocation.aus@.len()
            && #[trigger] (allocation.aus@[i] as nat) == au;
        assert(AuAllocation::vec_matches_run(allocation.aus@, allocation.run));
        assert((allocation.aus@[idx] as nat) == (allocation.run.start as nat) + (idx as nat));
        assert((allocation.run.start as nat) <= au);
        assert(au < (allocation.run.end as nat));
    }
    assert forall |au: AU| #[trigger] allocation.as_set().contains(au)
        implies iau_vec_set(allocation.aus@).contains(au) by {
        assert((allocation.run.start as nat) <= au);
        assert(au < (allocation.run.end as nat));
        let idx = (au - (allocation.run.start as nat)) as int;
        assert(0 <= idx < allocation.aus@.len());
        assert(AuAllocation::vec_matches_run(allocation.aus@, allocation.run));
        assert((allocation.aus@[idx] as nat) == au);
    }
}

proof fn au_allocation_vec_unique(allocation: AuAllocation, total_aus: IAU)
    requires
        allocation.wf(total_aus),
    ensures
        MiniAllocatorImpl::iau_seq_unique(allocation.aus@),
{
    assert forall |i: int, j: int| 0 <= i < allocation.aus@.len()
        && 0 <= j < allocation.aus@.len()
        && #[trigger] allocation.aus@[i] == #[trigger] allocation.aus@[j]
        implies i == j by {
        assert(AuAllocation::vec_matches_run(allocation.aus@, allocation.run));
        assert((allocation.aus@[i] as nat) == (allocation.run.start as nat) + (i as nat));
        assert((allocation.aus@[j] as nat) == (allocation.run.start as nat) + (j as nat));
    }
}

proof fn branch_path_extend_read_preserves(
    cache: Cache::State,
    reads_pre: Map<Address, RawPage>,
    lines_pre: Seq<LoadedPathReceiptLine>,
    current: Address,
    raw: RawPage,
    root_addr: Address,
    line: LoadedPathReceiptLine,
)
    requires
        line.addr == current,
        lines_pre.len() == 0 ==> current == root_addr,
        lines_pre.len() > 0 ==> lines_pre[0].addr == root_addr,
        reads_pre.dom() == Set::new(|addr: Address| exists |i: int|
            0 <= i < lines_pre.len() && #[trigger] lines_pre[i].addr == addr),
        forall |addr: Address| #[trigger] reads_pre.contains_key(addr)
            ==> cache.valid_read(addr, reads_pre[addr]),
        cache.valid_read(current, raw),
    ensures
        ({
            let reads = reads_pre.insert(current, raw);
            let lines = lines_pre.push(line);
            &&& lines.len() > 0
            &&& lines[0].addr == root_addr
            &&& reads.dom() == Set::new(|addr: Address| exists |i: int|
                0 <= i < lines.len() && #[trigger] lines[i].addr == addr)
            &&& forall |addr: Address| #[trigger] reads.contains_key(addr)
                ==> cache.valid_read(addr, reads[addr])
        }),
{
    let reads = reads_pre.insert(current, raw);
    let lines = lines_pre.push(line);
    assert(lines.len() > 0);
    if lines_pre.len() == 0 {
        assert(line.addr == root_addr);
        assert(lines[0].addr == root_addr);
    } else {
        assert(lines[0].addr == lines_pre[0].addr);
    }
    assert forall |addr: Address|
        #[trigger] reads.contains_key(addr)
        implies cache.valid_read(addr, reads[addr])
    by {
        if addr == current {
            assert(cache.valid_read(current, raw));
        } else {
            assert(reads_pre.contains_key(addr));
        }
    };
    assert(reads.dom() == Set::new(|addr: Address| exists |i: int|
        0 <= i < lines.len() && #[trigger] lines[i].addr == addr)) by {
        assert forall |addr: Address|
            reads.dom().contains(addr)
                <==> (exists |i: int| 0 <= i < lines.len()
                    && #[trigger] lines[i].addr == addr)
        by {
            if addr == current {
                assert(lines[(lines.len() - 1) as int].addr == addr);
            } else {
                if reads.dom().contains(addr) {
                    assert(reads_pre.dom().contains(addr));
                    let idx = choose |i: int| 0 <= i < lines_pre.len()
                        && #[trigger] lines_pre[i].addr == addr;
                    assert(lines[idx] == lines_pre[idx]);
                }
                if exists |i: int| 0 <= i < lines.len() && #[trigger] lines[i].addr == addr {
                    let idx = choose |i: int| 0 <= i < lines.len()
                        && #[trigger] lines[i].addr == addr;
                    if idx == lines.len() - 1 {
                        assert(addr == current);
                    } else {
                        assert(0 <= idx < lines_pre.len());
                        assert(lines[idx] == lines_pre[idx]);
                        assert(reads_pre.dom().contains(addr));
                    }
                }
            }
        };
    }
}

pub struct BranchStackImpl {
    pub load_state: BranchLoadState,
    pub image: BranchImageImpl,
    pub persistent_prefix_len: usize,
    pub persistent_seq_end: usize,
    pub persisted_root_count: usize,
    pub commit_phase: CommitPhase,
    pub branch_summary: BranchSummaryImpl,
    pub active_branch: Option<BranchImpl>,
    pub mini_allocator: MiniAllocatorImpl,
    pub active_store: MemBranchStore,
    pub store: MemBranchStore,
    pub seq_end: usize,
}

impl BranchStackImpl {
    pub open spec fn is_awaiting_superblock(&self) -> bool
    {
        self.load_state is AwaitingSuperblock
    }

    pub open spec fn metadata_loaded(&self) -> bool
    {
        self.load_state is MetadataLoaded
    }

    pub exec fn exec_seq_end(&self) -> (out: u64)
        requires
            self.wf(),
            !(self.load_state is AwaitingSuperblock),
        ensures
            out as nat == self@.seq_end,
    {
        self.seq_end as u64
    }

    pub exec fn persistent_roots(&self) -> (out: Vec<IAddress>)
        requires
            self.wf(),
            self.load_state is MetadataLoaded,
        ensures
            out@ == self.image.sealed_roots@.take(self.persistent_prefix_len as int),
    {
        let mut out = Vec::new();
        let mut i = 0usize;
        while i < self.persistent_prefix_len
            invariant
                self.wf(),
                self.load_state is MetadataLoaded,
                self.persistent_prefix_len <= self.image.sealed_roots@.len(),
                i <= self.persistent_prefix_len,
                out@ == self.image.sealed_roots@.take(i as int),
            decreases self.persistent_prefix_len - i,
        {
            out.push(self.image.sealed_roots[i]);
            i += 1;
        }
        out
    }

    pub exec fn all_roots(&self) -> (out: Vec<IAddress>)
        requires
            self.wf(),
            self.load_state is MetadataLoaded,
        ensures
            out@ == self.image.sealed_roots@,
            iaddr_seq(out@) == self.image@.sealed_roots,
    {
        let mut out = Vec::new();
        let mut i = 0usize;
        while i < self.image.sealed_roots.len()
            invariant
                self.wf(),
                self.load_state is MetadataLoaded,
                i <= self.image.sealed_roots.len(),
                out@ == self.image.sealed_roots@.take(i as int),
            decreases self.image.sealed_roots.len() - i,
        {
            out.push(self.image.sealed_roots[i]);
            i += 1;
        }
        proof {
            assert(self.image.sealed_roots@.take(
                self.image.sealed_roots@.len() as int,
            ) == self.image.sealed_roots@);
        }
        out
    }

    pub open spec fn persistent_image_i(&self) -> AtomicBranchImage
    {
        AtomicBranchImage {
            sealed_roots: self.image@.sealed_roots.take(self.persistent_prefix_len as int),
            seq_end: self.persistent_seq_end as nat,
        }
    }

    pub open spec fn in_flight_i(&self) -> Option<AtomicBranchImage>
    {
        match self.commit_phase {
            CommitPhase::Idle => None,
            CommitPhase::InFlight{prefix_len, seq_end, prepared: _} => Some(AtomicBranchImage {
                sealed_roots: self.image@.sealed_roots.take(prefix_len as int),
                seq_end: seq_end as nat,
            }),
        }
    }

    pub open spec fn prepared_i(&self) -> bool
    {
        match self.commit_phase {
            CommitPhase::Idle => false,
            CommitPhase::InFlight{prefix_len: _, seq_end: _, prepared} => prepared,
        }
    }

    pub open spec fn commit_phase_wf(&self) -> bool
    {
        match self.commit_phase {
            CommitPhase::Idle => true,
            CommitPhase::InFlight{prefix_len, seq_end, prepared: _} => {
                &&& prefix_len <= self.image.sealed_roots@.len()
                &&& seq_end <= self.seq_end
            },
        }
    }

    pub open spec fn active_branch_i(&self) -> CachedBranch::State
    {
        match self.active_branch {
            Some(branch) => {
                CachedBranch::State{ root: Some(branch.root@) }
            },
            None => CachedBranch::State::empty_active(),
        }
    }

    pub open spec fn wf(&self) -> bool
    {
        &&& self.image.wf()
        &&& match self.load_state {
            BranchLoadState::AwaitingSuperblock => {
                &&& self.image@ == empty_branch_image()
                &&& self.persistent_prefix_len == 0
                &&& self.persistent_seq_end == 0
                &&& self.persisted_root_count == 0
                &&& self.seq_end == 0
            },
            BranchLoadState::LoadingMetadata{next_root_idx} => {
                next_root_idx <= self.image.sealed_roots@.len()
            },
            BranchLoadState::MetadataLoaded => true,
        }
        &&& self.persistent_prefix_len <= self.image.sealed_roots@.len()
        &&& self.persisted_root_count <= self.image.sealed_roots@.len()
        &&& self.persistent_prefix_len <= self.persisted_root_count
        &&& self.persistent_seq_end <= self.seq_end
        &&& self.commit_phase_wf()
        &&& self.branch_summary.wf()
        &&& self.mini_allocator.wf()
        &&& self.active_store.wf()
        &&& self.store.wf()
        &&& !(self.load_state is AwaitingSuperblock) ==> self.i().wf()
    }

    pub open spec fn runtime_wf(&self, total_aus: IAU) -> bool
    {
        &&& self.wf()
        &&& self.load_state is MetadataLoaded
        &&& self.image.roots_wf()
        &&& self.image.roots_bounded(total_aus)
        &&& branch_stack_store_addrs_safe(&self.store)
        &&& branch_stack_store_addrs_safe(&self.active_store)
        &&& self.active_branch is Some ==> {
            &&& self.active_branch.unwrap().inv(&self.active_store)
            &&& self.active_branch_i().ready_for_operation(self.mini_allocator.i())
        }
        &&& self.active_branch is None ==>
            self.mini_allocator.i().allocated_aus() == Set::<AU>::empty()
        &&& MiniAllocatorImpl::allocators_unique(self.mini_allocator.allocators@)
        &&& self.mini_allocator.bounded(total_aus)
    }

    pub open spec fn owned_aus(&self) -> Set<AU>
    {
        MiniAllocatorImpl::allocators_au_set(self.mini_allocator.allocators@)
    }

    pub open spec fn branch_summary_covers_roots_up_to(&self, end: nat) -> bool
    {
        root_aus_up_to(self.image@.sealed_roots, end) <= self.branch_summary.i().dom()
    }

    pub open spec fn metadata_recovery_wf(&self) -> bool
    {
        &&& self.wf()
        &&& self.image.roots_wf()
        &&& branch_stack_store_addrs_safe(&self.store)
        &&& branch_stack_store_addrs_safe(&self.active_store)
        &&& match self.load_state {
            BranchLoadState::LoadingMetadata{next_root_idx} => {
                &&& self.branch_summary_covers_roots_up_to(next_root_idx as nat)
                &&& self@.mini_allocator == MiniAllocator::empty()
            },
            BranchLoadState::MetadataLoaded => {
                &&& self@.metadata_loaded()
                &&& self@.mini_allocator == MiniAllocator::empty()
            },
            BranchLoadState::AwaitingSuperblock => false,
        }
    }

    pub proof fn metadata_recovery_full_implies_loaded(&self, next_root_idx: usize)
        requires
            self.wf(),
            self.branch_summary_covers_roots_up_to(next_root_idx as nat),
            next_root_idx >= self.image@.sealed_roots.len(),
        ensures
            self@.metadata_loaded(),
    {
        assert forall |au: AU| #[trigger] root_aus_up_to(
            self.image@.sealed_roots,
            self.image@.sealed_roots.len() as nat,
        ).contains(au)
            implies self.branch_summary.i().dom().contains(au)
        by {
            let idx = root_aus_up_to_member_has_index(
                self.image@.sealed_roots,
                self.image@.sealed_roots.len() as nat,
                au,
            );
            assert(0 <= idx < self.image@.sealed_roots.len());
            assert(idx < next_root_idx as int);
            root_aus_up_to_contains(self.image@.sealed_roots, next_root_idx as nat, idx);
            assert(root_aus_up_to(
                self.image@.sealed_roots,
                next_root_idx as nat,
            ).contains(au));
        }
    }

    pub proof fn metadata_recovery_extend_prefix(&self, next_root_idx: usize, root: IAddress)
        requires
            self.wf(),
            self.branch_summary_covers_roots_up_to(next_root_idx as nat),
            next_root_idx < self.image@.sealed_roots.len(),
            self.image@.sealed_roots[next_root_idx as int] == root@,
            self.branch_summary.i().dom().contains(root.au as nat),
        ensures
            self.branch_summary_covers_roots_up_to((next_root_idx + 1) as nat),
    {
        assert forall |au: AU| #[trigger] root_aus_up_to(
            self.image@.sealed_roots,
            (next_root_idx + 1) as nat,
        ).contains(au)
            implies self.branch_summary.i().dom().contains(au)
        by {
            let idx = root_aus_up_to_member_has_index(
                self.image@.sealed_roots,
                (next_root_idx + 1) as nat,
                au,
            );
            if idx == next_root_idx as int {
                assert(self.image@.sealed_roots[idx] == root@);
                assert(au == root.au as nat);
            } else {
                assert(idx < next_root_idx as int);
                root_aus_up_to_contains(self.image@.sealed_roots, next_root_idx as nat, idx);
                assert(root_aus_up_to(
                    self.image@.sealed_roots,
                    next_root_idx as nat,
                ).contains(au));
            }
        }
    }

    pub open spec fn i(&self) -> AtomicBranchState::State
    {
        if self.load_state is AwaitingSuperblock {
            AtomicBranchState::State::empty()
        } else {
            AtomicBranchState::State {
                image: self.image@,
                persistent_image: self.persistent_image_i(),
                in_flight: self.in_flight_i(),
                prepared: self.prepared_i(),
                branch_summary: self.branch_summary.i(),
                persisted_root_count: self.persisted_root_count as nat,
                active_branch: self.active_branch_i(),
                mini_allocator: self.mini_allocator.i(),
                seq_end: self.seq_end as nat,
            }
        }
    }

    pub fn awaiting_superblock(free_au_threshold: IAU) -> (out: Self)
        ensures
            out.wf(),
            out.load_state is AwaitingSuperblock,
            out.i() == AtomicBranchState::State::empty(),
    {
        let image = BranchImageImpl::empty();
        let summary = BranchSummaryImpl::new();
        let allocator = MiniAllocatorImpl::empty(free_au_threshold);
        let active_store = MemBranchStore::new();
        let store = MemBranchStore::new();
        let out = Self {
            load_state: BranchLoadState::AwaitingSuperblock,
            persistent_prefix_len: 0,
            persistent_seq_end: 0,
            persisted_root_count: 0,
            commit_phase: CommitPhase::Idle,
            branch_summary: summary,
            active_branch: None,
            mini_allocator: allocator,
            active_store,
            store,
            seq_end: 0,
            image,
        };
        proof {
            assert(out.i() == AtomicBranchState::State::empty());
        }
        out
    }

    pub fn new(
        image: BranchImageImpl,
        initial_persisted_root_count: usize,
        free_au_threshold: IAU,
    ) -> (out: Self)
        requires
            initial_persisted_root_count == image.sealed_roots@.len(),
        ensures
            out.wf(),
            out.i().image == image@,
            out.i().persistent_image == image@,
            out.i().in_flight is None,
            !out.i().prepared,
            out.load_state is MetadataLoaded,
            out.mini_allocator.allocators@.len() == 0,
            MiniAllocatorImpl::allocators_unique(out.mini_allocator.allocators@),
            out.active_branch is None,
    {
        let summary = BranchSummaryImpl::new();
        let allocator = MiniAllocatorImpl::empty(free_au_threshold);
        let active_store = MemBranchStore::new();
        let store = MemBranchStore::new();
        let seq_end = image.seq_end;
        Self {
            load_state: BranchLoadState::MetadataLoaded,
            persistent_prefix_len: initial_persisted_root_count,
            persistent_seq_end: image.seq_end,
            persisted_root_count: initial_persisted_root_count,
            commit_phase: CommitPhase::Idle,
            branch_summary: summary,
            active_branch: None,
            mini_allocator: allocator,
            active_store,
            store,
            seq_end,
            image,
        }
    }

    pub fn initialize_from_image(
        &mut self,
        image: BranchImageImpl,
        initial_persisted_root_count: usize,
        total_aus: IAU,
    )
        requires
            old(self).wf(),
            old(self).load_state is AwaitingSuperblock,
            image.roots_wf(),
            image.roots_bounded(total_aus),
            initial_persisted_root_count == image.sealed_roots@.len(),
        ensures
            self.wf(),
            self.metadata_recovery_wf(),
            self.load_state is LoadingMetadata,
            self.i().image == image@,
            self.i().persistent_image == image@,
            self.i().in_flight is None,
            !self.i().prepared,
            self.i().branch_summary == Map::<nat, Summary>::empty(),
            self.i().persisted_root_count == initial_persisted_root_count as nat,
            self.i().active_branch == CachedBranch::State::empty_active(),
            self.i().mini_allocator.allocs == Map::<AU, SpecMiniPageAllocator>::empty(),
            self.i().mini_allocator.curr is None,
            self.i().seq_end == image@.seq_end,
            self.image.roots_bounded(total_aus),
            self.active_branch is None,
    {
        let summary = BranchSummaryImpl::new();
        let threshold = self.mini_allocator.free_au_threshold;
        let allocator = MiniAllocatorImpl::empty(threshold);
        let active_store = MemBranchStore::new();
        let store = MemBranchStore::new();
        let seq_end = image.seq_end;
        self.load_state = BranchLoadState::LoadingMetadata{next_root_idx: 0};
        self.persistent_prefix_len = initial_persisted_root_count;
        self.persistent_seq_end = image.seq_end;
        self.persisted_root_count = initial_persisted_root_count;
        self.commit_phase = CommitPhase::Idle;
        self.branch_summary = summary;
        self.active_branch = None;
        self.mini_allocator = allocator;
        self.active_store = active_store;
        self.store = store;
        self.seq_end = seq_end;
        self.image = image;
        proof {
            empty_branch_stack_store_addrs_safe(&self.store);
            empty_branch_stack_store_addrs_safe(&self.active_store);
            assert(self.metadata_recovery_wf());
        }
    }

    pub fn fill_aus(&mut self, aus: Vec<IAU>)
        requires
            old(self).wf(),
            !(old(self).load_state is AwaitingSuperblock),
            MiniAllocatorImpl::allocators_unique(old(self).mini_allocator.allocators@),
            MiniAllocatorImpl::iau_seq_unique(aus@),
            iau_vec_set(aus@).disjoint(
                MiniAllocatorImpl::allocators_au_set(old(self).mini_allocator.allocators@),
            ),
        ensures
            self.wf(),
            self.image == old(self).image,
            self.active_branch == old(self).active_branch,
            self.active_store@ =~= old(self).active_store@,
            self.store@ =~= old(self).store@,
            branch_stack_store_addrs_safe(&old(self).store)
                ==> branch_stack_store_addrs_safe(&self.store),
            branch_stack_store_addrs_safe(&old(self).active_store)
                ==> branch_stack_store_addrs_safe(&self.active_store),
            old(self).active_branch is Some
                && old(self).active_branch.unwrap().inv(&old(self).active_store)
                ==> self.active_branch.unwrap().inv(&self.active_store),
            old(self).active_branch_i().ready_for_operation(old(self).mini_allocator.i())
                ==> self.active_branch_i().ready_for_operation(self.mini_allocator.i()),
            old(self).load_state is MetadataLoaded ==> self.load_state is MetadataLoaded,
            MiniAllocatorImpl::allocators_unique(self.mini_allocator.allocators@),
            MiniAllocatorImpl::allocators_au_set(self.mini_allocator.allocators@) =~=
                MiniAllocatorImpl::allocators_au_set(old(self).mini_allocator.allocators@)
                    + iau_vec_set(aus@),
            AtomicBranchState::State::next(
                old(self)@,
                self@,
                AtomicBranchState::Label::FillAUs{aus: iau_vec_set(aus@)},
            ),
            old(self).mini_allocator.i().allocated_aus() == Set::<AU>::empty()
                ==> self.mini_allocator.i().allocated_aus() == Set::<AU>::empty(),
            forall |total_aus: IAU| old(self).mini_allocator.bounded(total_aus)
                && (forall |i: int| 0 <= i < aus@.len()
                    ==> 0 < (#[trigger] aus@[i] as nat) && (aus@[i] as nat) < (total_aus as nat))
                ==> self.mini_allocator.bounded(total_aus),
    {
        self.mini_allocator.add_aus(aus);
        proof {
            assert(self.active_store@ =~= old(self).active_store@);
            assert(self.store@ =~= old(self).store@);
            let lbl = AtomicBranchState::Label::FillAUs{
                aus: iau_vec_set(aus@),
            };
            assert(AtomicBranchState::State::fill_aus(old(self)@, self@, lbl)) by {
            }
            reveal(AtomicBranchState::State::next);
            reveal(AtomicBranchState::State::next_by);
            assert(AtomicBranchState::State::next_by(
                old(self)@,
                self@,
                lbl,
                AtomicBranchState::Step::fill_aus(),
            ));
            assert(AtomicBranchState::State::next(old(self)@, self@, lbl));
        }
    }

    pub fn background_refill_aus(
        &mut self,
        pool: &mut crate::implementation::AuPoolImpl_v::AuPoolImpl,
        total_aus: IAU,
    ) -> (out: Option<crate::implementation::AuPoolImpl_v::AuAllocation>)
        requires
            old(self).wf(),
            old(self).load_state is MetadataLoaded,
            old(pool).canonical_wf(total_aus),
            MiniAllocatorImpl::allocators_unique(old(self).mini_allocator.allocators@),
            old(pool)@.disjoint(
                MiniAllocatorImpl::allocators_au_set(old(self).mini_allocator.allocators@),
            ),
        ensures
            self.wf(),
            self.load_state is MetadataLoaded,
            self.image == old(self).image,
            old(self).image.roots_wf() ==> self.image.roots_wf(),
            self.active_branch == old(self).active_branch,
            self.active_store@ =~= old(self).active_store@,
            self.store@ =~= old(self).store@,
            branch_stack_store_addrs_safe(&old(self).store)
                ==> branch_stack_store_addrs_safe(&self.store),
            branch_stack_store_addrs_safe(&old(self).active_store)
                ==> branch_stack_store_addrs_safe(&self.active_store),
            old(self).active_branch is Some
                && old(self).active_branch.unwrap().inv(&old(self).active_store)
                ==> self.active_branch.unwrap().inv(&self.active_store),
            old(self).active_branch_i().ready_for_operation(old(self).mini_allocator.i())
                ==> self.active_branch_i().ready_for_operation(self.mini_allocator.i()),
            pool.canonical_wf(total_aus),
            MiniAllocatorImpl::allocators_unique(self.mini_allocator.allocators@),
            old(self).mini_allocator.bounded(total_aus) ==> self.mini_allocator.bounded(total_aus),
            old(self).mini_allocator.i().allocated_aus() == Set::<AU>::empty()
                ==> self.mini_allocator.i().allocated_aus() == Set::<AU>::empty(),
            pool@.disjoint(
                MiniAllocatorImpl::allocators_au_set(self.mini_allocator.allocators@),
            ),
            match out {
                Some(allocation) => {
                    &&& allocation.wf(total_aus)
                    &&& allocation.as_set() <= old(pool)@
                    &&& pool@ =~= old(pool)@ - allocation.as_set()
                    &&& AtomicBranchState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchState::Label::FillAUs{aus: allocation.as_set()},
                    )
                },
                None => {
                    &&& pool@ =~= old(pool)@
                    &&& self@ == old(self)@
                    &&& self.mini_allocator.i() == old(self).mini_allocator.i()
                    &&& self.mini_allocator.allocators@ == old(self).mini_allocator.allocators@
                    &&& self.mini_allocator.curr == old(self).mini_allocator.curr
                    &&& self.mini_allocator.free_au_threshold == old(self).mini_allocator.free_au_threshold
                },
            },
    {
        let free_count = self.mini_allocator.free_au_count();
        let threshold = self.mini_allocator.free_au_threshold;
        if free_count >= threshold {
            proof {
                assert(pool@ =~= old(pool)@);
                assert(self@ == old(self)@);
                assert(self.store@ =~= old(self).store@);
            }
            return None;
        }
        let needed = threshold - free_count;
        match pool.alloc(total_aus, needed) {
            Some(allocation) => {
                let aus = allocation.aus.clone();
                proof {
                    au_allocation_vec_unique(allocation, total_aus);
                    au_allocation_vec_set_matches(allocation, total_aus);
                    assert(iau_vec_set(aus@) =~= allocation.as_set());
	                    assert(iau_vec_set(aus@).disjoint(
	                        MiniAllocatorImpl::allocators_au_set(old(self).mini_allocator.allocators@),
	                    )) by {
                        assert forall |au: AU| #[trigger] iau_vec_set(aus@).contains(au)
                            implies !MiniAllocatorImpl::allocators_au_set(
                                old(self).mini_allocator.allocators@,
                            ).contains(au) by {
                            assert(allocation.as_set().contains(au));
                            assert(allocation.as_set() <= old(pool)@);
	                        }
	                    }
	                    assert forall |i: int| 0 <= i < aus@.len()
	                        implies 0 < (#[trigger] aus@[i] as nat)
	                            && (aus@[i] as nat) < (total_aus as nat) by {
	                        assert(allocation.wf(total_aus));
	                        assert(AuAllocation::vec_matches_run(aus@, allocation.run));
	                        assert(aus@[i] as nat == (allocation.run.start as nat) + (i as nat));
	                        assert((allocation.run.start as nat) <= (aus@[i] as nat));
	                        assert(0 < (allocation.run.start as nat));
	                        assert(i < allocation.run.len());
	                        assert((allocation.run.start as nat) + (i as nat) < (allocation.run.end as nat)) by {
	                            assert(allocation.run.len()
	                                == ((allocation.run.end as int) - (allocation.run.start as int)) as nat);
	                        }
	                        assert((allocation.run.end as nat) <= (total_aus as nat));
	                    }
	                }
                self.fill_aus(aus);
                proof {
                    assert(self.store@ =~= old(self).store@);
                    if old(self).active_branch_i().ready_for_operation(old(self).mini_allocator.i()) {
                        assert(AtomicBranchState::State::next(
                            old(self)@,
                            self@,
                            AtomicBranchState::Label::FillAUs{aus: allocation.as_set()},
                        ));
                        AtomicBranchState::State::fill_aus_effect(
                            old(self)@,
                            self@,
                            AtomicBranchState::Label::FillAUs{aus: allocation.as_set()},
                        );
                    }
                    assert(iau_vec_set(allocation.aus@) =~= allocation.as_set());
                    assert(MiniAllocatorImpl::allocators_unique(self.mini_allocator.allocators@));
                    assert(pool@.disjoint(
                        MiniAllocatorImpl::allocators_au_set(self.mini_allocator.allocators@),
                    )) by {
                        assert(pool@ =~= old(pool)@ - allocation.as_set());
                        assert(MiniAllocatorImpl::allocators_au_set(self.mini_allocator.allocators@)
                            =~= MiniAllocatorImpl::allocators_au_set(old(self).mini_allocator.allocators@)
                                + allocation.as_set());
                        assert forall |au: AU| #[trigger] pool@.contains(au)
                            implies !MiniAllocatorImpl::allocators_au_set(
                                self.mini_allocator.allocators@,
                            ).contains(au) by {
                            assert(!allocation.as_set().contains(au));
                            if MiniAllocatorImpl::allocators_au_set(
                                old(self).mini_allocator.allocators@,
                            ).contains(au) {
                                assert(old(pool)@.disjoint(
                                    MiniAllocatorImpl::allocators_au_set(
                                        old(self).mini_allocator.allocators@,
                                    ),
                                ));
                                assert(false);
                            }
                        }
                    }
                }
                Some(allocation)
            },
            None => {
                proof {
                    assert(pool@ =~= old(pool)@);
                    assert(self@ == old(self)@);
                    assert(self.store@ =~= old(self).store@);
                    assert(MiniAllocatorImpl::allocators_unique(self.mini_allocator.allocators@));
                    assert(pool@.disjoint(
                        MiniAllocatorImpl::allocators_au_set(self.mini_allocator.allocators@),
                    ));
                }
                None
            },
        }
    }

    pub fn query(&self, key: Key) -> (result: Result<Message, BranchError>)
        requires
            self.wf(),
            self.load_state is MetadataLoaded,
            self.active_branch is Some ==> self.active_branch.unwrap().invariants(&self.active_store),
    {
        let branch = match self.active_branch {
            Some(branch) => branch,
            None => return Err(BranchError::Uninitialized),
        };
        branch.query(&self.active_store, key)
    }

    pub fn load_path_for_key(
        &mut self,
        cache: &mut FracCacheImpl,
        key: Key,
        equiv_key: Option<Key>,
    ) -> (out: BranchPathLoadResult)
        requires
            old(self).wf(),
            old(self).load_state is MetadataLoaded,
            old(self).active_branch is Some,
            old(self).active_branch.unwrap().invariants(&old(self).active_store),
            branch_stack_store_addrs_safe(&old(self).active_store),
            old(cache).wf(),
        ensures
            self.wf(),
            self@ == old(self)@,
            self.image == old(self).image,
            old(self).image.roots_wf() ==> self.image.roots_wf(),
            self.load_state == old(self).load_state,
            self.active_branch == old(self).active_branch,
            self.mini_allocator.allocators@ == old(self).mini_allocator.allocators@,
            self.mini_allocator.curr == old(self).mini_allocator.curr,
            self.mini_allocator.free_au_threshold == old(self).mini_allocator.free_au_threshold,
            self.store@ =~= old(self).store@,
            self.active_store@ =~= old(self).active_store@,
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match out {
                BranchPathLoadResult::Loaded{leaf, reads, receipt} => {
                    &&& leaf@.wf()
                    &&& old(cache)@ == cache@
                    &&& receipt@.key == key
                    &&& old(self).active_store@.entries.contains_key(leaf@)
                    &&& old(self).active_store@.entries[leaf@] == receipt@.target().node
                    &&& receipt@.target().node is Leaf
                    &&& equiv_key is Some ==> receipt@.path_equiv(equiv_key.unwrap())
                    &&& forall |i: int| 0 <= i < receipt@.lines.len() ==> {
                        &&& old(self).active_store@.entries.contains_key(#[trigger] receipt@.lines[i].addr)
                        &&& receipt@.lines[i].node
                            == old(self).active_store@.entries[receipt@.lines[i].addr]
                    }
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        Cache::Label::Access{reads: reads@, writes: Map::empty()},
                    )
                    &&& receipt@.needed_addrs() == reads@.dom()
                    &&& receipt@.target().addr == leaf@
                    &&& receipt@.valid_for(
                        old(self).active_branch.unwrap().root@,
                        to_branch_nodes(reads@),
                    )
                },
                BranchPathLoadResult::NeedCacheLoad{addr, handle} => {
                    &&& addr@.wf()
                    &&& addr@ != spec_superblock_addr()
                    &&& cache.entry_fetched(&addr)
                    &&& cache.valid_load_handle(&addr, handle)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        crate::implementation::FracCacheImpl_v::cache_load_label(&addr),
                    )
                },
                BranchPathLoadResult::CacheFull => {
                    &&& old(cache)@ == cache@
                },
                BranchPathLoadResult::Blocked => {
                    &&& old(cache)@ == cache@
                },
            },
    {
        let branch = match self.active_branch {
            Some(branch) => branch,
            None => return BranchPathLoadResult::Blocked,
        };
        let mut current = branch.root;
        let mut remaining = self.active_store.entries.len();
        let ghost cache0 = *cache;
        let ghost root_addr = branch.root@;
        let ghost mut reads = Map::<Address, RawPage>::empty();
        let ghost mut lines = Seq::<LoadedPathReceiptLine>::empty();
        proof {
            if branch.inv(&self.active_store) {
                assert(branch.i(&self.active_store).wf());
                assert(branch.i(&self.active_store).has_root());
                assert(self.active_store@.entries.contains_key(current@));
            } else {
                assert(branch.sealed_inv(&self.active_store));
                assert(branch.i(&self.active_store).valid_sealed_branch());
                assert(branch.i(&self.active_store).inv());
                assert(branch.i(&self.active_store).wf());
                assert(branch.i(&self.active_store).has_root());
                assert(self.active_store@.entries.contains_key(current@));
            }
            assert(branch.i(&self.active_store).inv());
            assert(branch_cursor_inv(branch, &self.active_store, current));
        }

        while remaining > 0
            invariant
                self.wf(),
                self@ == old(self)@,
                branch.invariants(&self.active_store),
                branch_stack_store_addrs_safe(&self.active_store),
                cache.wf(),
                cache@ == cache0@,
                cache.valid_load_handles_preserved(cache0),
                remaining <= self.active_store.entries.len(),
                self.active_store@.entries.contains_key(current@),
                branch_cursor_inv(branch, &self.active_store, current),
                branch_partial_path_wf(key, root_addr, lines, current@),
                equiv_key is Some ==> branch_path_lines_equiv(key, equiv_key.unwrap(), lines),
                forall |i: int| 0 <= i < lines.len() ==> {
                    &&& self.active_store@.entries.contains_key(#[trigger] lines[i].addr)
                    &&& lines[i].node == self.active_store@.entries[lines[i].addr]
                },
                reads.dom() == Set::new(|addr: Address| exists |i: int|
                    0 <= i < lines.len() && #[trigger] lines[i].addr == addr),
                forall |i: int| 0 <= i < lines.len() ==> {
                    #[trigger] to_branch_nodes(reads)[lines[i].addr] == lines[i].node
                },
                forall |addr: Address| #[trigger] reads.contains_key(addr)
                    ==> cache0@.valid_read(addr, reads[addr]),
                forall |addr: Address| #[trigger] reads.contains_key(addr)
                    && self.active_store@.entries.contains_key(addr)
                    ==> raw_page_to_branch_node(reads[addr]) == self.active_store@.entries[addr],
            decreases remaining,
        {
            remaining -= 1;
            let ghost cache_pre_fetch = *cache;
            proof {
                assert(current@.wf());
                assert(current@ != spec_superblock_addr());
            }
            match cache.fetch(&current, true) {
                FetchErrorCode::LoadInitiate{slot_handle} => {
                    let ghost cache_post_fetch = *cache;
                    proof {
                        FracCacheImpl::valid_load_handles_preserved_transitive(
                            cache0,
                            cache_pre_fetch,
                            cache_post_fetch,
                        );
                    }
                    return BranchPathLoadResult::NeedCacheLoad{
                        addr: current,
                        handle: slot_handle,
                    };
                },
                FetchErrorCode::Success{slot_handle} => {
                    let ghost cache_post_fetch = *cache;
                    let ghost raw = slot_handle.rec@;
                    let ghost fetched_slot = slot_handle.idx;
                    let fmt = BranchNodePageFmt::new();
                    let all_slice = Slice::all(&slot_handle.rec);
                    let parsed = fmt.try_parse(&all_slice, &slot_handle.rec);
                    proof {
                        assert(cache_pre_fetch@ == cache0@);
                        assert(cache_pre_fetch@.valid_read(current@, raw));
                        if parsed is Some {
                            assert(fmt == BranchNodePageFmt::spec_new());
                            assert(all_slice@.i(slot_handle.rec@) == slot_handle.rec@);
                            assert(fmt.parsable(raw));
                            assert(parsed.unwrap().parsedv() == fmt.parse(raw));
                            assert(raw_page_to_branch_node(raw) == parsed.unwrap()@);
                        }
                    }
                    cache.handle_release(&current, slot_handle);
                    let ghost cache_post_release = *cache;
                    proof {
                        FracCacheImpl::valid_load_handles_preserved_transitive(
                            cache0,
                            cache_pre_fetch,
                            cache_post_fetch,
                        );
                        FracCacheImpl::valid_load_handles_preserved_transitive(
                            cache0,
                            cache_post_fetch,
                            cache_post_release,
                        );
                        assert(cache_pre_fetch@.entries == cache_post_fetch@.entries.insert(
                            fetched_slot,
                            Entry::Filled{addr: current@, data: raw},
                        ));
                        assert(cache@.entries == cache_post_fetch@.entries.insert(
                            fetched_slot,
                            Entry::Filled{addr: current@, data: raw},
                        ));
                        assert(cache@.entries == cache_pre_fetch@.entries);
                        assert(cache@.lookup_map == cache_pre_fetch@.lookup_map);
                        assert(cache@.status_map == cache_pre_fetch@.status_map);
                        assert(cache@ == cache_pre_fetch@);
                        assert(cache@ == cache0@);
                    }
                    let parsed_node = match parsed {
                        Some(node) => node,
                        None => {
                            proof {
                                assert(cache@ == old(cache)@);
                            }
                            return BranchPathLoadResult::Blocked;
                        },
                    };

                    match self.active_store.read_checked(&current) {
                        Some(node) => {
                            let ghost node_view = node@;
                            if !same_branch_node_view(&parsed_node, &node) {
                                proof {
                                    assert(cache@ == old(cache)@);
                                }
                                return BranchPathLoadResult::Blocked;
                            }
                            proof {
                                assert(parsed_node@ == node_view);
                                assert(node_view == self.active_store@.entries[current@]);
                                assert(raw_page_to_branch_node(raw) == node_view);
                                let linked = branch.i(&self.active_store);
                                let ranking = linked.the_ranking();
                                let cursor = SpecLinkedBranch{root: current@, disk_view: self.active_store@};
                                assert(cursor.root() == node_view);
                                assert(cursor.keys_strictly_sorted_internal(ranking));
                                assert(cursor.root().keys_strictly_sorted());
                                assert(node_view.keys_strictly_sorted());
                            }
                            match node {
                                BranchNode::Leaf{..} => {
                                    let ghost reads_pre = reads;
                                    let ghost lines_pre = lines;
                                    let ghost line = LoadedPathReceiptLine{
                                        addr: current@,
                                        node: node_view,
                                    };
                                    proof {
                                        assert(line.wf());
                                        branch_path_extend_read_preserves(
                                            cache0@,
                                            reads_pre,
                                            lines_pre,
                                            current@,
                                            raw,
                                            root_addr,
                                            line,
                                        );
                                        reads = reads.insert(current@, raw);
                                        lines = lines.push(line);
                                        assert(to_branch_nodes(reads)[current@] == node_view);
                                        assert forall |i: int| 0 <= i < lines.len()
                                            implies #[trigger] to_branch_nodes(reads)[lines[i].addr] == lines[i].node by {
                                            if i == lines.len() - 1 {
                                                assert(lines[i] == line);
                                            } else {
                                                assert(lines[i] == lines_pre[i]);
                                                assert(lines[i].node == self.active_store@.entries[lines[i].addr]);
                                                if lines[i].addr == current@ {
                                                    assert(line.node == self.active_store@.entries[current@]);
                                                    assert(line.node == node_view);
                                                    assert(to_branch_nodes(reads)[lines[i].addr]
                                                        == to_branch_nodes(reads)[current@]);
                                                    assert(to_branch_nodes(reads)[current@] == node_view);
                                                    assert(lines[i].node == line.node);
                                                } else {
                                                    assert(reads[lines[i].addr] == reads_pre[lines[i].addr]);
                                                }
                                                assert(reads.contains_key(lines[i].addr));
                                            }
                                        }
                                        assert forall |i: int| 0 <= i < lines.len()
                                            implies self.active_store@.entries.contains_key(#[trigger] lines[i].addr)
                                                && lines[i].node == self.active_store@.entries[lines[i].addr] by {
                                            if i == lines.len() - 1 {
                                                assert(lines[i] == line);
                                            } else {
                                                assert(lines[i] == lines_pre[i]);
                                            }
                                        }
                                        assert(branch_path_lines_wf(key, root_addr, lines));
                                    }
                                    let ghost receipt = LoadedPathReceipt{
                                        key,
                                        root: root_addr,
                                        lines,
                                    };
                                    proof {
                                        assert(receipt.needed_addrs() == reads.dom());
                                        assert(receipt.target().addr == current@) by {
                                            assert(receipt.lines.last() == line);
                                        }
                                        assert(receipt.target().node == node_view) by {
                                            assert(receipt.lines.last() == line);
                                        }
                                        assert(receipt.target().node is Leaf);
                                        assert(self.active_store@.entries.contains_key(current@));
                                        assert(self.active_store@.entries[current@] == receipt.target().node);
                                        assert(receipt.wf());
                                        assert(receipt.valid_for(root_addr, to_branch_nodes(reads)));
                                        if equiv_key is Some {
                                            let other_key = equiv_key.unwrap();
                                            assert(branch_path_lines_equiv(key, other_key, lines)) by {
                                                assert forall |i: int| 0 <= i < lines.len()
                                                    && lines[i].node is Index
                                                    implies #[trigger] lines[i].node.route(key)
                                                        == lines[i].node.route(other_key) by {
                                                    if i == lines.len() - 1 {
                                                        assert(lines[i] == line);
                                                        assert(!(line.node is Index));
                                                    } else {
                                                        assert(0 <= i < lines_pre.len());
                                                        assert(lines[i] == lines_pre[i]);
                                                        assert(lines_pre[i].node is Index);
                                                        assert(branch_path_lines_equiv(key, other_key, lines_pre));
                                                    }
                                                }
                                            }
                                            assert(receipt.path_equiv(equiv_key.unwrap()));
                                        }
                                        Cache::State::access_read_only_from_valid_reads(
                                            cache0@,
                                            reads,
                                        );
                                        assert(cache@ == cache0@);
                                    }
                                    return BranchPathLoadResult::Loaded{
                                        leaf: current,
                                        reads: Ghost(reads),
                                        receipt: Ghost(receipt),
                                    };
                                },
                                BranchNode::Index{pivots, children, ..} => {
                                    let ghost reads_pre = reads;
                                    let ghost lines_pre = lines;
                                    let ghost line = LoadedPathReceiptLine{
                                        addr: current@,
                                        node: node_view,
                                    };
                                    proof {
                                        assert(line.wf());
                                        branch_path_extend_read_preserves(
                                            cache0@,
                                            reads_pre,
                                            lines_pre,
                                            current@,
                                            raw,
                                            root_addr,
                                            line,
                                        );
                                        reads = reads.insert(current@, raw);
                                        lines = lines.push(line);
                                        assert(to_branch_nodes(reads)[current@] == node_view);
                                        assert forall |i: int| 0 <= i < lines.len()
                                            implies #[trigger] to_branch_nodes(reads)[lines[i].addr] == lines[i].node by {
                                            if i == lines.len() - 1 {
                                                assert(lines[i] == line);
                                            } else {
                                                assert(lines[i] == lines_pre[i]);
                                                assert(lines[i].node == self.active_store@.entries[lines[i].addr]);
                                                if lines[i].addr == current@ {
                                                    assert(line.node == self.active_store@.entries[current@]);
                                                    assert(line.node == node_view);
                                                    assert(to_branch_nodes(reads)[lines[i].addr]
                                                        == to_branch_nodes(reads)[current@]);
                                                    assert(to_branch_nodes(reads)[current@] == node_view);
                                                    assert(lines[i].node == line.node);
                                                } else {
                                                    assert(reads[lines[i].addr] == reads_pre[lines[i].addr]);
                                                }
                                                assert(reads.contains_key(lines[i].addr));
                                            }
                                        }
                                        assert forall |i: int| 0 <= i < lines.len()
                                            implies self.active_store@.entries.contains_key(#[trigger] lines[i].addr)
                                                && lines[i].node == self.active_store@.entries[lines[i].addr] by {
                                            if i == lines.len() - 1 {
                                                assert(lines[i] == line);
                                            } else {
                                                assert(lines[i] == lines_pre[i]);
                                            }
                                        }
                                        assert(branch_path_lines_wf(key, root_addr, lines));
                                    }
                                    let child_idx = branch_stack_route_index(&pivots, key);
                                    if child_idx >= children.len() {
                                        return BranchPathLoadResult::Blocked;
                                    }
                                    if equiv_key.is_some() {
                                        let other_child_idx = branch_stack_route_index(
                                            &pivots,
                                            equiv_key.unwrap(),
                                        );
                                        if other_child_idx != child_idx {
                                            return BranchPathLoadResult::Blocked;
                                        }
                                    }
                                    proof {
                                        assert(branch.i(&self.active_store).wf()) by {
                                            if branch.inv(&self.active_store) {
                                                assert(branch.i(&self.active_store).wf());
                                            } else {
                                                assert(branch.sealed_inv(&self.active_store));
                                                assert(branch.i(&self.active_store).valid_sealed_branch());
                                                assert(branch.i(&self.active_store).inv());
                                                assert(branch.i(&self.active_store).wf());
                                            }
                                        }
                                        assert(branch.i(&self.active_store).disk_view.wf());
                                        assert(branch.i(&self.active_store).disk_view.no_dangling_address());
                                        assert(self.active_store@.entries.contains_key(current@));
                                        assert(self.active_store@.entries[current@] == node_view);
                                        assert(node_view is Index);
                                        assert(node_view.wf());
                                        assert((child_idx as int) < node_view->children.len());
                                        assert(node_view.valid_child_index(child_idx as int));
                                        assert(branch.i(&self.active_store).disk_view.node_has_valid_child_address(node_view));
                                        assert(branch.i(&self.active_store).disk_view.valid_address(node_view->children[child_idx as int]));
                                        assert(node_view->children[child_idx as int] == children@[child_idx as int]@);
                                    }
                                    proof {
                                        let linked = branch.i(&self.active_store);
                                        let ranking = linked.the_ranking();
                                        let cursor = SpecLinkedBranch{root: current@, disk_view: self.active_store@};
                                        let next_cursor = cursor.child_at_idx(child_idx as int);
                                        assert(Key::is_strictly_sorted(pivots@));
                                        Key::strictly_sorted_implies_sorted(pivots@);
                                        assert(child_idx as int == node_view.route(key) + 1);
                                        if equiv_key is Some {
                                            let other_key = equiv_key.unwrap();
                                            assert(child_idx as int == node_view.route(other_key) + 1);
                                            assert(node_view.route(key) == node_view.route(other_key));
                                        }
                                        assert(cursor.root() == node_view);
                                        assert(cursor.root().valid_child_index(child_idx as int));
                                        assert(cursor.child_at_idx(child_idx as int) == next_cursor);
                                        assert(next_cursor.root == node_view->children[child_idx as int]);
                                        assert(next_cursor.wf());
                                        assert(next_cursor.valid_ranking(ranking));
                                        assert(next_cursor.keys_strictly_sorted_internal(ranking));
                                    }
                                    current = children[child_idx];
                                    proof {
                                        let linked = branch.i(&self.active_store);
                                        let ranking = linked.the_ranking();
                                        let cursor = SpecLinkedBranch{root: current@, disk_view: self.active_store@};
                                        assert(lines.last() == line);
                                        assert(line.node is Index);
                                        assert(line.node->children[line.node.route(key) + 1] == current@);
                                        if equiv_key is Some {
                                            let other_key = equiv_key.unwrap();
                                            assert(branch_path_lines_equiv(key, other_key, lines)) by {
                                                assert(line.node == node_view);
                                                assert(node_view.route(key) == node_view.route(other_key));
                                                assert forall |i: int| 0 <= i < lines.len()
                                                    && lines[i].node is Index
                                                    implies #[trigger] lines[i].node.route(key)
                                                        == lines[i].node.route(other_key) by {
                                                    if i == lines_pre.len() {
                                                        assert(lines[i] == line);
                                                        assert(line.node.route(key) == line.node.route(other_key));
                                                    } else {
                                                        assert(0 <= i < lines_pre.len());
                                                        assert(lines[i] == lines_pre[i]);
                                                        assert(lines_pre[i].node is Index);
                                                        assert(branch_path_lines_equiv(key, other_key, lines_pre));
                                                    }
                                                }
                                            }
                                        }
                                        assert(cursor.wf());
                                        assert(cursor.valid_ranking(ranking));
                                        assert(cursor.keys_strictly_sorted_internal(ranking));
                                        assert(branch_cursor_inv(branch, &self.active_store, current));
                                        assert(branch_partial_path_wf(key, root_addr, lines, current@));
                                    }
                                },
                                BranchNode::Auxiliary{..} => {
                                    return BranchPathLoadResult::Blocked;
                                }
                            }
                        },
                        None => {
                            return BranchPathLoadResult::Blocked;
                        },
                    }
                },
                FetchErrorCode::CacheFull => {
                    return BranchPathLoadResult::CacheFull;
                },
                FetchErrorCode::Awaiting
                | FetchErrorCode::NotPresent => {
                    return BranchPathLoadResult::Blocked;
                },
            }
        }

        BranchPathLoadResult::Blocked
    }

    pub fn query_with_cache(
        &mut self,
        cache: &mut FracCacheImpl,
        key: Key,
    ) -> (out: BranchQueryResult)
        requires
            old(self).wf(),
            old(self).load_state is MetadataLoaded,
            old(self).active_branch is Some ==> old(self).active_branch.unwrap().invariants(&old(self).active_store),
            branch_stack_store_addrs_safe(&old(self).store),
            branch_stack_store_addrs_safe(&old(self).active_store),
            old(cache).wf(),
        ensures
            self.wf(),
            self@ == old(self)@,
            self.image == old(self).image,
            old(self).image.roots_wf() ==> self.image.roots_wf(),
            self.load_state == old(self).load_state,
            self.mini_allocator.i() == old(self).mini_allocator.i(),
            self.mini_allocator.allocators@ == old(self).mini_allocator.allocators@,
            self.mini_allocator.curr == old(self).mini_allocator.curr,
            self.mini_allocator.free_au_threshold == old(self).mini_allocator.free_au_threshold,
            self.active_store@ =~= old(self).active_store@,
            branch_stack_store_addrs_safe(&old(self).store)
                ==> branch_stack_store_addrs_safe(&self.store),
            branch_stack_store_addrs_safe(&old(self).active_store)
                ==> branch_stack_store_addrs_safe(&self.active_store),
            old(self).active_branch is Some
                && old(self).active_branch.unwrap().inv(&old(self).active_store)
                ==> self.active_branch.unwrap().inv(&self.active_store),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match out {
                BranchQueryResult::Hit{value, msg, reads, receipts} => {
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        Cache::Label::Access{reads: reads@, writes: Map::empty()},
                    )
                    &&& AtomicBranchState::State::next(
                        old(self)@,
                        old(self)@,
                        AtomicBranchState::Label::Query{
                            key,
                            msg: msg@,
                            receipts: receipts@,
                            read_nodes: to_branch_nodes(reads@),
                        },
                    )
                    &&& reads@.dom() == query_receipts_read_addrs(
                        receipts@,
                        receipts@.len() as nat,
                    )
                    &&& crate::implementation::AllocationBranchStack_v::normalize_value(msg@) == value
                },
                BranchQueryResult::NeedCacheLoad{addr, handle} => {
                    &&& self@ == old(self)@
                    &&& addr@.wf()
                    &&& addr@ != spec_superblock_addr()
                    &&& cache.entry_fetched(&addr)
                    &&& cache.valid_load_handle(&addr, handle)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        crate::implementation::FracCacheImpl_v::cache_load_label(&addr),
                    )
                },
                BranchQueryResult::Blocked => {
                    &&& old(cache)@ == cache@
                },
            },
    {
        let ghost cache0 = *cache;
        let ghost roots = query_roots(self.image@.sealed_roots, self.active_branch_i());
        let ghost mut reads = Map::<Address, RawPage>::empty();
        let ghost mut receipts = Seq::<LoadedPathReceipt>::empty();
        let mut msg = Message::Update{delta: Delta(0)};
        proof {
            assert(msg == query_from_receipts_up_to(receipts, receipts.len() as nat));
            assert(cache.valid_load_handles_preserved(cache0));
            assert(branch_query_prefix_receipts_valid(roots, receipts, to_branch_nodes(reads), key));
            assert(branch_query_receipts_store_aligned(&self.store, receipts));
            assert forall |addr: Address| #[trigger] reads.contains_key(addr)
                && self.store@.entries.contains_key(addr)
                implies raw_page_to_branch_node(reads[addr]) == self.store@.entries[addr] by {
                assert(!reads.contains_key(addr));
            }
        }

        let mut root_idx = 0usize;
        while root_idx < self.image.sealed_roots.len()
            invariant
                self.wf(),
                self@ == old(self)@,
                self.load_state is MetadataLoaded,
                old(self).active_branch is Some ==> old(self).active_branch.unwrap().invariants(&old(self).active_store),
                branch_stack_store_addrs_safe(&self.store),
                cache.wf(),
                cache@ == cache0@,
                cache.valid_load_handles_preserved(cache0),
                roots == query_roots(self.image@.sealed_roots, self.active_branch_i()),
                root_idx <= self.image.sealed_roots.len(),
                receipts.len() == root_idx,
                branch_query_prefix_receipts_valid(roots, receipts, to_branch_nodes(reads), key),
                branch_query_receipts_store_aligned(&self.store, receipts),
                reads.dom() == query_receipts_read_addrs(receipts, receipts.len() as nat),
                msg == query_from_receipts_up_to(receipts, receipts.len() as nat),
                forall |addr: Address| #[trigger] reads.contains_key(addr)
                    ==> cache0@.valid_read(addr, reads[addr]),
                forall |addr: Address| #[trigger] reads.contains_key(addr)
                    && self.store@.entries.contains_key(addr)
                    ==> raw_page_to_branch_node(reads[addr]) == self.store@.entries[addr],
            decreases self.image.sealed_roots.len() - root_idx,
        {
            let root = self.image.sealed_roots[root_idx];
            let stored = self.store.read_checked(&root);
            let (keys, msgs) = match stored {
                Some(BranchNode::Leaf{keys, msgs}) => {
                    if keys.len() == 0 || keys.len() != msgs.len() {
                        proof {
                            assert(cache@ == cache0@);
                        }
                        return BranchQueryResult::Blocked;
                    }
                    if !branch_stack_keys_strictly_sorted(&keys) {
                        proof {
                            assert(cache@ == cache0@);
                        }
                        return BranchQueryResult::Blocked;
                    }
                    (keys, msgs)
                },
                _ => {
                    proof {
                        assert(cache@ == cache0@);
                    }
                    return BranchQueryResult::Blocked;
                },
            };

            proof {
                assert(self.store@.entries.contains_key(root@));
                assert(root@.wf());
                assert(root@ != spec_superblock_addr());
            }
            let ghost cache_pre_fetch = *cache;
            match cache.fetch(&root, true) {
                FetchErrorCode::LoadInitiate{slot_handle} => {
                    let ghost cache_post_fetch = *cache;
                    proof {
                        assert(cache_pre_fetch@ == cache0@);
                        FracCacheImpl::valid_load_handles_preserved_transitive(
                            cache0,
                            cache_pre_fetch,
                            cache_post_fetch,
                        );
                    }
                    return BranchQueryResult::NeedCacheLoad{addr: root, handle: slot_handle};
                },
                FetchErrorCode::Success{slot_handle} => {
                    let ghost cache_post_fetch = *cache;
                    let ghost raw = slot_handle.rec@;
                    let ghost fetched_slot = slot_handle.idx;
                    let fmt = BranchNodePageFmt::new();
                    let all_slice = Slice::all(&slot_handle.rec);
                    let parsed = fmt.try_parse(&all_slice, &slot_handle.rec);
                    proof {
                        assert(cache_pre_fetch@ == cache0@);
                        assert(cache_pre_fetch@.valid_read(root@, raw));
                        assert(cache0@.valid_read(root@, raw));
                        if parsed is Some {
                            assert(fmt == BranchNodePageFmt::spec_new());
                            assert(all_slice@.i(slot_handle.rec@) == slot_handle.rec@);
                            assert(fmt.parsable(raw));
                            assert(parsed.unwrap().parsedv() == fmt.parse(raw));
                            assert(raw_page_to_branch_node(raw) == parsed.unwrap()@);
                        }
                    }
                    cache.handle_release(&root, slot_handle);
                    let ghost cache_post_release = *cache;
                    proof {
                        FracCacheImpl::valid_load_handles_preserved_transitive(
                            cache0,
                            cache_pre_fetch,
                            cache_post_fetch,
                        );
                        FracCacheImpl::valid_load_handles_preserved_transitive(
                            cache0,
                            cache_post_fetch,
                            cache_post_release,
                        );
                        assert(cache_pre_fetch@.entries == cache_post_fetch@.entries.insert(
                            fetched_slot,
                            Entry::Filled{addr: root@, data: raw},
                        ));
                        assert(cache@.entries == cache_post_fetch@.entries.insert(
                            fetched_slot,
                            Entry::Filled{addr: root@, data: raw},
                        ));
                        assert(cache@.entries == cache_pre_fetch@.entries);
                        assert(cache@.lookup_map == cache_pre_fetch@.lookup_map);
                        assert(cache@.status_map == cache_pre_fetch@.status_map);
                        assert(cache@ == cache_pre_fetch@);
                        assert(cache@ == cache0@);
                    }
                    let parsed_node = match parsed {
                        Some(node) => node,
                        None => {
                            proof {
                                assert(cache@ == old(cache)@);
                            }
                            return BranchQueryResult::Blocked;
                        },
                    };
                    let stored_node = BranchNode::Leaf{keys: keys.clone(), msgs: msgs.clone()};
                    if !same_branch_node_view(&parsed_node, &stored_node) {
                        proof {
                            assert(cache@ == old(cache)@);
                        }
                        return BranchQueryResult::Blocked;
                    }

                    let piece_msg = query_leaf_message(&keys, &msgs, key);
                    let merged = branch_stack_merge_messages(msg, piece_msg);
                    proof {
                        let node = SpecBranchNode::Leaf{keys: keys@, msgs: msgs@};
                        assert(stored_node@ == node);
                        assert(parsed_node@ == node);
                        assert(self.store@.entries[root@] == node);
                        assert(raw_page_to_branch_node(raw) == node);
                        let line = LoadedPathReceiptLine{addr: root@, node};
                        let receipt = LoadedPathReceipt{key, root: root@, lines: seq![line]};
                        let reads_pre = reads;
                        let receipts_pre = receipts;
                        assert forall |addr: Address| #[trigger] reads_pre.contains_key(addr)
                            && self.store@.entries.contains_key(addr)
                            implies raw_page_to_branch_node(reads_pre[addr])
                                == self.store@.entries[addr] by {
                            assert(reads.contains_key(addr));
                        }
                        reads = reads.insert(root@, raw);
                        receipts = receipts.push(receipt);

                        assert(reads_pre.dom() <= reads.dom()) by {
                            assert forall |addr: Address| #[trigger] reads_pre.dom().contains(addr)
                                implies reads.dom().contains(addr) by {
                                assert(reads.contains_key(addr));
                            }
                        }
                        assert forall |addr: Address| #[trigger] reads.contains_key(addr)
                            implies cache0@.valid_read(addr, reads[addr]) by {
                            if addr == root@ {
                                assert(cache0@.valid_read(root@, raw));
                            } else {
                                assert(reads_pre.contains_key(addr));
                            }
                        }
                        assert forall |addr: Address| #[trigger] reads.contains_key(addr)
                            && self.store@.entries.contains_key(addr)
                            implies raw_page_to_branch_node(reads[addr]) == self.store@.entries[addr] by {
                            if addr == root@ {
                                assert(reads[addr] == raw);
                                assert(raw_page_to_branch_node(raw) == self.store@.entries[root@]);
                            } else {
                                assert(reads_pre.contains_key(addr));
                                assert(reads[addr] == reads_pre[addr]);
                                assert(raw_page_to_branch_node(reads_pre[addr])
                                    == self.store@.entries[addr]);
                            }
                        }
                        branch_query_prefix_valid_after_reads_grow(
                            roots,
                            receipts_pre,
                            reads_pre,
                            reads,
                            key,
                            &self.store,
                        );
                        one_line_leaf_receipt_facts(
                            key,
                            root@,
                            keys@,
                            msgs@,
                            to_branch_nodes(reads),
                        );
                        assert(receipt.needed_addrs() == set![root@]);
                        query_receipts_read_addrs_push(receipts_pre, receipt);
                        assert(reads.dom() == reads_pre.dom().insert(root@));
                        assert(reads.dom() == query_receipts_read_addrs(
                            receipts,
                            receipts.len() as nat,
                        )) by {
                            assert(reads_pre.dom() == query_receipts_read_addrs(
                                receipts_pre,
                                receipts_pre.len() as nat,
                            ));
                            assert(query_receipts_read_addrs(receipts, receipts.len() as nat)
                                == reads_pre.dom() + receipt.needed_addrs());
                            assert(receipt.needed_addrs() == set![root@]);
                            assert forall |addr: Address| #[trigger] reads.dom().contains(addr)
                                <==> (reads_pre.dom() + set![root@]).contains(addr) by {
                            }
                        }
                        assert(receipt.valid_for(root@, to_branch_nodes(reads)));
                        assert(piece_msg == receipt.result());
                        assert(branch_query_prefix_receipts_valid(
                            roots,
                            receipts,
                            to_branch_nodes(reads),
                            key,
                        )) by {
                            assert forall |i: int| #![trigger receipts[i]] 0 <= i < receipts.len()
                                implies {
                                    let receipt_i = receipts[i];
                                    &&& receipt_i.key == key
                                    &&& receipt_i.valid_for(roots[i], to_branch_nodes(reads))
                                    &&& receipt_i.target().node is Leaf
                                } by {
                                if i == receipts_pre.len() {
                                    assert(receipts[i] == receipt);
                                    assert(root@ == self.image@.sealed_roots[root_idx as int]);
                                    assert(roots[i] == root@);
                                } else {
                                    assert(0 <= i < receipts_pre.len());
                                    assert(receipts[i] == receipts_pre[i]);
                                    assert(branch_query_prefix_receipts_valid(
                                        roots,
                                        receipts_pre,
                                        to_branch_nodes(reads),
                                        key,
                                    ));
                                }
                            }
                        }
                        assert(branch_query_receipts_store_aligned(&self.store, receipts)) by {
                            assert forall |i: int, j: int|
                                0 <= i < receipts.len() && 0 <= j < receipts[i].lines.len()
                                implies {
                                    let line_i = #[trigger] receipts[i].lines[j];
                                    &&& self.store@.entries.contains_key(line_i.addr)
                                    &&& line_i.node == self.store@.entries[line_i.addr]
                                } by {
                                if i == receipts_pre.len() {
                                    assert(receipts[i] == receipt);
                                    assert(j == 0);
                                    assert(receipts[i].lines[j] == line);
                                } else {
                                    assert(0 <= i < receipts_pre.len());
                                    assert(receipts[i] == receipts_pre[i]);
                                    assert(branch_query_receipts_store_aligned(&self.store, receipts_pre));
                                }
                            }
                        }
                        query_from_receipts_push(receipts_pre, receipt);
                        assert(merged == query_from_receipts_up_to(receipts, receipts.len() as nat));
                    }
                    msg = merged;
                    root_idx = root_idx + 1;
                },
                FetchErrorCode::Awaiting
                | FetchErrorCode::CacheFull
                | FetchErrorCode::NotPresent => {
                    let ghost cache_post_fetch = *cache;
                    proof {
                        FracCacheImpl::valid_load_handles_preserved_transitive(
                            cache0,
                            cache_pre_fetch,
                            cache_post_fetch,
                        );
                        assert(cache@ == cache0@);
                    }
                    return BranchQueryResult::Blocked;
                },
            }
        }

        if self.active_branch.is_some() {
            let ghost cache_before_active = *cache;
            let ghost store_before_active = self.active_store@;
            let ghost active_root = self.active_branch.unwrap().root@;
            match self.load_path_for_key(cache, key, None) {
                BranchPathLoadResult::Loaded{leaf, reads: active_reads, receipt} => {
                    proof {
                        assert(self@ == old(self)@);
                        assert(self.active_store@ =~= store_before_active);
                        assert(store_before_active.entries.contains_key(leaf@));
                        assert(store_before_active.entries[leaf@] == receipt@.target().node);
                        assert(self.active_store@.entries.contains_key(leaf@));
                        assert(self.active_store@.entries[leaf@] == receipt@.target().node);
                        assert(receipt@.target().node is Leaf);
                        assert(receipt@.valid_for(active_root, to_branch_nodes(active_reads@)));
                        assert(receipt@.wf());
                        assert(receipt@.target().wf());
                    }
                    let active_msg = match self.active_store.read_checked(&leaf) {
                        Some(BranchNode::Leaf{keys, msgs}) => {
                            proof {
                                let active_receipt = receipt@;
                                assert(self.active_store@.entries.contains_key(leaf@));
                                assert(self.active_store@.entries[leaf@] == receipt@.target().node);
                                assert(receipt@.target().node == (SpecBranchNode::Leaf{keys: keys@, msgs: msgs@}));
                                assert(receipt@.target().node.wf());
                                assert(receipt@.target().wf());
                                assert(receipt@.target().node.keys_strictly_sorted());
                            }
                            let out = query_leaf_message(&keys, &msgs, key);
                            proof {
                                let active_receipt = receipt@;
                                receipt_result_matches_leaf_query(active_receipt, keys@, msgs@);
                                assert(out == active_receipt.result());
                            }
                            out
                        },
                        _ => {
                            proof {
                                assert(self.active_store@.entries.contains_key(leaf@));
                                assert(self.active_store@.entries[leaf@] == receipt@.target().node);
                                assert(receipt@.target().node is Leaf);
                                assert(false);
                            }
                            return BranchQueryResult::Blocked;
                        },
                    };
                    let merged = branch_stack_merge_messages(msg, active_msg);
                    proof {
                        let active_receipt = receipt@;
                        let reads_pre = reads;
                        let receipts_pre = receipts;
                        let active_reads_map = active_reads@;
                        assert forall |addr: Address| #[trigger] reads_pre.contains_key(addr)
                            && self.store@.entries.contains_key(addr)
                            implies raw_page_to_branch_node(reads_pre[addr])
                                == self.store@.entries[addr] by {
                            assert(reads.contains_key(addr));
                        }
                        assert(cache_before_active@ == cache0@);
                        assert(cache@ == cache0@);
                        assert(branch_query_receipts_store_aligned(&self.store, receipts_pre));
                        assert forall |addr: Address| #[trigger] active_reads_map.contains_key(addr)
                            implies cache0@.valid_read(addr, active_reads_map[addr]) by {
                            Cache::State::access_read_valid(
                                cache_before_active@,
                                cache@,
                                active_reads_map,
                                Map::empty(),
                                addr,
                            );
                        }
                        assert forall |addr: Address| #[trigger] reads_pre.contains_key(addr)
                            implies cache0@.valid_read(addr, reads_pre[addr]) by {
                            assert(reads.contains_key(addr));
                        }
                        assert(active_receipt.needed_addrs() == active_reads_map.dom());
                        assert forall |addr: Address| #[trigger] active_reads_map.contains_key(addr)
                            && self.active_store@.entries.contains_key(addr)
                            implies raw_page_to_branch_node(active_reads_map[addr])
                                == self.active_store@.entries[addr] by {
                            assert(active_receipt.needed_addrs().contains(addr));
                            let k = choose |k: int| 0 <= k < active_receipt.lines.len()
                                && #[trigger] active_receipt.lines[k].addr == addr;
                            assert(active_receipt.valid_for(active_root, to_branch_nodes(active_reads_map)));
                            assert(to_branch_nodes(active_reads_map)[addr] == active_receipt.lines[k].node);
                            assert(active_receipt.lines[k].node
                                == store_before_active.entries[active_receipt.lines[k].addr]);
                            assert(self.active_store@ =~= store_before_active);
                            assert(self.active_store@.entries[addr] == store_before_active.entries[addr]);
                        }
                        reads = reads_pre.union_prefer_right(active_reads_map);
                        receipts = receipts.push(active_receipt);
                        assert(reads_pre.dom() <= reads.dom()) by {
                            assert forall |addr: Address| #[trigger] reads_pre.dom().contains(addr)
                                implies reads.dom().contains(addr) by {
                                assert(reads.contains_key(addr));
                            }
                        }
                        assert forall |addr: Address| #[trigger] reads.contains_key(addr)
                            implies cache0@.valid_read(addr, reads[addr]) by {
                            if active_reads_map.contains_key(addr) {
                                assert(reads[addr] == active_reads_map[addr]);
                            } else {
                                assert(reads_pre.contains_key(addr));
                                assert(reads[addr] == reads_pre[addr]);
                            }
                        }
                        assert forall |i: int, j: int|
                            0 <= i < receipts_pre.len() && 0 <= j < receipts_pre[i].lines.len()
                            implies #[trigger] reads[receipts_pre[i].lines[j].addr]
                                == reads_pre[receipts_pre[i].lines[j].addr] by {
                            let line = receipts_pre[i].lines[j];
                            assert(branch_query_prefix_receipts_valid(
                                roots,
                                receipts_pre,
                                to_branch_nodes(reads_pre),
                                key,
                            ));
                            assert(receipts_pre[i].valid_for(roots[i], to_branch_nodes(reads_pre)));
                            assert(to_branch_nodes(reads_pre).contains_key(line.addr));
                            assert(reads_pre.contains_key(line.addr));
                            if active_reads_map.contains_key(line.addr) {
                                assert(reads[line.addr] == active_reads_map[line.addr]);
                                assert(cache0@.valid_read(line.addr, active_reads_map[line.addr]));
                                assert(cache0@.valid_read(line.addr, reads_pre[line.addr]));
                                Cache::State::valid_read_unique(
                                    cache0@,
                                    line.addr,
                                    active_reads_map[line.addr],
                                    reads_pre[line.addr],
                                );
                            } else {
                                assert(reads[line.addr] == reads_pre[line.addr]);
                            }
                        }
                        branch_query_prefix_valid_after_reads_preserve_lines(
                            roots,
                            receipts_pre,
                            reads_pre,
                            reads,
                            key,
                        );
                        assert(active_msg == active_receipt.result());
                        assert(active_receipt.valid_for(
                            active_root,
                            to_branch_nodes(reads),
                        )) by {
                            assert(active_receipt.valid_for(
                                active_root,
                                to_branch_nodes(active_reads_map),
                            ));
                            assert forall |j: int| 0 <= j < active_receipt.lines.len()
                                implies {
                                    &&& to_branch_nodes(reads).contains_key(active_receipt.lines[j].addr)
                                    &&& #[trigger] to_branch_nodes(reads)[active_receipt.lines[j].addr]
                                        == active_receipt.lines[j].node
                                } by {
                                let line = active_receipt.lines[j];
                                assert(active_reads_map.contains_key(line.addr));
                                assert(reads.contains_key(line.addr));
                                if active_reads_map.contains_key(line.addr) {
                                    assert(reads[line.addr] == active_reads_map[line.addr]);
                                }
                                assert(to_branch_nodes(active_reads_map)[line.addr] == line.node);
                                assert(to_branch_nodes(reads)[line.addr] == line.node);
                            }
                        }
                        assert(branch_query_prefix_receipts_valid(
                            roots,
                            receipts,
                            to_branch_nodes(reads),
                            key,
                        )) by {
                            assert forall |i: int| #![trigger receipts[i]] 0 <= i < receipts.len()
                                implies {
                                    let receipt_i = receipts[i];
                                    &&& receipt_i.key == key
                                    &&& receipt_i.valid_for(roots[i], to_branch_nodes(reads))
                                    &&& receipt_i.target().node is Leaf
                                } by {
                                if i == receipts_pre.len() {
                                    assert(receipts[i] == active_receipt);
                                    assert(receipts_pre.len() == self.image@.sealed_roots.len());
                                    assert(active_receipt.key == key);
                                    assert(active_receipt.valid_for(active_root, to_branch_nodes(reads)));
                                    assert(active_receipt.target().node is Leaf);
                                    assert(roots[i] == active_root);
                                } else {
                                    assert(0 <= i < receipts_pre.len());
                                    assert(receipts[i] == receipts_pre[i]);
                                    assert(branch_query_prefix_receipts_valid(
                                        roots,
                                        receipts_pre,
                                        to_branch_nodes(reads),
                                        key,
                                    ));
                                }
                            }
                        }
                        query_receipts_read_addrs_push(receipts_pre, active_receipt);
                        assert(reads.dom() == reads_pre.dom() + active_reads_map.dom()) by {
                            assert forall |addr: Address| #[trigger] reads.dom().contains(addr)
                                <==> (reads_pre.dom() + active_reads_map.dom()).contains(addr) by {
                                if reads.dom().contains(addr) {
                                    if active_reads_map.contains_key(addr) {
                                    } else {
                                        assert(reads_pre.contains_key(addr));
                                    }
                                } else {
                                    if reads_pre.dom().contains(addr) {
                                        assert(reads.contains_key(addr));
                                    }
                                    if active_reads_map.dom().contains(addr) {
                                        assert(reads.contains_key(addr));
                                    }
                                }
                            }
                        }
                        assert(reads.dom() == query_receipts_read_addrs(
                            receipts,
                            receipts.len() as nat,
                        )) by {
                            assert(reads_pre.dom() == query_receipts_read_addrs(
                                receipts_pre,
                                receipts_pre.len() as nat,
                            ));
                            assert(active_receipt.needed_addrs() == active_reads_map.dom());
                            assert(query_receipts_read_addrs(receipts, receipts.len() as nat)
                                == reads_pre.dom() + active_reads_map.dom());
                        }
                        query_from_receipts_push(receipts_pre, active_receipt);
                        assert(merged == query_from_receipts_up_to(receipts, receipts.len() as nat));
                        FracCacheImpl::valid_load_handles_preserved_transitive(
                            cache0,
                            cache_before_active,
                            *cache,
                        );
                    }
                    msg = merged;
                },
                BranchPathLoadResult::NeedCacheLoad{addr, handle} => {
                    proof {
                        assert(cache_before_active@ == cache0@);
                        FracCacheImpl::valid_load_handles_preserved_transitive(
                            cache0,
                            cache_before_active,
                            *cache,
                        );
                    }
                    return BranchQueryResult::NeedCacheLoad{addr, handle};
                },
                BranchPathLoadResult::CacheFull
                | BranchPathLoadResult::Blocked => {
                    proof {
                        assert(cache@ == cache0@);
                        FracCacheImpl::valid_load_handles_preserved_transitive(
                            cache0,
                            cache_before_active,
                            *cache,
                        );
                    }
                    return BranchQueryResult::Blocked;
                },
            }
        }

        let value = branch_stack_normalize_value(msg);
        proof {
            assert(receipts.len() == roots.len());
            branch_query_full_prefix_receipts_valid(
                roots,
                receipts,
                to_branch_nodes(reads),
                key,
            );
            Cache::State::access_read_only_from_valid_reads(cache0@, reads);
            reveal(AtomicBranchState::State::next);
            reveal(AtomicBranchState::State::next_by);
            assert(AtomicBranchState::State::query(
                old(self)@,
                old(self)@,
                AtomicBranchState::Label::Query{
                    key,
                    msg,
                    receipts,
                    read_nodes: to_branch_nodes(reads),
                },
            ));
            assert(AtomicBranchState::State::next_by(
                old(self)@,
                old(self)@,
                AtomicBranchState::Label::Query{
                    key,
                    msg,
                    receipts,
                    read_nodes: to_branch_nodes(reads),
                },
                AtomicBranchState::Step::query(),
            ));
            assert(AtomicBranchState::State::next(
                old(self)@,
                old(self)@,
                AtomicBranchState::Label::Query{
                    key,
                    msg,
                    receipts,
                    read_nodes: to_branch_nodes(reads),
                },
            ));
        }
        BranchQueryResult::Hit{
            value,
            msg: Ghost(msg),
            reads: Ghost(reads),
            receipts: Ghost(receipts),
        }
    }

    pub fn load_metadata(&mut self, root: IAddress, discovered_aus: Vec<IAU>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self.active_branch == old(self).active_branch,
            self.load_state == old(self).load_state,
            self.image@ == old(self).image@,
            old(self).image.roots_wf() ==> self.image.roots_wf(),
            self.persistent_prefix_len == old(self).persistent_prefix_len,
            self.persistent_seq_end == old(self).persistent_seq_end,
            self.persisted_root_count == old(self).persisted_root_count,
            self.seq_end == old(self).seq_end,
            self.commit_phase == old(self).commit_phase,
            self.mini_allocator.i() == old(self).mini_allocator.i(),
            self.store@ == old(self).store@,
            self.active_store@ == old(self).active_store@,
            self.branch_summary.i().dom().contains(root.au as nat),
            self.branch_summary.i()[root.au as nat] == iau_seq_set(discovered_aus@),
            self.branch_summary.i()
                == old(self).branch_summary.i().insert(root.au as nat, iau_seq_set(discovered_aus@)),
            self.branch_summary.i().dom() =~= old(self).branch_summary.i().dom().insert(root.au as nat),
    {
        self.branch_summary.insert_or_update(root.au, discovered_aus);
    }

    pub fn grow_active_leaf_with_cache(
        &mut self,
        cache: &mut FracCacheImpl,
        disk_au_count: IAU,
        disk_page_count: IPage,
    ) -> (out: BranchMaintenanceResult)
        requires
            old(self).wf(),
            old(self).load_state is MetadataLoaded,
            old(cache).wf(),
            0 < (disk_page_count as nat),
            (disk_page_count as nat) == crate::disk::GenericDisk_v::page_count(),
            old(self).active_branch is Some && old(self).mini_allocator.allocation_ready() ==> {
                &&& old(self).active_branch_i().ready_for_mutation(old(self).mini_allocator.i())
                &&& old(self).active_branch.unwrap().inv(&old(self).active_store)
                &&& branch_stack_store_addrs_safe(&old(self).active_store)
                &&& MiniAllocatorImpl::allocators_unique(old(self).mini_allocator.allocators@)
                &&& old(self).mini_allocator.bounded(disk_au_count)
            },
        ensures
            self.wf(),
            self.load_state == old(self).load_state,
            self.image == old(self).image,
            old(self).image.roots_wf() ==> self.image.roots_wf(),
            self.store@ =~= old(self).store@,
            branch_stack_store_addrs_safe(&old(self).store)
                ==> branch_stack_store_addrs_safe(&self.store),
            branch_stack_store_addrs_safe(&old(self).active_store)
                ==> branch_stack_store_addrs_safe(&self.active_store),
            old(self).active_branch is Some
                && old(self).active_branch.unwrap().inv(&old(self).active_store)
                ==> self.active_branch.unwrap().inv(&self.active_store),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            old(self)@.metadata_loaded() ==> self@.metadata_loaded(),
            old(self).mini_allocator.bounded(disk_au_count)
                ==> self.mini_allocator.bounded(disk_au_count),
            MiniAllocatorImpl::allocators_unique(old(self).mini_allocator.allocators@)
                ==> MiniAllocatorImpl::allocators_unique(self.mini_allocator.allocators@),
            MiniAllocatorImpl::allocators_au_set(self.mini_allocator.allocators@) =~=
                MiniAllocatorImpl::allocators_au_set(old(self).mini_allocator.allocators@),
            old(self).active_branch_i().ready_for_operation(old(self).mini_allocator.i())
                ==> self.active_branch_i().ready_for_operation(self.mini_allocator.i()),
            match out {
                BranchMaintenanceResult::Grew{new_root_addr, reads, writes} => {
                    &&& self.active_branch is Some
                    &&& branch_stack_store_addrs_safe(&self.active_store)
                    &&& self.active_branch.unwrap().inv(&self.active_store)
                    &&& self.active_branch_i().ready_for_operation(self.mini_allocator.i())
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        Cache::Label::Access{reads: reads@, writes: writes@},
                    )
                    &&& AtomicBranchState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchState::Label::Grow{
                            new_root_addr: new_root_addr@,
                            read_nodes: to_branch_nodes(reads@),
                            write_nodes: to_branch_nodes(writes@),
                        },
                    )
                },
                BranchMaintenanceResult::GrewAfterPrepare{new_root_addr, reads, writes} => {
                    &&& self.active_branch is Some
                    &&& branch_stack_store_addrs_safe(&self.active_store)
                    &&& self.active_branch.unwrap().inv(&self.active_store)
                    &&& self.active_branch_i().ready_for_operation(self.mini_allocator.i())
                    &&& exists |prepared_cache: Cache::State| {
                        &&& Cache::State::next(
                            old(cache)@,
                            prepared_cache,
                            Cache::Label::Internal,
                        )
                        &&& Cache::State::next(
                            prepared_cache,
                            cache@,
                            Cache::Label::Access{reads: reads@, writes: writes@},
                        )
                    }
                    &&& AtomicBranchState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchState::Label::Grow{
                            new_root_addr: new_root_addr@,
                            read_nodes: to_branch_nodes(reads@),
                            write_nodes: to_branch_nodes(writes@),
                        },
                    )
                },
                BranchMaintenanceResult::NeedsAUs => {
                    &&& self@ == old(self)@
                    &&& old(cache)@ == cache@
                },
                BranchMaintenanceResult::CacheFull => {
                    &&& self@ == old(self)@
                    &&& old(cache)@ == cache@
                },
                BranchMaintenanceResult::Noop => {
                    &&& self@ == old(self)@
                    &&& old(cache)@ == cache@
                },
                BranchMaintenanceResult::Blocked => {
                    &&& self@ == old(self)@
                    &&& old(cache)@ == cache@
                },
            },
    {
        let branch = match self.active_branch {
            Some(branch) => branch,
            None => {
                proof {
                    assert(cache@ == old(cache)@);
                    assert(self@ == old(self)@);
                }
                return BranchMaintenanceResult::Noop;
            },
        };
        let root_node = match self.active_store.read_checked(&branch.root) {
            Some(node) => node,
            None => {
                proof {
                    assert(cache@ == old(cache)@);
                    assert(self@ == old(self)@);
                }
                return BranchMaintenanceResult::Blocked;
            },
        };
        match root_node {
            BranchNode::Leaf{ref keys, ref msgs} => {
                if keys.len() == 0 || keys.len() != msgs.len()
                    || !branch_stack_keys_strictly_sorted(keys) {
                    proof {
                        assert(cache@ == old(cache)@);
                        assert(self@ == old(self)@);
                    }
                    return BranchMaintenanceResult::Blocked;
                }
                if keys.len() < BRANCH_GROW_LEAF_THRESHOLD {
                    proof {
                        assert(cache@ == old(cache)@);
                        assert(self@ == old(self)@);
                    }
                    return BranchMaintenanceResult::Noop;
                }
            },
            _ => {
                proof {
                    assert(cache@ == old(cache)@);
                    assert(self@ == old(self)@);
                }
                return BranchMaintenanceResult::Noop;
            },
        }
        if !self.mini_allocator.is_allocation_ready() {
            proof {
                assert(cache@ == old(cache)@);
                assert(self@ == old(self)@);
            }
            return BranchMaintenanceResult::NeedsAUs;
        }

        let ghost pre_stack = *self;
        let ghost cache0 = *cache;
        let new_root = self.mini_allocator.peek_next_addr();
        if new_root.page >= disk_page_count {
            proof {
                assert(cache@ == old(cache)@);
                assert(self@ == old(self)@);
            }
            return BranchMaintenanceResult::NeedsAUs;
        }
        match self.active_store.read_checked(&new_root) {
            Some(_) => {
                proof {
                    assert(cache@ == old(cache)@);
                    assert(self@ == old(self)@);
                }
                return BranchMaintenanceResult::Blocked;
            },
            None => {},
        }

        let ghost root_node_view = root_node@;
        let ghost cache_before_root_fetch = *cache;
        let reads = match cache.fetch(&branch.root, false) {
            FetchErrorCode::Success{slot_handle} => {
                let ghost cache_after_root_fetch = *cache;
                let ghost raw = slot_handle.rec@;
                let ghost fetched_slot = slot_handle.idx;
                let fmt = BranchNodePageFmt::new();
                let all_slice = Slice::all(&slot_handle.rec);
                let parsed = fmt.try_parse(&all_slice, &slot_handle.rec);
                proof {
                    assert(cache_before_root_fetch@ == cache0@);
                    assert(cache_before_root_fetch@.valid_read(branch.root@, raw));
                    if parsed is Some {
                        assert(fmt == BranchNodePageFmt::spec_new());
                        assert(all_slice@.i(slot_handle.rec@) == slot_handle.rec@);
                        assert(fmt.parsable(raw));
                        assert(parsed.unwrap().parsedv() == fmt.parse(raw));
                        assert(raw_page_to_branch_node(raw) == parsed.unwrap()@);
                    }
                }
                cache.handle_release(&branch.root, slot_handle);
                proof {
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        cache0,
                        cache_before_root_fetch,
                        cache_after_root_fetch,
                    );
                    assert(cache_before_root_fetch@.entries =~= cache_after_root_fetch@.entries.insert(
                        fetched_slot,
                        Entry::Filled{addr: branch.root@, data: raw},
                    ));
                    assert(cache@.entries =~= cache_after_root_fetch@.entries.insert(
                        fetched_slot,
                        Entry::Filled{addr: branch.root@, data: raw},
                    ));
                    assert(cache@.entries =~= cache_before_root_fetch@.entries);
                    assert(cache@.lookup_map =~= cache_before_root_fetch@.lookup_map);
                    assert(cache@.status_map =~= cache_before_root_fetch@.status_map);
                    assert(cache@ == cache_before_root_fetch@);
                    assert(cache@ == cache0@);
                }
                let parsed_node = match parsed {
                    Some(node) => node,
                    None => {
                        proof {
                            assert(cache@ == old(cache)@);
                            assert(self@ == old(self)@);
                        }
                        return BranchMaintenanceResult::Blocked;
                    },
                };
                if !same_branch_node_view(&parsed_node, &root_node) {
                    proof {
                        assert(cache@ == old(cache)@);
                        assert(self@ == old(self)@);
                    }
                    return BranchMaintenanceResult::Blocked;
                }
                proof {
                    assert(parsed_node@ == root_node_view);
                    assert(raw_page_to_branch_node(raw) == root_node_view);
                }
                let ghost reads = map![branch.root@ => raw];
                Ghost(reads)
            },
            FetchErrorCode::Awaiting => {
                proof {
                    assert(cache@ == old(cache)@);
                    assert(self@ == old(self)@);
                }
                return BranchMaintenanceResult::Blocked;
            },
            FetchErrorCode::CacheFull
            | FetchErrorCode::LoadInitiate{..} => {
                proof {
                    assert(cache@ == old(cache)@);
                    assert(self@ == old(self)@);
                }
                return BranchMaintenanceResult::CacheFull;
            },
            FetchErrorCode::NotPresent => {
                proof {
                    assert(cache@ == old(cache)@);
                    assert(self@ == old(self)@);
                }
                return BranchMaintenanceResult::Blocked;
            },
        };
        let ghost reads_map = reads@;

        let mut children = Vec::new();
        children.push(branch.root);
        let node = BranchNode::Index{
            pivots: Vec::new(),
            children,
            aux_ptr: None,
        };
        let node_for_page = node.clone_checked();
        proof {
            match node {
                BranchNode::Index{ref pivots, ref children, ref aux_ptr} => {
                    assert(branch.root.wf());
                    assert(pivots@ == Seq::<Key>::empty());
                    assert(children@.len() == 1);
                    assert(children@[0] == branch.root);
                    assert(iaddr_seq(children@) == seq![branch.root@]) by {
                        assert forall |i: int| 0 <= i < iaddr_seq(children@).len()
                            implies #[trigger] iaddr_seq(children@)[i] == seq![branch.root@][i] by {
                            assert(i == 0);
                        }
                    }
                    assert(iopt_addr(*aux_ptr) == Option::<Address>::None);
                    assert(pivots.wf());
                    assert(children.wf());
                    assert(aux_ptr.wf());
                    assert(node@ == SpecBranchNode::Index{
                        pivots: Seq::<Key>::empty(),
                        children: seq![branch.root@],
                        aux_ptr: None,
                    });
                },
                _ => {},
            }
            assert(loaded_grow_write_nodes(branch.root@, new_root@).contains_key(new_root@));
            assert(loaded_grow_write_nodes(branch.root@, new_root@)[new_root@]
                == SpecBranchNode::Index{
                    pivots: Seq::<Key>::empty(),
                    children: seq![branch.root@],
                    aux_ptr: None,
                });
            assert(node@ == loaded_grow_write_nodes(branch.root@, new_root@)[new_root@]);
            assert(node.wf()) by {
                match node {
                    BranchNode::Index{ref pivots, ref children, ref aux_ptr} => {
                        assert(branch.root.wf());
                        assert(pivots.wf());
                        assert(children.wf());
                        assert(aux_ptr.wf());
                        assert(pivots.view().len() == 0);
                        assert(children.view().len() == 1);
                        assert(children.view().len() == pivots.view().len() + 1);
                        assert(children.len() == pivots.len() + 1);
                    },
                    _ => {},
                }
            }
            assert(node_for_page@ == node@);
            assert(node_for_page.wf());
            grow_root_branch_node_marshallable(&node_for_page);
        }
        let page = marshall_branch_node_page(&node_for_page);
        let ghost page_view = page@;
        let ghost writes = map![new_root@ => page_view];
        proof {
            assert(to_branch_nodes(writes) == loaded_grow_write_nodes(branch.root@, new_root@)) by {
                assert forall |addr: Address| #[trigger] to_branch_nodes(writes).contains_key(addr)
                    == loaded_grow_write_nodes(branch.root@, new_root@).contains_key(addr) by {
                }
                assert forall |addr: Address| to_branch_nodes(writes).contains_key(addr)
                    implies #[trigger] to_branch_nodes(writes)[addr]
                        == loaded_grow_write_nodes(branch.root@, new_root@)[addr] by {
                    assert(addr == new_root@);
                    assert(raw_page_to_branch_node(page_view) == node_for_page@);
                    assert(node_for_page@ == loaded_grow_write_nodes(branch.root@, new_root@)[new_root@]);
                }
            }
        }

        let ghost cache_before_write_fetch = *cache;
        match cache.fetch(&new_root, false) {
            FetchErrorCode::Success{slot_handle} => {
                let mut handle = slot_handle;
                let ghost write_slot = handle.idx;
                let ghost fetched_data = handle.rec@;
                let insert_result = self.active_store.insert_fresh(new_root, node);
                proof {
                    assert(!pre_stack.active_store@.entries.contains_key(new_root@));
                    assert(insert_result is Ok);
                    assert(self.active_store@.entries == pre_stack.active_store@.entries.insert(new_root@, node_for_page@));
                }
                match insert_result {
                    Ok(()) => {},
                    Err(_) => {
                        proof {
                            assert(false);
                        }
                        return unreached::<BranchMaintenanceResult>();
                    },
                }
                let allocated_root = match self.mini_allocator.allocate_fresh_addr_checked(
                    disk_au_count,
                    disk_page_count,
                ) {
                    Some(addr) => addr,
                    None => {
                        proof {
                            assert(false);
                        }
                        return unreached::<BranchMaintenanceResult>();
                    },
                };
                proof {
                    assert(allocated_root == new_root);
                    assert(new_root@.wf());
                    pre_stack.mini_allocator.active_allocator_bounded(disk_au_count);
                    assert(0 < pre_stack.mini_allocator.alloc_au_nat());
                    assert(new_root@.au == pre_stack.mini_allocator.alloc_au_nat());
                    assert(new_root@ != spec_superblock_addr());
                }
                self.active_branch = Some(BranchImpl::new(new_root));
                handle.rec = page;
                proof {
                    crate::implementation::FracCacheImpl_v::FracCacheImpl::valid_write_handle_model_entry(
                        cache,
                        &new_root,
                        handle,
                    );
                    assert(cache.entry_fetched(&new_root));
                    assert(cache.valid_handle(handle));
                    assert(cache.lookup_addr_slot(&new_root) == handle.idx);
                    assert(cache.valid_write_handle(&new_root, handle));
                    assert(cache@.valid_write(new_root@));
                }
                let ghost borrowed_cache = *cache;
                cache.write_release(&new_root, handle);

                proof {
                    assert(cache_before_write_fetch@ == cache0@);
                    assert(borrowed_cache@.lookup_map == cache_before_write_fetch@.lookup_map);
                    assert(borrowed_cache@.status_map == cache_before_write_fetch@.status_map);
                    assert(cache_before_write_fetch@.lookup_map.contains_key(new_root@));
                    assert(cache_before_write_fetch@.lookup_map[new_root@] == write_slot);
                    assert(cache_before_write_fetch@.valid_read(new_root@, fetched_data));
                    assert(cache_before_write_fetch@.entries[write_slot]
                        == (Entry::Filled{addr: new_root@, data: fetched_data}));
                    assert(cache_before_write_fetch@.entries
                        == borrowed_cache@.entries.insert(
                            write_slot,
                            cache_before_write_fetch@.entries[write_slot],
                        ));
                    assert(cache_before_write_fetch@.valid_write(new_root@));
                    assert(borrowed_cache@.valid_write(new_root@));
                    assert forall |read_addr: Address| #[trigger] reads_map.contains_key(read_addr)
                        implies cache_before_write_fetch@.valid_read(read_addr, reads_map[read_addr]) by {
                        assert(read_addr == branch.root@);
                        assert(cache0@.valid_read(read_addr, reads_map[read_addr]));
                    }
                    Cache::State::access_from_borrowed_write_slot(
                        cache_before_write_fetch@,
                        borrowed_cache@,
                        cache@,
                        reads_map,
                        new_root@,
                        write_slot,
                        page_view,
                    );
                    assert(to_branch_nodes(reads_map).contains_key(branch.root@));
                    assert(to_branch_nodes(reads_map)[branch.root@] == root_node_view);
                    assert(LoadedPathReceiptLine{
                        addr: branch.root@,
                        node: root_node_view,
                    }.wf()) by {
                        match root_node {
                            BranchNode::Leaf{ref keys, ref msgs} => {
                                assert(keys.len() > 0);
                                assert(keys.len() == msgs.len());
                                assert(Key::is_strictly_sorted(keys@));
                                assert(root_node_view.wf());
                                assert(root_node_view.keys_strictly_sorted());
                            },
                            _ => {},
                        }
                    }
                    assert(loaded_line_wf(to_branch_nodes(reads_map), branch.root@));
                    assert(to_branch_nodes(writes) == loaded_grow_write_nodes(
                        branch.root@,
                        new_root@,
                    ));
                    let addr = Address{
                        au: pre_stack.mini_allocator.alloc_au_nat(),
                        page: pre_stack.mini_allocator.next_page() as nat,
                    };
                    assert(addr == new_root@);
                    assert(self.mini_allocator.i() == pre_stack.mini_allocator.i().allocate(new_root@));
                    let cached_branch_lbl = CachedBranch::Label::Grow{
                        mini_allocator: pre_stack.mini_allocator.i(),
                        new_root_addr: new_root@,
                        read_nodes: to_branch_nodes(reads_map),
                        write_nodes: to_branch_nodes(writes),
                    };
                    assert(pre_stack.active_branch_i().root == Some(branch.root@));
                    assert(pre_stack.active_branch_i().ready_for_mutation(pre_stack.mini_allocator.i()));
                    assert(pre_stack.mini_allocator.i().can_allocate(new_root@));
                    assert(self.active_branch_i().root == Some(new_root@));
                    assert(CachedBranch::State::grow_step(
                        pre_stack.active_branch_i(),
                        self.active_branch_i(),
                        cached_branch_lbl,
                    )) by {
                    }
                    reveal(CachedBranch::State::next);
                    reveal(CachedBranch::State::next_by);
                    assert(CachedBranch::State::next_by(
                        pre_stack.active_branch_i(),
                        self.active_branch_i(),
                        cached_branch_lbl,
                        CachedBranch::Step::grow_step(),
                    ));
                    assert(CachedBranch::State::next(
                        pre_stack.active_branch_i(),
                        self.active_branch_i(),
                        cached_branch_lbl,
                    ));
                    let atomic_lbl = AtomicBranchState::Label::Grow{
                        new_root_addr: new_root@,
                        read_nodes: to_branch_nodes(reads_map),
                        write_nodes: to_branch_nodes(writes),
                    };
                    assert(AtomicBranchState::State::grow(
                        pre_stack@,
                        self@,
                        atomic_lbl,
                        self.active_branch_i(),
                    )) by {
                    }
                    reveal(AtomicBranchState::State::next);
                    reveal(AtomicBranchState::State::next_by);
                    assert(AtomicBranchState::State::next_by(
                        pre_stack@,
                        self@,
                        atomic_lbl,
                        AtomicBranchState::Step::grow(self.active_branch_i()),
                    ));
                    assert(AtomicBranchState::State::next(pre_stack@, self@, atomic_lbl));
                    assert(pre_stack@ == old(self)@);
                    if pre_stack.active_branch is Some
                        && pre_stack.active_branch.unwrap().inv(&pre_stack.active_store) {
                        let pre_linked = pre_stack.active_branch.unwrap().i(&pre_stack.active_store);
                        let post_linked = self.active_branch.unwrap().i(&self.active_store);
                        assert(pre_linked.inv());
                        assert(pre_linked.disk_view.is_fresh(set![new_root@]));
                        LinkedBranchRefinement::grow_refines(pre_linked, new_root@);
                        assert(post_linked == pre_linked.grow(new_root@)) by {
                            assert(post_linked.root == new_root@);
                            assert(pre_linked.root == branch.root@);
                            assert(node_for_page@ == SpecBranchNode::Index{
                                pivots: Seq::<Key>::empty(),
                                children: seq![branch.root@],
                                aux_ptr: None,
                            });
                            assert(post_linked.disk_view.entries
                                == pre_linked.disk_view.entries.insert(new_root@, node_for_page@));
                            assert(pre_linked.grow(new_root@).disk_view.entries
                                == pre_linked.disk_view.entries.insert(new_root@, node_for_page@));
                        }
                        assert(post_linked.inv());
                        assert(post_linked.tight_disk_view());
                        branch_stack_store_addrs_safe_after_insert(
                            &pre_stack.active_store,
                            &self.active_store,
                            new_root@,
                            node_for_page@,
                        );
                        assert(self.active_branch.unwrap().inv(&self.active_store));
                    }
                }

                BranchMaintenanceResult::Grew{
                    new_root_addr: new_root,
                    reads: Ghost(reads_map),
                    writes: Ghost(writes),
                }
            },
            FetchErrorCode::NotPresent => {
                let ghost cache_before_reserve = *cache;
                match cache.reserve_for_write_absent(&new_root) {
                    ReserveWriteResult::Reserved{slot_handle} => {
                        let mut handle = slot_handle;
                        let ghost prepared_cache = *cache;
                        let ghost write_slot = handle.idx;
                        let insert_result = self.active_store.insert_fresh(new_root, node);
                        proof {
                            assert(!pre_stack.active_store@.entries.contains_key(new_root@));
                            assert(insert_result is Ok);
                            assert(self.active_store@.entries == pre_stack.active_store@.entries.insert(new_root@, node_for_page@));
                        }
                        match insert_result {
                            Ok(()) => {},
                            Err(_) => {
                                proof {
                                    assert(false);
                                }
                                return unreached::<BranchMaintenanceResult>();
                            },
                        }
                        let allocated_root = match self.mini_allocator.allocate_fresh_addr_checked(
                            disk_au_count,
                            disk_page_count,
                        ) {
                            Some(addr) => addr,
                            None => {
                                proof {
                                    assert(false);
                                }
                                return unreached::<BranchMaintenanceResult>();
                            },
                        };
                        proof {
                            assert(allocated_root == new_root);
                            assert(new_root@.wf());
                            pre_stack.mini_allocator.active_allocator_bounded(disk_au_count);
                            assert(0 < pre_stack.mini_allocator.alloc_au_nat());
                            assert(new_root@.au == pre_stack.mini_allocator.alloc_au_nat());
                            assert(new_root@ != spec_superblock_addr());
                        }
                        self.active_branch = Some(BranchImpl::new(new_root));
                        handle.rec = page;
                        proof {
                            assert(cache.entry_fetched(&new_root));
                            assert(cache.valid_handle(handle));
                            assert(cache.lookup_addr_slot(&new_root) == handle.idx);
                            assert(cache.valid_write_handle(&new_root, handle));
                            assert(cache@.valid_write(new_root@));
                        }
                        cache.write_release(&new_root, handle);

                        proof {
                            assert(cache_before_reserve@ == cache_before_write_fetch@);
                            assert(cache_before_reserve@ == cache0@);
                            assert(Cache::State::next(
                                cache_before_reserve@,
                                prepared_cache@,
                                Cache::Label::Internal,
                            ));
                            assert(prepared_cache@.valid_write(new_root@));
                            assert(pre_stack.active_store@.entries.contains_key(branch.root@));
                            assert(new_root@ != branch.root@) by {
                                if new_root@ == branch.root@ {
                                    assert(pre_stack.active_store@.entries.contains_key(new_root@));
                                    assert(false);
                                }
                            }
                            assert forall |read_addr: Address| #[trigger] reads_map.contains_key(read_addr)
                                implies prepared_cache@.valid_read(read_addr, reads_map[read_addr]) by {
                                assert(read_addr == branch.root@);
                                assert(cache_before_reserve@.valid_read(read_addr, reads_map[read_addr]));
                            }
                            Cache::State::access_add_reads(
                                prepared_cache@,
                                cache@,
                                reads_map,
                                writes,
                            );
                            assert(exists |mid_cache: Cache::State| {
                                &&& Cache::State::next(
                                    cache0@,
                                    mid_cache,
                                    Cache::Label::Internal,
                                )
                                &&& Cache::State::next(
                                    mid_cache,
                                    cache@,
                                    Cache::Label::Access{reads: reads_map, writes},
                                )
                            }) by {
                                let mid_cache = prepared_cache@;
                                assert(Cache::State::next(
                                    cache0@,
                                    mid_cache,
                                    Cache::Label::Internal,
                                ));
                                assert(Cache::State::next(
                                    mid_cache,
                                    cache@,
                                    Cache::Label::Access{reads: reads_map, writes},
                                ));
                            }
                            assert(to_branch_nodes(reads_map).contains_key(branch.root@));
                            assert(to_branch_nodes(reads_map)[branch.root@] == root_node_view);
                            assert(LoadedPathReceiptLine{
                                addr: branch.root@,
                                node: root_node_view,
                            }.wf()) by {
                                match root_node {
                                    BranchNode::Leaf{ref keys, ref msgs} => {
                                        assert(keys.len() > 0);
                                        assert(keys.len() == msgs.len());
                                        assert(Key::is_strictly_sorted(keys@));
                                        assert(root_node_view.wf());
                                        assert(root_node_view.keys_strictly_sorted());
                                    },
                                    _ => {},
                                }
                            }
                            assert(loaded_line_wf(to_branch_nodes(reads_map), branch.root@));
                            assert(to_branch_nodes(writes) == loaded_grow_write_nodes(
                                branch.root@,
                                new_root@,
                            ));
                            let addr = Address{
                                au: pre_stack.mini_allocator.alloc_au_nat(),
                                page: pre_stack.mini_allocator.next_page() as nat,
                            };
                            assert(addr == new_root@);
                            assert(self.mini_allocator.i() == pre_stack.mini_allocator.i().allocate(new_root@));
                            let cached_branch_lbl = CachedBranch::Label::Grow{
                                mini_allocator: pre_stack.mini_allocator.i(),
                                new_root_addr: new_root@,
                                read_nodes: to_branch_nodes(reads_map),
                                write_nodes: to_branch_nodes(writes),
                            };
                            assert(pre_stack.active_branch_i().root == Some(branch.root@));
                            assert(pre_stack.active_branch_i().ready_for_mutation(pre_stack.mini_allocator.i()));
                            assert(pre_stack.mini_allocator.i().can_allocate(new_root@));
                            assert(self.active_branch_i().root == Some(new_root@));
                            assert(CachedBranch::State::grow_step(
                                pre_stack.active_branch_i(),
                                self.active_branch_i(),
                                cached_branch_lbl,
                            )) by {
                            }
                            reveal(CachedBranch::State::next);
                            reveal(CachedBranch::State::next_by);
                            assert(CachedBranch::State::next_by(
                                pre_stack.active_branch_i(),
                                self.active_branch_i(),
                                cached_branch_lbl,
                                CachedBranch::Step::grow_step(),
                            ));
                            assert(CachedBranch::State::next(
                                pre_stack.active_branch_i(),
                                self.active_branch_i(),
                                cached_branch_lbl,
                            ));
                            let atomic_lbl = AtomicBranchState::Label::Grow{
                                new_root_addr: new_root@,
                                read_nodes: to_branch_nodes(reads_map),
                                write_nodes: to_branch_nodes(writes),
                            };
                            assert(AtomicBranchState::State::grow(
                                pre_stack@,
                                self@,
                                atomic_lbl,
                                self.active_branch_i(),
                            )) by {
                            }
                            reveal(AtomicBranchState::State::next);
                            reveal(AtomicBranchState::State::next_by);
                            assert(AtomicBranchState::State::next_by(
                                pre_stack@,
                                self@,
                                atomic_lbl,
                                AtomicBranchState::Step::grow(self.active_branch_i()),
                            ));
                            assert(AtomicBranchState::State::next(pre_stack@, self@, atomic_lbl));
                            assert(pre_stack@ == old(self)@);
                            if pre_stack.active_branch is Some
                                && pre_stack.active_branch.unwrap().inv(&pre_stack.active_store) {
                                let pre_linked = pre_stack.active_branch.unwrap().i(&pre_stack.active_store);
                                let post_linked = self.active_branch.unwrap().i(&self.active_store);
                                assert(pre_linked.inv());
                                assert(pre_linked.disk_view.is_fresh(set![new_root@]));
                                LinkedBranchRefinement::grow_refines(pre_linked, new_root@);
                                assert(post_linked == pre_linked.grow(new_root@)) by {
                                    assert(post_linked.root == new_root@);
                                    assert(pre_linked.root == branch.root@);
                                    assert(node_for_page@ == SpecBranchNode::Index{
                                        pivots: Seq::<Key>::empty(),
                                        children: seq![branch.root@],
                                        aux_ptr: None,
                                    });
                                    assert(post_linked.disk_view.entries
                                        == pre_linked.disk_view.entries.insert(new_root@, node_for_page@));
                                    assert(pre_linked.grow(new_root@).disk_view.entries
                                        == pre_linked.disk_view.entries.insert(new_root@, node_for_page@));
	                                }
	                                assert(post_linked.inv());
	                                assert(post_linked.tight_disk_view());
                                    branch_stack_store_addrs_safe_after_insert(
                                        &pre_stack.active_store,
                                        &self.active_store,
                                        new_root@,
                                        node_for_page@,
                                    );
	                                assert(self.active_branch.unwrap().inv(&self.active_store));
	                            }
                            FracCacheImpl::valid_load_handles_preserved_transitive(
                                cache0,
                                prepared_cache,
                                *cache,
                            );
                        }

                        BranchMaintenanceResult::GrewAfterPrepare{
                            new_root_addr: new_root,
                            reads: Ghost(reads_map),
                            writes: Ghost(writes),
                        }
                    },
                    ReserveWriteResult::CacheFull => {
                        proof {
                            assert(self@ == old(self)@);
                            assert(cache@ == old(cache)@);
                        }
                        BranchMaintenanceResult::CacheFull
                    },
                }
            },
            FetchErrorCode::Awaiting
            | FetchErrorCode::LoadInitiate{..} => {
                proof {
                    assert(cache@ == old(cache)@);
                    assert(self@ == old(self)@);
                }
                BranchMaintenanceResult::Blocked
            },
            FetchErrorCode::CacheFull => {
                proof {
                    assert(self@ == old(self)@);
                }
                BranchMaintenanceResult::CacheFull
            },
        }
        /*
        // TODO: this was the original absent-slot growth path. It reserves a
        // missing cache entry and then writes the new root, but that is an
        // internal cache update followed by an access write, not a single
        // Cache::Access from the pre-state required by BranchMaintenanceResult::Grew.
        let mut handle = match cache.reserve_for_write_absent(&new_root) {
            ReserveWriteResult::Reserved{slot_handle} => slot_handle,
            ReserveWriteResult::CacheFull => return BranchMaintenanceResult::CacheFull,
        };
        match self.grow() {
            Ok(()) => {},
            Err(_) => return unreached::<BranchMaintenanceResult>(),
        }
        let node = match self.store.read(&new_root) {
            Some(node) => node,
            None => return unreached::<BranchMaintenanceResult>(),
        };
        let page = marshall_branch_node_page(&node);
        let ghost page_view = page@;
        let ghost writes = map![new_root@ => page_view];
        handle.rec = page;
        cache.write_release(&new_root, handle);

        BranchMaintenanceResult::Grew{
            new_root_addr: new_root,
            reads: Ghost(Map::empty()),
            writes: Ghost(writes),
        }
        */
    }

    pub fn append_with_cache(
        &mut self,
        cache: &mut FracCacheImpl,
        keys: &Vec<Key>,
        msgs: &Vec<Message>,
        disk_au_count: IAU,
        disk_page_count: IPage,
    ) -> (out: BranchReplayAppendResult)
        requires
            old(self).wf(),
            old(self).load_state is MetadataLoaded,
            old(cache).wf(),
            0 < (disk_page_count as nat),
            (disk_page_count as nat) == crate::disk::GenericDisk_v::page_count(),
            keys@.len() > 0,
            keys@.len() == msgs@.len(),
            old(self).active_branch is Some ==> {
                &&& old(self).active_branch.unwrap().inv(&old(self).active_store)
                &&& old(self).active_branch_i().ready_for_mutation(old(self).mini_allocator.i())
                &&& branch_stack_store_addrs_safe(&old(self).active_store)
            },
            branch_stack_store_addrs_safe(&old(self).active_store),
            old(self).active_branch is None && old(self).mini_allocator.allocation_ready() ==> {
                &&& MiniAllocatorImpl::allocators_unique(old(self).mini_allocator.allocators@)
                &&& old(self).mini_allocator.bounded(disk_au_count)
                &&& old(self).mini_allocator.i().allocated_aus() == Set::<AU>::empty()
            },
        ensures
            self.wf(),
            self.load_state == old(self).load_state,
            self.image == old(self).image,
            old(self).image.roots_wf() ==> self.image.roots_wf(),
            old(self)@.metadata_loaded() ==> self@.metadata_loaded(),
            self.store@ =~= old(self).store@,
            branch_stack_store_addrs_safe(&old(self).store)
                ==> branch_stack_store_addrs_safe(&self.store),
            branch_stack_store_addrs_safe(&old(self).active_store)
                ==> branch_stack_store_addrs_safe(&self.active_store),
            old(self).active_branch is Some
                && old(self).active_branch.unwrap().inv(&old(self).active_store)
                ==> self.active_branch.unwrap().inv(&self.active_store),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            old(self).mini_allocator.bounded(disk_au_count)
                ==> self.mini_allocator.bounded(disk_au_count),
            MiniAllocatorImpl::allocators_unique(old(self).mini_allocator.allocators@)
                ==> MiniAllocatorImpl::allocators_unique(self.mini_allocator.allocators@),
            MiniAllocatorImpl::allocators_au_set(self.mini_allocator.allocators@) =~=
                MiniAllocatorImpl::allocators_au_set(old(self).mini_allocator.allocators@),
            old(self).mini_allocator.i().allocated_aus() == Set::<AU>::empty()
                && self.active_branch is None
                ==> self.mini_allocator.i().allocated_aus() == Set::<AU>::empty(),
            match out {
                BranchReplayAppendResult::Appended{prepared_cache, branch_reads, writes, receipt, init_root} => {
                    &&& self.active_branch is Some
                    &&& branch_stack_store_addrs_safe(&self.active_store)
                    &&& self.active_branch.unwrap().inv(&self.active_store)
                    &&& self.active_branch_i().ready_for_operation(self.mini_allocator.i())
                    &&& if old(self).active_branch is Some {
                        branch_reads@.dom() == receipt@.needed_addrs()
                    } else {
                        branch_reads@.dom() == Set::<Address>::empty()
                    }
                    &&& Cache::State::next(
                        old(cache)@,
                        prepared_cache@,
                        Cache::Label::Internal,
                    )
                    &&& Cache::State::next(
                        prepared_cache@,
                        cache@,
                        Cache::Label::Access{reads: branch_reads@, writes: writes@},
                    )
                    &&& forall |read_addr: Address, data: RawPage|
                        #[trigger] old(cache)@.valid_read(read_addr, data)
                        ==> prepared_cache@.valid_read(read_addr, data)
	                    &&& AtomicBranchState::State::next(
	                        old(self)@,
	                        self@,
	                        AtomicBranchState::Label::Append{
	                            keys: keys@,
	                            msgs: msgs@,
	                            receipt: receipt@,
	                            init_root: init_root@,
	                            read_nodes: to_branch_nodes(branch_reads@),
	                            write_nodes: to_branch_nodes(writes@),
	                        },
	                    )
	                },
                BranchReplayAppendResult::NeedCacheLoad{addr, handle} => {
                    &&& self@ == old(self)@
                    &&& self.active_branch == old(self).active_branch
                    &&& self.mini_allocator.i() == old(self).mini_allocator.i()
                    &&& self.mini_allocator.allocators@ == old(self).mini_allocator.allocators@
                    &&& self.mini_allocator.curr == old(self).mini_allocator.curr
                    &&& self.mini_allocator.free_au_threshold == old(self).mini_allocator.free_au_threshold
                    &&& addr@.wf()
                    &&& addr@ != spec_superblock_addr()
                    &&& cache.entry_fetched(&addr)
                    &&& cache.valid_load_handle(&addr, handle)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        crate::implementation::FracCacheImpl_v::cache_load_label(&addr),
                    )
                },
                BranchReplayAppendResult::NeedsAUs => {
                    &&& self@ == old(self)@
                    &&& self.active_branch == old(self).active_branch
                    &&& self.mini_allocator.i() == old(self).mini_allocator.i()
                    &&& self.mini_allocator.allocators@ == old(self).mini_allocator.allocators@
                    &&& self.mini_allocator.curr == old(self).mini_allocator.curr
                    &&& self.mini_allocator.free_au_threshold == old(self).mini_allocator.free_au_threshold
                    &&& old(cache)@ == cache@
                },
                BranchReplayAppendResult::CacheFull => {
                    &&& self@ == old(self)@
                    &&& self.active_branch == old(self).active_branch
                    &&& self.mini_allocator.i() == old(self).mini_allocator.i()
                    &&& self.mini_allocator.allocators@ == old(self).mini_allocator.allocators@
                    &&& self.mini_allocator.curr == old(self).mini_allocator.curr
                    &&& self.mini_allocator.free_au_threshold == old(self).mini_allocator.free_au_threshold
                    &&& old(cache)@ == cache@
                },
                BranchReplayAppendResult::Blocked => {
                    &&& self@ == old(self)@
                    &&& self.active_branch == old(self).active_branch
                    &&& self.mini_allocator.i() == old(self).mini_allocator.i()
                    &&& self.mini_allocator.allocators@ == old(self).mini_allocator.allocators@
                    &&& self.mini_allocator.curr == old(self).mini_allocator.curr
                    &&& self.mini_allocator.free_au_threshold == old(self).mini_allocator.free_au_threshold
                    &&& old(cache)@ == cache@
                },
            },
    {
        if !branch_stack_keys_strictly_sorted(keys) {
            proof {
                assert(cache@ == old(cache)@);
            }
            return BranchReplayAppendResult::Blocked;
        }
        if keys.len() > usize::MAX - self.seq_end {
            proof {
                assert(cache@ == old(cache)@);
            }
            return BranchReplayAppendResult::Blocked;
        }
        if keys.len() > BRANCH_GROW_LEAF_THRESHOLD {
            proof {
                assert(cache@ == old(cache)@);
            }
            return BranchReplayAppendResult::Blocked;
        }
        if self.active_branch.is_some() {
            let last_key = keys[keys.len() - 1];
            let ghost pre_stack = *self;
            let ghost cache0 = *cache;
            let (leaf, branch_reads, receipt) = match self.load_path_for_key(
                cache,
                keys[0],
                Some(last_key),
            ) {
                BranchPathLoadResult::Loaded{leaf, reads, receipt} => {
                    (leaf, reads, receipt)
                },
                BranchPathLoadResult::NeedCacheLoad{addr, handle} => {
                    return BranchReplayAppendResult::NeedCacheLoad{addr, handle};
                },
                BranchPathLoadResult::CacheFull => {
                    return BranchReplayAppendResult::CacheFull;
                },
                BranchPathLoadResult::Blocked => {
                    return BranchReplayAppendResult::Blocked;
                },
            };

            let (mut new_keys, mut new_msgs) = match self.active_store.read_checked(&leaf) {
                Some(BranchNode::Leaf{keys: existing_keys, msgs: existing_msgs}) => {
                    if existing_keys.len() == 0 || existing_keys.len() != existing_msgs.len() {
                        proof {
                            assert(cache@ == cache0@);
                        }
                        return BranchReplayAppendResult::Blocked;
                    }
                    if !branch_stack_key_lt(existing_keys[existing_keys.len() - 1], keys[0]) {
                        proof {
                            assert(cache@ == cache0@);
                        }
                        return BranchReplayAppendResult::Blocked;
                    }
                    if existing_keys.len() > BRANCH_GROW_LEAF_THRESHOLD - keys.len() {
                        proof {
                            assert(cache@ == cache0@);
                        }
                        return BranchReplayAppendResult::Blocked;
                    }
                    proof {
                        assert(self.active_store@.entries[leaf@] == receipt@.target().node);
                        assert(receipt@.target().node
                            == (SpecBranchNode::Leaf{keys: existing_keys@, msgs: existing_msgs@}));
                        assert(loaded_append_ready(receipt@, to_branch_nodes(branch_reads@), keys@, msgs@));
                    }
                    (existing_keys.clone(), existing_msgs.clone())
                },
                _ => {
                    proof {
                        assert(cache@ == cache0@);
                        assert(false);
                    }
                    return BranchReplayAppendResult::Blocked;
                },
            };

            let append_fmt = BranchNodePageFmt::new();
            if keys.len() > append_fmt.leaf_fmt.max_length {
                proof {
                    assert(cache@ == cache0@);
                }
                return BranchReplayAppendResult::Blocked;
            }
            if new_keys.len() > append_fmt.leaf_fmt.max_length - keys.len() {
                proof {
                    assert(cache@ == cache0@);
                }
                return BranchReplayAppendResult::Blocked;
            }

            let ghost cache_before_fetch = *cache;
            match cache.fetch(&leaf, false) {
                FetchErrorCode::Success{slot_handle} => {
                    let mut handle = slot_handle;
                    let ghost write_slot = handle.idx;
                    let ghost fetched_data = handle.rec@;
                    let ghost old_leaf = receipt@.target().node;
                    let ghost old_leaf_keys = old_leaf->keys;
                    let ghost old_leaf_msgs = old_leaf->msgs;
                    let mut append_idx = 0usize;
                    while append_idx < keys.len()
                        invariant
                            append_idx <= keys.len(),
                            new_keys@ == old_leaf_keys + keys@.subrange(0, append_idx as int),
                            new_msgs@ == old_leaf_msgs + msgs@.subrange(0, append_idx as int),
                            keys@.len() == msgs@.len(),
                        decreases keys.len() - append_idx,
                    {
                        new_keys.push(keys[append_idx]);
                        new_msgs.push(msgs[append_idx]);
                        append_idx += 1;
                    }
                    let node = BranchNode::Leaf{keys: new_keys, msgs: new_msgs};
                    let node_for_page = node.clone_checked();
                    proof {
                        assert(append_idx == keys.len());
                        assert(keys@.subrange(0, keys@.len() as int) == keys@);
                        assert(msgs@.subrange(0, msgs@.len() as int) == msgs@);
                        assert(node@ == (SpecBranchNode::Leaf{
                            keys: old_leaf_keys + keys@,
                            msgs: old_leaf_msgs + msgs@,
                        }));
                        assert(node@ == loaded_append_write_nodes(
                            receipt@,
                            keys@,
                            msgs@,
                        )[leaf@]);
                        assert(node.wf());
                        assert(new_keys@.len() <= BRANCH_GROW_LEAF_THRESHOLD);
                        assert(new_keys@.len() <= append_fmt.leaf_fmt.max_length);
                        assert(append_fmt == BranchNodePageFmt::spec_new());
                        small_leaf_branch_node_marshallable(&node_for_page);
                    }
                    let overwrite_result = self.active_store.overwrite(leaf, node);
                    proof {
                        assert(overwrite_result is Ok);
                    }
                    match overwrite_result {
                        Ok(()) => {},
                        Err(_) => {
                            proof {
                                assert(false);
                            }
                            return unreached::<BranchReplayAppendResult>();
                        },
                    }
                    self.seq_end = self.seq_end + keys.len();
                    let page = marshall_branch_node_page(&node_for_page);
                    let ghost page_view = page@;
                    let ghost writes = map![leaf@ => page_view];
                    proof {
                        assert(node_for_page@ == loaded_append_write_nodes(
                            receipt@,
                            keys@,
                            msgs@,
                        )[leaf@]);
                    }
                    handle.rec = page;
                    proof {
                        crate::implementation::FracCacheImpl_v::FracCacheImpl::valid_write_handle_model_entry(
                            cache,
                            &leaf,
                            handle,
                        );
                        assert(cache.entry_fetched(&leaf));
                        assert(cache.valid_handle(handle));
                        assert(cache.slot_entry(handle.idx) == (crate::implementation::FracCacheImpl_v::IEntry::Filled{addr: leaf}));
                        assert(cache.lookup_addr_slot(&leaf) == handle.idx);
                        assert(cache.valid_write_handle(&leaf, handle));
                        assert(cache@.valid_write(leaf@));
                    }
                    let ghost borrowed_cache = *cache;
                    cache.write_release(&leaf, handle);

                    proof {
                        assert(cache_before_fetch@ == cache0@);
                        assert(borrowed_cache@.lookup_map == cache_before_fetch@.lookup_map);
                        assert(borrowed_cache@.status_map == cache_before_fetch@.status_map);
                        assert(cache_before_fetch@.lookup_map.contains_key(leaf@));
                        assert(cache_before_fetch@.lookup_map[leaf@] == write_slot);
                        assert(cache_before_fetch@.valid_read(leaf@, fetched_data));
                        assert(cache_before_fetch@.entries[write_slot]
                            == (Entry::Filled{addr: leaf@, data: fetched_data}));
                        assert(cache_before_fetch@.entries
                            == borrowed_cache@.entries.insert(
                                write_slot,
                                cache_before_fetch@.entries[write_slot],
                            ));
                        assert(cache_before_fetch@.valid_write(leaf@));
                        assert(borrowed_cache@.valid_write(leaf@));
                        assert forall |read_addr: Address| #[trigger] branch_reads@.contains_key(read_addr)
                            implies cache_before_fetch@.valid_read(read_addr, branch_reads@[read_addr]) by {
                            Cache::State::access_read_valid(
                                cache0@,
                                cache_before_fetch@,
                                branch_reads@,
                                Map::empty(),
                                read_addr,
                            );
                        }
                        Cache::State::access_from_borrowed_write_slot(
                            cache_before_fetch@,
                            borrowed_cache@,
                            cache@,
                            branch_reads@,
                            leaf@,
                            write_slot,
                            page_view,
                        );
                        assert(to_branch_nodes(writes) == loaded_append_write_nodes(
                            receipt@,
                            keys@,
                            msgs@,
                        ));
                        let cached_branch_lbl = CachedBranch::Label::Append{
                            mini_allocator: pre_stack.mini_allocator.i(),
                            receipt: receipt@,
                            keys: keys@,
                            msgs: msgs@,
                            read_nodes: to_branch_nodes(branch_reads@),
                            write_nodes: to_branch_nodes(writes),
                        };
                        assert(self.active_branch_i() == pre_stack.active_branch_i());
                        assert(CachedBranch::State::append_step(
                            pre_stack.active_branch_i(),
                            self.active_branch_i(),
                            cached_branch_lbl,
                        )) by {
                        }
                        reveal(CachedBranch::State::next);
                        reveal(CachedBranch::State::next_by);
                        assert(CachedBranch::State::next_by(
                            pre_stack.active_branch_i(),
                            self.active_branch_i(),
                            cached_branch_lbl,
                            CachedBranch::Step::append_step(),
                        ));
                        assert(CachedBranch::State::next(
                            pre_stack.active_branch_i(),
                            self.active_branch_i(),
                            cached_branch_lbl,
                        ));
                        let atomic_lbl = AtomicBranchState::Label::Append{
                            keys: keys@,
                            msgs: msgs@,
                            receipt: receipt@,
                            init_root: None,
                            read_nodes: to_branch_nodes(branch_reads@),
                            write_nodes: to_branch_nodes(writes),
                        };
                        assert(AtomicBranchState::State::append_nonempty(
                            pre_stack@,
                            self@,
                            atomic_lbl,
                            self.active_branch_i(),
                        )) by {
                        }
                        reveal(AtomicBranchState::State::next);
                        reveal(AtomicBranchState::State::next_by);
	                        assert(AtomicBranchState::State::next_by(
	                            pre_stack@,
	                            self@,
	                            atomic_lbl,
	                            AtomicBranchState::Step::append_nonempty(self.active_branch_i()),
	                        ));
	                        assert(AtomicBranchState::State::next(pre_stack@, self@, atomic_lbl));
	                        AtomicBranchState::State::append_effect(pre_stack@, self@, atomic_lbl);
                        assert(Cache::State::next_by(
                            cache0@,
                            cache0@,
                            Cache::Label::Internal,
                            Cache::Step::noop(),
                        )) by {
                            reveal(Cache::State::next_by);
                        }
	                        assert(Cache::State::next(cache0@, cache0@, Cache::Label::Internal)) by {
	                            reveal(Cache::State::next);
	                        }
	                        assert(pre_stack@ == old(self)@);
                            if pre_stack.active_branch is Some
                                && pre_stack.active_branch.unwrap().inv(&pre_stack.active_store) {
                                let pre_linked = pre_stack.active_branch.unwrap().i(&pre_stack.active_store);
                                let post_linked = self.active_branch.unwrap().i(&self.active_store);
                                let path = SpecPath{
                                    branch: pre_linked,
                                    key: keys@[0],
                                    depth: receipt@.depth(),
                                };
                                assert(pre_linked.inv());
                                assert(receipt@.valid_for(pre_linked.root, pre_linked.disk_view.entries)) by {
                                    assert(receipt@.valid_for(receipt@.root, to_branch_nodes(branch_reads@)));
                                    assert(receipt@.root == pre_linked.root);
                                    assert(receipt@.needed_addrs() <= pre_linked.disk_view.entries.dom()) by {
                                        assert forall |addr: Address| #[trigger] receipt@.needed_addrs().contains(addr)
                                            implies pre_linked.disk_view.entries.dom().contains(addr) by {
                                            let idx = choose |i: int| 0 <= i < receipt@.lines.len()
                                                && #[trigger] receipt@.lines[i].addr == addr;
                                            assert(0 <= idx < receipt@.lines.len());
                                            assert(pre_stack.active_store@.entries.contains_key(addr));
                                        }
                                    }
                                    assert forall |i: int| 0 <= i < receipt@.lines.len()
                                        implies {
                                            &&& pre_linked.disk_view.entries.contains_key(receipt@.lines[i].addr)
                                            &&& #[trigger] pre_linked.disk_view.entries[receipt@.lines[i].addr]
                                                == receipt@.lines[i].node
                                        } by {
                                        assert(pre_stack.active_store@.entries.contains_key(receipt@.lines[i].addr));
                                        assert(pre_stack.active_store@.entries[receipt@.lines[i].addr]
                                            == receipt@.lines[i].node);
                                    }
                                }
                                assert(receipt@.target().wf());
                                assert(receipt@.target().node.keys_strictly_sorted());
                                assert(receipt@.target().node is Leaf);
                                assert(Key::is_strictly_sorted(receipt@.target().node->keys));
                                branch_stack_leaf_append_route_equiv(receipt@.target().node, keys@);
                                receipt_path_valid_for_branch_disk(
                                    pre_linked,
                                    pre_linked.the_ranking(),
                                    receipt@,
                                    keys@.last(),
                                );
                                assert(path.valid());
                                assert(path.branch == pre_linked);
                                assert(path.target().root() == receipt@.target().node);
                                assert(path.target().root() is Leaf);
                                assert(path.target().root()->keys.len() > 0);
                                assert(Key::lt(path.target().root()->keys.last(), keys@[0]));
                                assert(path.key == keys@[0]);
                                assert(path.path_equiv(keys@.last()));
                                LinkedBranchRefinement::append_refines(pre_linked, keys@, msgs@, path);
                                assert(post_linked == pre_linked.append(keys@, msgs@, path)) by {
                                    assert(post_linked.root == pre_linked.root);
                                    assert(path.target().root == leaf@);
                                    assert(node_for_page@ == loaded_append_write_nodes(
                                        receipt@,
                                        keys@,
                                        msgs@,
                                    )[leaf@]);
                                    assert(pre_linked.append(keys@, msgs@, path).disk_view.entries
                                        == pre_linked.disk_view.entries.insert(leaf@, node_for_page@));
                                    assert(post_linked.disk_view.entries
                                        == pre_linked.disk_view.entries.insert(leaf@, node_for_page@));
                                }
                                assert(post_linked.inv());
                                assert(post_linked.tight_disk_view());
                                assert(self.active_branch.unwrap().inv(&self.active_store));
                            }
	                    }
	                    return BranchReplayAppendResult::Appended{
	                        prepared_cache: Ghost(cache0@),
	                        branch_reads,
	                        writes: Ghost(writes),
	                        receipt,
                        init_root: Ghost(None),
                    };
                },
                FetchErrorCode::Awaiting
                | FetchErrorCode::NotPresent
                | FetchErrorCode::LoadInitiate{..} => {
                    proof {
                        assert(cache@ == old(cache)@);
                    }
                    return BranchReplayAppendResult::Blocked;
                },
                FetchErrorCode::CacheFull => {
                    return BranchReplayAppendResult::CacheFull;
                },
            }
        }

		        if self.active_branch.is_some() {
		            return BranchReplayAppendResult::Blocked;
		        }

		        if !self.mini_allocator.is_allocation_ready() {
	            proof {
	                assert(cache@ == old(cache)@);
	                assert(self@ == old(self)@);
	            }
		            return BranchReplayAppendResult::NeedsAUs;
		        }

                let fresh_active_store = MemBranchStore::new();
                self.active_store = fresh_active_store;
                proof {
                    empty_branch_stack_store_addrs_safe(&self.active_store);
                }
				        let ghost pre_stack = *self;
			        let ghost cache0 = *cache;
			        let root = self.mini_allocator.peek_next_addr();
		        if root.page >= disk_page_count {
		            proof {
		                assert(cache@ == old(cache)@);
		                assert(self@ == old(self)@);
		            }
		            return BranchReplayAppendResult::NeedsAUs;
		        }
		        match self.active_store.read_checked(&root) {
	            Some(_) => {
	                proof {
	                    assert(cache@ == old(cache)@);
	                    assert(self@ == old(self)@);
	                }
	                return BranchReplayAppendResult::Blocked;
	            },
	            None => {},
	        }

		        let init_fmt = BranchNodePageFmt::new();
		        if keys.len() > init_fmt.leaf_fmt.max_length {
		            proof {
		                assert(cache@ == old(cache)@);
		                assert(self@ == old(self)@);
		            }
		            return BranchReplayAppendResult::Blocked;
		        }

		        let node = BranchNode::Leaf{keys: keys.clone(), msgs: msgs.clone()};
		        let node_for_page = node.clone_checked();
		        proof {
		            assert(node@ == SpecBranchNode::Leaf{keys: keys@, msgs: msgs@});
		            assert(node.wf());
		            assert(node_for_page@ == node@);
		            assert(node_for_page.wf());
		            assert(keys@.len() <= BRANCH_GROW_LEAF_THRESHOLD);
		            assert(init_fmt == BranchNodePageFmt::spec_new());
		            assert(keys@.len() <= init_fmt.leaf_fmt.max_length);
		            small_leaf_branch_node_marshallable(&node_for_page);
		        }
	        let page = marshall_branch_node_page(&node_for_page);
	        let ghost page_view = page@;
	        let ghost writes = map![root@ => page_view];
	        let ghost init_receipt = LoadedPathReceipt{
	            key: keys@[0],
	            root: root@,
	            lines: Seq::empty(),
	        };
	        proof {
	            assert(raw_page_to_branch_node(page_view) == node_for_page@);
	            assert(to_branch_nodes(writes) == loaded_initialize_write_nodes(
	                root@,
	                keys@,
	                msgs@,
	            )) by {
	                assert forall |addr: Address| #[trigger] to_branch_nodes(writes).contains_key(addr)
	                    == loaded_initialize_write_nodes(root@, keys@, msgs@).contains_key(addr) by {
	                }
	                assert forall |addr: Address| to_branch_nodes(writes).contains_key(addr)
	                    implies #[trigger] to_branch_nodes(writes)[addr]
	                        == loaded_initialize_write_nodes(root@, keys@, msgs@)[addr] by {
	                    assert(addr == root@);
	                    assert(raw_page_to_branch_node(page_view) == node_for_page@);
	                    assert(node_for_page@ == SpecBranchNode::Leaf{keys: keys@, msgs: msgs@});
	                }
	            }
	        }

	        match cache.fetch(&root, false) {
	            FetchErrorCode::Success{slot_handle} => {
	                let mut handle = slot_handle;
	                let ghost write_slot = handle.idx;
	                let ghost fetched_data = handle.rec@;
	                let insert_result = self.active_store.insert_fresh(root, node);
	                proof {
	                    assert(!pre_stack.active_store@.entries.contains_key(root@));
	                    assert(insert_result is Ok);
	                    assert(self.active_store@.entries == pre_stack.active_store@.entries.insert(root@, node_for_page@));
	                }
	                match insert_result {
	                    Ok(()) => {},
	                    Err(_) => {
	                        proof {
	                            assert(false);
	                        }
	                        return unreached::<BranchReplayAppendResult>();
	                    },
	                }
			                let allocated_root = self.mini_allocator.allocate_fresh_addr_checked(
			                    disk_au_count,
			                    disk_page_count,
			                );
			                proof {
			                    assert(allocated_root is Some);
			                    assert(allocated_root.unwrap() == root);
                                assert(root@.wf());
                                pre_stack.mini_allocator.active_allocator_bounded(disk_au_count);
                                assert(0 < pre_stack.mini_allocator.alloc_au_nat());
                                assert(root@.au == pre_stack.mini_allocator.alloc_au_nat());
                                assert(root@ != spec_superblock_addr());
			                }
			                self.active_branch = Some(BranchImpl::new(root));
	                self.seq_end = self.seq_end + keys.len();
	                handle.rec = page;
	                proof {
	                    FracCacheImpl::valid_write_handle_model_entry(cache, &root, handle);
	                    assert(cache.entry_fetched(&root));
	                    assert(cache.valid_handle(handle));
	                    assert(cache.lookup_addr_slot(&root) == handle.idx);
	                    assert(cache.valid_write_handle(&root, handle));
	                    assert(cache@.valid_write(root@));
	                }
	                let ghost borrowed_cache = *cache;
	                cache.write_release(&root, handle);

	                proof {
	                    assert(borrowed_cache@.lookup_map == cache0@.lookup_map);
	                    assert(borrowed_cache@.status_map == cache0@.status_map);
	                    assert(cache0@.lookup_map.contains_key(root@));
	                    assert(cache0@.lookup_map[root@] == write_slot);
	                    assert(cache0@.valid_read(root@, fetched_data));
	                    assert(cache0@.entries[write_slot]
	                        == (Entry::Filled{addr: root@, data: fetched_data}));
	                    assert(cache0@.entries
	                        == borrowed_cache@.entries.insert(
	                            write_slot,
	                            cache0@.entries[write_slot],
	                        ));
	                    assert(cache0@.valid_write(root@));
	                    assert(borrowed_cache@.valid_write(root@));
		                    assert(Cache::State::next_by(
		                        cache0@,
		                        cache0@,
		                        Cache::Label::Internal,
		                        Cache::Step::noop(),
		                    )) by {
		                        reveal(Cache::State::next_by);
		                    }
		                    assert(Cache::State::next(cache0@, cache0@, Cache::Label::Internal)) by {
		                        reveal(Cache::State::next);
		                    }
	                    let ghost empty_reads = Map::<Address, RawPage>::empty();
	                    Cache::State::access_from_borrowed_write_slot(
	                        cache0@,
	                        borrowed_cache@,
	                        cache@,
	                        empty_reads,
	                        root@,
	                        write_slot,
	                        page_view,
	                    );
	                    assert(to_branch_nodes(writes) == loaded_initialize_write_nodes(
	                        root@,
	                        keys@,
	                        msgs@,
	                    ));
	                    let addr = Address{
	                        au: pre_stack.mini_allocator.alloc_au_nat(),
	                        page: pre_stack.mini_allocator.next_page() as nat,
	                    };
	                    assert(addr == root@);
	                    let cached_branch_lbl = CachedBranch::Label::Initialize{
	                        mini_allocator: pre_stack.mini_allocator.i(),
	                        init_root: root@,
	                        keys: keys@,
	                        msgs: msgs@,
	                        write_nodes: to_branch_nodes(writes),
	                    };
	                    assert(pre_stack.active_branch_i().is_empty_active());
	                    assert(pre_stack.mini_allocator.i().can_allocate(root@));
	                    assert(self.active_branch_i().root == Some(root@));
	                    assert(CachedBranch::State::initialize_branch(
	                        pre_stack.active_branch_i(),
	                        self.active_branch_i(),
	                        cached_branch_lbl,
	                    )) by {
	                    }
	                    reveal(CachedBranch::State::next);
	                    reveal(CachedBranch::State::next_by);
	                    assert(CachedBranch::State::next_by(
	                        pre_stack.active_branch_i(),
	                        self.active_branch_i(),
	                        cached_branch_lbl,
	                        CachedBranch::Step::initialize_branch(),
	                    ));
	                    assert(CachedBranch::State::next(
	                        pre_stack.active_branch_i(),
	                        self.active_branch_i(),
	                        cached_branch_lbl,
	                    ));
	                    let atomic_lbl = AtomicBranchState::Label::Append{
	                        keys: keys@,
	                        msgs: msgs@,
	                        receipt: init_receipt,
	                        init_root: Some(root@),
	                        read_nodes: to_branch_nodes(empty_reads),
	                        write_nodes: to_branch_nodes(writes),
	                    };
	                    assert(AtomicBranchState::State::append_empty(
	                        pre_stack@,
	                        self@,
	                        atomic_lbl,
	                        self.active_branch_i(),
	                    )) by {
	                    }
	                    reveal(AtomicBranchState::State::next);
	                    reveal(AtomicBranchState::State::next_by);
	                    assert(AtomicBranchState::State::next_by(
	                        pre_stack@,
	                        self@,
	                        atomic_lbl,
	                        AtomicBranchState::Step::append_empty(self.active_branch_i()),
		                    ));
		                    assert(AtomicBranchState::State::next(pre_stack@, self@, atomic_lbl));
		                    AtomicBranchState::State::append_effect(pre_stack@, self@, atomic_lbl);
		                    assert(pre_stack@ == old(self)@);
	                            branch_stack_store_addrs_safe_after_insert(
	                                &pre_stack.active_store,
	                                &self.active_store,
	                                root@,
	                                node_for_page@,
	                            );
                            let post_linked = self.active_branch.unwrap().i(&self.active_store);
                            let ranking = map![root@ => 1nat];
                            assert(post_linked.valid_ranking(ranking)) by {
                                assert(post_linked.disk_view.valid_ranking(ranking)) by {
                                    assert forall |addr: Address|
                                        #[trigger] ranking.contains_key(addr)
                                            && post_linked.disk_view.entries.contains_key(addr)
                                        implies post_linked.disk_view.node_children_respects_rank(ranking, addr) by {
                                        assert(addr == root@);
                                        assert(post_linked.disk_view.entries[addr] == node_for_page@);
                                        assert(node_for_page@ is Leaf);
                                        assert forall |child_idx: int|
                                            #[trigger] post_linked.disk_view.entries[addr].valid_child_index(child_idx)
                                            implies {
                                                &&& ranking.contains_key(
                                                    post_linked.disk_view.entries[addr]->children[child_idx])
                                                &&& ranking[
                                                    post_linked.disk_view.entries[addr]->children[child_idx]]
                                                    < ranking[addr]
                                            } by {
                                            assert(false);
                                        }
                                    }
                                }
                                assert(ranking.contains_key(root@));
                            }
                            assert(post_linked.acyclic()) by {
                                assert(exists |ranking: Ranking| post_linked.valid_ranking(ranking));
                            }
                            assert(post_linked.inv());
	                            assert(self.active_branch.unwrap().inv(&self.active_store));
			                }
		                return BranchReplayAppendResult::Appended{
	                    prepared_cache: Ghost(cache0@),
	                    branch_reads: Ghost(Map::empty()),
	                    writes: Ghost(writes),
	                    receipt: Ghost(init_receipt),
	                    init_root: Ghost(Some(root@)),
	                };
	            },
	            FetchErrorCode::NotPresent => {
	                let ghost cache_before_reserve = *cache;
	                match cache.reserve_for_write_absent(&root) {
	                    ReserveWriteResult::Reserved{slot_handle} => {
	                        let mut handle = slot_handle;
	                        let ghost prepared_cache = *cache;
	                        let ghost write_slot = handle.idx;
	                        let insert_result = self.active_store.insert_fresh(root, node);
	                        proof {
	                            assert(cache_before_reserve@ == cache0@);
	                            assert(!pre_stack.active_store@.entries.contains_key(root@));
	                            assert(insert_result is Ok);
	                            assert(self.active_store@.entries == pre_stack.active_store@.entries.insert(root@, node_for_page@));
	                        }
	                        match insert_result {
	                            Ok(()) => {},
	                            Err(_) => {
	                                proof {
	                                    assert(false);
	                                }
	                                return unreached::<BranchReplayAppendResult>();
	                            },
	                        }
			                        let allocated_root = self.mini_allocator.allocate_fresh_addr_checked(
			                            disk_au_count,
			                            disk_page_count,
			                        );
			                        proof {
			                            assert(allocated_root is Some);
			                            assert(allocated_root.unwrap() == root);
                                        assert(root@.wf());
                                        pre_stack.mini_allocator.active_allocator_bounded(disk_au_count);
                                        assert(0 < pre_stack.mini_allocator.alloc_au_nat());
                                        assert(root@.au == pre_stack.mini_allocator.alloc_au_nat());
                                        assert(root@ != spec_superblock_addr());
			                        }
			                        self.active_branch = Some(BranchImpl::new(root));
	                        self.seq_end = self.seq_end + keys.len();
	                        handle.rec = page;
	                        proof {
	                            assert(cache.entry_fetched(&root));
	                            assert(cache.valid_handle(handle));
	                            assert(cache.lookup_addr_slot(&root) == handle.idx);
	                            assert(cache.valid_write_handle(&root, handle));
	                            assert(cache@.valid_write(root@));
	                        }
	                        cache.write_release(&root, handle);

		                        proof {
		                            assert(Cache::State::next(
		                                cache0@,
		                                prepared_cache@,
		                                Cache::Label::Internal,
		                            ));
		                            assert(prepared_cache@.valid_write(root@));
		                            crate::implementation::FracCacheImpl_v::FracCacheImpl::entry_fetched_from_view(
		                                &cache_before_reserve,
		                                &root,
		                            );
		                            assert(!cache_before_reserve@.lookup_map.contains_key(root@));
		                            assert forall |read_addr: Address, data: RawPage|
		                                #[trigger] cache0@.valid_read(read_addr, data)
		                                implies prepared_cache@.valid_read(read_addr, data) by {
		                                assert(cache_before_reserve@ == cache0@);
		                                if read_addr == root@ {
		                                    assert(cache0@.lookup_map.contains_key(read_addr));
		                                    assert(false);
		                                } else {
		                                    assert(prepared_cache@.valid_read(read_addr, data));
		                                }
		                            }
		                            assert(Cache::State::next(
		                                prepared_cache@,
		                                cache@,
		                                Cache::Label::Access{reads: Map::empty(), writes},
		                            ));
	                            assert(to_branch_nodes(writes) == loaded_initialize_write_nodes(
	                                root@,
	                                keys@,
	                                msgs@,
	                            ));
	                            let addr = Address{
	                                au: pre_stack.mini_allocator.alloc_au_nat(),
	                                page: pre_stack.mini_allocator.next_page() as nat,
	                            };
	                            assert(addr == root@);
	                            let cached_branch_lbl = CachedBranch::Label::Initialize{
	                                mini_allocator: pre_stack.mini_allocator.i(),
	                                init_root: root@,
	                                keys: keys@,
	                                msgs: msgs@,
	                                write_nodes: to_branch_nodes(writes),
	                            };
	                            assert(pre_stack.active_branch_i().is_empty_active());
	                            assert(pre_stack.mini_allocator.i().can_allocate(root@));
	                            assert(self.active_branch_i().root == Some(root@));
	                            assert(CachedBranch::State::initialize_branch(
	                                pre_stack.active_branch_i(),
	                                self.active_branch_i(),
	                                cached_branch_lbl,
	                            )) by {
	                            }
	                            reveal(CachedBranch::State::next);
	                            reveal(CachedBranch::State::next_by);
	                            assert(CachedBranch::State::next_by(
	                                pre_stack.active_branch_i(),
	                                self.active_branch_i(),
	                                cached_branch_lbl,
	                                CachedBranch::Step::initialize_branch(),
	                            ));
	                            assert(CachedBranch::State::next(
	                                pre_stack.active_branch_i(),
	                                self.active_branch_i(),
	                                cached_branch_lbl,
	                            ));
	                            let ghost empty_reads = Map::<Address, RawPage>::empty();
	                            let atomic_lbl = AtomicBranchState::Label::Append{
	                                keys: keys@,
	                                msgs: msgs@,
	                                receipt: init_receipt,
	                                init_root: Some(root@),
	                                read_nodes: to_branch_nodes(empty_reads),
	                                write_nodes: to_branch_nodes(writes),
	                            };
	                            assert(AtomicBranchState::State::append_empty(
	                                pre_stack@,
	                                self@,
	                                atomic_lbl,
	                                self.active_branch_i(),
	                            )) by {
	                            }
	                            reveal(AtomicBranchState::State::next);
	                            reveal(AtomicBranchState::State::next_by);
	                            assert(AtomicBranchState::State::next_by(
	                                pre_stack@,
	                                self@,
	                                atomic_lbl,
	                                AtomicBranchState::Step::append_empty(self.active_branch_i()),
	                            ));
		                            assert(AtomicBranchState::State::next(pre_stack@, self@, atomic_lbl));
		                            AtomicBranchState::State::append_effect(pre_stack@, self@, atomic_lbl);
		                            assert(pre_stack@ == old(self)@);
                                    branch_stack_store_addrs_safe_after_insert(
                                        &pre_stack.active_store,
                                        &self.active_store,
                                        root@,
                                        node_for_page@,
                                    );
                                    let post_linked = self.active_branch.unwrap().i(&self.active_store);
                                    let ranking = map![root@ => 1nat];
                                    assert(post_linked.valid_ranking(ranking)) by {
                                        assert(post_linked.disk_view.valid_ranking(ranking)) by {
                                            assert forall |addr: Address|
                                                #[trigger] ranking.contains_key(addr)
                                                    && post_linked.disk_view.entries.contains_key(addr)
                                                implies post_linked.disk_view.node_children_respects_rank(ranking, addr) by {
                                                assert(addr == root@);
                                                assert(post_linked.disk_view.entries[addr] == node_for_page@);
                                                assert(node_for_page@ is Leaf);
                                                assert forall |child_idx: int|
                                                    #[trigger] post_linked.disk_view.entries[addr].valid_child_index(child_idx)
                                                    implies {
                                                        &&& ranking.contains_key(
                                                            post_linked.disk_view.entries[addr]->children[child_idx])
                                                        &&& ranking[
                                                            post_linked.disk_view.entries[addr]->children[child_idx]]
                                                            < ranking[addr]
                                                    } by {
                                                    assert(false);
                                                }
                                            }
                                        }
                                        assert(ranking.contains_key(root@));
                                    }
                                    assert(post_linked.acyclic()) by {
                                        assert(exists |ranking: Ranking| post_linked.valid_ranking(ranking));
                                    }
                                    assert(post_linked.inv());
                                    assert(self.active_branch.unwrap().inv(&self.active_store));
		                            FracCacheImpl::valid_load_handles_preserved_transitive(
		                                cache0,
	                                prepared_cache,
	                                *cache,
	                            );
	                        }
	                        return BranchReplayAppendResult::Appended{
	                            prepared_cache: Ghost(prepared_cache@),
	                            branch_reads: Ghost(Map::empty()),
	                            writes: Ghost(writes),
	                            receipt: Ghost(init_receipt),
	                            init_root: Ghost(Some(root@)),
	                        };
	                    },
	                    ReserveWriteResult::CacheFull => {
	                        proof {
	                            assert(self@ == old(self)@);
	                            assert(cache@ == old(cache)@);
	                        }
	                        return BranchReplayAppendResult::CacheFull;
	                    },
	                }
	            },
	            FetchErrorCode::Awaiting
	            | FetchErrorCode::LoadInitiate{..} => {
	                proof {
	                    assert(cache@ == old(cache)@);
	                    assert(self@ == old(self)@);
	                }
	                return BranchReplayAppendResult::Blocked;
	            },
	            FetchErrorCode::CacheFull => {
	                proof {
	                    assert(self@ == old(self)@);
	                }
	                return BranchReplayAppendResult::CacheFull;
	            },
	        }
        /*
        // TODO: restore empty-branch initialization once the fresh-root cache load
        // protocol and MiniAllocatorImpl::allocate model delta are proven. The old
        // reserve-then-write path is kept here as reference, but it cannot refine to
        // a single Cache::Access from a pre-state where root is absent.
        if !self.mini_allocator.is_allocation_ready() {
            return BranchReplayAppendResult::NeedsAUs;
        }

        let root = self.mini_allocator.peek_next_addr();
        if self.store.contains(&root) {
            return BranchReplayAppendResult::Blocked;
        }

        match cache.fetch(&root, false) {
            FetchErrorCode::Success{slot_handle} => {
                cache.handle_release(&root, slot_handle);
                return BranchReplayAppendResult::Blocked;
            },
            FetchErrorCode::Awaiting => {
                return BranchReplayAppendResult::Blocked;
            },
            FetchErrorCode::CacheFull
            | FetchErrorCode::LoadInitiate{..} => {
                return BranchReplayAppendResult::CacheFull;
            },
            FetchErrorCode::NotPresent => {},
        }

        let mut handle = match cache.reserve_for_write_absent(&root) {
            ReserveWriteResult::Reserved{slot_handle} => slot_handle,
            ReserveWriteResult::CacheFull => {
                return BranchReplayAppendResult::CacheFull;
            },
        };

        match self.append(keys.clone(), msgs.clone()) {
            Ok(()) => {},
            Err(_) => {
                return unreached::<BranchReplayAppendResult>();
            },
        }

        let node = match self.store.read(&root) {
            Some(node) => node,
            None => {
                return unreached::<BranchReplayAppendResult>();
            },
        };
        let page = marshall_branch_node_page(&node);
        let ghost page_view = page@;
        let ghost writes = map![root@ => page_view];
        let ghost init_receipt = LoadedPathReceipt{
            key: keys@[0],
            root: root@,
            lines: Seq::empty(),
        };
        handle.rec = page;
        cache.write_release(&root, handle);

        BranchReplayAppendResult::Appended{
            branch_reads: Ghost(Map::empty()),
            writes: Ghost(writes),
            receipt: Ghost(init_receipt),
            init_root: Ghost(Some(root@)),
        }
        */
    }

    pub fn replay_append_from_journal(
        &mut self,
        cache: &mut FracCacheImpl,
        keys: &Vec<Key>,
        msgs: &Vec<Message>,
        disk_au_count: IAU,
        disk_page_count: IPage,
    ) -> (out: BranchReplayAppendResult)
        requires
            old(self).wf(),
            old(self).load_state is MetadataLoaded,
            old(cache).wf(),
            0 < (disk_page_count as nat),
            (disk_page_count as nat) == crate::disk::GenericDisk_v::page_count(),
            keys@.len() > 0,
            keys@.len() == msgs@.len(),
            old(self).active_branch is Some ==> {
                &&& old(self).active_branch.unwrap().inv(&old(self).active_store)
                &&& old(self).active_branch_i().ready_for_mutation(old(self).mini_allocator.i())
                &&& branch_stack_store_addrs_safe(&old(self).active_store)
            },
            branch_stack_store_addrs_safe(&old(self).active_store),
            old(self).active_branch is None && old(self).mini_allocator.allocation_ready() ==> {
                &&& MiniAllocatorImpl::allocators_unique(old(self).mini_allocator.allocators@)
                &&& old(self).mini_allocator.bounded(disk_au_count)
                &&& old(self).mini_allocator.i().allocated_aus() == Set::<AU>::empty()
            },
        ensures
            self.wf(),
            self.load_state == old(self).load_state,
            self.image == old(self).image,
            old(self).image.roots_wf() ==> self.image.roots_wf(),
            old(self)@.metadata_loaded() ==> self@.metadata_loaded(),
            self.store@ =~= old(self).store@,
            branch_stack_store_addrs_safe(&old(self).store)
                ==> branch_stack_store_addrs_safe(&self.store),
            branch_stack_store_addrs_safe(&old(self).active_store)
                ==> branch_stack_store_addrs_safe(&self.active_store),
            old(self).active_branch is Some
                && old(self).active_branch.unwrap().inv(&old(self).active_store)
                ==> self.active_branch.unwrap().inv(&self.active_store),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            old(self).mini_allocator.bounded(disk_au_count)
                ==> self.mini_allocator.bounded(disk_au_count),
            MiniAllocatorImpl::allocators_unique(old(self).mini_allocator.allocators@)
                ==> MiniAllocatorImpl::allocators_unique(self.mini_allocator.allocators@),
            MiniAllocatorImpl::allocators_au_set(self.mini_allocator.allocators@) =~=
                MiniAllocatorImpl::allocators_au_set(old(self).mini_allocator.allocators@),
            old(self).mini_allocator.i().allocated_aus() == Set::<AU>::empty()
                && self.active_branch is None
                ==> self.mini_allocator.i().allocated_aus() == Set::<AU>::empty(),
            match out {
                BranchReplayAppendResult::Appended{prepared_cache, branch_reads, writes, receipt, init_root} => {
                    &&& self.active_branch is Some
                    &&& branch_stack_store_addrs_safe(&self.active_store)
                    &&& self.active_branch.unwrap().inv(&self.active_store)
                    &&& self.active_branch_i().ready_for_operation(self.mini_allocator.i())
                    &&& if old(self).active_branch is Some {
                        branch_reads@.dom() == receipt@.needed_addrs()
                    } else {
                        branch_reads@.dom() == Set::<Address>::empty()
                    }
                    &&& Cache::State::next(
                        old(cache)@,
                        prepared_cache@,
                        Cache::Label::Internal,
                    )
                    &&& Cache::State::next(
                        prepared_cache@,
                        cache@,
                        Cache::Label::Access{reads: branch_reads@, writes: writes@},
                    )
                    &&& forall |read_addr: Address, data: RawPage|
                        #[trigger] old(cache)@.valid_read(read_addr, data)
                        ==> prepared_cache@.valid_read(read_addr, data)
	                    &&& AtomicBranchState::State::next(
	                        old(self)@,
	                        self@,
	                        AtomicBranchState::Label::Append{
	                            keys: keys@,
	                            msgs: msgs@,
	                            receipt: receipt@,
	                            init_root: init_root@,
	                            read_nodes: to_branch_nodes(branch_reads@),
	                            write_nodes: to_branch_nodes(writes@),
	                        },
	                    )
	                },
                BranchReplayAppendResult::NeedCacheLoad{addr, handle} => {
                    &&& self@ == old(self)@
                    &&& self.active_branch == old(self).active_branch
                    &&& self.mini_allocator.i() == old(self).mini_allocator.i()
                    &&& self.mini_allocator.allocators@ == old(self).mini_allocator.allocators@
                    &&& self.mini_allocator.curr == old(self).mini_allocator.curr
                    &&& self.mini_allocator.free_au_threshold == old(self).mini_allocator.free_au_threshold
                    &&& addr@.wf()
                    &&& addr@ != spec_superblock_addr()
                    &&& cache.entry_fetched(&addr)
                    &&& cache.valid_load_handle(&addr, handle)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        crate::implementation::FracCacheImpl_v::cache_load_label(&addr),
                    )
                },
                BranchReplayAppendResult::NeedsAUs => {
                    &&& self@ == old(self)@
                    &&& self.active_branch == old(self).active_branch
                    &&& self.mini_allocator.i() == old(self).mini_allocator.i()
                    &&& self.mini_allocator.allocators@ == old(self).mini_allocator.allocators@
                    &&& self.mini_allocator.curr == old(self).mini_allocator.curr
                    &&& self.mini_allocator.free_au_threshold == old(self).mini_allocator.free_au_threshold
                    &&& old(cache)@ == cache@
                },
                BranchReplayAppendResult::CacheFull => {
                    &&& self@ == old(self)@
                    &&& self.active_branch == old(self).active_branch
                    &&& self.mini_allocator.i() == old(self).mini_allocator.i()
                    &&& self.mini_allocator.allocators@ == old(self).mini_allocator.allocators@
                    &&& self.mini_allocator.curr == old(self).mini_allocator.curr
                    &&& self.mini_allocator.free_au_threshold == old(self).mini_allocator.free_au_threshold
                    &&& old(cache)@ == cache@
                },
                BranchReplayAppendResult::Blocked => {
                    &&& self@ == old(self)@
                    &&& self.active_branch == old(self).active_branch
                    &&& self.mini_allocator.i() == old(self).mini_allocator.i()
                    &&& self.mini_allocator.allocators@ == old(self).mini_allocator.allocators@
                    &&& self.mini_allocator.curr == old(self).mini_allocator.curr
                    &&& self.mini_allocator.free_au_threshold == old(self).mini_allocator.free_au_threshold
                    &&& old(cache)@ == cache@
                },
            },
    {
        self.append_with_cache(cache, keys, msgs, disk_au_count, disk_page_count)
    }

    pub fn recover_metadata_step(
        &mut self,
        cache: &mut FracCacheImpl,
        disk_au_count: IAU,
        disk_page_count: IPage,
    ) -> (out: BranchMetadataStepResult)
        requires
            old(self).wf(),
            old(self).metadata_recovery_wf(),
            old(self).image.roots_bounded(disk_au_count),
            old(cache).wf(),
            (disk_page_count as nat) == crate::disk::GenericDisk_v::page_count(),
        ensures
            self.wf(),
            self.metadata_recovery_wf(),
            self.image.roots_bounded(disk_au_count),
            self.active_branch == old(self).active_branch,
            self.persistent_prefix_len == old(self).persistent_prefix_len,
            self.persistent_seq_end == old(self).persistent_seq_end,
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match out {
                BranchMetadataStepResult::NeedCacheLoad{addr, handle, ..} => {
                    &&& self@ == old(self)@
                    &&& addr@ != spec_superblock_addr()
                    &&& cache.entry_fetched(&addr)
                    &&& cache.valid_load_handle(&addr, handle)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        crate::implementation::FracCacheImpl_v::cache_load_label(&addr),
                    )
                },
                BranchMetadataStepResult::RootComplete{root, reads, discovered_aus} => {
                    &&& self.load_state is LoadingMetadata || self.load_state is MetadataLoaded
                    &&& reads@.contains_key(root@)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        Cache::Label::Access{reads: reads@, writes: Map::empty()},
                    )
                    &&& AtomicBranchState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchState::Label::LoadMetadata{
                            root: root@,
                            discovered_aus: iau_seq_set(discovered_aus@),
                            read_nodes: to_branch_nodes(reads@),
                        },
                    )
                    &&& old(cache)@ == cache@
                },
                BranchMetadataStepResult::AllComplete => {
                    &&& self.load_state is MetadataLoaded
                    &&& self@ == old(self)@
                    &&& self@.metadata_loaded()
                    &&& self@.mini_allocator == MiniAllocator::empty()
                    &&& old(cache)@ == cache@
                },
                BranchMetadataStepResult::Blocked => {
                    &&& self@ == old(self)@
                    &&& old(cache)@ == cache@
                },
            },
    {
        let next_root_idx = match self.load_state {
            BranchLoadState::AwaitingSuperblock => {
                return BranchMetadataStepResult::Blocked;
            },
            BranchLoadState::MetadataLoaded => {
                proof {
                    assert(self.metadata_recovery_wf());
                }
                return BranchMetadataStepResult::AllComplete;
            },
            BranchLoadState::LoadingMetadata{next_root_idx} => next_root_idx,
        };
        proof {
            assert(old(self).branch_summary_covers_roots_up_to(next_root_idx as nat));
            assert(old(self).image.roots_wf());
        }

        if next_root_idx >= self.image.sealed_roots.len() {
            proof {
                self.metadata_recovery_full_implies_loaded(next_root_idx);
            }
            self.load_state = BranchLoadState::MetadataLoaded;
            proof {
                assert(cache@ == old(cache)@);
                assert(self.metadata_recovery_wf());
            }
            return BranchMetadataStepResult::AllComplete;
        }
        proof {
            assert(next_root_idx < self.image.sealed_roots@.len());
        }

        let root = self.image.sealed_roots[next_root_idx];
        let superblock = superblock_addr();
        if root.au == superblock.au && root.page == superblock.page {
            proof {
                assert(cache@ == old(cache)@);
            }
            return BranchMetadataStepResult::Blocked;
        }
        if next_root_idx == usize::MAX {
            return BranchMetadataStepResult::Blocked;
        }
        let ghost recovery_image = self.image@;
        let ghost prefix_summary_dom = self.branch_summary.i().dom();
        proof {
            assert(root_aus_up_to(recovery_image.sealed_roots, next_root_idx as nat)
                <= prefix_summary_dom);
        }
        match cache.fetch(&root, true) {
            FetchErrorCode::LoadInitiate{slot_handle} => {
                proof {
                    assert(self.image.roots_wf());
                    assert(root@ == self.image.sealed_roots@[next_root_idx as int]@);
                    assert(root@.wf());
                }
                return BranchMetadataStepResult::NeedCacheLoad{
                    addr: root,
                    handle: slot_handle,
                    kind: BranchMetadataReadKind::Root{root_idx: next_root_idx},
                };
            },
            FetchErrorCode::Success{slot_handle} => {
                let ghost root_raw = slot_handle.rec@;
                let fmt = BranchNodePageFmt::new();
                let all_slice = Slice::all(&slot_handle.rec);
                let parsed = fmt.try_parse(&all_slice, &slot_handle.rec);
                proof {
                    if parsed is Some {
                        assert(fmt == BranchNodePageFmt::spec_new());
                        assert(all_slice@.i(slot_handle.rec@) == slot_handle.rec@);
                        assert(fmt.parsable(root_raw));
                        assert(parsed.unwrap().parsedv() == fmt.parse(root_raw));
                        assert(raw_page_to_branch_node(root_raw) == parsed.unwrap()@);
                    }
                }
                cache.handle_release(&root, slot_handle);

                let root_node = match parsed {
                    Some(node) => node,
                    None => {
                        proof {
                            assert(cache@ == old(cache)@);
                        }
                        return BranchMetadataStepResult::Blocked;
                    },
                };

                match root_node {
                    BranchNode::Leaf{keys, msgs} => {
                        let node = BranchNode::Leaf{keys, msgs};
                        proof {
                            assert(raw_page_to_branch_node(root_raw) == node@);
                        }
                        let ghost store_before_root = self.store;
                        match self.store.insert_fresh(root, node) {
                            Ok(()) => {},
                            Err(_) => {
                                proof {
                                    assert(cache@ == old(cache)@);
                                }
                                return BranchMetadataStepResult::Blocked;
                            },
                        }
                        proof {
                            assert(root@.wf());
                            assert(root@ != spec_superblock_addr());
                            branch_stack_store_addrs_safe_after_insert(
                                &store_before_root,
                                &self.store,
                                root@,
                                node@,
                            );
                        }
                        let mut discovered_aus = Vec::<IAU>::new();
                        discovered_aus.push(root.au);
                        let result_aus = discovered_aus.clone();
                        proof {
                            assert(self.branch_summary.i().dom() == prefix_summary_dom);
                            assert(self.image@ == recovery_image);
                            assert(self.image.roots_wf());
                        }
                        self.load_metadata(root, discovered_aus);
                        proof {
                            assert(self.branch_summary.i().dom().contains(root.au as nat));
                            assert(self.branch_summary_covers_roots_up_to(next_root_idx as nat)) by {
                                assert forall |au: AU| #[trigger] root_aus_up_to(
                                    self.image@.sealed_roots,
                                    next_root_idx as nat,
                                ).contains(au)
                                    implies self.branch_summary.i().dom().contains(au)
                                by {
                                    assert(self.image@ == recovery_image);
                                    assert(root_aus_up_to(
                                        recovery_image.sealed_roots,
                                        next_root_idx as nat,
                                    ).contains(au));
                                    assert(prefix_summary_dom.contains(au));
                                    assert(self.branch_summary.i().dom()
                                        =~= prefix_summary_dom.insert(root.au as nat));
                                }
                            }
                            self.metadata_recovery_extend_prefix(next_root_idx, root);
                        }
                        self.load_state = BranchLoadState::LoadingMetadata{
                            next_root_idx: next_root_idx + 1,
                        };
                        proof {
                            assert(self.metadata_recovery_wf());
                        }
                        let ghost reads = map![root@ => root_raw];
                        proof {
                            assert(result_aus@.len() == 1);
                            assert(result_aus@[0] == root.au);
                            assert(reads.contains_key(root@));
                            assert(reads[root@] == root_raw);
                            assert(raw_page_to_branch_node(root_raw) == node@);
                            assert(to_branch_nodes(reads).contains_key(root@));
                            assert(to_branch_nodes(reads)[root@] == node@);
                            assert(root_summary_read_valid(root@, to_branch_nodes(reads)));
                            assert(root_summary_from_read(root@, to_branch_nodes(reads)) == set![root@.au]);
                            iau_seq_set_singleton(result_aus@, root.au);
                            assert(iau_seq_set(result_aus@) == set![root@.au]);
                            assert(iau_seq_set(result_aus@)
                                == root_summary_from_read(root@, to_branch_nodes(reads)));
                            assert(old(self)@.image.sealed_roots.contains(root@)) by {
                                assert(root@ == old(self).image@.sealed_roots[next_root_idx as int]);
                            }
                            Cache::State::access_read_only_from_valid_reads(old(cache)@, reads);
                            reveal(AtomicBranchState::State::next);
                            reveal(AtomicBranchState::State::next_by);
                            assert(AtomicBranchState::State::load_metadata(
                                old(self)@,
                                self@,
                                AtomicBranchState::Label::LoadMetadata{
                                    root: root@,
                                    discovered_aus: iau_seq_set(result_aus@),
                                    read_nodes: to_branch_nodes(reads),
                                },
                            ));
                            assert(AtomicBranchState::State::next_by(
                                old(self)@,
                                self@,
                                AtomicBranchState::Label::LoadMetadata{
                                    root: root@,
                                    discovered_aus: iau_seq_set(result_aus@),
                                    read_nodes: to_branch_nodes(reads),
                                },
                                AtomicBranchState::Step::load_metadata(),
                            ));
                        }
                        BranchMetadataStepResult::RootComplete{
                            root,
                            reads: Ghost(reads),
                            discovered_aus: result_aus,
                        }
                    },
                    BranchNode::Index{pivots, children, aux_ptr} => {
                        let aux = match aux_ptr {
                            Some(aux) => aux,
                            None => {
                                proof {
                                    assert(cache@ == old(cache)@);
                                }
                                return BranchMetadataStepResult::Blocked;
                            },
                        };
                        if aux.au >= disk_au_count || aux.page >= disk_page_count {
                            proof {
                                assert(cache@ == old(cache)@);
                            }
                            return BranchMetadataStepResult::Blocked;
                        }
                        if aux.au == superblock.au && aux.page == superblock.page {
                            proof {
                                assert(cache@ == old(cache)@);
                            }
                            return BranchMetadataStepResult::Blocked;
                        }
                        match cache.fetch(&aux, true) {
                            FetchErrorCode::LoadInitiate{slot_handle} => {
                                return BranchMetadataStepResult::NeedCacheLoad{
                                    addr: aux,
                                    handle: slot_handle,
                                    kind: BranchMetadataReadKind::Aux{
                                        root_idx: next_root_idx,
                                        root,
                                        aux,
                                    },
                                };
                            },
                            FetchErrorCode::Success{slot_handle} => {
                                let ghost aux_raw = slot_handle.rec@;
                                let aux_slice = Slice::all(&slot_handle.rec);
                                let aux_parsed = fmt.try_parse(&aux_slice, &slot_handle.rec);
                                proof {
                                    if aux_parsed is Some {
                                        assert(fmt == BranchNodePageFmt::spec_new());
                                        assert(aux_slice@.i(slot_handle.rec@) == slot_handle.rec@);
                                        assert(fmt.parsable(aux_raw));
                                        assert(aux_parsed.unwrap().parsedv() == fmt.parse(aux_raw));
                                        assert(raw_page_to_branch_node(aux_raw) == aux_parsed.unwrap()@);
                                    }
                                }
                                cache.handle_release(&aux, slot_handle);
                                let summary_aus = match aux_parsed {
                                    Some(BranchNode::Auxiliary{summary_aus}) => summary_aus,
                                    _ => {
                                        proof {
                                            assert(cache@ == old(cache)@);
                                        }
                                        return BranchMetadataStepResult::Blocked;
                                    },
                                };
                                let result_aus = summary_aus.clone();
                                let aux_node = BranchNode::Auxiliary{summary_aus};
                                let root_node = BranchNode::Index{
                                    pivots,
                                    children,
                                    aux_ptr: Some(aux),
                                };
                                proof {
                                    assert(raw_page_to_branch_node(root_raw) == root_node@);
                                    assert(raw_page_to_branch_node(aux_raw) == aux_node@);
                                }
                                let ghost store_before_root = self.store;
                                match self.store.insert_fresh(root, root_node) {
                                    Ok(()) => {},
                                    Err(_) => {
                                        proof {
                                            assert(cache@ == old(cache)@);
                                        }
                                        return BranchMetadataStepResult::Blocked;
                                    },
                                }
                                proof {
                                    assert(root@.wf());
                                    assert(root@ != spec_superblock_addr());
                                    branch_stack_store_addrs_safe_after_insert(
                                        &store_before_root,
                                        &self.store,
                                        root@,
                                        root_node@,
                                    );
                                }
                                let ghost store_before_aux = self.store;
                                match self.store.insert_fresh(aux, aux_node) {
                                    Ok(()) => {},
                                    Err(_) => {
                                        proof {
                                            assert(cache@ == old(cache)@);
                                        }
                                        return BranchMetadataStepResult::Blocked;
                                    },
                                }
                                proof {
                                    assert(root_node.wf());
                                    assert(aux.wf());
                                    assert(aux@.wf());
                                    assert(aux@ != spec_superblock_addr());
                                    branch_stack_store_addrs_safe_after_insert(
                                        &store_before_aux,
                                        &self.store,
                                        aux@,
                                        aux_node@,
                                    );
                                }
                                let metadata_aus = result_aus.clone();
                                proof {
                                    assert(self.branch_summary.i().dom() == prefix_summary_dom);
                                    assert(self.image@ == recovery_image);
                                    assert(self.image.roots_wf());
                                }
                                self.load_metadata(root, metadata_aus);
                                proof {
                                    assert(self.branch_summary.i().dom().contains(root.au as nat));
                                    assert(self.branch_summary_covers_roots_up_to(next_root_idx as nat)) by {
                                        assert forall |au: AU| #[trigger] root_aus_up_to(
                                            self.image@.sealed_roots,
                                            next_root_idx as nat,
                                        ).contains(au)
                                            implies self.branch_summary.i().dom().contains(au)
                                        by {
                                            assert(self.image@ == recovery_image);
                                            assert(root_aus_up_to(
                                                recovery_image.sealed_roots,
                                                next_root_idx as nat,
                                            ).contains(au));
                                            assert(prefix_summary_dom.contains(au));
                                            assert(self.branch_summary.i().dom()
                                                =~= prefix_summary_dom.insert(root.au as nat));
                                        }
                                    }
                                    self.metadata_recovery_extend_prefix(next_root_idx, root);
                                }
                                self.load_state = BranchLoadState::LoadingMetadata{
                                    next_root_idx: next_root_idx + 1,
                                };
                                proof {
                                    assert(self.metadata_recovery_wf());
                                }
                                let ghost reads = map![root@ => root_raw, aux@ => aux_raw];
                                proof {
                                    assert(reads.contains_key(root@));
                                    assert(reads.contains_key(aux@));
                                    assert(reads[root@] == root_raw);
                                    assert(reads[aux@] == aux_raw);
                                    assert(raw_page_to_branch_node(root_raw) == root_node@);
                                    assert(raw_page_to_branch_node(aux_raw) == aux_node@);
                                    assert(to_branch_nodes(reads).contains_key(root@));
                                    assert(to_branch_nodes(reads).contains_key(aux@));
                                    assert(to_branch_nodes(reads)[root@] == root_node@);
                                    assert(to_branch_nodes(reads)[aux@] == aux_node@);
                                    assert(root_summary_read_valid(root@, to_branch_nodes(reads)));
                                    iau_seq_set_matches_to_set(result_aus@);
                                    assert(iau_seq_set(result_aus@)
                                        == root_summary_from_read(root@, to_branch_nodes(reads)));
                                    assert(old(self)@.image.sealed_roots.contains(root@)) by {
                                        assert(root@ == old(self).image@.sealed_roots[next_root_idx as int]);
                                    }
                                    Cache::State::access_read_only_from_valid_reads(old(cache)@, reads);
                                    reveal(AtomicBranchState::State::next);
                                    reveal(AtomicBranchState::State::next_by);
                                    assert(AtomicBranchState::State::load_metadata(
                                        old(self)@,
                                        self@,
                                        AtomicBranchState::Label::LoadMetadata{
                                            root: root@,
                                            discovered_aus: iau_seq_set(result_aus@),
                                            read_nodes: to_branch_nodes(reads),
                                        },
                                    ));
                                    assert(AtomicBranchState::State::next_by(
                                        old(self)@,
                                        self@,
                                        AtomicBranchState::Label::LoadMetadata{
                                            root: root@,
                                            discovered_aus: iau_seq_set(result_aus@),
                                            read_nodes: to_branch_nodes(reads),
                                        },
                                        AtomicBranchState::Step::load_metadata(),
                                    ));
                                }
                                BranchMetadataStepResult::RootComplete{
                                    root,
                                    reads: Ghost(reads),
                                    discovered_aus: result_aus,
                                }
                            },
                            FetchErrorCode::Awaiting
                            | FetchErrorCode::CacheFull
                            | FetchErrorCode::NotPresent => {
                                proof {
                                    assert(cache@ == old(cache)@);
                                }
                                BranchMetadataStepResult::Blocked
                            },
                        }
                    },
                    BranchNode::Auxiliary{..} => {
                        proof {
                            assert(cache@ == old(cache)@);
                        }
                        BranchMetadataStepResult::Blocked
                    },
                }
            },
            FetchErrorCode::Awaiting
            | FetchErrorCode::CacheFull
            | FetchErrorCode::NotPresent => {
                proof {
                    assert(cache@ == old(cache)@);
                }
                BranchMetadataStepResult::Blocked
            },
        }
    }

    pub fn append(&mut self, keys: Vec<Key>, msgs: Vec<Message>) -> (result: Result<(), BranchError>)
        requires
            old(self).wf(),
            old(self).load_state is MetadataLoaded,
            old(self).active_branch is Some ==> old(self).active_branch.unwrap().inv(&old(self).active_store),
        ensures
            result is Ok ==> self.wf(),
    {
        if keys.is_empty() || keys.len() != msgs.len() {
            return Err(BranchError::InvalidAppend);
        }
        let appended_count = keys.len();
        if appended_count > usize::MAX - self.seq_end {
            return Err(BranchError::InvalidAppend);
        }

        match self.active_branch {
            Some(branch) => {
                branch.append(&mut self.active_store, keys, msgs)?;
                proof {
                    assert(self.active_store.wf());
                }
            },
            None => {
                let init_root = match allocate_fresh_addr_from_mini(&mut self.mini_allocator)? {
                    addr => addr,
                };
                let mut store = MemBranchStore::new();
                store.insert_fresh(init_root, BranchNode::Leaf { keys, msgs })?;
                proof {
                    assert(store.wf());
                }
                self.active_store = store;
                self.active_branch = Some(BranchImpl::new(init_root));
            },
        }

        self.seq_end = self.seq_end + appended_count;
        Ok(())
    }

    pub fn grow(&mut self) -> (result: Result<(), BranchError>)
        requires
            old(self).wf(),
            old(self).load_state is MetadataLoaded,
            old(self).active_branch is Some ==> old(self).active_branch.unwrap().inv(&old(self).active_store),
        ensures
            result is Ok ==> self.wf(),
    {
        let mut branch = match self.active_branch {
            Some(branch) => branch,
            None => return Err(BranchError::Uninitialized),
        };
        branch.grow(&mut self.active_store, &mut self.mini_allocator)?;
        proof {
            assert(self.active_store.wf());
            assert(self.mini_allocator.wf());
        }
        self.active_branch = Some(branch);
        Ok(())
    }

    pub fn split(&mut self, pivot: Key) -> (result: Result<(), BranchError>)
        requires
            old(self).wf(),
            old(self).load_state is MetadataLoaded,
            old(self).active_branch is Some ==> old(self).active_branch.unwrap().inv(&old(self).active_store),
        ensures
            result is Ok ==> self.wf(),
    {
        let branch = match self.active_branch {
            Some(branch) => branch,
            None => return Err(BranchError::Uninitialized),
        };
        branch.split(&mut self.active_store, pivot, &mut self.mini_allocator)?;
        proof {
            assert(self.active_store.wf());
            assert(self.mini_allocator.wf());
        }
        Ok(())
    }

    pub fn seal_active_branch_with_cache(
        &mut self,
        cache: &mut FracCacheImpl,
        disk_au_count: IAU,
        disk_page_count: IPage,
    ) -> (out: BranchSealResult)
        requires
            old(self).wf(),
            old(self).load_state is MetadataLoaded,
            old(cache).wf(),
            old(cache)@.inv(),
            old(self).active_branch is Some,
            old(self).commit_phase is Idle,
            old(self).active_branch.unwrap().inv(&old(self).active_store),
            branch_stack_store_addrs_safe(&old(self).active_store),
            old(self).active_branch_i().ready_for_mutation(old(self).mini_allocator.i()),
            MiniAllocatorImpl::allocators_unique(old(self).mini_allocator.allocators@),
            old(self).mini_allocator.bounded(disk_au_count),
            0 < (disk_page_count as nat),
            (disk_page_count as nat) == crate::disk::GenericDisk_v::page_count(),
        ensures
            self.wf(),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            self.load_state == old(self).load_state,
            self.store == old(self).store,
            match out {
                BranchSealResult::Sealed{root, aux_ptr, summary_aus, reads, writes} => {
                    &&& self.active_branch is None
                    &&& self.active_store@.entries == Map::<Address, SpecBranchNode>::empty()
                    &&& self.image.sealed_roots@ == old(self).image.sealed_roots@.push(root)
                    &&& self.persisted_root_count == old(self).persisted_root_count
                    &&& iau_vec_set(summary_aus@) =~= old(self).mini_allocator.i().allocated_aus()
                    &&& MiniAllocatorImpl::allocators_unique(self.mini_allocator.allocators@)
                    &&& self.mini_allocator.bounded(disk_au_count)
                    &&& MiniAllocatorImpl::allocators_au_set(self.mini_allocator.allocators@) =~=
                        MiniAllocatorImpl::allocators_au_set(old(self).mini_allocator.allocators@)
                            - iau_vec_set(summary_aus@)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        Cache::Label::Access{reads: reads@, writes: writes@},
                    )
                    &&& AtomicBranchState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchState::Label::Seal{
                            aux_ptr: iopt_addr(aux_ptr),
                            summary: iau_vec_set(summary_aus@),
                            read_nodes: to_branch_nodes(reads@),
                            write_nodes: to_branch_nodes(writes@),
                        },
                    )
                    &&& root@ == old(self).active_branch_i().root.unwrap()
                },
                BranchSealResult::SealedAfterPrepare{
                    root,
                    aux_ptr,
                    summary_aus,
                    reads,
                    writes,
                    prepared_cache,
                } => {
                    &&& self.active_branch is None
                    &&& self.active_store@.entries == Map::<Address, SpecBranchNode>::empty()
                    &&& self.image.sealed_roots@ == old(self).image.sealed_roots@.push(root)
                    &&& self.persisted_root_count == old(self).persisted_root_count
                    &&& iau_vec_set(summary_aus@) =~= old(self).mini_allocator.i().allocated_aus()
                    &&& MiniAllocatorImpl::allocators_unique(self.mini_allocator.allocators@)
                    &&& self.mini_allocator.bounded(disk_au_count)
                    &&& MiniAllocatorImpl::allocators_au_set(self.mini_allocator.allocators@) =~=
                        MiniAllocatorImpl::allocators_au_set(old(self).mini_allocator.allocators@)
                            - iau_vec_set(summary_aus@)
                    &&& Cache::State::next(
                        old(cache)@,
                        prepared_cache@,
                        Cache::Label::Internal,
                    )
                    &&& Cache::State::next(
                        prepared_cache@,
                        cache@,
                        Cache::Label::Access{reads: reads@, writes: writes@},
                    )
                    &&& AtomicBranchState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchState::Label::Seal{
                            aux_ptr: iopt_addr(aux_ptr),
                            summary: iau_vec_set(summary_aus@),
                            read_nodes: to_branch_nodes(reads@),
                            write_nodes: to_branch_nodes(writes@),
                        },
                    )
                    &&& root@ == old(self).active_branch_i().root.unwrap()
                },
                BranchSealResult::NeedsAUs
                | BranchSealResult::CacheFull
                | BranchSealResult::Blocked => {
                    &&& *self == *old(self)
                    &&& self@ == old(self)@
                    &&& cache@ == old(cache)@
                },
            },
    {
        let ghost pre_stack = *self;
        let ghost pre_cache = *cache;
        let branch = self.active_branch.unwrap();
        let root = branch.root;
        let root_node = match self.active_store.read_checked(&root) {
            Some(node) => node,
            None => {
                proof {
                    assert(self@ == old(self)@);
                    assert(cache@ == old(cache)@);
                }
                return BranchSealResult::Blocked;
            },
        };
        let ghost root_node_view = root_node@;
        let root_handle = match cache.fetch(&root, false) {
            FetchErrorCode::Success{slot_handle} => slot_handle,
            FetchErrorCode::Awaiting | FetchErrorCode::NotPresent => {
                proof {
                    assert(self@ == old(self)@);
                    assert(cache@ == old(cache)@);
                }
                return BranchSealResult::Blocked;
            },
            FetchErrorCode::CacheFull | FetchErrorCode::LoadInitiate{..} => {
                proof {
                    assert(self@ == old(self)@);
                    assert(cache@ == old(cache)@);
                }
                return BranchSealResult::CacheFull;
            },
        };
        let ghost raw = root_handle.rec@;
        let fmt = BranchNodePageFmt::new();
        let all_slice = Slice::all(&root_handle.rec);
        let parsed = fmt.try_parse(&all_slice, &root_handle.rec);
        proof {
            assert(pre_cache@.valid_read(root@, raw));
            if parsed is Some {
                assert(fmt == BranchNodePageFmt::spec_new());
                assert(all_slice@.i(root_handle.rec@) == root_handle.rec@);
                assert(raw_page_to_branch_node(raw) == parsed.unwrap()@);
            }
        }
        cache.handle_release(&root, root_handle);
        proof {
            assert(cache@ == pre_cache@) by {
                assert(cache@.lookup_map == pre_cache@.lookup_map);
                assert(cache@.status_map == pre_cache@.status_map);
                assert(cache@.entries == pre_cache@.entries);
            }
        }
        let parsed_node = match parsed {
            Some(node) => node,
            None => {
                proof {
                    assert(self@ == old(self)@);
                    assert(cache@ == old(cache)@);
                }
                return BranchSealResult::Blocked;
            },
        };
        if !same_branch_node_view(&parsed_node, &root_node) {
            proof {
                assert(self@ == old(self)@);
                assert(cache@ == old(cache)@);
            }
            return BranchSealResult::Blocked;
        }
        proof {
            assert(parsed_node@ == root_node_view);
            assert(raw_page_to_branch_node(raw) == root_node_view);
        }

        match root_node {
            BranchNode::Index{..} => {
                proof {
                    assert(self@ == pre_stack@);
                    assert(cache@ == pre_cache@);
                }
                return self.seal_index_with_cache_after_root_read(
                    cache,
                    root,
                    root_node,
                    Ghost(raw),
                    disk_au_count,
                    disk_page_count,
                );
            },
            BranchNode::Auxiliary{..} => {
                proof {
                    assert(self@ == old(self)@);
                    assert(cache@ == old(cache)@);
                }
                return BranchSealResult::Blocked;
            },
            BranchNode::Leaf{..} => {},
        }

        let ghost reads = map![root@ => raw];
        let ghost writes = Map::<Address, RawPage>::empty();
        let summary_aus = self.mini_allocator.prune_allocated_aus(
            disk_au_count,
        );
        let summary_for_store = summary_aus.clone();
        proof {
            assert(summary_for_store@ =~= summary_aus@) by {
                assert forall |i: int| 0 <= i < summary_for_store@.len()
                    implies #[trigger] summary_for_store@[i] == summary_aus@[i] by {
                }
            }
        }
        self.image.sealed_roots.push(root);
        let ghost pre_branch_summary = self.branch_summary.i();
        self.branch_summary.insert_or_update(root.au, summary_for_store);
        proof {
            iau_seq_set_matches_to_set(summary_aus@);
            assert(iau_seq_set(summary_aus@) =~= iau_vec_set(summary_aus@)) by {
                assert forall |au: AU| #[trigger] iau_seq_set(summary_aus@).contains(au)
                    <==> iau_vec_set(summary_aus@).contains(au) by {
                    if iau_seq_set(summary_aus@).contains(au) {
                        assert(iau_seq(summary_aus@).to_set().contains(au));
                        let i = choose |i: int| 0 <= i < iau_seq(summary_aus@).len()
                            && #[trigger] iau_seq(summary_aus@)[i] == au;
                        assert(summary_aus@[i] as nat == au);
                    }
                    if iau_vec_set(summary_aus@).contains(au) {
                        let i = choose |i: int| 0 <= i < summary_aus@.len()
                            && #[trigger] summary_aus@[i] as nat == au;
                        assert(iau_seq(summary_aus@)[i] == au);
                        assert(iau_seq(summary_aus@).to_set().contains(au));
                    }
                }
            }
            assert(pre_branch_summary == pre_stack.branch_summary.i());
            assert(self.branch_summary.i()
                == pre_branch_summary.insert(root@.au, iau_seq_set(summary_aus@)));
        }
        self.active_branch = None;
        self.active_store = MemBranchStore::new();

        proof {
            let summary = iau_vec_set(summary_aus@);
            assert(summary =~= pre_stack.mini_allocator.i().allocated_aus());
            assert(to_branch_nodes(reads).contains_key(root@));
            assert(to_branch_nodes(reads)[root@] == root_node_view);
            assert(loaded_line_wf(to_branch_nodes(reads), root@)) by {
                assert(root_node_view.wf());
                assert(!(root_node_view is Auxiliary));
                assert(root_node_view.keys_strictly_sorted());
            }
            assert(loaded_seal_write_nodes(
                root@,
                to_branch_nodes(reads),
                Option::<Address>::None,
                summary,
            ) == to_branch_nodes(writes));
            Cache::State::access_read_only_from_valid_reads(pre_cache@, reads);
            assert(Cache::State::next(
                pre_cache@,
                cache@,
                Cache::Label::Access{reads, writes},
            ));
            let cached_lbl = CachedBranch::Label::Seal{
                mini_allocator: pre_stack.mini_allocator.i(),
                aux_ptr: None,
                read_nodes: to_branch_nodes(reads),
                write_nodes: to_branch_nodes(writes),
            };
            assert(CachedBranch::State::seal_step(
                pre_stack.active_branch_i(),
                pre_stack.active_branch_i(),
                cached_lbl,
            )) by {
                assert(pre_stack.active_branch_i().ready_for_mutation(
                    pre_stack.mini_allocator.i(),
                ));
            }
            reveal(CachedBranch::State::next);
            reveal(CachedBranch::State::next_by);
            assert(CachedBranch::State::next_by(
                pre_stack.active_branch_i(),
                pre_stack.active_branch_i(),
                cached_lbl,
                CachedBranch::Step::seal_step(),
            ));
            assert(CachedBranch::State::next(
                pre_stack.active_branch_i(),
                pre_stack.active_branch_i(),
                cached_lbl,
            ));
            let atomic_lbl = AtomicBranchState::Label::Seal{
                aux_ptr: None,
                summary,
                read_nodes: to_branch_nodes(reads),
                write_nodes: to_branch_nodes(writes),
            };
            assert(AtomicBranchState::State::seal(
                pre_stack@,
                self@,
                atomic_lbl,
            )) by {
                assert(self.image@.sealed_roots
                    == pre_stack.image@.sealed_roots.push(root@));
                assert(self.active_branch_i() == CachedBranch::State::empty_active());
                assert(self.mini_allocator.i()
                    == pre_stack.mini_allocator.i().prune(summary));
                assert(self.branch_summary.i()
                    == pre_stack.branch_summary.i().insert(root@.au, summary));
                assert(self.image@.seq_end == pre_stack.image@.seq_end);
                assert(self.seq_end == pre_stack.seq_end);
                assert(self.persisted_root_count == pre_stack.persisted_root_count);
                assert(self.commit_phase == pre_stack.commit_phase);
                assert(self.in_flight_i() == pre_stack.in_flight_i());
                assert(self.persistent_image_i() == pre_stack.persistent_image_i()) by {
                    assert(self.persistent_prefix_len == pre_stack.persistent_prefix_len);
                    assert(pre_stack.persistent_prefix_len
                        <= pre_stack.image.sealed_roots@.len());
                    assert(self.image.sealed_roots@.take(
                        self.persistent_prefix_len as int,
                    ) == pre_stack.image.sealed_roots@.take(
                        pre_stack.persistent_prefix_len as int,
                    ));
                }
            }
            reveal(AtomicBranchState::State::next);
            reveal(AtomicBranchState::State::next_by);
            assert(AtomicBranchState::State::next_by(
                pre_stack@,
                self@,
                atomic_lbl,
                AtomicBranchState::Step::seal(),
            ));
            assert(AtomicBranchState::State::next(pre_stack@, self@, atomic_lbl));
            assert(self.wf());
        }
        BranchSealResult::Sealed{
            root,
            aux_ptr: None,
            summary_aus,
            reads: Ghost(reads),
            writes: Ghost(writes),
        }
    }

    fn seal_index_with_cache_after_root_read(
        &mut self,
        cache: &mut FracCacheImpl,
        root: IAddress,
        root_node: BranchNode,
        root_raw: Ghost<RawPage>,
        disk_au_count: IAU,
        disk_page_count: IPage,
    ) -> (out: BranchSealResult)
        requires
            old(self).wf(),
            old(self).load_state is MetadataLoaded,
            old(self).commit_phase is Idle,
            old(self).active_branch is Some,
            old(self).active_branch.unwrap().root@ == root@,
            old(self).active_branch.unwrap().inv(&old(self).active_store),
            branch_stack_store_addrs_safe(&old(self).active_store),
            old(self).active_store@.entries.contains_key(root@),
            old(self).active_store@.entries[root@] == root_node@,
            root_node is Index,
            root_node.wf(),
            raw_page_to_branch_node(root_raw@) == root_node@,
            old(cache).wf(),
            old(cache)@.inv(),
            old(cache)@.valid_read(root@, root_raw@),
            old(cache).entry_available_for_fetch(&root),
            old(self).active_branch_i().ready_for_mutation(old(self).mini_allocator.i()),
            MiniAllocatorImpl::allocators_unique(old(self).mini_allocator.allocators@),
            old(self).mini_allocator.bounded(disk_au_count),
            0 < (disk_page_count as nat),
            (disk_page_count as nat) == crate::disk::GenericDisk_v::page_count(),
        ensures
            self.wf(),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            self.load_state == old(self).load_state,
            self.store == old(self).store,
            match out {
                BranchSealResult::Sealed{root: out_root, aux_ptr, summary_aus, reads, writes} => {
                    &&& self.active_branch is None
                    &&& self.active_store@.entries == Map::<Address, SpecBranchNode>::empty()
                    &&& self.image.sealed_roots@ == old(self).image.sealed_roots@.push(out_root)
                    &&& self.persisted_root_count == old(self).persisted_root_count
                    &&& iau_vec_set(summary_aus@) =~= old(self).mini_allocator.i().allocated_aus()
                    &&& MiniAllocatorImpl::allocators_unique(self.mini_allocator.allocators@)
                    &&& self.mini_allocator.bounded(disk_au_count)
                    &&& MiniAllocatorImpl::allocators_au_set(self.mini_allocator.allocators@) =~=
                        MiniAllocatorImpl::allocators_au_set(old(self).mini_allocator.allocators@)
                            - iau_vec_set(summary_aus@)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        Cache::Label::Access{reads: reads@, writes: writes@},
                    )
                    &&& AtomicBranchState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchState::Label::Seal{
                            aux_ptr: iopt_addr(aux_ptr),
                            summary: iau_vec_set(summary_aus@),
                            read_nodes: to_branch_nodes(reads@),
                            write_nodes: to_branch_nodes(writes@),
                        },
                    )
                    &&& out_root@ == root@
                },
                BranchSealResult::SealedAfterPrepare{
                    root: out_root,
                    aux_ptr,
                    summary_aus,
                    reads,
                    writes,
                    prepared_cache,
                } => {
                    &&& self.active_branch is None
                    &&& self.active_store@.entries == Map::<Address, SpecBranchNode>::empty()
                    &&& self.image.sealed_roots@ == old(self).image.sealed_roots@.push(out_root)
                    &&& self.persisted_root_count == old(self).persisted_root_count
                    &&& iau_vec_set(summary_aus@) =~= old(self).mini_allocator.i().allocated_aus()
                    &&& MiniAllocatorImpl::allocators_unique(self.mini_allocator.allocators@)
                    &&& self.mini_allocator.bounded(disk_au_count)
                    &&& MiniAllocatorImpl::allocators_au_set(self.mini_allocator.allocators@) =~=
                        MiniAllocatorImpl::allocators_au_set(old(self).mini_allocator.allocators@)
                            - iau_vec_set(summary_aus@)
                    &&& Cache::State::next(
                        old(cache)@,
                        prepared_cache@,
                        Cache::Label::Internal,
                    )
                    &&& Cache::State::next(
                        prepared_cache@,
                        cache@,
                        Cache::Label::Access{reads: reads@, writes: writes@},
                    )
                    &&& AtomicBranchState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchState::Label::Seal{
                            aux_ptr: iopt_addr(aux_ptr),
                            summary: iau_vec_set(summary_aus@),
                            read_nodes: to_branch_nodes(reads@),
                            write_nodes: to_branch_nodes(writes@),
                        },
                    )
                    &&& out_root@ == root@
                },
                BranchSealResult::NeedsAUs
                | BranchSealResult::CacheFull
                | BranchSealResult::Blocked => {
                    &&& *self == *old(self)
                    &&& self@ == old(self)@
                    &&& cache@ == old(cache)@
                },
            },
    {
        let ghost pre_stack = *self;
        let ghost cache0 = *cache;
        let (pivots, children, old_aux_ptr) = match root_node {
            BranchNode::Index{pivots, children, aux_ptr} => (pivots, children, aux_ptr),
            _ => return unreached::<BranchSealResult>(),
        };
        if old_aux_ptr.is_some() {
            proof {
                assert(self@ == old(self)@);
                assert(cache@ == old(cache)@);
            }
            return BranchSealResult::Blocked;
        }
        if !self.mini_allocator.is_allocation_ready() {
            proof {
                assert(self@ == old(self)@);
                assert(cache@ == old(cache)@);
            }
            return BranchSealResult::NeedsAUs;
        }
        let aux = self.mini_allocator.peek_next_addr();
        if aux.page == 0 || aux.page >= disk_page_count || same_iaddr_local(&aux, &root) {
            proof {
                assert(self@ == old(self)@);
                assert(cache@ == old(cache)@);
            }
            return BranchSealResult::NeedsAUs;
        }
        if self.active_store.read_checked(&aux).is_some() {
            proof {
                assert(self@ == old(self)@);
                assert(cache@ == old(cache)@);
            }
            return BranchSealResult::Blocked;
        }
        let node_fmt = BranchNodePageFmt::new();
        if pivots.len() > node_fmt.index_routes_fmt.max_length
            || pivots.len() > u8::MAX as usize
        {
            proof {
                assert(self@ == old(self)@);
                assert(cache@ == old(cache)@);
            }
            return BranchSealResult::Blocked;
        }
        if self.mini_allocator.allocators.len() > node_fmt.aux_fmt.max_length {
            proof {
                assert(self@ == old(self)@);
                assert(cache@ == old(cache)@);
            }
            return BranchSealResult::Blocked;
        }

        proof {
            pre_stack.mini_allocator.prove_active_next_addr_can_allocate(
                disk_au_count,
                disk_page_count,
            );
            pre_stack.mini_allocator.active_au_allocated_if_next_page_positive(
                disk_au_count,
                disk_page_count,
            );
            assert(aux@ == pre_stack.mini_allocator.next_addr());
            assert(pre_stack.mini_allocator.i().can_allocate(aux@));
            assert(pre_stack.mini_allocator.i().allocated_aus().contains(aux@.au));
            assert(aux@.wf());
        }

        let ghost before_aux_fetch = *cache;
        let mut prepared = false;
        let mut aux_handle = match cache.fetch(&aux, false) {
            FetchErrorCode::Success{slot_handle} => {
                proof {
                    FracCacheImpl::valid_write_handle_model_entry(
                        &*cache,
                        &aux,
                        slot_handle,
                    );
                    assert(before_aux_fetch@.lookup_map == cache@.lookup_map);
                    assert(before_aux_fetch@.lookup_map[aux@] == slot_handle.idx);
                }
                slot_handle
            },
            FetchErrorCode::NotPresent => {
                match cache.reserve_for_write_absent(&aux) {
                    ReserveWriteResult::Reserved{slot_handle} => {
                        prepared = true;
                        slot_handle
                    },
                    ReserveWriteResult::CacheFull => {
                        proof {
                            assert(self@ == old(self)@);
                            assert(cache@ == old(cache)@);
                        }
                        return BranchSealResult::CacheFull;
                    },
                }
            },
            FetchErrorCode::Awaiting | FetchErrorCode::LoadInitiate{..} => {
                proof {
                    assert(self@ == old(self)@);
                    assert(cache@ == old(cache)@);
                }
                return BranchSealResult::Blocked;
            },
            FetchErrorCode::CacheFull => {
                proof {
                    assert(self@ == old(self)@);
                    assert(cache@ == old(cache)@);
                }
                return BranchSealResult::CacheFull;
            },
        };
        let ghost access_pre = if prepared { *cache } else { before_aux_fetch };
        let ghost borrowed_aux = *cache;
        let aux_slot = aux_handle.idx;
        proof {
            assert(access_pre@.inv()) by {
                if prepared {
                    assert(Cache::State::next(
                        cache0@,
                        access_pre@,
                        Cache::Label::Internal,
                    ));
                    Cache::State::inv_next(cache0@, access_pre@, Cache::Label::Internal);
                } else {
                    assert(access_pre@ == cache0@);
                }
            }
            assert(aux != root);
            assert(cache.lookup_addr_slot(&aux) == aux_slot) by {
            }
            FracCacheImpl::entry_available_preserved_except(
                before_aux_fetch,
                *cache,
                &aux,
                aux_slot,
                &root,
            );
        }
        let summary_aus = self.mini_allocator.prune_allocated_aus(
            disk_au_count,
        );
        let root_summary = summary_aus.clone();
        let aux_summary = summary_aus.clone();
        proof {
            assert(root_summary@ =~= summary_aus@) by {
                assert forall |i: int| 0 <= i < root_summary@.len()
                    implies #[trigger] root_summary@[i] == summary_aus@[i] by {}
            }
            assert(aux_summary@ =~= summary_aus@) by {
                assert forall |i: int| 0 <= i < aux_summary@.len()
                    implies #[trigger] aux_summary@[i] == summary_aus@[i] by {}
            }
        }
        let sealed_root = BranchNode::Index{
            pivots,
            children,
            aux_ptr: Some(aux),
        };
        let aux_node = BranchNode::Auxiliary{summary_aus: aux_summary};
        proof {
            assert(summary_aus.len() <= pre_stack.mini_allocator.allocators.len());
            assert(summary_aus.len() <= node_fmt.aux_fmt.max_length);
            assert(sealed_root.wf());
            assert(aux_node.wf());
            assert(node_fmt == BranchNodePageFmt::spec_new());
            bounded_index_branch_node_marshallable(&sealed_root);
            assert(node_fmt.marshallable(aux_node.parsedv()));
            assert(node_fmt.impl_marshallable(aux_node));
            assert(node_fmt.spec_size(aux_node.parsedv()) == PAGE_SIZE_BYTES);
        }
        let aux_page = marshall_branch_node_page(&aux_node);
        let root_page = marshall_branch_node_page(&sealed_root);
        let ghost aux_raw = aux_page@;
        let ghost sealed_root_raw = root_page@;
        aux_handle.rec = aux_page;
        cache.write_release(&aux, aux_handle);
        let ghost after_aux_write = *cache;
        let ghost aux_writes = map![aux@ => aux_raw];
        proof {
            FracCacheImpl::entry_available_preserved_except(
                borrowed_aux,
                after_aux_write,
                &aux,
                aux_slot,
                &root,
            );
            if prepared {
                assert(borrowed_aux@ == access_pre@);
                assert(Cache::State::next(
                    access_pre@,
                    after_aux_write@,
                    Cache::Label::Access{reads: Map::empty(), writes: aux_writes},
                ));
            } else {
                assert(access_pre@ == before_aux_fetch@);
                assert(before_aux_fetch@.valid_write(aux@));
                assert(borrowed_aux@.lookup_map == before_aux_fetch@.lookup_map);
                assert(borrowed_aux@.status_map == before_aux_fetch@.status_map);
                assert(before_aux_fetch@.lookup_map.contains_key(aux@));
                assert(before_aux_fetch@.lookup_map[aux@] == aux_slot);
                assert(before_aux_fetch@.entries
                    == borrowed_aux@.entries.insert(
                        aux_slot,
                        before_aux_fetch@.entries[aux_slot],
                    ));
                Cache::State::access_from_borrowed_write_slot(
                    before_aux_fetch@,
                    borrowed_aux@,
                    after_aux_write@,
                    Map::empty(),
                    aux@,
                    aux_slot,
                    aux_raw,
                );
            }
        }

        let ghost before_root_fetch = *cache;
        let mut root_write_handle = match cache.fetch(&root, false) {
            FetchErrorCode::Success{slot_handle} => slot_handle,
            _ => {
                proof {
                    assert(before_root_fetch.entry_available_for_fetch(&root));
                    assert(false);
                }
                return unreached::<BranchSealResult>();
            },
        };
        let root_slot = root_write_handle.idx;
        let ghost borrowed_root = *cache;
        proof {
            FracCacheImpl::valid_write_handle_model_entry(
                &borrowed_root,
                &root,
                root_write_handle,
            );
        }
        root_write_handle.rec = root_page;
        cache.write_release(&root, root_write_handle);
        let ghost root_writes = map![root@ => sealed_root_raw];
        proof {
            assert(before_root_fetch@.valid_write(root@));
            assert(borrowed_root@.lookup_map == before_root_fetch@.lookup_map);
            assert(borrowed_root@.status_map == before_root_fetch@.status_map);
            assert(before_root_fetch@.lookup_map.contains_key(root@));
            assert(before_root_fetch@.lookup_map[root@] == root_slot);
            assert(before_root_fetch@.entries
                == borrowed_root@.entries.insert(
                    root_slot,
                    before_root_fetch@.entries[root_slot],
                ));
            Cache::State::access_from_borrowed_write_slot(
                before_root_fetch@,
                borrowed_root@,
                cache@,
                Map::empty(),
                root@,
                root_slot,
                sealed_root_raw,
            );
            assert(before_root_fetch@ == after_aux_write@);
            assert(aux_writes.dom().disjoint(root_writes.dom())) by {
                assert(aux@ != root@);
            }
            Cache::State::access_compose_disjoint_writes(
                access_pre@,
                after_aux_write@,
                cache@,
                aux_writes,
                root_writes,
            );
        }
        let ghost reads = map![root@ => root_raw@];
        let ghost writes = aux_writes.union_prefer_right(root_writes);
        proof {
            assert(access_pre@.valid_read(root@, root_raw@)) by {
                if prepared {
                    assert(root@ != aux@);
                } else {
                    assert(access_pre@ == cache0@);
                }
            }
            Cache::State::access_add_reads(access_pre@, cache@, reads, writes);
        }

        let summary_for_store = root_summary;
        self.image.sealed_roots.push(root);
        let ghost pre_branch_summary = self.branch_summary.i();
        self.branch_summary.insert_or_update(root.au, summary_for_store);
        self.active_branch = None;
        self.active_store = MemBranchStore::new();
        proof {
            let summary = iau_vec_set(summary_aus@);
            iau_seq_set_matches_vec_set(summary_aus@);
            iau_seq_set_matches_to_set(aux_summary@);
            iau_seq_set_matches_vec_set(aux_summary@);
            assert(iau_vec_set(aux_summary@) =~= summary) by {
                assert forall |au: AU| #[trigger] iau_vec_set(aux_summary@).contains(au)
                    <==> summary.contains(au) by {
                    if iau_vec_set(aux_summary@).contains(au) {
                        let i = choose |i: int| 0 <= i < aux_summary@.len()
                            && #[trigger] aux_summary@[i] as nat == au;
                        assert(aux_summary@[i] == summary_aus@[i]);
                        assert(summary.contains(au));
                    }
                    if summary.contains(au) {
                        let i = choose |i: int| 0 <= i < summary_aus@.len()
                            && #[trigger] summary_aus@[i] as nat == au;
                        assert(aux_summary@[i] == summary_aus@[i]);
                        assert(iau_vec_set(aux_summary@).contains(au));
                    }
                }
            }
            assert(pre_branch_summary == pre_stack.branch_summary.i());
            assert(self.branch_summary.i()
                == pre_stack.branch_summary.i().insert(root@.au, summary));
            assert(to_branch_nodes(reads)[root@] == root_node@);
            assert(loaded_line_wf(to_branch_nodes(reads), root@));
            let seal_writes = loaded_seal_write_nodes(
                root@,
                to_branch_nodes(reads),
                Some(aux@),
                summary,
            );
            assert(raw_page_to_branch_node(aux_raw) == aux_node@);
            assert(raw_page_to_branch_node(sealed_root_raw) == sealed_root@);
            assert_maps_equal!(to_branch_nodes(writes), seal_writes, addr => {
                if addr == root@ {
                    assert(writes.contains_key(root@));
                    assert(writes[root@] == sealed_root_raw);
                    assert(sealed_root@ == SpecBranchNode::Index{
                        pivots: root_node@->pivots,
                        children: root_node@->children,
                        aux_ptr: Some(aux@),
                    });
                } else if addr == aux@ {
                    assert(writes.contains_key(aux@));
                    assert(writes[aux@] == aux_raw);
                    assert(aux_node@ == SpecBranchNode::Auxiliary(summary));
                } else {
                    assert(!writes.contains_key(addr));
                    assert(!seal_writes.contains_key(addr));
                }
            });
            let cached_lbl = CachedBranch::Label::Seal{
                mini_allocator: pre_stack.mini_allocator.i(),
                aux_ptr: Some(aux@),
                read_nodes: to_branch_nodes(reads),
                write_nodes: to_branch_nodes(writes),
            };
            assert(CachedBranch::State::next(
                pre_stack.active_branch_i(),
                pre_stack.active_branch_i(),
                cached_lbl,
            )) by {
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                assert(CachedBranch::State::seal_step(
                    pre_stack.active_branch_i(),
                    pre_stack.active_branch_i(),
                    cached_lbl,
                )) by {
                }
                assert(CachedBranch::State::next_by(
                    pre_stack.active_branch_i(),
                    pre_stack.active_branch_i(),
                    cached_lbl,
                    CachedBranch::Step::seal_step(),
                ));
            }
            let atomic_lbl = AtomicBranchState::Label::Seal{
                aux_ptr: Some(aux@),
                summary,
                read_nodes: to_branch_nodes(reads),
                write_nodes: to_branch_nodes(writes),
            };
            assert(AtomicBranchState::State::seal(pre_stack@, self@, atomic_lbl)) by {
                assert(self.image@.sealed_roots
                    == pre_stack.image@.sealed_roots.push(root@));
                assert(self.active_branch_i() == CachedBranch::State::empty_active());
                assert(self.mini_allocator.i()
                    == pre_stack.mini_allocator.i().prune(summary));
                assert(self.branch_summary.i()
                    == pre_stack.branch_summary.i().insert(root@.au, summary));
                assert(self.image@.seq_end == pre_stack.image@.seq_end);
                assert(self.seq_end == pre_stack.seq_end);
                assert(self.persisted_root_count == pre_stack.persisted_root_count);
                assert(self.commit_phase == pre_stack.commit_phase);
                assert(self.persistent_image_i() == pre_stack.persistent_image_i()) by {
                    assert(self.image.sealed_roots@.take(self.persistent_prefix_len as int)
                        == pre_stack.image.sealed_roots@.take(
                            pre_stack.persistent_prefix_len as int,
                        ));
                }
                assert(self.in_flight_i() == pre_stack.in_flight_i());
            }
            reveal(AtomicBranchState::State::next);
            reveal(AtomicBranchState::State::next_by);
            assert(AtomicBranchState::State::next_by(
                pre_stack@,
                self@,
                atomic_lbl,
                AtomicBranchState::Step::seal(),
            ));
            assert(AtomicBranchState::State::next(pre_stack@, self@, atomic_lbl));
            assert(self.wf());
        }

        if prepared {
            BranchSealResult::SealedAfterPrepare{
                root,
                aux_ptr: Some(aux),
                summary_aus,
                reads: Ghost(reads),
                writes: Ghost(writes),
                prepared_cache: Ghost(access_pre@),
            }
        } else {
            BranchSealResult::Sealed{
                root,
                aux_ptr: Some(aux),
                summary_aus,
                reads: Ghost(reads),
                writes: Ghost(writes),
            }
        }
    }

    pub fn seal(&mut self) -> (result: Result<(), BranchError>)
        requires
            old(self).wf(),
            old(self).load_state is MetadataLoaded,
            old(self).active_branch is Some ==> old(self).active_branch.unwrap().inv(&old(self).active_store),
        ensures
            result is Ok ==> self.wf(),
    {
        let branch = match self.active_branch {
            Some(branch) => branch,
            None => return Err(BranchError::Uninitialized),
        };
        let root = branch.root;
        branch.seal(&mut self.active_store, &mut self.mini_allocator)?;
        proof {
            assert(self.active_store.wf());
            assert(self.mini_allocator.wf());
        }
        self.image.sealed_roots.push(root);
        self.branch_summary.insert_or_update(root.au, Vec::new());
        self.active_branch = None;
        Ok(())
    }

    pub fn observe_persisted_roots(&mut self, target_count: usize) -> (result: Result<(), BranchError>)
        requires
            old(self).wf(),
            old(self).load_state is MetadataLoaded,
        ensures
            self.wf(),
            self.load_state == old(self).load_state,
            self.seq_end == old(self).seq_end,
            self.image == old(self).image,
            self.branch_summary == old(self).branch_summary,
            self.active_branch == old(self).active_branch,
            self.mini_allocator == old(self).mini_allocator,
            self.active_store == old(self).active_store,
            self.store == old(self).store,
            old(self).persisted_root_count <= target_count
                && target_count <= old(self).image.sealed_roots.len()
                ==> result is Ok,
            match result {
                Ok(()) => AtomicBranchState::State::next(
                    old(self)@,
                    self@,
                    AtomicBranchState::Label::ObservePersistedRoots{
                        target_count: target_count as nat,
                    },
                ),
                Err(_) => *self == *old(self),
            },
    {
        if target_count < self.persisted_root_count || target_count > self.image.sealed_roots.len() {
            return Err(BranchError::InvalidCommit);
        }
        self.persisted_root_count = target_count;
        proof {
            reveal(AtomicBranchState::State::next);
            reveal(AtomicBranchState::State::next_by);
            assert(AtomicBranchState::State::observe_persisted_roots(
                old(self)@,
                self@,
                AtomicBranchState::Label::ObservePersistedRoots{
                    target_count: target_count as nat,
                },
            )) by {
            }
            assert(AtomicBranchState::State::next_by(
                old(self)@,
                self@,
                AtomicBranchState::Label::ObservePersistedRoots{
                    target_count: target_count as nat,
                },
                AtomicBranchState::Step::observe_persisted_roots(),
            ));
        }
        Ok(())
    }

    pub fn commit_start(&mut self, prefix_len: usize, seq_end: usize) -> (result: Result<(), BranchError>)
        requires
            old(self).wf(),
            old(self).load_state is MetadataLoaded,
            old(self)@.metadata_loaded(),
        ensures
            self.wf(),
            self.load_state == old(self).load_state,
            self.image == old(self).image,
            self.persistent_prefix_len == old(self).persistent_prefix_len,
            self.persistent_seq_end == old(self).persistent_seq_end,
            self.persisted_root_count == old(self).persisted_root_count,
            self.branch_summary == old(self).branch_summary,
            self.active_branch == old(self).active_branch,
            self.mini_allocator == old(self).mini_allocator,
            self.active_store == old(self).active_store,
            self.store == old(self).store,
            self.seq_end == old(self).seq_end,
            old(self).commit_phase is Idle
                && (
                    (prefix_len == old(self).persistent_prefix_len
                        && seq_end == old(self).persistent_seq_end)
                    || (prefix_len == old(self).image.sealed_roots.len()
                        && seq_end == old(self).seq_end
                        && old(self).active_branch is None)
                )
                ==> result is Ok,
            match result {
                Ok(()) => {
                    &&& self.commit_phase == CommitPhase::InFlight {
                        prefix_len,
                        seq_end,
                        prepared: false,
                    }
                    &&& AtomicBranchState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchState::Label::CommitStart{
                            branch_image: AtomicBranchImage{
                                sealed_roots: old(self).image@.sealed_roots.take(prefix_len as int),
                                seq_end: seq_end as nat,
                            },
                        },
                    )
                },
                Err(_) => *self == *old(self),
            },
    {
        match self.commit_phase {
            CommitPhase::Idle => {},
            _ => return Err(BranchError::InvalidCommit),
        }

        if prefix_len > self.image.sealed_roots.len() || seq_end > self.seq_end {
            return Err(BranchError::InvalidCommit);
        }

        let persistent_match =
            prefix_len == self.persistent_prefix_len && seq_end == self.persistent_seq_end;
        let freeze_match =
            prefix_len == self.image.sealed_roots.len()
            && seq_end == self.seq_end
            && self.active_branch.is_none();
        if !persistent_match && !freeze_match {
            return Err(BranchError::InvalidCommit);
        }

        self.commit_phase = CommitPhase::InFlight { prefix_len, seq_end, prepared: false };
        proof {
            let branch_image = AtomicBranchImage{
                sealed_roots: old(self).image@.sealed_roots.take(prefix_len as int),
                seq_end: seq_end as nat,
            };
            reveal(AtomicBranchState::State::next);
            reveal(AtomicBranchState::State::next_by);
            assert(AtomicBranchState::State::commit_start(
                old(self)@,
                self@,
                AtomicBranchState::Label::CommitStart{branch_image},
            )) by {
                assert(old(self)@.persistent_image == old(self).persistent_image_i());
                if persistent_match {
                    assert(prefix_len == old(self).persistent_prefix_len);
                    assert(seq_end == old(self).persistent_seq_end);
                    assert(branch_image == old(self).persistent_image_i());
                    assert(branch_image == old(self)@.persistent_image);
                } else {
                    assert(freeze_match);
                    assert(prefix_len == old(self).image.sealed_roots.len());
                    assert(old(self).image@.sealed_roots.take(prefix_len as int)
                        == old(self).image@.sealed_roots);
                    assert(old(self)@.metadata_loaded());
                    assert(old(self).active_branch is None);
                    assert(old(self)@.active_branch.root is None);
                    assert(branch_image == old(self)@.freeze_image());
                }
            }
            assert(AtomicBranchState::State::next_by(
                old(self)@,
                self@,
                AtomicBranchState::Label::CommitStart{branch_image},
                AtomicBranchState::Step::commit_start(),
            ));
        }
        Ok(())
    }

    pub fn commit_prepared(&mut self) -> (result: Result<(), BranchError>)
        requires
            old(self).wf(),
            old(self).load_state is MetadataLoaded,
        ensures
            self.wf(),
            self.load_state == old(self).load_state,
            self.image == old(self).image,
            self.persistent_prefix_len == old(self).persistent_prefix_len,
            self.persistent_seq_end == old(self).persistent_seq_end,
            self.persisted_root_count == old(self).persisted_root_count,
            self.branch_summary == old(self).branch_summary,
            self.active_branch == old(self).active_branch,
            self.mini_allocator == old(self).mini_allocator,
            self.active_store == old(self).active_store,
            self.store == old(self).store,
            self.seq_end == old(self).seq_end,
            old(self).commit_phase is InFlight
                && !old(self).commit_phase->prepared
                && old(self).commit_phase->prefix_len <= old(self).persisted_root_count
                ==> result is Ok,
            match result {
                Ok(()) => {
                    &&& self.commit_phase is InFlight
                    &&& self.commit_phase->prefix_len == old(self).commit_phase->prefix_len
                    &&& self.commit_phase->seq_end == old(self).commit_phase->seq_end
                    &&& self.commit_phase->prepared
                    &&& AtomicBranchState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchState::Label::CommitPrepared,
                    )
                },
                Err(_) => *self == *old(self),
            },
    {
        match self.commit_phase {
            CommitPhase::InFlight{prefix_len, seq_end, prepared} => {
                if prepared || prefix_len > self.persisted_root_count {
                    return Err(BranchError::InvalidCommit);
                }
                self.commit_phase = CommitPhase::InFlight {
                    prefix_len,
                    seq_end,
                    prepared: true,
                };
                proof {
                    reveal(AtomicBranchState::State::next);
                    reveal(AtomicBranchState::State::next_by);
                    assert(AtomicBranchState::State::commit_prepared(
                        old(self)@,
                        self@,
                        AtomicBranchState::Label::CommitPrepared,
                    )) by {
                    }
                    assert(AtomicBranchState::State::next_by(
                        old(self)@,
                        self@,
                        AtomicBranchState::Label::CommitPrepared,
                        AtomicBranchState::Step::commit_prepared(),
                    ));
                }
                Ok(())
            },
            CommitPhase::Idle => Err(BranchError::InvalidCommit),
        }
    }

    pub fn commit_complete(&mut self) -> (result: Result<(), BranchError>)
        requires
            old(self).wf(),
            old(self).load_state is MetadataLoaded,
        ensures
            self.wf(),
            self.load_state == old(self).load_state,
            self.image == old(self).image,
            self.branch_summary == old(self).branch_summary,
            self.active_branch == old(self).active_branch,
            self.mini_allocator == old(self).mini_allocator,
            self.active_store == old(self).active_store,
            self.store == old(self).store,
            self.seq_end == old(self).seq_end,
            old(self).commit_phase is InFlight
                && old(self).commit_phase->prepared
                ==> result is Ok,
            match result {
                Ok(()) => {
                    &&& self.commit_phase is Idle
                    &&& self.persistent_prefix_len == old(self).commit_phase->prefix_len
                    &&& self.persistent_seq_end == old(self).commit_phase->seq_end
                    &&& AtomicBranchState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchState::Label::CommitComplete,
                    )
                },
                Err(_) => *self == *old(self),
            },
    {
        match self.commit_phase {
            CommitPhase::InFlight{prefix_len, seq_end, prepared} => {
                if !prepared {
                    return Err(BranchError::InvalidCommit);
                }
                if self.persisted_root_count < prefix_len {
                    self.persisted_root_count = prefix_len;
                }
                self.persistent_prefix_len = prefix_len;
                self.persistent_seq_end = seq_end;
                self.commit_phase = CommitPhase::Idle;
                proof {
                    reveal(AtomicBranchState::State::next);
                    reveal(AtomicBranchState::State::next_by);
                    assert(AtomicBranchState::State::commit_complete(
                        old(self)@,
                        self@,
                        AtomicBranchState::Label::CommitComplete,
                    )) by {
                    }
                    assert(AtomicBranchState::State::next_by(
                        old(self)@,
                        self@,
                        AtomicBranchState::Label::CommitComplete,
                        AtomicBranchState::Step::commit_complete(),
                    ));
                }
                Ok(())
            },
            CommitPhase::Idle => Err(BranchError::InvalidCommit),
        }
    }

    pub fn smoke_scenarios() -> Result<(), BranchError> {
        let image = BranchImageImpl::empty();
        let mut branch = BranchStackImpl::new(image, 0, 2);
        let aus = vec![9];
        proof {
            assert(branch.mini_allocator.allocators@.len() == 0);
            assert(MiniAllocatorImpl::allocators_unique(branch.mini_allocator.allocators@));
            assert(MiniAllocatorImpl::iau_seq_unique(aus@));
            assert(iau_vec_set(aus@).disjoint(
                MiniAllocatorImpl::allocators_au_set(branch.mini_allocator.allocators@),
            ));
        }
        branch.fill_aus(aus);
        branch.append(
            vec![Key(10), Key(20), Key(30), Key(40)],
            vec![
                Message::Define { value: Value(10) },
                Message::Define { value: Value(20) },
                Message::Define { value: Value(30) },
                Message::Define { value: Value(40) },
            ],
        )?;

        Ok(())
    }

    // -------------------------------------------------------------------------
    // Utility proofs
    // -------------------------------------------------------------------------

    pub proof fn no_in_flight_implies_commit_idle(&self)
        requires
            self.wf(),
            self.in_flight_i() is None,
        ensures
            self.commit_phase is Idle,
    {
        match self.commit_phase {
            CommitPhase::Idle => {},
            CommitPhase::InFlight{..} => {
                assert(self.in_flight_i() is Some);
                assert(false);
            },
        }
    }

    pub proof fn prepared_i_implies_commit_prepared(&self)
        requires
            self.wf(),
            self.prepared_i(),
        ensures
            self.commit_phase is InFlight,
            self.commit_phase->prepared,
    {
        match self.commit_phase {
            CommitPhase::Idle => {
                assert(!self.prepared_i());
                assert(false);
            },
            CommitPhase::InFlight{prepared, ..} => {
                assert(prepared);
            },
        }
    }
}

impl View for BranchStackImpl {
    type V = AtomicBranchState::State;

    open spec fn view(&self) -> Self::V
    {
        self.i()
    }
}

} // verus!
