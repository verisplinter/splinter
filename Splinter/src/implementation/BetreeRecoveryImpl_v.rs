// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_multisets_equal, assert_seqs_equal};
use vstd::multiset::Multiset;

use crate::disk::GenericDisk_v::{Address, Pointer};
use crate::betree::LinkedBetree_v::LinkedBetree;
use crate::allocation_layer::BranchTypes_v::BranchNode;
use crate::allocation_layer::Likes_v::{
    Likes, to_au_likes, to_au_likes_commutative_over_add,
    to_au_likes_singleton,
};
use crate::implementation::AuLikesImpl_v::{
    AuLikesImpl, AuLikesUpdateResult, iau_seq_set, seq_to_au_likes,
    unique_iau_seq,
};
use crate::implementation::BranchBetreeOwnershipImpl_v::{
    BetreeOwnershipUpdateResult, BranchBetreeOwnershipImpl,
    BranchOwnershipUpdateResult,
};
use crate::implementation::CrashAwareCachingDiskBranchBetree_v::{
    BetreeMetadataRecoveryCore, CachingDiskBranchBetreeMetadata,
    betree_buffer_roots, betree_child_addrs,
};
use crate::implementation::IBetreeNode_v::IBetreeNode;
use crate::implementation::BetreeSplitWriteImpl_v::{
    iaddr_views, iaddress_aus_likes,
};
use crate::implementation::IBranchNode_v::{
    IBranchNode, iau_seq, iau_seq_set as branch_iau_seq_set, iopt_addr,
};
use crate::marshalling::WF_v::WF;
use crate::spec::ImplDisk_t::{IAddress, IAU};

verus! {

#[derive(Debug)]
pub enum BetreeRecoveryApplyResult {
    Applied,
    Invalid,
}

#[derive(Clone, Copy, Debug)]
pub enum BetreeRecoveryNeed {
    Betree { addr: IAddress },
    BranchRoot { root: IAddress },
    BranchAux { root: IAddress, aux: IAddress },
    Complete,
}

fn validate_summary(summary: &Vec<IAU>, root_au: IAU) -> (out: bool)
    ensures
        out ==> unique_iau_seq(summary@),
        out ==> iau_seq_set(summary@).contains(root_au as nat),
{
    let mut root_found = false;
    let mut left = 0usize;
    while left < summary.len()
        invariant
            left <= summary.len(),
            root_found == exists |i: int| #![auto]
                0 <= i < left && summary@[i] == root_au,
            forall |i: int, j: int| #![trigger summary@[i], summary@[j]]
                0 <= i < left
                && 0 <= j < left
                && summary@[i] == summary@[j]
                ==> i == j,
        decreases summary.len() - left,
    {
        if summary[left] == root_au {
            root_found = true;
        }
        let mut right = 0usize;
        while right < left
            invariant
                right <= left,
                left < summary.len(),
                forall |i: int| #![trigger summary@[i]]
                    0 <= i < right ==> summary@[i] != summary@[left as int],
            decreases left - right,
        {
            if summary[right] == summary[left] {
                return false;
            }
            right += 1;
        }
        proof {
            assert forall |i: int, j: int|
                #![trigger summary@[i], summary@[j]]
                0 <= i < left + 1
                && 0 <= j < left + 1
                && summary@[i] == summary@[j]
                implies i == j by {
                if i < left && j < left {
                } else if i < left {
                    assert(j == left);
                    assert(i < right);
                } else if j < left {
                    assert(i == left);
                    assert(j < right);
                }
            }
        }
        left += 1;
    }
    if !root_found {
        return false;
    }
    proof {
        assert(unique_iau_seq(summary@));
        let i = choose |i: int| #![auto]
            0 <= i < summary@.len() && summary@[i] == root_au;
        assert(iau_seq_set(summary@).contains(root_au as nat));
    }
    true
}

proof fn summary_set_views_agree(aus: Seq<IAU>)
    ensures branch_iau_seq_set(aus) =~= iau_seq_set(aus),
{
    let mapped = Map::new(
        |i: int| 0 <= i < aus.len(),
        |i: int| aus[i] as nat,
    );
    assert forall |au: nat|
        #![trigger branch_iau_seq_set(aus).contains(au)]
        branch_iau_seq_set(aus).contains(au)
            == iau_seq_set(aus).contains(au) by {
        if branch_iau_seq_set(aus).contains(au) {
            let i = choose |i: int| #![auto]
                mapped.contains_key(i) && mapped[i] == au;
            assert(0 <= i < aus.len());
            assert(aus[i] as nat == au);
            assert(iau_seq_set(aus).contains(au));
        } else if iau_seq_set(aus).contains(au) {
            let i = choose |i: int| #![auto]
                0 <= i < aus.len() && aus[i] as nat == au;
            assert(mapped.contains_key(i));
            assert(mapped[i] == au);
            assert(exists |key: int| #![auto]
                mapped.contains_key(key) && mapped[key] == au);
            assert(branch_iau_seq_set(aus).contains(au));
        }
    }
}

proof fn mapped_summary_set_agrees(aus: Seq<IAU>)
    ensures iau_seq(aus).to_set() =~= iau_seq_set(aus),
{
    assert forall |au: nat|
        #![trigger iau_seq(aus).to_set().contains(au)]
        iau_seq(aus).to_set().contains(au)
            == iau_seq_set(aus).contains(au) by {
        if iau_seq(aus).to_set().contains(au) {
            let i = choose |i: int| #![auto]
                0 <= i < iau_seq(aus).len() && iau_seq(aus)[i] == au;
            assert(0 <= i < aus.len());
            assert(aus[i] as nat == au);
            assert(iau_seq_set(aus).contains(au));
        } else if iau_seq_set(aus).contains(au) {
            let i = choose |i: int| #![auto]
                0 <= i < aus.len() && aus[i] as nat == au;
            assert(iau_seq(aus)[i] == au);
            assert(iau_seq(aus).to_set().contains(au));
        }
    }
}

pub open spec fn child_prefix(
    node: crate::betree::LinkedBetree_v::BetreeNode,
    count: nat,
) -> Set<Address> {
    Set::new(|addr: Address| exists |i: int| #![auto]
        0 <= i < count
        && i < node.children.len()
        && node.children[i] == Option::Some(addr))
}

proof fn child_prefix_next(
    node: crate::betree::LinkedBetree_v::BetreeNode,
    count: nat,
)
    requires count < node.children.len(),
    ensures child_prefix(node, count + 1) =~= child_prefix(node, count)
        + match node.children[count as int] {
            Some(addr) => set![addr],
            None => Set::<Address>::empty(),
        },
{
    assert forall |addr: Address|
        #![trigger child_prefix(node, count + 1).contains(addr)]
        child_prefix(node, count + 1).contains(addr)
        == (child_prefix(node, count)
            + match node.children[count as int] {
                Some(child) => set![child],
                None => Set::<Address>::empty(),
            }).contains(addr) by {
        if child_prefix(node, count + 1).contains(addr) {
            let i = choose |i: int| #![auto]
                0 <= i < count + 1
                && i < node.children.len()
                && node.children[i] == Option::Some(addr);
            if i < count {
                assert(child_prefix(node, count).contains(addr));
            } else {
                assert(i == count);
            }
        } else if child_prefix(node, count).contains(addr) {
            let i = choose |i: int| #![auto]
                0 <= i < count
                && i < node.children.len()
                && node.children[i] == Option::Some(addr);
            assert(i < count + 1);
            assert(child_prefix(node, count + 1).contains(addr));
        }
    }
}

pub open spec fn buffer_prefix(
    node: crate::betree::LinkedBetree_v::BetreeNode,
    count: nat,
) -> Set<Address> {
    Set::new(|addr: Address| exists |i: int| #![auto]
        0 <= i < count
        && i < node.buffers.addrs.len()
        && node.buffers.addrs[i] == addr)
}

proof fn iaddr_views_push_ensures(addrs: Seq<IAddress>, addr: IAddress)
    ensures iaddr_views(addrs.push(addr))
        == iaddr_views(addrs).push(addr@),
{
    assert_seqs_equal!(
        iaddr_views(addrs.push(addr)),
        iaddr_views(addrs).push(addr@),
        i => { }
    );
}

proof fn unique_seq_multiset_single<A>(values: Seq<A>)
    requires
        forall |i: int, j: int| #![trigger values[i], values[j]]
            0 <= i < values.len()
            && 0 <= j < values.len()
            && values[i] == values[j]
            ==> i == j,
    ensures crate::allocation_layer::Likes_v::all_elems_single(
        values.to_multiset(),
    ),
    decreases values.len(),
{
    if values.len() == 0 {
        values.to_multiset_ensures();
        assert(values.to_multiset().len() == 0);
        assert_multisets_equal!(
            values.to_multiset(),
            Multiset::<A>::empty(),
            e => { }
        );
    } else {
        let prefix = values.drop_last();
        let last = values.last();
        assert forall |i: int, j: int|
            #![trigger prefix[i], prefix[j]]
            0 <= i < prefix.len()
            && 0 <= j < prefix.len()
            && prefix[i] == prefix[j]
            implies i == j by { }
        unique_seq_multiset_single(prefix);
        assert(!prefix.contains(last)) by {
            if prefix.contains(last) {
                let i = choose |i: int| #![auto]
                    0 <= i < prefix.len() && prefix[i] == last;
                assert(prefix[i] == values[i]);
                assert(last == values[values.len() - 1]);
                assert(i != values.len() - 1);
            }
        }
        prefix.to_multiset_ensures();
        values.to_multiset_ensures();
        crate::allocation_layer::Likes_v::singleton_all_elems_single(last);
        assert(prefix.to_multiset().dom().disjoint(
            Multiset::singleton(last).dom(),
        ));
        crate::allocation_layer::Likes_v::all_elems_single_add_disjoint(
            prefix.to_multiset(),
            Multiset::singleton(last),
        );
        assert(values == prefix.push(last));
        assert(values.to_multiset()
            == prefix.to_multiset().insert(last));
        assert(values.to_multiset()
            == prefix.to_multiset().add(Multiset::singleton(last)));
        assert(crate::allocation_layer::Likes_v::all_elems_single(
            values.to_multiset(),
        ));
    }
}

proof fn buffer_prefix_next(
    node: crate::betree::LinkedBetree_v::BetreeNode,
    count: nat,
)
    requires count < node.buffers.addrs.len(),
    ensures buffer_prefix(node, count + 1)
        =~= buffer_prefix(node, count)
            .insert(node.buffers.addrs[count as int]),
{
    assert forall |addr: Address|
        #![trigger buffer_prefix(node, count + 1).contains(addr)]
        buffer_prefix(node, count + 1).contains(addr)
        == buffer_prefix(node, count)
            .insert(node.buffers.addrs[count as int]).contains(addr) by {
        if buffer_prefix(node, count + 1).contains(addr) {
            let i = choose |i: int| #![auto]
                0 <= i < count + 1
                && i < node.buffers.addrs.len()
                && node.buffers.addrs[i] == addr;
            if i < count {
                assert(buffer_prefix(node, count).contains(addr));
            } else {
                assert(i == count);
            }
        } else if buffer_prefix(node, count).contains(addr) {
            let i = choose |i: int| #![auto]
                0 <= i < count
                && i < node.buffers.addrs.len()
                && node.buffers.addrs[i] == addr;
            assert(i < count + 1);
            assert(buffer_prefix(node, count + 1).contains(addr));
        }
    }
}

fn same_iaddr(left: &IAddress, right: &IAddress) -> (out: bool)
    ensures out == (left@ == right@),
{
    left.au == right.au && left.page == right.page
}

pub struct RecoveryAddressSet {
    pub entries: Vec<IAddress>,
}

impl RecoveryAddressSet {
    pub open spec fn unique(entries: Seq<IAddress>) -> bool {
        forall |i: int, j: int| #![trigger entries[i]@, entries[j]@]
            0 <= i < entries.len()
            && 0 <= j < entries.len()
            && entries[i]@ == entries[j]@
            ==> i == j
    }

    pub open spec fn entries_set(entries: Seq<IAddress>) -> Set<Address> {
        Set::new(|addr: Address| exists |i: int| #![auto]
            0 <= i < entries.len() && entries[i]@ == addr)
    }

    pub open spec fn wf(&self) -> bool {
        Self::unique(self.entries@)
    }

    pub fn new() -> (out: Self)
        ensures
            out.wf(),
            out.entries@ == Seq::<IAddress>::empty(),
            out@ =~= Set::<Address>::empty(),
    {
        Self { entries: Vec::new() }
    }

    pub fn from_pointer(root: Option<IAddress>) -> (out: Self)
        ensures
            out.wf(),
            out@ =~= match root {
                Some(addr) => set![addr@],
                None => Set::<Address>::empty(),
            },
    {
        match root {
            Some(addr) => {
                let mut entries = Vec::new();
                entries.push(addr);
                let out = Self { entries };
                proof {
                    assert(out.wf());
                    assert(out@ =~= set![addr@]) by {
                        assert forall |candidate: Address|
                            #![trigger out@.contains(candidate)]
                            out@.contains(candidate) == (candidate == addr@) by {
                            if out@.contains(candidate) {
                                let i = choose |i: int| #![auto]
                                    0 <= i < out.entries@.len()
                                    && out.entries@[i]@ == candidate;
                                assert(i == 0);
                                assert(out.entries@[i] == addr);
                                assert(candidate == addr@);
                            } else if candidate == addr@ {
                                assert(out.entries@[0] == addr);
                                assert(exists |i: int| #![auto]
                                    0 <= i < out.entries@.len()
                                    && out.entries@[i]@ == candidate);
                            }
                        }
                    }
                }
                out
            },
            None => Self::new(),
        }
    }

    pub fn contains(&self, addr: &IAddress) -> (out: bool)
        requires self.wf(),
        ensures out == self@.contains(addr@),
    {
        let mut index = 0usize;
        while index < self.entries.len()
            invariant
                self.wf(),
                index <= self.entries.len(),
                forall |i: int| #![auto]
                    0 <= i < index ==> self.entries@[i]@ != addr@,
            decreases self.entries.len() - index,
        {
            if same_iaddr(&self.entries[index], addr) {
                return true;
            }
            index += 1;
        }
        proof {
            assert(!self@.contains(addr@)) by {
                if self@.contains(addr@) {
                    let i = choose |i: int| #![auto]
                        0 <= i < self.entries@.len()
                        && self.entries@[i]@ == addr@;
                    assert(i < index);
                }
            }
        }
        false
    }

    pub fn insert(&mut self, addr: IAddress) -> (inserted: bool)
        requires old(self).wf(),
        ensures
            self.wf(),
            inserted == !old(self)@.contains(addr@),
            self@ =~= old(self)@.insert(addr@),
            inserted ==> self.entries@ == old(self).entries@.push(addr),
            !inserted ==> self.entries@ == old(self).entries@,
    {
        if self.contains(&addr) {
            return false;
        }
        let ghost old_entries = self.entries@;
        self.entries.push(addr);
        proof {
            assert(self.entries@ == old_entries.push(addr));
            assert(self.wf()) by {
                assert forall |i: int, j: int|
                    #![trigger self.entries@[i]@, self.entries@[j]@]
                    0 <= i < self.entries@.len()
                    && 0 <= j < self.entries@.len()
                    && self.entries@[i]@ == self.entries@[j]@
                    implies i == j by {
                    if i < old_entries.len() && j < old_entries.len() {
                    } else if i < old_entries.len() {
                        assert(j == old_entries.len());
                        assert(old(self)@.contains(addr@));
                    } else if j < old_entries.len() {
                        assert(i == old_entries.len());
                        assert(old(self)@.contains(addr@));
                    }
                }
            }
            assert(self@ =~= old(self)@.insert(addr@)) by {
                assert forall |candidate: Address|
                    #![trigger self@.contains(candidate)]
                    self@.contains(candidate)
                    == old(self)@.insert(addr@).contains(candidate) by {
                    if self@.contains(candidate) {
                        let i = choose |i: int| #![auto]
                            0 <= i < self.entries@.len()
                            && self.entries@[i]@ == candidate;
                        if i < old_entries.len() {
                            assert(self.entries@[i] == old_entries[i]);
                            assert(exists |old_i: int| #![auto]
                                0 <= old_i < old_entries.len()
                                && old_entries[old_i]@ == candidate);
                            assert(old(self)@.contains(candidate));
                        } else {
                            assert(i == old_entries.len());
                            assert(self.entries@[i] == addr);
                            assert(candidate == addr@);
                        }
                    } else if old(self)@.insert(addr@).contains(candidate) {
                        if candidate == addr@ {
                            assert(self.entries@[old_entries.len() as int] == addr);
                            assert(exists |i: int| #![auto]
                                0 <= i < self.entries@.len()
                                && self.entries@[i]@ == candidate);
                        } else {
                            assert(old(self)@.contains(candidate));
                            let i = choose |i: int| #![auto]
                                0 <= i < old_entries.len()
                                && old_entries[i]@ == candidate;
                            assert(self.entries@[i] == old_entries[i]);
                            assert(exists |new_i: int| #![auto]
                                0 <= new_i < self.entries@.len()
                                && self.entries@[new_i]@ == candidate);
                        }
                    }
                }
            }
        }
        true
    }

    pub fn remove(&mut self, addr: &IAddress) -> (removed: bool)
        requires old(self).wf(),
        ensures
            self.wf(),
            removed == old(self)@.contains(addr@),
            self@ =~= old(self)@.remove(addr@),
    {
        let ghost old_entries = self.entries@;
        let mut index = 0usize;
        while index < self.entries.len()
            invariant
                self.wf(),
                self.entries@ == old_entries,
                index <= self.entries.len(),
                forall |i: int| #![auto]
                    0 <= i < index ==> self.entries@[i]@ != addr@,
            decreases self.entries.len() - index,
        {
            if same_iaddr(&self.entries[index], addr) {
                self.entries.remove(index);
                proof {
                    assert(self.wf()) by {
                        assert forall |i: int, j: int|
                            #![trigger self.entries@[i]@, self.entries@[j]@]
                            0 <= i < self.entries@.len()
                            && 0 <= j < self.entries@.len()
                            && self.entries@[i]@ == self.entries@[j]@
                            implies i == j by {
                            let old_i = if i < index { i } else { i + 1 };
                            let old_j = if j < index { j } else { j + 1 };
                            assert(self.entries@[i] == old_entries[old_i]);
                            assert(self.entries@[j] == old_entries[old_j]);
                            assert(old_i == old_j);
                        }
                    }
                    assert(self@ =~= old(self)@.remove(addr@)) by {
                        assert forall |candidate: Address|
                            #![trigger self@.contains(candidate)]
                            self@.contains(candidate)
                            == old(self)@.remove(addr@).contains(candidate) by {
                            if self@.contains(candidate) {
                                let i = choose |i: int| #![auto]
                                    0 <= i < self.entries@.len()
                                    && self.entries@[i]@ == candidate;
                                let old_i = if i < index { i } else { i + 1 };
                                assert(self.entries@[i] == old_entries[old_i]);
                                assert(candidate != addr@);
                            } else if old(self)@.contains(candidate)
                                && candidate != addr@
                            {
                                let old_i = choose |i: int| #![auto]
                                    0 <= i < old_entries.len()
                                    && old_entries[i]@ == candidate;
                                assert(old_i != index);
                                let i = if old_i < index { old_i } else { old_i - 1 };
                                assert(self.entries@[i] == old_entries[old_i]);
                            }
                        }
                    }
                }
                return true;
            }
            index += 1;
        }
        proof {
            assert(!old(self)@.contains(addr@)) by {
                if old(self)@.contains(addr@) {
                    let i = choose |i: int| #![auto]
                        0 <= i < old_entries.len()
                        && old_entries[i]@ == addr@;
                    assert(i < index);
                }
            }
            assert(self@ =~= old(self)@.remove(addr@));
        }
        false
    }
}

impl View for RecoveryAddressSet {
    type V = Set<Address>;

    open spec fn view(&self) -> Self::V {
        Self::entries_set(self.entries@)
    }
}

pub struct RecoveryAddressMap {
    pub entries: Vec<(IAddress, IAddress)>,
}

impl RecoveryAddressMap {
    pub open spec fn unique_keys(entries: Seq<(IAddress, IAddress)>) -> bool {
        forall |i: int, j: int| #![trigger entries[i].0@, entries[j].0@]
            0 <= i < entries.len()
            && 0 <= j < entries.len()
            && entries[i].0@ == entries[j].0@
            ==> i == j
    }

    pub open spec fn entries_map(
        entries: Seq<(IAddress, IAddress)>,
    ) -> Map<Address, Address>
        recommends Self::unique_keys(entries)
    {
        Map::new(
            |key: Address| exists |i: int| #![auto]
                0 <= i < entries.len() && entries[i].0@ == key,
            |key: Address| entries[choose |i: int| #![auto]
                0 <= i < entries.len() && entries[i].0@ == key].1@,
        )
    }

    pub open spec fn wf(&self) -> bool {
        Self::unique_keys(self.entries@)
    }

    pub fn new() -> (out: Self)
        ensures
            out.wf(),
            out@ == Map::<Address, Address>::empty(),
    {
        let out = Self { entries: Vec::new() };
        proof {
            assert_maps_equal!(out@, Map::<Address, Address>::empty(), key => { });
        }
        out
    }

    pub fn get(&self, key: &IAddress) -> (out: Option<IAddress>)
        requires self.wf(),
        ensures
            (out is Some) == self@.contains_key(key@),
            out is Some ==> out.unwrap()@ == self@[key@],
    {
        let mut index = 0usize;
        while index < self.entries.len()
            invariant
                self.wf(),
                index <= self.entries.len(),
                forall |i: int| #![auto]
                    0 <= i < index ==> self.entries@[i].0@ != key@,
            decreases self.entries.len() - index,
        {
            if same_iaddr(&self.entries[index].0, key) {
                proof {
                    let chosen = choose |i: int| #![auto]
                        0 <= i < self.entries@.len()
                        && self.entries@[i].0@ == key@;
                    assert(chosen == index);
                }
                return Some(self.entries[index].1);
            }
            index += 1;
        }
        proof {
            assert(!self@.contains_key(key@)) by {
                if self@.contains_key(key@) {
                    let i = choose |i: int| #![auto]
                        0 <= i < self.entries@.len()
                        && self.entries@[i].0@ == key@;
                    assert(i < index);
                }
            }
        }
        None
    }

    pub fn insert_fresh(
        &mut self,
        key: IAddress,
        value: IAddress,
    ) -> (inserted: bool)
        requires old(self).wf(),
        ensures
            self.wf(),
            inserted == !old(self)@.contains_key(key@),
            self@ == if inserted {
                old(self)@.insert(key@, value@)
            } else {
                old(self)@
            },
    {
        if self.get(&key).is_some() {
            return false;
        }
        let ghost old_entries = self.entries@;
        self.entries.push((key, value));
        proof {
            assert(self.entries@ == old_entries.push((key, value)));
            assert(self.wf()) by {
                assert forall |i: int, j: int|
                    #![trigger self.entries@[i].0@, self.entries@[j].0@]
                    0 <= i < self.entries@.len()
                    && 0 <= j < self.entries@.len()
                    && self.entries@[i].0@ == self.entries@[j].0@
                    implies i == j by {
                    if i < old_entries.len() && j < old_entries.len() {
                    } else if i < old_entries.len() {
                        assert(j == old_entries.len());
                        assert(old(self)@.contains_key(key@));
                    } else if j < old_entries.len() {
                        assert(i == old_entries.len());
                        assert(old(self)@.contains_key(key@));
                    }
                }
            }
            assert_maps_equal!(
                self@,
                old(self)@.insert(key@, value@),
                candidate => {
                    if self@.contains_key(candidate) {
                        let i = choose |i: int| #![auto]
                            0 <= i < self.entries@.len()
                            && self.entries@[i].0@ == candidate;
                        if i == old_entries.len() {
                            assert(candidate == key@);
                        } else {
                            assert(self.entries@[i] == old_entries[i]);
                        }
                    }
                    if old(self)@.contains_key(candidate) {
                        let old_i = choose |i: int| #![auto]
                            0 <= i < old_entries.len()
                            && old_entries[i].0@ == candidate;
                        assert(self.entries@[old_i] == old_entries[old_i]);
                        assert(exists |i: int| #![auto]
                            0 <= i < self.entries@.len()
                            && self.entries@[i].0@ == candidate);
                    } else if candidate == key@ {
                        assert(self.entries@[old_entries.len() as int]
                            == (key, value));
                        assert(exists |i: int| #![auto]
                            0 <= i < self.entries@.len()
                            && self.entries@[i].0@ == candidate);
                    }
                }
            );
        }
        true
    }

    pub fn remove(&mut self, key: &IAddress) -> (out: Option<IAddress>)
        requires old(self).wf(),
        ensures
            self.wf(),
            (out is Some) == old(self)@.contains_key(key@),
            out is Some ==> out.unwrap()@ == old(self)@[key@],
            self@ == old(self)@.remove(key@),
    {
        let ghost old_entries = self.entries@;
        let mut index = 0usize;
        while index < self.entries.len()
            invariant
                self.wf(),
                self.entries@ == old_entries,
                index <= self.entries.len(),
                forall |i: int| #![auto]
                    0 <= i < index ==> self.entries@[i].0@ != key@,
            decreases self.entries.len() - index,
        {
            if same_iaddr(&self.entries[index].0, key) {
                let removed = self.entries.remove(index);
                proof {
                    assert(removed == old_entries[index as int]);
                    assert(self.wf()) by {
                        assert forall |i: int, j: int|
                            #![trigger self.entries@[i].0@, self.entries@[j].0@]
                            0 <= i < self.entries@.len()
                            && 0 <= j < self.entries@.len()
                            && self.entries@[i].0@ == self.entries@[j].0@
                            implies i == j by {
                            let old_i = if i < index { i } else { i + 1 };
                            let old_j = if j < index { j } else { j + 1 };
                            assert(self.entries@[i] == old_entries[old_i]);
                            assert(self.entries@[j] == old_entries[old_j]);
                            assert(old_i == old_j);
                        }
                    }
                    assert_maps_equal!(
                        self@,
                        old(self)@.remove(key@),
                        candidate => {
                            if self@.contains_key(candidate) {
                                let i = choose |i: int| #![auto]
                                    0 <= i < self.entries@.len()
                                    && self.entries@[i].0@ == candidate;
                                let old_i = if i < index { i } else { i + 1 };
                                assert(self.entries@[i] == old_entries[old_i]);
                                assert(candidate != key@);
                            }
                            if old(self)@.contains_key(candidate)
                                && candidate != key@
                            {
                                let old_i = choose |i: int| #![auto]
                                    0 <= i < old_entries.len()
                                    && old_entries[i].0@ == candidate;
                                assert(old_i != index);
                                let i = if old_i < index { old_i } else { old_i - 1 };
                                assert(self.entries@[i] == old_entries[old_i]);
                            }
                        }
                    );
                }
                return Some(removed.1);
            }
            index += 1;
        }
        proof {
            assert(!old(self)@.contains_key(key@)) by {
                if old(self)@.contains_key(key@) {
                    let i = choose |i: int| #![auto]
                        0 <= i < old_entries.len()
                        && old_entries[i].0@ == key@;
                    assert(i < index);
                }
            }
            assert(self@ == old(self)@.remove(key@));
        }
        None
    }
}

impl View for RecoveryAddressMap {
    type V = Map<Address, Address>;

    open spec fn view(&self) -> Self::V {
        Self::entries_map(self.entries@)
    }
}

pub struct BetreeRecoveryImpl {
    pub core: Ghost<BetreeMetadataRecoveryCore>,
    pub root: Option<IAddress>,
    pub pending_betree: RecoveryAddressSet,
    pub loaded_betree: RecoveryAddressSet,
    pub branch_roots: RecoveryAddressSet,
    pub pending_branch_roots: RecoveryAddressSet,
    pub pending_branch_aux: RecoveryAddressMap,
    pub ownership: BranchBetreeOwnershipImpl,
    pub branch_likes: AuLikesImpl,
}

impl BetreeRecoveryImpl {
    pub open spec fn root_wf(&self) -> bool {
        match self.root {
            Some(root) => root@.wf(),
            None => true,
        }
    }

    pub open spec fn loaded_betree_likes(&self) -> Likes {
        iaddr_views(self.loaded_betree.entries@).to_multiset()
    }

    pub proof fn loaded_betree_likes_dom(&self)
        requires self.loaded_betree.wf(),
        ensures self.loaded_betree_likes().dom()
            =~= self.loaded_betree@,
    {
        let views = iaddr_views(self.loaded_betree.entries@);
        views.to_multiset_ensures();
        assert forall |i: int| 0 <= i < views.len()
            implies #[trigger] views[i]
                == self.loaded_betree.entries@[i]@ by { }
        assert forall |addr: Address|
            #![trigger self.loaded_betree_likes().dom().contains(addr)]
            self.loaded_betree_likes().dom().contains(addr)
                == self.loaded_betree@.contains(addr) by {
            if self.loaded_betree_likes().dom().contains(addr) {
                assert(self.loaded_betree_likes().contains(addr));
                let i = choose |i: int| #![auto]
                    0 <= i < views.len() && views[i] == addr;
                assert(self.loaded_betree.entries@[i]@ == addr);
            } else if self.loaded_betree@.contains(addr) {
                let i = choose |i: int| #![auto]
                    0 <= i < self.loaded_betree.entries@.len()
                    && self.loaded_betree.entries@[i]@ == addr;
                assert(views[i] == addr);
                assert(views.contains(addr));
                assert(self.loaded_betree_likes().contains(addr));
            }
        }
    }

    pub proof fn loaded_betree_likes_all_single(&self)
        requires self.loaded_betree.wf(),
        ensures crate::allocation_layer::Likes_v::all_elems_single(
            self.loaded_betree_likes(),
        ),
    {
        let views = iaddr_views(self.loaded_betree.entries@);
        assert forall |i: int, j: int| #![trigger views[i], views[j]]
            0 <= i < views.len()
            && 0 <= j < views.len()
            && views[i] == views[j]
            implies i == j by {
            assert(views[i] == self.loaded_betree.entries@[i]@);
            assert(views[j] == self.loaded_betree.entries@[j]@);
        }
        unique_seq_multiset_single(views);
    }

    pub open spec fn recovered_likes_tree(&self)
        -> LinkedBetree<BranchNode>
    {
        self@.recovered_likes_tree(CachingDiskBranchBetreeMetadata {
            root: iopt_addr(self.root),
            seq_end: 0,
        })
    }

    pub open spec fn loaded_branch_likes(&self) -> Likes {
        self.recovered_likes_tree().buffer_likes(
            self.loaded_betree_likes(),
        )
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.pending_betree.wf()
        &&& self.loaded_betree.wf()
        &&& self.branch_roots.wf()
        &&& self.pending_branch_roots.wf()
        &&& self.pending_branch_aux.wf()
        &&& self.ownership.wf()
        &&& self.branch_likes.wf()
        &&& self.branch_likes.bucket_count
            == self.ownership.betree.active.bucket_count
        &&& self.pending_betree@ == self@.pending_betree
        &&& self.loaded_betree@ == self@.betree_nodes.dom()
        &&& self.pending_betree@.disjoint(self.loaded_betree@)
        &&& self.branch_roots@ == self@.branch_roots
        &&& self.pending_branch_roots@ == self@.pending_branch_roots
        &&& self.pending_branch_roots@ <= self.branch_roots@
        &&& self.pending_branch_aux@ == self@.pending_branch_aux
        &&& self.pending_branch_aux@.dom() <= self.branch_roots@
        &&& self.ownership.branches@ == self@.branch_summary
        &&& self.ownership.betree.persistent_aus()
            == self.ownership.betree.active_aus()
        &&& self.ownership.branches.persistent_aus()
            == self.ownership.branches.active_summary_aus()
        &&& self.ownership.betree.frozen_aus().is_empty()
        &&& self.ownership.branches.frozen_aus().is_empty()
        &&& self.ownership.betree@ == to_au_likes(
            self.loaded_betree_likes(),
        )
        &&& self.branch_likes@ == to_au_likes(
            self.loaded_branch_likes(),
        )
    }

    pub open spec fn completion_matches(
        &self,
        metadata: CachingDiskBranchBetreeMetadata,
    ) -> bool {
        &&& self.wf()
        &&& self@.complete()
        &&& self.ownership.betree@ == self@.betree_aus(metadata)
        &&& self.branch_likes@ == self@.branch_aus(metadata)
        &&& self.branch_likes@.dom()
            == self.ownership.branches@.dom()
        &&& self.ownership.persistent_aus()
            == self@.loaded_betree(metadata).durable_aus()
    }

    pub proof fn completion_matches_from_semantic_recovery(
        &self,
        metadata: CachingDiskBranchBetreeMetadata,
        recovery: crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::BetreeMetadataRecovery,
        image: crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::CachingDiskBranchBetreeImage,
    )
        requires
            self.wf(),
            iopt_addr(self.root) == metadata.root,
            self@ == recovery.core(),
            metadata == image.metadata,
            recovery.refinement_inv(image),
            recovery.complete(),
        ensures self.completion_matches(metadata),
    {
        crate::implementation::
            CrashAwareCachingDiskBranchBetreeRefinement_v::
                recovery_core_loaded_betree_matches(recovery, image);
        assert(self@.loaded_betree(metadata)
            == recovery.loaded_state(image).betree);
        self.loaded_betree_likes_dom();
        self.loaded_betree_likes_all_single();
        let tree = self@.recovered_likes_tree(metadata);
        assert(tree == self.recovered_likes_tree());
        assert(tree.acyclic());
        tree.tree_likes_all_elems_single(tree.the_ranking());
        tree.tree_likes_domain(tree.the_ranking());
        let tree_likes = tree.tree_likes(tree.the_ranking());
        assert(self.loaded_betree_likes().dom()
            == tree_likes.dom());
        assert forall |addr: Address|
            #[trigger] self.loaded_betree_likes().contains(addr)
            == tree_likes.contains(addr) by {
            assert(self.loaded_betree_likes().dom().contains(addr)
                == tree_likes.dom().contains(addr));
        }
        assert_multisets_equal!(
            self.loaded_betree_likes(),
            tree_likes,
            addr => {
                if self.loaded_betree_likes().contains(addr) {
                    assert(tree_likes.contains(addr));
                    assert(crate::allocation_layer::Likes_v::
                        all_elems_single(self.loaded_betree_likes()));
                    assert(crate::allocation_layer::Likes_v::
                        all_elems_single(tree_likes));
                    assert(self.loaded_betree_likes().count(addr) == 1);
                    assert(tree_likes.count(addr) == 1);
                } else {
                    assert(!tree_likes.contains(addr));
                    assert(self.loaded_betree_likes().count(addr) == 0);
                    assert(tree_likes.count(addr) == 0);
                }
            }
        );





        assert(self.ownership.betree@
            == self@.betree_aus(metadata));
        assert(self.branch_likes@
            == self@.branch_aus(metadata));
        crate::implementation::
            CrashAwareCachingDiskBranchBetreeRefinement_v::
                recovery_complete_witness_valid(recovery, image);
        let recovered = crate::implementation::
            CrashAwareCachingDiskBranchBetreeRefinement_v::
                RecoveredCachingDiskBranchBetreeMetadata {
                    betree_aus: recovery.betree_aus(image),
                    branch_aus: recovery.branch_aus(image),
                    branch_summary: recovery.branch_summary,
                    initial_betree: recovery.initial_betree(image),
                };


        let initial = recovered.initial_betree;
        let target = crate::implementation::
            CachingDiskBranchBetreeRefinement_v::initial_allocation_state(
                initial,
                recovered.betree_aus,
                recovered.branch_aus,
                recovered.branch_summary,
            );

        let branch_likes = initial.linked.transitive_likes().1;
        crate::allocation_layer::Likes_v::to_au_likes_domain(
            branch_likes,
        );
        initial.linked.buffer_dv.build_branch_domain(
            branch_likes.dom(),
        );
        assert(target.branch_aus.dom()
            == target.branch_summary.dom());
        assert(self.branch_likes@.dom()
            == self.ownership.branches@.dom());

        self.ownership.current_durable_matches_views(
            self.branch_likes@,
        );
        assert(self.ownership.persistent_aus()
            =~= self.ownership.current_durable_aus()) by {
            assert forall |au|
                #[trigger] self.ownership.persistent_aus().contains(au)
                == self.ownership.current_durable_aus().contains(au) by { }
        }

        assert(self.ownership.persistent_aus()
            == self@.loaded_betree(metadata).durable_aus());
        assert(self.completion_matches(metadata));
    }

    pub proof fn completion_loaded_betree_matches(
        &self,
        metadata: CachingDiskBranchBetreeMetadata,
    )
        requires self.completion_matches(metadata),
        ensures
            self@.loaded_betree(metadata)
                == (crate::implementation::CachedBranchBetree_v::CachedBranchBetree::State {
                    root: metadata.root,
                    memtable: crate::betree::Memtable_v::Memtable::empty_memtable(
                        metadata.seq_end,
                    ),
                    betree_aus: self.ownership.betree@,
                    branch_aus: self.branch_likes@,
                    branch_summary: self.ownership.branches@,
                    compactors: Seq::empty(),
                    compactor_receipts: Seq::empty(),
                    wip_branches: Seq::empty(),
                }),
    {

    }

    pub fn next_need(&self) -> (out: BetreeRecoveryNeed)
        requires self.wf(),
        ensures match out {
            BetreeRecoveryNeed::Betree { addr } => {
                self@.pending_betree.contains(addr@)
            },
            BetreeRecoveryNeed::BranchRoot { root } => {
                self@.pending_branch_roots.contains(root@)
            },
            BetreeRecoveryNeed::BranchAux { root, aux } => {
                &&& self@.pending_branch_aux.contains_key(root@)
                &&& self@.pending_branch_aux[root@] == aux@
            },
            BetreeRecoveryNeed::Complete => self@.complete(),
        },
    {
        if self.pending_betree.entries.len() > 0 {
            return BetreeRecoveryNeed::Betree {
                addr: self.pending_betree.entries[0],
            };
        }
        if self.pending_branch_roots.entries.len() > 0 {
            return BetreeRecoveryNeed::BranchRoot {
                root: self.pending_branch_roots.entries[0],
            };
        }
        if self.pending_branch_aux.entries.len() > 0 {
            return BetreeRecoveryNeed::BranchAux {
                root: self.pending_branch_aux.entries[0].0,
                aux: self.pending_branch_aux.entries[0].1,
            };
        }
        proof {
            assert(self.pending_betree@.is_empty()) by {
                assert forall |addr: Address|
                    #![trigger self.pending_betree@.contains(addr)]
                    !self.pending_betree@.contains(addr) by {
                    if self.pending_betree@.contains(addr) {
                        let i = choose |i: int| #![auto]
                            0 <= i < self.pending_betree.entries@.len()
                            && self.pending_betree.entries@[i]@ == addr;
                        assert(false);
                    }
                }
            }
            assert(self.pending_branch_roots@.is_empty()) by {
                assert forall |addr: Address|
                    #![trigger self.pending_branch_roots@.contains(addr)]
                    !self.pending_branch_roots@.contains(addr) by {
                    if self.pending_branch_roots@.contains(addr) {
                        let i = choose |i: int| #![auto]
                            0 <= i < self.pending_branch_roots.entries@.len()
                            && self.pending_branch_roots.entries@[i]@ == addr;
                        assert(false);
                    }
                }
            }
            assert(self.pending_branch_aux@.dom().is_empty()) by {
                assert forall |root: Address|
                    #![trigger self.pending_branch_aux@.dom().contains(root)]
                    !self.pending_branch_aux@.dom().contains(root) by {
                    if self.pending_branch_aux@.dom().contains(root) {
                        let i = choose |i: int| #![auto]
                            0 <= i < self.pending_branch_aux.entries@.len()
                            && self.pending_branch_aux.entries@[i].0@ == root;
                        assert(false);
                    }
                }
            }
        }
        BetreeRecoveryNeed::Complete
    }

    pub fn read_betree(
        &mut self,
        addr: IAddress,
        node: IBetreeNode,
    ) -> (result: BetreeRecoveryApplyResult)
        requires
            old(self).wf(),
            node.wf(),
        ensures
            self.wf(),
            self.root == old(self).root,
            self.ownership.betree.active.bucket_count
                == old(self).ownership.betree.active.bucket_count,
            self.branch_likes.bucket_count
                == old(self).branch_likes.bucket_count,
            match result {
                BetreeRecoveryApplyResult::Applied => {
                    &&& old(self)@.pending_betree.contains(addr@)
                    &&& self@ == old(self)@.read_betree(addr@, node@)
                },
                BetreeRecoveryApplyResult::Invalid => self@ == old(self)@,
            },
    {
        if !self.pending_betree.contains(&addr)
            || self.loaded_betree.contains(&addr)
        {
            return BetreeRecoveryApplyResult::Invalid;
        }
        let betree_owned = self.ownership.betree.contains_owned_au(addr.au);
        let branch_owned = self.ownership.branches.contains_owned_au(addr.au);
        if betree_owned || branch_owned {
            return BetreeRecoveryApplyResult::Invalid;
        }

        let ghost node_view = node@;
        let ghost old_core = self@;
        let ghost initial_root = self.root;
        let saved_root = self.root;
        let ghost initial_pending = self.pending_betree@;
        let ghost initial_loaded = self.loaded_betree@;
        let ghost initial_branch_roots = self.branch_roots@;
        let ghost initial_pending_branch_roots = self.pending_branch_roots@;
        let ghost initial_loaded_likes = self.loaded_betree_likes();
        let ghost initial_loaded_branch_likes = self.loaded_branch_likes();
        let ghost initial_branch_au_likes = self.branch_likes@;
        let ghost initial_recovered_tree = self.recovered_likes_tree();
        let ghost initial_betree_owner = self.ownership.betree;
        let ghost initial_betree_ownership = self.ownership.betree@;
        let ghost initial_loaded_entries = self.loaded_betree.entries@;
        proof {
            self.loaded_betree_likes_dom();
            assert(initial_loaded_likes.dom()
                <= initial_recovered_tree.dv.entries.dom());
        }
        let initial_ownership_bucket_count = self.ownership.betree.active.bucket_count;
        let initial_likes_bucket_count = self.branch_likes.bucket_count;

        let mut buffer_aus = Vec::<IAU>::new();
        let mut au_index = 0usize;
        while au_index < node.buffers.len()
            invariant
                au_index <= node.buffers.len(),
                buffer_aus@.len() == au_index,
                forall |i: int| #![trigger buffer_aus@[i]]
                    0 <= i < au_index
                    ==> buffer_aus@[i] == node.buffers@[i].au,
            decreases node.buffers.len() - au_index,
        {
            buffer_aus.push(node.buffers[au_index].au);
            au_index += 1;
        }
        let empty_removes = Vec::<IAU>::new();
        let likes_result = self.branch_likes.apply_delta(
            &empty_removes,
            &buffer_aus,
        );
        match likes_result {
            AuLikesUpdateResult::Applied { became_zero: _ } => { },
            AuLikesUpdateResult::Noop => {
                return BetreeRecoveryApplyResult::Invalid;
            },
        }
        proof {
            assert(self.branch_likes@
                == old(self).branch_likes@.add(seq_to_au_likes(buffer_aus@)));
        }

        let mut recovered_aus = Vec::<IAU>::new();
        recovered_aus.push(addr.au);
        proof {
            assert(recovered_aus@ == seq![addr.au]);
            assert(unique_iau_seq(recovered_aus@));
            assert(iau_seq_set(recovered_aus@) =~= set![addr.au as nat]) by {
                assert forall |au: nat|
                    #![trigger iau_seq_set(recovered_aus@).contains(au)]
                    iau_seq_set(recovered_aus@).contains(au)
                        == (au == addr.au as nat) by {
                    if iau_seq_set(recovered_aus@).contains(au) {
                        let i = choose |i: int| #![auto]
                            0 <= i < recovered_aus@.len()
                            && recovered_aus@[i] as nat == au;
                        assert(i == 0);
                    } else if au == addr.au as nat {
                        assert(recovered_aus@[0] == addr.au);
                        assert(exists |i: int| #![auto]
                            0 <= i < recovered_aus@.len()
                            && recovered_aus@[i] as nat == au);
                    }
                }
            }
        }
        let installed = self.ownership.betree.install_recovered(&recovered_aus);
        match installed {
            BetreeOwnershipUpdateResult::Applied { reclaimed: _ } => { },
            BetreeOwnershipUpdateResult::Noop => {
                proof { assert(false); }
                return BetreeRecoveryApplyResult::Invalid;
            },
        }
        proof {
            initial_betree_owner.view_domain_matches_active();
            self.ownership.betree.view_domain_matches_active();
            assert(self.ownership.betree.active_aus()
                =~= initial_betree_owner.active_aus().insert(addr@.au));
            assert_multisets_equal!(
                self.ownership.betree@,
                initial_betree_ownership.insert(addr@.au),
                au => {
                    self.ownership.betree.view_count_matches_active(au);
                    initial_betree_owner.view_count_matches_active(au);
                }
            );
            assert(self.ownership.wf()) by {
                assert(self.ownership.betree.all_aus().disjoint(
                    self.ownership.branches.all_summary_aus(),
                )) by {
                    assert forall |au: nat|
                        #[trigger] self.ownership.betree.all_aus().contains(au)
                        implies !self.ownership.branches
                            .all_summary_aus().contains(au) by { }
                }
            }
        }

        let loaded_inserted = self.loaded_betree.insert(addr);
        let pending_removed = self.pending_betree.remove(&addr);
        proof {
            assert(loaded_inserted);
            assert(pending_removed);
            assert(self.loaded_betree@
                =~= initial_loaded.insert(addr@));
            assert(self.pending_betree@
                =~= initial_pending.remove(addr@));
            assert(self.loaded_betree.entries@
                == initial_loaded_entries.push(addr));
        }

        let mut child_index = 0usize;
        while child_index < node.children.len()
            invariant
                self.pending_betree.wf(),
                self.loaded_betree.wf(),
                self.branch_roots.wf(),
                self.pending_branch_roots.wf(),
                self.pending_branch_aux.wf(),
                self.ownership.wf(),
                self.ownership.betree.persistent_aus()
                    == self.ownership.betree.active_aus(),
                self.ownership.branches.persistent_aus()
                    == self.ownership.branches.active_summary_aus(),
                self.ownership.betree.frozen_aus().is_empty(),
                self.ownership.branches.frozen_aus().is_empty(),
                self.branch_likes.wf(),
                self.ownership.betree.active.bucket_count
                    == initial_ownership_bucket_count,
                self.branch_likes.bucket_count == initial_likes_bucket_count,
                self.branch_likes.bucket_count
                    == self.ownership.betree.active.bucket_count,
                self.loaded_betree.entries@
                    == initial_loaded_entries.push(addr),
                self.loaded_betree@ =~= initial_loaded.insert(addr@),
                self.ownership.betree@
                    == initial_betree_ownership.insert(addr@.au),
                self.branch_likes@
                    == initial_branch_au_likes.add(
                        seq_to_au_likes(buffer_aus@),
                    ),
                self.branch_roots@ =~= initial_branch_roots,
                self.pending_branch_roots@ =~= initial_pending_branch_roots,
                self.pending_branch_roots@ <= self.branch_roots@,
                self.pending_branch_aux@ == old_core.pending_branch_aux,
                self.pending_branch_aux@.dom() <= self.branch_roots@,
                self.ownership.branches@ == old_core.branch_summary,
                child_index <= node.children.len(),
                node.children@.len() == node_view.children.len(),
                self.pending_betree@
                    =~= (initial_pending.remove(addr@)
                        + child_prefix(node_view, child_index as nat))
                        - self.loaded_betree@,
            decreases node.children.len() - child_index,
        {
            let child = node.children[child_index];
            match child {
                Some(child_addr) => {
                    if !self.loaded_betree.contains(&child_addr) {
                        self.pending_betree.insert(child_addr);
                    }
                },
                None => { },
            }
            proof {
                assert(node_view.children[child_index as int]
                    == match child {
                        Some(child_addr) => Some(child_addr@),
                        None => None,
                    });
                child_prefix_next(node_view, child_index as nat);
                assert(self.pending_betree@
                    =~= (initial_pending.remove(addr@)
                        + child_prefix(node_view, child_index as nat + 1))
                        - self.loaded_betree@) by {
                    assert forall |candidate: Address|
                        #![trigger self.pending_betree@.contains(candidate)]
                        self.pending_betree@.contains(candidate)
                        == ((initial_pending.remove(addr@)
                            + child_prefix(node_view, child_index as nat + 1))
                            - self.loaded_betree@).contains(candidate) by { }
                }
            }
            child_index += 1;
        }

        let mut buffer_index = 0usize;
        while buffer_index < node.buffers.len()
            invariant
                self.pending_betree.wf(),
                self.loaded_betree.wf(),
                self.branch_roots.wf(),
                self.pending_branch_roots.wf(),
                self.pending_branch_aux.wf(),
                self.ownership.wf(),
                self.ownership.betree.persistent_aus()
                    == self.ownership.betree.active_aus(),
                self.ownership.branches.persistent_aus()
                    == self.ownership.branches.active_summary_aus(),
                self.ownership.betree.frozen_aus().is_empty(),
                self.ownership.branches.frozen_aus().is_empty(),
                self.branch_likes.wf(),
                self.ownership.betree.active.bucket_count
                    == initial_ownership_bucket_count,
                self.branch_likes.bucket_count == initial_likes_bucket_count,
                self.branch_likes.bucket_count
                    == self.ownership.betree.active.bucket_count,
                self.loaded_betree.entries@
                    == initial_loaded_entries.push(addr),
                buffer_index <= node.buffers.len(),
                node.buffers@.len() == node_view.buffers.addrs.len(),
                self.loaded_betree@ =~= initial_loaded.insert(addr@),
                self.ownership.betree@
                    == initial_betree_ownership.insert(addr@.au),
                self.branch_likes@
                    == initial_branch_au_likes.add(
                        seq_to_au_likes(buffer_aus@),
                    ),
                self.pending_betree@
                    =~= (initial_pending.remove(addr@)
                        + child_prefix(node_view, node_view.children.len()))
                        - self.loaded_betree@,
                self.pending_betree@.disjoint(self.loaded_betree@),
                self.pending_branch_aux@ == old_core.pending_branch_aux,
                self.pending_branch_aux@.dom() <= self.branch_roots@,
                self.ownership.branches@ == old_core.branch_summary,
                self.branch_roots@
                    =~= initial_branch_roots
                        + buffer_prefix(node_view, buffer_index as nat),
                self.pending_branch_roots@
                    =~= initial_pending_branch_roots
                        + (buffer_prefix(node_view, buffer_index as nat)
                            - initial_branch_roots),
                self.pending_branch_roots@ <= self.branch_roots@,
            decreases node.buffers.len() - buffer_index,
        {
            let root = node.buffers[buffer_index];
            let newly_seen = self.branch_roots.insert(root);
            if newly_seen {
                let pending_inserted = self.pending_branch_roots.insert(root);
                proof {
                    assert(pending_inserted) by {
                        if !pending_inserted {
                            assert(initial_pending_branch_roots.contains(root@));
                            assert(initial_pending_branch_roots
                                <= initial_branch_roots);
                    }
                }
            }
            assert(self.ownership.betree.persistent_aus()
                == self.ownership.betree.active_aus());
            assert(self.ownership.branches.persistent_aus()
                == self.ownership.branches.active_summary_aus());
            assert(self.ownership.betree.frozen_aus().is_empty());
            assert(self.ownership.branches.frozen_aus().is_empty());
        }
            proof {
                assert(node_view.buffers.addrs[buffer_index as int] == root@);
                buffer_prefix_next(node_view, buffer_index as nat);
                assert(self.branch_roots@
                    =~= initial_branch_roots
                        + buffer_prefix(node_view, buffer_index as nat + 1));
                assert(self.pending_branch_roots@
                    =~= initial_pending_branch_roots
                        + (buffer_prefix(node_view, buffer_index as nat + 1)
                            - initial_branch_roots)) by {
                    assert forall |candidate: Address|
                        #![trigger self.pending_branch_roots@.contains(candidate)]
                        self.pending_branch_roots@.contains(candidate)
                        == (initial_pending_branch_roots
                            + (buffer_prefix(node_view, buffer_index as nat + 1)
                                - initial_branch_roots)).contains(candidate) by { }
                }
            }
            buffer_index += 1;
        }

        proof {
            assert(child_index == node_view.children.len());
            assert(child_prefix(node_view, child_index as nat)
                =~= betree_child_addrs(node_view)) by {
                assert forall |child: Address|
                    #![trigger child_prefix(node_view, child_index as nat).contains(child)]
                    child_prefix(node_view, child_index as nat).contains(child)
                        == betree_child_addrs(node_view).contains(child) by { }
            }
            assert(buffer_index == node_view.buffers.addrs.len());
            assert(buffer_prefix(node_view, buffer_index as nat)
                =~= betree_buffer_roots(node_view)) by {
                assert forall |root: Address|
                    #![trigger buffer_prefix(node_view, buffer_index as nat).contains(root)]
                    buffer_prefix(node_view, buffer_index as nat).contains(root)
                        == betree_buffer_roots(node_view).contains(root) by { }
            }
        }
        let ghost new_core = old_core.read_betree(addr@, node_view);
        proof {
            assert(self.branch_roots@ == new_core.branch_roots) by {
                assert forall |root: Address|
                    #![trigger self.branch_roots@.contains(root)]
                    self.branch_roots@.contains(root)
                        == new_core.branch_roots.contains(root) by { }
            }
        }
        self.core = Ghost(new_core);
        self.root = saved_root;
        proof {
            broadcast use vstd::multiset::group_multiset_axioms;
            let ghost loaded_likes = self.loaded_betree_likes();
            assert(self.loaded_betree.entries@
                == initial_loaded_entries.push(addr));
            vstd::seq_lib::to_multiset_build(
                iaddr_views(initial_loaded_entries),
                addr@,
            );
            iaddr_views_push_ensures(initial_loaded_entries, addr);
            assert(iaddr_views(self.loaded_betree.entries@)
                == iaddr_views(initial_loaded_entries)
                    .push(addr@));
            assert(loaded_likes
                == initial_loaded_likes.insert(addr@));

            to_au_likes_singleton(addr@);
            to_au_likes_commutative_over_add(
                initial_loaded_likes,
                Multiset::singleton(addr@),
            );
            assert(to_au_likes(loaded_likes)
                == initial_betree_ownership.insert(addr@.au));
            assert(self.ownership.betree@
                == to_au_likes(loaded_likes));

            iaddress_aus_likes(node.buffers@, buffer_aus@);
            assert(iaddr_views(node.buffers@) == node_view.buffers.addrs);
            assert(seq_to_au_likes(buffer_aus@)
                =~= to_au_likes(node_view.buffers.likes()));

            let ghost recovered_tree = self.recovered_likes_tree();
            self.loaded_betree_likes_dom();
            assert(initial_recovered_tree.dv.is_sub_disk(
                recovered_tree.dv,
            )) by {

            }
            initial_recovered_tree.subdisk_implies_same_buffer_likes(
                recovered_tree,
                initial_loaded_likes,
            );
            recovered_tree.buffer_likes_additive(
                initial_loaded_likes,
                Multiset::singleton(addr@),
            );
            let ghost singleton_tree = LinkedBetree {
                root: Option::Some(addr@),
                dv: recovered_tree.dv,
                buffer_dv: recovered_tree.buffer_dv,
            };
            singleton_tree.root_buffer_likes_ensures();
            singleton_tree.subdisk_implies_same_buffer_likes(
                recovered_tree,
                Multiset::singleton(addr@),
            );
            assert(singleton_tree.root_likes()
                == Multiset::singleton(addr@));
            assert(singleton_tree.root().buffers == node_view.buffers);
            assert(recovered_tree.buffer_likes(
                Multiset::singleton(addr@),
            ) == node_view.buffers.likes());
            assert(self.loaded_branch_likes()
                =~= initial_loaded_branch_likes.add(
                    node_view.buffers.likes(),
                ));
            to_au_likes_commutative_over_add(
                initial_loaded_branch_likes,
                node_view.buffers.likes(),
            );
            assert(self.branch_likes@
                == to_au_likes(self.loaded_branch_likes()));
            assert(self.root == initial_root);
            assert(self.wf());
        }
        BetreeRecoveryApplyResult::Applied
    }

    pub fn read_branch_root(
        &mut self,
        root: IAddress,
        node: IBranchNode,
    ) -> (result: BetreeRecoveryApplyResult)
        requires
            old(self).wf(),
            node.wf(),
        ensures
            self.wf(),
            self.root == old(self).root,
            self.ownership.betree.active.bucket_count
                == old(self).ownership.betree.active.bucket_count,
            self.branch_likes.bucket_count
                == old(self).branch_likes.bucket_count,
            match result {
                BetreeRecoveryApplyResult::Applied => {
                    &&& old(self)@.pending_branch_roots.contains(root@)
                    &&& (node@ is Leaf || node@ is Index)
                    &&& (node@ is Index ==>
                        node@.arrow_Index_aux_ptr() is Some)
                    &&& self@ == old(self)@.read_branch_root(root@, node@)
                },
                BetreeRecoveryApplyResult::Invalid => self@ == old(self)@,
            },
    {
        if !self.pending_branch_roots.contains(&root) {
            return BetreeRecoveryApplyResult::Invalid;
        }
        let ghost node_view = node@;
        let ghost old_core = self@;
        let ghost initial_root = self.root;
        let saved_root = self.root;
        match node {
            IBranchNode::Leaf { keys: _, msgs: _ } => {
                let betree_owned = self.ownership.betree.contains_owned_au(root.au);
                let branch_owned = self.ownership.branches.contains_owned_au(root.au);
                let root_recorded = self.ownership.branches.contains_root_au(root.au);
                if betree_owned || branch_owned || root_recorded {
                    return BetreeRecoveryApplyResult::Invalid;
                }
                let mut summary = Vec::<IAU>::new();
                summary.push(root.au);
                proof {
                    assert(summary@ == seq![root.au]);
                    assert(unique_iau_seq(summary@));
                    assert(iau_seq_set(summary@) =~= set![root.au as nat]) by {
                        assert forall |au: nat|
                            #![trigger iau_seq_set(summary@).contains(au)]
                            iau_seq_set(summary@).contains(au)
                                == (au == root.au as nat) by {
                        if iau_seq_set(summary@).contains(au) {
                            let i = choose |i: int| #![auto]
                                0 <= i < summary@.len()
                                && summary@[i] as nat == au;
                            assert(i == 0);
                            assert(summary@[i] == root.au);
                        } else if au == root.au as nat {
                            assert(summary@[0] == root.au);
                            assert(exists |i: int| #![auto]
                                0 <= i < summary@.len()
                                && summary@[i] as nat == au);
                        }
                        }
                    }
                    assert(self.ownership.branches.all_summary_aus()
                        .disjoint(iau_seq_set(summary@))) by {
                        assert forall |au: nat|
                            #[trigger] iau_seq_set(summary@).contains(au)
                            implies !self.ownership.branches
                                .all_summary_aus().contains(au) by { }
                    }
                }
                let added = self.ownership.branches.add_recovered(
                    root.au,
                    summary,
                );
                match added {
                    BranchOwnershipUpdateResult::Applied { reclaimed: _ } => { },
                    BranchOwnershipUpdateResult::Noop => {
                        proof { assert(false); }
                        return BetreeRecoveryApplyResult::Invalid;
                    },
                }
                proof {
                    assert(self.ownership.wf()) by {
                        assert(self.ownership.betree.all_aus().disjoint(
                            self.ownership.branches.all_summary_aus(),
                        )) by {
                            assert forall |au: nat|
                                #[trigger] self.ownership.betree.all_aus()
                                    .contains(au)
                                implies !self.ownership.branches
                                    .all_summary_aus().contains(au) by { }
                        }
                    }
                }
            },
            IBranchNode::Index { pivots: _, children: _, aux_ptr } => {
                if aux_ptr.is_none() || self.pending_branch_aux.get(&root).is_some() {
                    return BetreeRecoveryApplyResult::Invalid;
                }
                let inserted = self.pending_branch_aux.insert_fresh(
                    root,
                    aux_ptr.unwrap(),
                );
                proof { assert(inserted); }
            },
            IBranchNode::Auxiliary { summary_aus: _ } => {
                return BetreeRecoveryApplyResult::Invalid;
            },
        }
        let removed = self.pending_branch_roots.remove(&root);
        proof { assert(removed); }
        self.core = Ghost(old_core.read_branch_root(root@, node_view));
        self.root = saved_root;
        proof {
            assert(self.root == initial_root);
            assert(self.wf());
        }
        BetreeRecoveryApplyResult::Applied
    }

    pub fn read_branch_aux(
        &mut self,
        root: IAddress,
        node: IBranchNode,
    ) -> (result: BetreeRecoveryApplyResult)
        requires
            old(self).wf(),
            node.wf(),
        ensures
            self.wf(),
            self.root == old(self).root,
            self.ownership.betree.active.bucket_count
                == old(self).ownership.betree.active.bucket_count,
            self.branch_likes.bucket_count
                == old(self).branch_likes.bucket_count,
            match result {
                BetreeRecoveryApplyResult::Applied => {
                    &&& old(self)@.pending_branch_aux.contains_key(root@)
                    &&& node@ is Auxiliary
                    &&& self@ == old(self)@.read_branch_aux(root@, node@)
                },
                BetreeRecoveryApplyResult::Invalid => self@ == old(self)@,
            },
    {
        if self.pending_branch_aux.get(&root).is_none() {
            return BetreeRecoveryApplyResult::Invalid;
        }
        proof { node.auxiliary_view(); }
        let ghost node_view = node@;
        let ghost old_core = self@;
        let ghost initial_root = self.root;
        let saved_root = self.root;
        let ghost initial_branch_summary = self.ownership.branches@;
        match node {
            IBranchNode::Auxiliary { summary_aus } => {
                let ghost summary_view = summary_aus@;
                if !validate_summary(&summary_aus, root.au) {
                    return BetreeRecoveryApplyResult::Invalid;
                }
                let root_recorded = self.ownership.branches.contains_root_au(root.au);
                if root_recorded {
                    return BetreeRecoveryApplyResult::Invalid;
                }
                let mut index = 0usize;
                while index < summary_aus.len()
                    invariant
                        self.ownership.wf(),
                        index <= summary_aus.len(),
                        forall |i: int| #![trigger summary_aus@[i]]
                            0 <= i < index
                            ==> !self.ownership.betree.all_aus()
                                    .contains(summary_aus@[i] as nat)
                                && !self.ownership.branches.all_summary_aus()
                                    .contains(summary_aus@[i] as nat),
                    decreases summary_aus.len() - index,
                {
                    let betree_owned = self.ownership.betree
                        .contains_owned_au(summary_aus[index]);
                    let branch_owned = self.ownership.branches
                        .contains_owned_au(summary_aus[index]);
                    if betree_owned || branch_owned {
                        return BetreeRecoveryApplyResult::Invalid;
                    }
                    index += 1;
                }
                proof {
                    summary_set_views_agree(summary_view);
                    mapped_summary_set_agrees(summary_view);
                    assert(self.ownership.branches.all_summary_aus()
                        .disjoint(iau_seq_set(summary_aus@))) by {
                        assert forall |au: nat|
                            #[trigger] iau_seq_set(summary_aus@).contains(au)
                            implies !self.ownership.branches
                                .all_summary_aus().contains(au) by {
                            let i = choose |i: int| #![auto]
                                0 <= i < summary_aus@.len()
                                && summary_aus@[i] as nat == au;
                            assert(i < index);
                        }
                    }
                }
                let added = self.ownership.branches.add_recovered(
                    root.au,
                    summary_aus,
                );
                match added {
                    BranchOwnershipUpdateResult::Applied { reclaimed: _ } => { },
                    BranchOwnershipUpdateResult::Noop => {
                        proof { assert(false); }
                        return BetreeRecoveryApplyResult::Invalid;
                    },
                }
                proof {
                    assert(self.ownership.branches@
                        == initial_branch_summary.insert(
                            root.au as nat,
                            iau_seq_set(summary_view),
                        ));
                    assert(node_view is Auxiliary);
                    assert(node_view.arrow_Auxiliary_0()
                        =~= iau_seq_set(summary_view));
                    assert(self.ownership.branches@
                        == old_core.branch_summary.insert(
                            root.au as nat,
                            node_view.arrow_Auxiliary_0(),
                        ));
                    assert(self.ownership.wf()) by {
                        assert(self.ownership.betree.all_aus().disjoint(
                            self.ownership.branches.all_summary_aus(),
                        )) by {
                            assert forall |au: nat|
                                #[trigger] self.ownership.betree.all_aus()
                                    .contains(au)
                                implies !self.ownership.branches
                                    .all_summary_aus().contains(au) by { }
                        }
                    }
                }
            },
            IBranchNode::Leaf { keys: _, msgs: _ }
            | IBranchNode::Index { pivots: _, children: _, aux_ptr: _ } => {
                return BetreeRecoveryApplyResult::Invalid;
            },
        }
        let removed = self.pending_branch_aux.remove(&root);
        proof { assert(removed is Some); }
        let ghost new_core = old_core.read_branch_aux(root@, node_view);
        proof {
            assert(self.ownership.branches@ == new_core.branch_summary);
        }
        self.core = Ghost(new_core);
        self.root = saved_root;
        proof {
            assert(self.root == initial_root);
            assert(self.wf());
        }
        BetreeRecoveryApplyResult::Applied
    }

    pub fn start(
        root: Option<IAddress>,
        seq_end: u64,
        bucket_count: u32,
    ) -> (out: Self)
        requires
            bucket_count > 0,
        ensures
            out.wf(),
            out.root == root,
            out.ownership.betree.active.bucket_count == bucket_count,
            out.branch_likes.bucket_count == bucket_count,
            out@ == BetreeMetadataRecoveryCore::start(
                CachingDiskBranchBetreeMetadata {
                    root: iopt_addr(root),
                    seq_end: seq_end as nat,
                },
            ),
    {
        let ghost metadata = CachingDiskBranchBetreeMetadata {
            root: iopt_addr(root),
            seq_end: seq_end as nat,
        };
        let pending_betree = RecoveryAddressSet::from_pointer(root);
        let loaded_betree = RecoveryAddressSet::new();
        let branch_roots = RecoveryAddressSet::new();
        let pending_branch_roots = RecoveryAddressSet::new();
        let pending_branch_aux = RecoveryAddressMap::new();
        let ownership = BranchBetreeOwnershipImpl::new(bucket_count);
        let branch_likes = AuLikesImpl::new(bucket_count);
        let out = Self {
            core: Ghost(BetreeMetadataRecoveryCore::start(metadata)),
            root,
            pending_betree,
            loaded_betree,
            branch_roots,
            pending_branch_roots,
            pending_branch_aux,
            ownership,
            branch_likes,
        };
        proof {
            out.ownership.betree.ownership_sets_bounded();
            out.ownership.branches.ownership_sets_bounded();
            assert(out.ownership.betree.active_aus().is_empty()) by {
                assert(out.ownership.betree.active_aus()
                    <= out.ownership.betree.all_aus());
            }
            assert(out.ownership.betree.persistent_aus().is_empty());
            assert(out.ownership.betree.frozen_aus().is_empty());
            assert(out.ownership.branches.active_summary_aus().is_empty()) by {
                assert(out.ownership.branches.active_summary_aus()
                    <= out.ownership.branches.all_summary_aus());
            }
            assert(out.ownership.branches.persistent_aus().is_empty());
            assert(out.ownership.branches.frozen_aus().is_empty());
            assert(out.ownership.branches@
                == Map::<nat, crate::allocation_layer::BranchTypes_v::Summary>::empty());
            assert(out.loaded_betree.entries@.len() == 0);
            assert_seqs_equal!(
                iaddr_views(out.loaded_betree.entries@),
                Seq::<Address>::empty(),
                i => { }
            );
            iaddr_views(out.loaded_betree.entries@)
                .to_multiset_ensures();
            assert(out.loaded_betree_likes() == Likes::empty());
            crate::allocation_layer::Likes_v::to_au_likes_empty();
            assert(out.loaded_branch_likes() == Likes::empty()) by {

            }
            assert(out.wf());
        }
        out
    }
}

impl View for BetreeRecoveryImpl {
    type V = BetreeMetadataRecoveryCore;

    open spec fn view(&self) -> Self::V {
        self.core@
    }
}

#[allow(dead_code)]
fn verify_recovery_collections() {
    let addr = IAddress { au: 1, page: 2 };
    let mut set = RecoveryAddressSet::from_pointer(Some(addr));
    let duplicate = set.insert(addr);
    proof { assert(!duplicate); }
    let removed = set.remove(&addr);
    proof {
        assert(removed);
        assert(set@ =~= Set::<Address>::empty());
    }
}

} // verus!
