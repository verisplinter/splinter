// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::map::*;

use crate::allocation_layer::AllocationBranch_v::Summary;
use crate::implementation::AtomicBranchState_v::{AtomicBranchImage, AtomicBranchState};
use crate::implementation::BranchImpl_v::{
    allocate_fresh_addr_from_mini, BranchError, BranchImpl, BranchNode, BranchStore, MemBranchStore,
};
use crate::implementation::CachedBranch_v::CachedBranch;
use crate::implementation::IBranchNode_v::{iaddr_seq, iau_seq_set};
use crate::implementation::MiniAllocatorImpl_v::MiniAllocatorImpl;
use crate::spec::ImplDisk_t::{IAddress, IAU};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Delta, Message, Value};

verus! {

pub struct BranchImageImpl {
    pub sealed_roots: Vec<IAddress>,
    pub seq_end: usize,
}

impl BranchImageImpl {
    pub open spec fn wf(&self) -> bool
    {
        true
    }

    pub fn empty() -> (out: Self)
        ensures
            out.wf(),
            out@ == (AtomicBranchImage{sealed_roots: Seq::empty(), seq_end: 0}),
            out.sealed_roots@.len() == 0,
    {
        Self { sealed_roots: Vec::new(), seq_end: 0 }
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
        true
    }

    pub open spec fn i(&self) -> Map<nat, Summary>
    {
        let entries = self.entries@;
        Map::new(
            |au: nat| exists |idx: int| 0 <= idx < entries.len() && entries[idx].0 as nat == au,
            |au: nat| {
                let idx = choose |idx: int| 0 <= idx < entries.len() && entries[idx].0 as nat == au;
                iau_seq_set(entries[idx].1@)
            },
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
    {
        let mut idx: usize = 0;
        while idx < self.entries.len()
            invariant
                idx <= self.entries.len(),
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
    {
        match self.find_root_au(root_au) {
            Some(idx) => {
                self.entries[idx] = (root_au, discovered_aus);
            },
            None => {
                self.entries.push((root_au, discovered_aus));
            },
        }
    }
}

pub enum CommitPhase {
    Idle,
    InFlight { prefix_len: usize, seq_end: usize, prepared: bool },
}

pub struct BranchStackImpl {
    pub image: BranchImageImpl,
    pub persistent_prefix_len: usize,
    pub persistent_seq_end: usize,
    pub persisted_root_count: usize,
    pub commit_phase: CommitPhase,
    pub branch_summary: BranchSummaryImpl,
    pub active_branch: Option<BranchImpl>,
    pub mini_allocator: MiniAllocatorImpl,
    pub store: MemBranchStore,
    pub seq_end: usize,
}

impl BranchStackImpl {
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
        &&& self.persistent_prefix_len <= self.image.sealed_roots@.len()
        &&& self.persisted_root_count <= self.image.sealed_roots@.len()
        &&& self.persistent_prefix_len <= self.persisted_root_count
        &&& self.persistent_seq_end <= self.seq_end
        &&& self.commit_phase_wf()
        &&& self.branch_summary.wf()
        &&& self.mini_allocator.wf()
        &&& self.store.wf()
        &&& self.i().wf()
    }

    pub open spec fn i(&self) -> AtomicBranchState::State
    {
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
            out.active_branch is None,
    {
        let summary = BranchSummaryImpl::new();
        let allocator = MiniAllocatorImpl::empty(free_au_threshold);
        let store = MemBranchStore::new();
        let seq_end = image.seq_end;
        Self {
            persistent_prefix_len: initial_persisted_root_count,
            persistent_seq_end: image.seq_end,
            persisted_root_count: initial_persisted_root_count,
            commit_phase: CommitPhase::Idle,
            branch_summary: summary,
            active_branch: None,
            mini_allocator: allocator,
            store,
            seq_end,
            image,
        }
    }

    pub fn fill_aus(&mut self, aus: Vec<IAU>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self.active_branch == old(self).active_branch,
    {
        self.mini_allocator.add_aus(aus);
    }

    pub fn query(&self, key: Key) -> (result: Result<Message, BranchError>)
        requires
            self.wf(),
            self.active_branch is Some ==> self.active_branch.unwrap().invariants(&self.store),
    {
        let branch = match self.active_branch {
            Some(branch) => branch,
            None => return Err(BranchError::Uninitialized),
        };
        branch.query(&self.store, key)
    }

    pub fn load_metadata(&mut self, root: IAddress, discovered_aus: Vec<IAU>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self.active_branch == old(self).active_branch,
    {
        self.branch_summary.insert_or_update(root.au, discovered_aus);
    }

    pub fn append(&mut self, keys: Vec<Key>, msgs: Vec<Message>) -> (result: Result<(), BranchError>)
        requires
            old(self).wf(),
            old(self).active_branch is Some ==> old(self).active_branch.unwrap().inv(&old(self).store),
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
                branch.append(&mut self.store, keys, msgs)?;
                proof {
                    assert(self.store.wf());
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
                self.store = store;
                self.active_branch = Some(BranchImpl::new(init_root));
            },
        }

        self.seq_end = self.seq_end + appended_count;
        Ok(())
    }

    pub fn grow(&mut self) -> (result: Result<(), BranchError>)
        requires
            old(self).wf(),
            old(self).active_branch is Some ==> old(self).active_branch.unwrap().inv(&old(self).store),
        ensures
            result is Ok ==> self.wf(),
    {
        let mut branch = match self.active_branch {
            Some(branch) => branch,
            None => return Err(BranchError::Uninitialized),
        };
        branch.grow(&mut self.store, &mut self.mini_allocator)?;
        proof {
            assert(self.store.wf());
            assert(self.mini_allocator.wf());
        }
        self.active_branch = Some(branch);
        Ok(())
    }

    pub fn split(&mut self, pivot: Key) -> (result: Result<(), BranchError>)
        requires
            old(self).wf(),
            old(self).active_branch is Some ==> old(self).active_branch.unwrap().inv(&old(self).store),
        ensures
            result is Ok ==> self.wf(),
    {
        let branch = match self.active_branch {
            Some(branch) => branch,
            None => return Err(BranchError::Uninitialized),
        };
        branch.split(&mut self.store, pivot, &mut self.mini_allocator)?;
        proof {
            assert(self.store.wf());
            assert(self.mini_allocator.wf());
        }
        Ok(())
    }

    pub fn seal(&mut self) -> (result: Result<(), BranchError>)
        requires
            old(self).wf(),
            old(self).active_branch is Some ==> old(self).active_branch.unwrap().inv(&old(self).store),
        ensures
            result is Ok ==> self.wf(),
    {
        let branch = match self.active_branch {
            Some(branch) => branch,
            None => return Err(BranchError::Uninitialized),
        };
        let root = branch.root;
        branch.seal(&mut self.store, &mut self.mini_allocator)?;
        proof {
            assert(self.store.wf());
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
        ensures
            self.wf(),
    {
        if target_count < self.persisted_root_count || target_count > self.image.sealed_roots.len() {
            return Err(BranchError::InvalidCommit);
        }
        self.persisted_root_count = target_count;
        Ok(())
    }

    pub fn commit_start(&mut self, prefix_len: usize, seq_end: usize) -> (result: Result<(), BranchError>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
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
        Ok(())
    }

    pub fn commit_prepared(&mut self) -> (result: Result<(), BranchError>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
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
                Ok(())
            },
            CommitPhase::Idle => Err(BranchError::InvalidCommit),
        }
    }

    pub fn commit_complete(&mut self) -> (result: Result<(), BranchError>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
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
                Ok(())
            },
            CommitPhase::Idle => Err(BranchError::InvalidCommit),
        }
    }

    pub fn smoke_scenarios() -> Result<(), BranchError> {
        let image = BranchImageImpl::empty();
        let mut branch = BranchStackImpl::new(image, 0, 2);
        branch.fill_aus(vec![9]);
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
}

impl View for BranchStackImpl {
    type V = AtomicBranchState::State;

    open spec fn view(&self) -> Self::V
    {
        self.i()
    }
}

} // verus!
