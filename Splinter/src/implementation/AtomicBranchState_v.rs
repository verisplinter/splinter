// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Branch component state used by the unified shared-cache model.
//
// This model keeps journal and branch fields present from initialization, but
// service readiness is represented by their internal status fields.

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::multiset::*;
use verus_state_machines_macros::state_machine;

use crate::abstract_system::MsgHistory_v::{KeyedMessage, MsgHistory};
use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::AllocationJournal_v::lsn_au_index_discard_up_to;
use crate::allocation_layer::AllocationBranch_v::{BranchNode, Summary};
use crate::allocation_layer::AllocationBranchBetree_v::summary_aus;
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::LinkedBranch_v::SplitArg;
use crate::disk::GenericDisk_v::{Address, AU, Pointer, to_aus};
use crate::implementation::AllocationBranchStack_v::normalize_value;
use crate::implementation::AllocationBranchStackRefinement_v::append_puts;
use crate::implementation::Cache_v::{addr_maps_to_req, Cache, Entry, Slot, Status};
use crate::implementation::CachedBranch_v::{
    CachedBranch, LoadedBranch, LoadedPathReceipt, root_summary_from_read,
    root_summary_read_valid,
};
use crate::implementation::CachedJournal_v::{CachedJournal, JournalSnapshot};
use crate::implementation::CachingDiskBranch_v::{
    root_aus_up_to, sealed_summary_aus_between, split_read_addrs,
};
use crate::implementation::CachingDisk_v::addresses_in_aus;
use crate::implementation::AbstractSuperblock_v::{
    AbstractSuperblockImage, empty_abstract_superblock_image, marshal_abstract_superblock,
    superblock_matches,
};
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::JournalTypes_v::to_journal_records;
use crate::implementation::RecoveryState_v::RecoveryState;
use crate::journal::LinkedJournal_v::JournalRecord;
use crate::marshalling::IBranchNodeFormat_v::raw_page_to_branch_node;
use crate::marshalling::IJournalRecordFormat_v::IJournalRecordFormat;
use crate::marshalling::Marshalling_v::Marshal;
use crate::spec::AsyncDisk_t::{DiskRequest, DiskResponse, RawPage};
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::{ID, Input, MapSpec, Reply, Request, SyncReqId};
use crate::spec::Messages_t::{Message, Value, nop_delta};

verus! {
#[verifier::ext_equal]
pub struct AtomicBranchImage {
    pub sealed_roots: Seq<Address>,
    pub seq_end: nat,
}

state_machine!{ AtomicBranchState {
    fields {
        pub image: AtomicBranchImage,
        pub persistent_image: AtomicBranchImage,
        pub in_flight: Option<AtomicBranchImage>,
        pub prepared: bool,
        pub branch_summary: Map<AU, Summary>,
        pub persisted_root_count: nat,
        pub active_branch: CachedBranch::State,
        pub mini_allocator: MiniAllocator,
        pub seq_end: nat,
    }

    pub enum Label {
        Query{
            key: Key,
            msg: Message,
            receipts: Seq<LoadedPathReceipt>,
            read_nodes: LoadedBranch,
        },
        LoadMetadata{ root: Address, discovered_aus: Set<AU>, read_nodes: LoadedBranch },
        Append{
            keys: Seq<Key>,
            msgs: Seq<Message>,
            receipt: LoadedPathReceipt,
            init_root: Option<Address>,
            read_nodes: LoadedBranch,
            write_nodes: LoadedBranch,
        },
        Grow{ new_root_addr: Address, read_nodes: LoadedBranch, write_nodes: LoadedBranch },
        Split{
            new_child_addr: Address,
            receipt: LoadedPathReceipt,
            split_arg: SplitArg,
            read_nodes: LoadedBranch,
            write_nodes: LoadedBranch,
        },
        Seal{ aux_ptr: Pointer, summary: Summary, read_nodes: LoadedBranch, write_nodes: LoadedBranch },
        FillAUs{ aus: Set<AU> },
        ObservePersistedRoots{ target_count: nat },
        CommitStart{ branch_image: AtomicBranchImage },
        CommitPrepared,
        CommitComplete,
    }

    init!{ initialize(branch_image: AtomicBranchImage, initial_persisted_root_count: nat) {
        init image = branch_image;
        init persistent_image = branch_image;
        init in_flight = None;
        init prepared = false;
        init branch_summary = Map::empty();
        init persisted_root_count = initial_persisted_root_count;
        init active_branch = CachedBranch::State::empty_active();
        init mini_allocator = MiniAllocator::empty();
        init seq_end = branch_image.seq_end;
    }}

    transition!{ query(lbl: Label) {
        require let Label::Query{key, msg, receipts, read_nodes} = lbl;
        let roots = query_roots(pre.image.sealed_roots, pre.active_branch);
        require query_receipts_valid(roots, receipts, read_nodes, key);
        require msg == query_from_receipts_up_to(receipts, receipts.len() as nat);
    }}

    transition!{ load_metadata(lbl: Label) {
        require let Label::LoadMetadata{root, discovered_aus, read_nodes} = lbl;
        require pre.image.sealed_roots.contains(root);
        require root_summary_read_valid(root, read_nodes);
        require discovered_aus == root_summary_from_read(root, read_nodes);

        update branch_summary = pre.branch_summary.insert(root.au, discovered_aus);
    }}

    transition!{ append_nonempty(lbl: Label, new_active_branch: CachedBranch::State) {
        require let Label::Append{keys, msgs, receipt, init_root, read_nodes, write_nodes} = lbl;
        require pre.active_branch.root is Some;
        require init_root is None;
        let branch_lbl = CachedBranch::Label::Append{
            mini_allocator: pre.mini_allocator,
            receipt,
            keys,
            msgs,
            read_nodes,
            write_nodes,
        };
        require CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl);

        update active_branch = new_active_branch;
        update seq_end = pre.seq_end + keys.len();
    }}

    transition!{ append_empty(lbl: Label, new_active_branch: CachedBranch::State) {
        require let Label::Append{keys, msgs, receipt, init_root, read_nodes, write_nodes} = lbl;
        require pre.active_branch.root is None;
        require init_root is Some;

        let branch_lbl = CachedBranch::Label::Initialize{
            mini_allocator: pre.mini_allocator,
            init_root: init_root.unwrap(),
            keys,
            msgs,
            write_nodes,
        };
        require CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl);

        update active_branch = new_active_branch;
        update mini_allocator = pre.mini_allocator.allocate(init_root.unwrap());
        update seq_end = pre.seq_end + keys.len();
    }}

    transition!{ grow(lbl: Label, new_active_branch: CachedBranch::State) {
        require let Label::Grow{new_root_addr, read_nodes, write_nodes} = lbl;
        let branch_lbl = CachedBranch::Label::Grow{
            mini_allocator: pre.mini_allocator,
            new_root_addr,
            read_nodes,
            write_nodes,
        };
        require CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl);

        update active_branch = new_active_branch;
        update mini_allocator = pre.mini_allocator.allocate(new_root_addr);
    }}

    transition!{ split(lbl: Label, new_active_branch: CachedBranch::State) {
        require let Label::Split{new_child_addr, receipt, split_arg, read_nodes, write_nodes} = lbl;
        let branch_lbl = CachedBranch::Label::Split{
            mini_allocator: pre.mini_allocator,
            new_child_addr,
            receipt,
            split_arg,
            read_nodes,
            write_nodes,
        };
        require CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl);

        update active_branch = new_active_branch;
        update mini_allocator = pre.mini_allocator.allocate(new_child_addr);
    }}

    transition!{ seal(lbl: Label) {
        require let Label::Seal{aux_ptr, summary, read_nodes, write_nodes} = lbl;
        let root = pre.active_branch.root.unwrap();
        let branch_lbl = CachedBranch::Label::Seal{
            mini_allocator: pre.mini_allocator,
            aux_ptr,
            read_nodes,
            write_nodes,
        };
        require CachedBranch::State::next(pre.active_branch, pre.active_branch, branch_lbl);
        require summary == pre.mini_allocator.reserved_aus();

        update image = AtomicBranchImage{
            sealed_roots: pre.image.sealed_roots.push(root),
            seq_end: pre.image.seq_end,
        };
        update active_branch = CachedBranch::State::empty_active();
        update mini_allocator = pre.mini_allocator.prune(summary);
        update branch_summary = pre.branch_summary.insert(root.au, summary);
    }}

    transition!{ fill_aus(lbl: Label) {
        require let Label::FillAUs{aus} = lbl;

        update mini_allocator = pre.mini_allocator.add_aus(aus);
    }}

    transition!{ observe_persisted_roots(lbl: Label) {
        require let Label::ObservePersistedRoots{target_count} = lbl;
        require pre.persisted_root_count <= target_count <= pre.image.sealed_roots.len();

        update persisted_root_count = target_count;
    }}

    transition!{ commit_start(lbl: Label) {
        require let Label::CommitStart{branch_image} = lbl;
        require pre.in_flight is None;
        require {
            ||| {
                &&& pre.metadata_loaded()
                &&& pre.active_branch.root is None
                &&& branch_image == pre.freeze_image()
            }
            ||| branch_image == pre.persistent_image
        };

        update in_flight = Option::Some(branch_image);
        update prepared = false;
    }}

    transition!{ commit_prepared(lbl: Label) {
        require lbl is CommitPrepared;
        require pre.in_flight is Some;
        let image = pre.in_flight.unwrap();
        require image.sealed_roots.len() <= pre.persisted_root_count;
        require image.sealed_roots.len() <= pre.image.sealed_roots.len();
        require pre.image.sealed_roots.subrange(0, image.sealed_roots.len() as int) == image.sealed_roots;

        update prepared = true;
    }}

    transition!{ commit_complete(lbl: Label) {
        require lbl is CommitComplete;
        require pre.in_flight is Some;
        require pre.prepared;
        let image = pre.in_flight.unwrap();
        let committed_root_count = image.sealed_roots.len() as nat;
        let new_persisted_root_count = if pre.persisted_root_count < committed_root_count {
            committed_root_count
        } else {
            pre.persisted_root_count
        };

        update persisted_root_count = new_persisted_root_count;
        update persistent_image = image;
        update in_flight = Option::None;
        update prepared = false;
    }}
}}

pub open spec fn empty_branch_image() -> AtomicBranchImage
{
    AtomicBranchImage{
        sealed_roots: Seq::empty(),
        seq_end: 0,
    }
}

pub open spec fn to_branch_nodes(reads: Map<Address, RawPage>) -> LoadedBranch
{
    Map::new(
        |addr| reads.contains_key(addr),
        |addr| raw_page_to_branch_node(reads[addr]),
    )
}

pub open spec fn mini_allocator_allocated_addrs(mini_allocator: MiniAllocator) -> Set<Address>
{
    Set::new(|addr: Address| {
        &&& mini_allocator.allocs.contains_key(addr.au)
        &&& (mini_allocator.allocs[addr.au].reserved
            + mini_allocator.allocs[addr.au].observed).contains(addr)
    })
}

pub open spec fn atomic_branch_support_addrs(branch: AtomicBranchState::State) -> Set<Address>
{
    addresses_in_aus(summary_aus(branch.branch_summary) + branch.mini_allocator.all_aus())
}

pub open spec fn active_query_roots(active_branch: CachedBranch::State) -> Seq<Address>
{
    if active_branch.root is Some {
        seq![active_branch.root.unwrap()]
    } else {
        seq![]
    }
}

pub open spec fn query_roots(sealed_roots: Seq<Address>, active_branch: CachedBranch::State) -> Seq<Address>
{
    sealed_roots + active_query_roots(active_branch)
}

pub open spec fn query_from_receipts_up_to(
    receipts: Seq<LoadedPathReceipt>,
    end: nat,
) -> Message
    recommends
        end <= receipts.len(),
    decreases end
{
    if end == 0 {
        Message::Update{delta: nop_delta()}
    } else {
        let idx = (end - 1) as int;
        query_from_receipts_up_to(receipts, (end - 1) as nat).merge(receipts[idx].result())
    }
}

pub open spec fn query_receipts_valid(
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
            let root_idx = roots.len() as int - receipts.len() as int + i;
            &&& receipt.key == key
            &&& receipt.valid_for(roots[root_idx], read_nodes)
            &&& receipt.target().node is Leaf
    }
    &&& receipts.len() < roots.len() ==>
        query_from_receipts_up_to(receipts, receipts.len() as nat) is Define
}

pub open spec fn query_receipts_read_addrs(
    receipts: Seq<LoadedPathReceipt>,
    end: nat,
) -> Set<Address>
    recommends
        end <= receipts.len(),
    decreases end
{
    if end == 0 {
        Set::empty()
    } else {
        let idx = (end - 1) as int;
        query_receipts_read_addrs(receipts, (end - 1) as nat) + receipts[idx].needed_addrs()
    }
}

impl AtomicBranchState::State {
    pub open spec fn empty() -> Self
    {
        AtomicBranchState::State{
            image: empty_branch_image(),
            persistent_image: empty_branch_image(),
            in_flight: None,
            prepared: false,
            branch_summary: Map::empty(),
            persisted_root_count: 0,
            active_branch: CachedBranch::State::empty_active(),
            mini_allocator: MiniAllocator::empty(),
            seq_end: 0,
        }
    }

    pub open spec fn owned_aus(self) -> Set<AU>
    {
        summary_aus(self.branch_summary) + self.mini_allocator.all_aus()
    }

    pub open spec fn wf(self) -> bool
    {
        &&& self.persisted_root_count <= self.image.sealed_roots.len()
        &&& self.image.seq_end <= self.seq_end
        &&& self.persistent_image.sealed_roots.len() <= self.image.sealed_roots.len()
        &&& self.image.sealed_roots.take(self.persistent_image.sealed_roots.len() as int)
            == self.persistent_image.sealed_roots
        &&& self.persistent_image.sealed_roots.len() <= self.persisted_root_count
        &&& self.persistent_image.seq_end <= self.seq_end
        &&& self.in_flight is Some ==> {
            let image = self.in_flight.unwrap();
            &&& image.sealed_roots.len() <= self.image.sealed_roots.len()
            &&& self.image.sealed_roots.take(image.sealed_roots.len() as int)
                == image.sealed_roots
            &&& image.seq_end <= self.seq_end
        }
        &&& self.prepared ==> self.in_flight is Some
        &&& self.active_branch.wf()
        &&& self.mini_allocator.wf()
    }

    pub open spec fn freeze_image(self) -> AtomicBranchImage
    {
        AtomicBranchImage{
            sealed_roots: self.image.sealed_roots,
            seq_end: self.seq_end,
        }
    }

    pub open spec fn metadata_loaded(self) -> bool
    {
        root_aus_up_to(self.image.sealed_roots, self.image.sealed_roots.len() as nat)
            <= self.branch_summary.dom()
    }

    pub open spec fn seq_end(self) -> nat
    {
        self.seq_end
    }

    pub open spec fn root_addrs(self) -> Set<Address>
    {
        let sealed_roots = self.image.sealed_roots.to_set();
        let active_roots = if self.active_branch.root is Some {
            set![self.active_branch.root.unwrap()]
        } else {
            Set::empty()
        };
        sealed_roots + active_roots
    }

    pub proof fn wf_next(pre: Self, post: Self, lbl: AtomicBranchState::Label)
        requires
            pre.wf(),
            AtomicBranchState::State::next(pre, post, lbl),
        ensures
            post.wf(),
    {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let step = choose |step| AtomicBranchState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicBranchState::Step::query() => {
                assert(AtomicBranchState::State::query(pre, post, lbl));
            },
            AtomicBranchState::Step::load_metadata() => {
                assert(AtomicBranchState::State::load_metadata(pre, post, lbl));
            },
            AtomicBranchState::Step::append_nonempty(new_active_branch) => {
                assert(AtomicBranchState::State::append_nonempty(
                    pre,
                    post,
                    lbl,
                    new_active_branch,
                ));
                assert(post.mini_allocator == pre.mini_allocator);
            },
            AtomicBranchState::Step::append_empty(new_active_branch) => {
                assert(AtomicBranchState::State::append_empty(pre, post, lbl, new_active_branch));
                let (keys, msgs, init_root, write_nodes) = match lbl {
                    AtomicBranchState::Label::Append{keys, msgs, init_root, write_nodes, ..} =>
                        (keys, msgs, init_root, write_nodes),
                    _ => arbitrary(),
                };
                assert(init_root is Some);
                let init_addr = init_root.unwrap();
                let branch_lbl = CachedBranch::Label::Initialize{
                    mini_allocator: pre.mini_allocator,
                    init_root: init_addr,
                    keys,
                    msgs,
                    write_nodes,
                };
                assert(CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                assert(CachedBranch::State::next_by(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                    CachedBranch::Step::initialize_branch(),
                ));
                assert(CachedBranch::State::initialize_branch(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                ));
                assert(pre.mini_allocator.can_allocate(init_addr));
                assert(init_addr.wf());
                assert(post.mini_allocator.wf());
            },
            AtomicBranchState::Step::grow(new_active_branch) => {
                assert(AtomicBranchState::State::grow(pre, post, lbl, new_active_branch));
                let (new_root_addr, read_nodes, write_nodes) = match lbl {
                    AtomicBranchState::Label::Grow{new_root_addr, read_nodes, write_nodes} =>
                        (new_root_addr, read_nodes, write_nodes),
                    _ => arbitrary(),
                };
                let branch_lbl = CachedBranch::Label::Grow{
                    mini_allocator: pre.mini_allocator,
                    new_root_addr,
                    read_nodes,
                    write_nodes,
                };
                assert(CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                assert(CachedBranch::State::next_by(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                    CachedBranch::Step::grow_step(),
                ));
                assert(CachedBranch::State::grow_step(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                ));
                assert(pre.mini_allocator.can_allocate(new_root_addr));
                assert(new_root_addr.wf());
                assert(post.mini_allocator.wf());
            },
            AtomicBranchState::Step::split(new_active_branch) => {
                assert(AtomicBranchState::State::split(pre, post, lbl, new_active_branch));
                let (new_child_addr, receipt, split_arg, read_nodes, write_nodes) = match lbl {
                    AtomicBranchState::Label::Split{
                        new_child_addr,
                        receipt,
                        split_arg,
                        read_nodes,
                        write_nodes,
                    } => (new_child_addr, receipt, split_arg, read_nodes, write_nodes),
                    _ => arbitrary(),
                };
                let branch_lbl = CachedBranch::Label::Split{
                    mini_allocator: pre.mini_allocator,
                    new_child_addr,
                    receipt,
                    split_arg,
                    read_nodes,
                    write_nodes,
                };
                assert(CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                assert(CachedBranch::State::next_by(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                    CachedBranch::Step::split_step(),
                ));
                assert(CachedBranch::State::split_step(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                ));
                assert(pre.mini_allocator.can_allocate(new_child_addr));
                assert(new_child_addr.wf());
                assert(post.mini_allocator.wf());
            },
            AtomicBranchState::Step::seal() => {
                assert(AtomicBranchState::State::seal(pre, post, lbl));
                pre.mini_allocator.prune_preserves_wf(lbl->summary);
                let n = pre.persistent_image.sealed_roots.len();
                assert(post.persistent_image == pre.persistent_image);
                assert(post.image.sealed_roots == pre.image.sealed_roots.push(pre.active_branch.root.unwrap()));
                assert(n <= pre.image.sealed_roots.len());
                assert forall |i: int| #![auto] 0 <= i < n implies
                    post.image.sealed_roots[i] == pre.image.sealed_roots[i]
                by {
                    assert(post.image.sealed_roots[i] == pre.image.sealed_roots.push(pre.active_branch.root.unwrap())[i]);
                }
	                assert(post.image.sealed_roots.take(n as int) == pre.image.sealed_roots.take(n as int));
	                assert(post.active_branch == CachedBranch::State::empty_active());
	                assert(post.active_branch.wf());
	            },
            AtomicBranchState::Step::fill_aus() => {
                assert(AtomicBranchState::State::fill_aus(pre, post, lbl));
                assert(post.mini_allocator.wf());
            },
            AtomicBranchState::Step::observe_persisted_roots() => {
                assert(AtomicBranchState::State::observe_persisted_roots(pre, post, lbl));
            },
            AtomicBranchState::Step::commit_start() => {
                assert(AtomicBranchState::State::commit_start(pre, post, lbl));
                let branch_image = match lbl {
                    AtomicBranchState::Label::CommitStart{branch_image} => branch_image,
                    _ => arbitrary(),
                };
                assert(post.image == pre.image);
                assert(post.persisted_root_count == pre.persisted_root_count);
                assert(post.in_flight == Option::Some(branch_image));
                if branch_image == pre.persistent_image {
                    assert(branch_image.sealed_roots.len() <= pre.image.sealed_roots.len());
                    assert(pre.image.sealed_roots.take(branch_image.sealed_roots.len() as int)
                        == branch_image.sealed_roots);
                    assert(branch_image.sealed_roots.len() <= pre.persisted_root_count);
                    assert(branch_image.seq_end <= pre.seq_end);
                    assert(post.image.sealed_roots.take(branch_image.sealed_roots.len() as int)
                        == branch_image.sealed_roots);
                } else {
                    assert(branch_image == pre.freeze_image());
                    assert(branch_image.sealed_roots == pre.image.sealed_roots);
                    assert(branch_image.seq_end == pre.seq_end);
                    assert(branch_image.sealed_roots.len() == post.image.sealed_roots.len());
                    assert forall |i: int| #![auto] 0 <= i < branch_image.sealed_roots.len() implies
                        post.image.sealed_roots.take(branch_image.sealed_roots.len() as int)[i]
                            == branch_image.sealed_roots[i]
                    by {
                        assert(post.image.sealed_roots.take(branch_image.sealed_roots.len() as int)[i]
                            == post.image.sealed_roots[i]);
                    }
                    assert(post.image.sealed_roots.take(branch_image.sealed_roots.len() as int)
                        == branch_image.sealed_roots);
                }
            },
            AtomicBranchState::Step::commit_prepared() => {
                assert(AtomicBranchState::State::commit_prepared(pre, post, lbl));
                assert(post == AtomicBranchState::State{
                    prepared: true,
                    ..pre
                });
            },
            AtomicBranchState::Step::commit_complete() => {
                assert(AtomicBranchState::State::commit_complete(pre, post, lbl));
                assert(pre.in_flight is Some);
                let image = pre.in_flight.unwrap();
                let n = image.sealed_roots.len();
                assert(post.persistent_image == image);
                assert(post.image.sealed_roots.take(n as int) == image.sealed_roots);
                assert(post.image.sealed_roots.take(post.persistent_image.sealed_roots.len() as int)
                    == post.persistent_image.sealed_roots);
            },
            AtomicBranchState::Step::dummy_to_use_type_params(_) => {
                assert(false);
            },
        }
        if post.in_flight is Some {
            let image = post.in_flight.unwrap();
            match step {
                AtomicBranchState::Step::query() => {
                    assert(AtomicBranchState::State::query(pre, post, lbl));
                    assert(post == pre);
                },
                AtomicBranchState::Step::load_metadata() => {
                    assert(AtomicBranchState::State::load_metadata(pre, post, lbl));
                    assert(post.image == pre.image);
                    assert(post.in_flight == pre.in_flight);
                },
                AtomicBranchState::Step::append_nonempty(new_active_branch) => {
                    assert(AtomicBranchState::State::append_nonempty(
                        pre,
                        post,
                        lbl,
                        new_active_branch,
                    ));
                    assert(post.image == pre.image);
                    assert(post.in_flight == pre.in_flight);
                },
                AtomicBranchState::Step::append_empty(new_active_branch) => {
                    assert(AtomicBranchState::State::append_empty(pre, post, lbl, new_active_branch));
                    assert(post.image == pre.image);
                    assert(post.in_flight == pre.in_flight);
                },
                AtomicBranchState::Step::grow(new_active_branch) => {
                    assert(AtomicBranchState::State::grow(pre, post, lbl, new_active_branch));
                    assert(post.image == pre.image);
                    assert(post.in_flight == pre.in_flight);
                },
                AtomicBranchState::Step::split(new_active_branch) => {
                    assert(AtomicBranchState::State::split(pre, post, lbl, new_active_branch));
                    assert(post.image == pre.image);
                    assert(post.in_flight == pre.in_flight);
                },
                AtomicBranchState::Step::seal() => {
                    assert(AtomicBranchState::State::seal(pre, post, lbl));
                    assert(post.in_flight == pre.in_flight);
                    let n = image.sealed_roots.len();
                    assert(n <= pre.image.sealed_roots.len());
                    assert(pre.image.sealed_roots.take(n as int) == image.sealed_roots);
                    assert(post.image.sealed_roots == pre.image.sealed_roots.push(pre.active_branch.root.unwrap()));
                    assert forall |i: int| #![auto] 0 <= i < n implies
                        post.image.sealed_roots[i] == pre.image.sealed_roots[i]
                    by {
                        assert(post.image.sealed_roots[i] == pre.image.sealed_roots.push(pre.active_branch.root.unwrap())[i]);
                    }
	                    assert(post.image.sealed_roots.take(n as int) == pre.image.sealed_roots.take(n as int));
	                    assert(post.image.sealed_roots.take(n as int) == image.sealed_roots);
	                    assert(post.active_branch == CachedBranch::State::empty_active());
	                    assert(post.active_branch.wf());
	                },
                AtomicBranchState::Step::fill_aus() => {
                    assert(AtomicBranchState::State::fill_aus(pre, post, lbl));
                    assert(post.image == pre.image);
                    assert(post.in_flight == pre.in_flight);
                },
                AtomicBranchState::Step::observe_persisted_roots() => {
                    assert(AtomicBranchState::State::observe_persisted_roots(pre, post, lbl));
                    assert(post.image == pre.image);
                    assert(post.in_flight == pre.in_flight);
                },
                AtomicBranchState::Step::commit_start() => {
                    assert(AtomicBranchState::State::commit_start(pre, post, lbl));
                    let branch_image = match lbl {
                        AtomicBranchState::Label::CommitStart{branch_image} => branch_image,
                        _ => arbitrary(),
                    };
                    assert(image == branch_image);
                },
                AtomicBranchState::Step::commit_prepared() => {
                    assert(AtomicBranchState::State::commit_prepared(pre, post, lbl));
                    assert(post == AtomicBranchState::State{
                        prepared: true,
                        ..pre
                    });
                    assert(post.in_flight == pre.in_flight);
                },
                AtomicBranchState::Step::commit_complete() => {
                    assert(false);
                },
                AtomicBranchState::Step::dummy_to_use_type_params(_) => {
                    assert(false);
                },
            }
        }
        assert(post.wf());
    }

    pub proof fn append_preserves_owned_aus(pre: Self, post: Self, lbl: AtomicBranchState::Label)
        requires
            pre.wf(),
            AtomicBranchState::State::next(pre, post, lbl),
            lbl is Append,
        ensures
            post.image == pre.image,
            post.branch_summary == pre.branch_summary,
            post.mini_allocator.all_aus() == pre.mini_allocator.all_aus(),
            post.owned_aus() == pre.owned_aus(),
    {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let step = choose |step| AtomicBranchState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicBranchState::Step::append_nonempty(new_active_branch) => {
                assert(AtomicBranchState::State::append_nonempty(
                    pre,
                    post,
                    lbl,
                    new_active_branch,
                ));
                assert(post.branch_summary == pre.branch_summary);
                assert(post.mini_allocator == pre.mini_allocator);
                assert(post.mini_allocator.all_aus() == pre.mini_allocator.all_aus());
                assert(post.owned_aus() == pre.owned_aus());
            },
            AtomicBranchState::Step::append_empty(new_active_branch) => {
                assert(AtomicBranchState::State::append_empty(pre, post, lbl, new_active_branch));
                assert(post.branch_summary == pre.branch_summary);
                let (keys, msgs, init_root, write_nodes) = match lbl {
                    AtomicBranchState::Label::Append{keys, msgs, init_root, write_nodes, ..} =>
                        (keys, msgs, init_root, write_nodes),
                    _ => arbitrary(),
                };
                assert(init_root is Some);
                let init_addr = init_root.unwrap();
                let branch_lbl = CachedBranch::Label::Initialize{
                    mini_allocator: pre.mini_allocator,
                    init_root: init_addr,
                    keys,
                    msgs,
                    write_nodes,
                };
                assert(CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                assert(CachedBranch::State::next_by(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                    CachedBranch::Step::initialize_branch(),
                ));
                assert(CachedBranch::State::initialize_branch(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                ));
                assert(pre.mini_allocator.can_allocate(init_addr));
                crate::implementation::AllocationBranchStack_v::mini_allocator_allocate_preserves_all_aus(
                    pre.mini_allocator,
                    init_addr,
                );
                assert(post.mini_allocator.all_aus() == pre.mini_allocator.all_aus());
                assert(post.owned_aus() == pre.owned_aus());
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn append_effect(pre: Self, post: Self, lbl: AtomicBranchState::Label)
        requires
            AtomicBranchState::State::next(pre, post, lbl),
            lbl is Append,
        ensures
            post.image == pre.image,
            post.persistent_image == pre.persistent_image,
            post.in_flight == pre.in_flight,
            post.prepared == pre.prepared,
            post.branch_summary == pre.branch_summary,
            post.persisted_root_count == pre.persisted_root_count,
            post.seq_end == pre.seq_end + lbl->keys.len(),
    {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let step = choose |step| AtomicBranchState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicBranchState::Step::append_nonempty(new_active_branch) => {
                assert(AtomicBranchState::State::append_nonempty(
                    pre,
                    post,
                    lbl,
                    new_active_branch,
                ));
            },
            AtomicBranchState::Step::append_empty(new_active_branch) => {
                assert(AtomicBranchState::State::append_empty(pre, post, lbl, new_active_branch));
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn grow_preserves_backing_aus(pre: Self, post: Self, lbl: AtomicBranchState::Label)
        requires
            pre.wf(),
            AtomicBranchState::State::next(pre, post, lbl),
            lbl is Grow,
        ensures
            post.image == pre.image,
            post.branch_summary == pre.branch_summary,
            post.mini_allocator.all_aus() == pre.mini_allocator.all_aus(),
    {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let step = choose |step| AtomicBranchState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicBranchState::Step::grow(new_active_branch) => {
                assert(AtomicBranchState::State::grow(pre, post, lbl, new_active_branch));
                let (new_root_addr, read_nodes, write_nodes) = match lbl {
                    AtomicBranchState::Label::Grow{new_root_addr, read_nodes, write_nodes} =>
                        (new_root_addr, read_nodes, write_nodes),
                    _ => arbitrary(),
                };
                let branch_lbl = CachedBranch::Label::Grow{
                    mini_allocator: pre.mini_allocator,
                    new_root_addr,
                    read_nodes,
                    write_nodes,
                };
                assert(CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                assert(CachedBranch::State::next_by(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                    CachedBranch::Step::grow_step(),
                ));
                assert(CachedBranch::State::grow_step(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                ));
                assert(pre.mini_allocator.can_allocate(new_root_addr));
                crate::implementation::AllocationBranchStack_v::mini_allocator_allocate_preserves_all_aus(
                    pre.mini_allocator,
                    new_root_addr,
                );
            },
            _ => { assert(false); },
        }
    }

    pub proof fn split_preserves_backing_aus(pre: Self, post: Self, lbl: AtomicBranchState::Label)
        requires
            pre.wf(),
            AtomicBranchState::State::next(pre, post, lbl),
            lbl is Split,
        ensures
            post.image == pre.image,
            post.branch_summary == pre.branch_summary,
            post.mini_allocator.all_aus() == pre.mini_allocator.all_aus(),
    {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let step = choose |step| AtomicBranchState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicBranchState::Step::split(new_active_branch) => {
                assert(AtomicBranchState::State::split(pre, post, lbl, new_active_branch));
                let (new_child_addr, receipt, split_arg, read_nodes, write_nodes) = match lbl {
                    AtomicBranchState::Label::Split{
                        new_child_addr,
                        receipt,
                        split_arg,
                        read_nodes,
                        write_nodes,
                    } => (new_child_addr, receipt, split_arg, read_nodes, write_nodes),
                    _ => arbitrary(),
                };
                let branch_lbl = CachedBranch::Label::Split{
                    mini_allocator: pre.mini_allocator,
                    new_child_addr,
                    receipt,
                    split_arg,
                    read_nodes,
                    write_nodes,
                };
                assert(CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                assert(CachedBranch::State::next_by(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                    CachedBranch::Step::split_step(),
                ));
                assert(CachedBranch::State::split_step(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                ));
                assert(pre.mini_allocator.can_allocate(new_child_addr));
                crate::implementation::AllocationBranchStack_v::mini_allocator_allocate_preserves_all_aus(
                    pre.mini_allocator,
                    new_child_addr,
                );
            },
            _ => { assert(false); },
        }
    }

    pub proof fn append_support_effect(pre: Self, post: Self, lbl: AtomicBranchState::Label)
        requires
            AtomicBranchState::State::next(pre, post, lbl),
            lbl is Append,
        ensures
            atomic_branch_support_addrs(post) == atomic_branch_support_addrs(pre),
    {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let step = choose |step| AtomicBranchState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicBranchState::Step::append_nonempty(new_active_branch) => {
                assert(AtomicBranchState::State::append_nonempty(
                    pre,
                    post,
                    lbl,
                    new_active_branch,
                )) by {
                    reveal(AtomicBranchState::State::append_nonempty);
                }
                assert(post.branch_summary == pre.branch_summary);
                assert(post.mini_allocator == pre.mini_allocator);
                assert(atomic_branch_support_addrs(post) == atomic_branch_support_addrs(pre));
            },
            AtomicBranchState::Step::append_empty(new_active_branch) => {
                assert(AtomicBranchState::State::append_empty(pre, post, lbl, new_active_branch)) by {
                    reveal(AtomicBranchState::State::append_empty);
                }
                let (keys, msgs, init_root, write_nodes) = match lbl {
                    AtomicBranchState::Label::Append{keys, msgs, init_root, write_nodes, ..} =>
                        (keys, msgs, init_root, write_nodes),
                    _ => arbitrary(),
                };
                assert(post.branch_summary == pre.branch_summary);
                assert(init_root is Some);
                let init_addr = init_root.unwrap();
                let branch_lbl = CachedBranch::Label::Initialize{
                    mini_allocator: pre.mini_allocator,
                    init_root: init_addr,
                    keys,
                    msgs,
                    write_nodes,
                };
                assert(CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                assert(CachedBranch::State::next_by(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                    CachedBranch::Step::initialize_branch(),
                ));
                assert(CachedBranch::State::initialize_branch(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                )) by {
                    reveal(CachedBranch::State::initialize_branch);
                }
                reveal(CachedBranch::State::initialize_branch);
                assert(pre.mini_allocator.wf());
                assert(pre.mini_allocator.can_allocate(init_addr));
                crate::implementation::AllocationBranchStack_v::mini_allocator_allocate_preserves_all_aus(
                    pre.mini_allocator,
                    init_addr,
                );
                assert(post.mini_allocator.all_aus() == pre.mini_allocator.all_aus());
                assert(atomic_branch_support_addrs(post) == atomic_branch_support_addrs(pre));
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn fill_aus_effect(pre: Self, post: Self, lbl: AtomicBranchState::Label)
        requires
            AtomicBranchState::State::next(pre, post, lbl),
            lbl is FillAUs,
        ensures
            post.image == pre.image,
            post.persistent_image == pre.persistent_image,
            post.in_flight == pre.in_flight,
            post.prepared == pre.prepared,
            post.branch_summary == pre.branch_summary,
            post.persisted_root_count == pre.persisted_root_count,
            post.active_branch == pre.active_branch,
            post.seq_end == pre.seq_end,
            post.mini_allocator == pre.mini_allocator.add_aus(lbl->aus),
            post.metadata_loaded() == pre.metadata_loaded(),
    {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let step = choose |step| AtomicBranchState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicBranchState::Step::fill_aus() => {
                assert(AtomicBranchState::State::fill_aus(pre, post, lbl)) by {
                    reveal(AtomicBranchState::State::fill_aus);
                }
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn commit_complete_effect(
        pre: Self,
        post: Self,
        lbl: AtomicBranchState::Label,
    )
        requires
            AtomicBranchState::State::next(pre, post, lbl),
            lbl is CommitComplete,
        ensures
            post.image == pre.image,
            post.branch_summary == pre.branch_summary,
            post.active_branch == pre.active_branch,
            post.mini_allocator == pre.mini_allocator,
            post.seq_end == pre.seq_end,
            pre.in_flight is Some,
            post.in_flight is None,
            post.prepared == false,
            post.persistent_image == pre.in_flight.unwrap(),
            post.owned_aus() == pre.owned_aus(),
            post.metadata_loaded() == pre.metadata_loaded(),
    {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let step = choose |step| AtomicBranchState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicBranchState::Step::commit_complete() => {
                assert(AtomicBranchState::State::commit_complete(pre, post, lbl));
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn commit_start_effect(
        pre: Self,
        post: Self,
        lbl: AtomicBranchState::Label,
    )
        requires
            AtomicBranchState::State::next(pre, post, lbl),
            lbl is CommitStart,
        ensures
            post.image == pre.image,
            post.persistent_image == pre.persistent_image,
            post.branch_summary == pre.branch_summary,
            post.persisted_root_count == pre.persisted_root_count,
            post.active_branch == pre.active_branch,
            post.mini_allocator == pre.mini_allocator,
            post.seq_end == pre.seq_end,
            post.in_flight == Option::Some(lbl->branch_image),
            post.prepared == false,
    {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let step = choose |step| AtomicBranchState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicBranchState::Step::commit_start() => {
                assert(AtomicBranchState::State::commit_start(pre, post, lbl));
            },
            _ => {
                assert(false);
            },
        }
    }
}

} // verus!
