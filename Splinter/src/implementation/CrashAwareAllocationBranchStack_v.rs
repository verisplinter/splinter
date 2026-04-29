// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::map::*;

use verus_state_machines_macros::state_machine;

use crate::allocation_layer::AllocationBranch_v::{AllocationBranch, BranchNode, Summary};
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::LinkedBranch_v::{Path, SplitArg};
use crate::disk::GenericDisk_v::{AU, Address, Pointer};
use crate::implementation::AllocationBranchStack_v::{
    mini_allocator_add_aus_preserves_all_aus, mini_allocator_allocate_preserves_all_aus,
    new_branch_inv, AllocationBranchStack, SealedAllocationBranchStack,
};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::Message;

verus! {

pub enum EphemeralAllocationBranchStack {
    Unknown,
    Known{ v: AllocationBranchStack::State },
}

pub struct InFlightAllocationBranchStack {
    pub sealed_stack: SealedAllocationBranchStack,
    pub seq_end: nat,
}

pub open spec fn empty_sealed_stack() -> SealedAllocationBranchStack
{
    SealedAllocationBranchStack{
        sealed_roots: Seq::empty(),
        sealed_disk: BufferDisk{ entries: Map::empty() },
    }
}

pub open spec fn load_stack(
    persistent: SealedAllocationBranchStack,
    persistent_seq_end: nat,
    init_aus: Set<AU>,
) -> AllocationBranchStack::State
{
    AllocationBranchStack::State{
        sealed_stack: persistent,
        branch_summary: persistent.branch_summary(),
        active_branch: AllocationBranch::new(init_aus),
        seq_end: persistent_seq_end,
    }
}

state_machine!{ CrashAwareAllocationBranchStack {
    fields {
        pub persistent: SealedAllocationBranchStack,
        pub persistent_seq_end: nat,
        pub ephemeral: EphemeralAllocationBranchStack,
        pub in_flight: Option<InFlightAllocationBranchStack>,
    }

    pub enum Label {
        LoadEphemeral{ init_aus: Set<AU> },
        Query{ key: Key, msg: Message },
        Append{ keys: Seq<Key>, msgs: Seq<Message> },
        Internal,
        CommitStart{ new_boundary_lsn: nat },
        CommitComplete,
        Crash{ keep_in_flight: bool },
    }

    init!{ initialize() {
        init persistent = empty_sealed_stack();
        init persistent_seq_end = 0;
        init ephemeral = EphemeralAllocationBranchStack::Unknown;
        init in_flight = Option::None;
    }}

    transition!{ load_ephemeral(lbl: Label) {
        require pre.wf();
        require let Label::LoadEphemeral{init_aus} = lbl;
        require pre.ephemeral is Unknown;
        require pre.in_flight is None;
        let stack = load_stack(pre.persistent, pre.persistent_seq_end, init_aus);
        require stack.wf();
        update ephemeral = EphemeralAllocationBranchStack::Known{ v: stack };
    }}

    transition!{ query(lbl: Label, new_stack: AllocationBranchStack::State) {
        require pre.wf();
        require let Label::Query{key, msg} = lbl;
        require pre.ephemeral is Known;
        let old_stack = pre.ephemeral->v;
        let stack_lbl = AllocationBranchStack::Label::QueryLabel{key, msg};
        require AllocationBranchStack::State::query_step(old_stack, new_stack, stack_lbl);
        update ephemeral = EphemeralAllocationBranchStack::Known{ v: new_stack };
    }}

    transition!{ append_to_active(
        lbl: Label,
        new_stack: AllocationBranchStack::State,
        path: Path<Summary>,
    ) {
        require pre.wf();
        require let Label::Append{keys, msgs} = lbl;
        require pre.ephemeral is Known;
        let old_stack = pre.ephemeral->v;
        let stack_lbl = AllocationBranchStack::Label::AppendLabel{keys, msgs};
        require AllocationBranchStack::State::append_to_active(old_stack, new_stack, stack_lbl, path);
        update ephemeral = EphemeralAllocationBranchStack::Known{ v: new_stack };
    }}

    transition!{ append_to_empty(
        lbl: Label,
        new_stack: AllocationBranchStack::State,
        init_root: Address,
    ) {
        require pre.wf();
        require let Label::Append{keys, msgs} = lbl;
        require pre.ephemeral is Known;
        let old_stack = pre.ephemeral->v;
        let stack_lbl = AllocationBranchStack::Label::AppendLabel{keys, msgs};
        require AllocationBranchStack::State::append_to_empty(old_stack, new_stack, stack_lbl, init_root);
        update ephemeral = EphemeralAllocationBranchStack::Known{ v: new_stack };
    }}

    transition!{ ephemeral_internal_noop(lbl: Label, new_stack: AllocationBranchStack::State) {
        require pre.wf();
        require lbl is Internal;
        require pre.ephemeral is Known;
        let old_stack = pre.ephemeral->v;
        require AllocationBranchStack::State::internal_noop(
            old_stack,
            new_stack,
            AllocationBranchStack::Label::InternalLabel,
        );
        update ephemeral = EphemeralAllocationBranchStack::Known{ v: new_stack };
    }}

    transition!{ ephemeral_internal_grow(
        lbl: Label,
        new_stack: AllocationBranchStack::State,
        new_root_addr: Address,
    ) {
        require pre.wf();
        require lbl is Internal;
        require pre.ephemeral is Known;
        let old_stack = pre.ephemeral->v;
        require AllocationBranchStack::State::internal_grow(
            old_stack,
            new_stack,
            AllocationBranchStack::Label::InternalLabel,
            new_root_addr,
        );
        update ephemeral = EphemeralAllocationBranchStack::Known{ v: new_stack };
    }}

    transition!{ ephemeral_internal_split(
        lbl: Label,
        new_stack: AllocationBranchStack::State,
        new_child_addr: Address,
        path: Path<Summary>,
        split_arg: SplitArg,
    ) {
        require pre.wf();
        require lbl is Internal;
        require pre.ephemeral is Known;
        let old_stack = pre.ephemeral->v;
        require AllocationBranchStack::State::internal_split(
            old_stack,
            new_stack,
            AllocationBranchStack::Label::InternalLabel,
            new_child_addr,
            path,
            split_arg,
        );
        update ephemeral = EphemeralAllocationBranchStack::Known{ v: new_stack };
    }}

    transition!{ ephemeral_internal_seal(
        lbl: Label,
        new_stack: AllocationBranchStack::State,
        aux_ptr: Pointer,
    ) {
        require pre.wf();
        require lbl is Internal;
        require pre.ephemeral is Known;
        let old_stack = pre.ephemeral->v;
        require AllocationBranchStack::State::internal_seal(
            old_stack,
            new_stack,
            AllocationBranchStack::Label::InternalLabel,
            aux_ptr,
        );
        update ephemeral = EphemeralAllocationBranchStack::Known{ v: new_stack };
    }}

    transition!{ ephemeral_internal_fill_au(
        lbl: Label,
        new_stack: AllocationBranchStack::State,
        aus: Set<AU>,
    ) {
        require pre.wf();
        require lbl is Internal;
        require pre.ephemeral is Known;
        let old_stack = pre.ephemeral->v;
        require AllocationBranchStack::State::internal_fill_au(
            old_stack,
            new_stack,
            AllocationBranchStack::Label::InternalLabel,
            aus,
        );
        update ephemeral = EphemeralAllocationBranchStack::Known{ v: new_stack };
    }}

    transition!{ freeze_map_internal(lbl: Label) {
        require pre.wf();
        require lbl is Internal;
        require pre.ephemeral is Known;
        require pre.in_flight is None;
        let stack = pre.ephemeral->v;
        let sealed_stack = stack.freeze_snapshot();
        require AllocationBranchStack::State::freeze_as(
            stack,
            stack,
            AllocationBranchStack::Label::FreezeAsLabel{ sealed_stack },
        );
        update in_flight = Option::Some(InFlightAllocationBranchStack{ sealed_stack, seq_end: stack.seq_end });
    }}

    transition!{ freeze_persistent_internal(lbl: Label) {
        require pre.wf();
        require lbl is Internal;
        require pre.ephemeral is Known;
        require pre.in_flight is None;
        update in_flight = Option::Some(InFlightAllocationBranchStack{
            sealed_stack: pre.persistent,
            seq_end: pre.persistent_seq_end,
        });
    }}

    transition!{ commit_start(lbl: Label) {
        require pre.wf();
        require let Label::CommitStart{new_boundary_lsn} = lbl;
        require pre.ephemeral is Known;
        require pre.in_flight is Some;
        require new_boundary_lsn == pre.in_flight.unwrap().seq_end;
    }}

    transition!{ commit_complete(lbl: Label) {
        require pre.wf();
        require lbl is CommitComplete;
        require pre.in_flight is Some;
        update persistent = pre.in_flight.unwrap().sealed_stack;
        update persistent_seq_end = pre.in_flight.unwrap().seq_end;
        update in_flight = Option::None;
    }}

    transition!{ crash(lbl: Label) {
        require pre.wf();
        require let Label::Crash{keep_in_flight} = lbl;
        require keep_in_flight ==> pre.in_flight is Some;
        update ephemeral = EphemeralAllocationBranchStack::Unknown;
        update in_flight = Option::None;
        update persistent = if keep_in_flight {
            pre.in_flight.unwrap().sealed_stack
        } else {
            pre.persistent
        };
        update persistent_seq_end = if keep_in_flight {
            pre.in_flight.unwrap().seq_end
        } else {
            pre.persistent_seq_end
        };
    }}

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.wf()
        &&& self.stack_compatible()
    }

    #[invariant]
    pub open spec(checked) fn stack_compatible(self) -> bool {
        &&& self.in_flight is Some ==> self.persistent_seq_end <= self.in_flight.unwrap().seq_end
        &&& self.ephemeral is Known ==> self.persistent_seq_end <= self.ephemeral->v.seq_end
        &&& self.ephemeral is Known && self.in_flight is Some
            ==> self.in_flight.unwrap().seq_end <= self.ephemeral->v.seq_end
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) {
        assert(post.persistent.wf());
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(load_ephemeral)]
    fn load_ephemeral_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(query)]
    fn query_inductive(pre: Self, post: Self, lbl: Label, new_stack: AllocationBranchStack::State) {
        match lbl {
            Label::Query{key, msg} => {
                reveal(AllocationBranchStack::State::query_step);
                assert(new_stack == pre.ephemeral->v);
            }
            _ => { }
        }
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(append_to_active)]
    fn append_to_active_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_stack: AllocationBranchStack::State,
        path: Path<Summary>,
    ) {
        match lbl {
            Label::Append{keys, msgs} => {
                let old_stack = pre.ephemeral->v;
                reveal(AllocationBranchStack::State::append_to_active);
                AllocationBranch::build_next_preserves_inv(
                    old_stack.active_branch,
                    new_stack.active_branch,
                    crate::allocation_layer::AllocationBranch_v::BuildEvent::Append{keys, msgs, path},
                    Set::empty(),
                    Set::empty(),
                );
                assert(new_stack.active_branch.mini_allocator == old_stack.active_branch.mini_allocator);
                assert(new_stack.wf());
                assert(new_stack.sealed_stack == old_stack.sealed_stack);
            }
            _ => { }
        }
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(append_to_empty)]
    fn append_to_empty_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_stack: AllocationBranchStack::State,
        init_root: Address,
    ) {
        match lbl {
            Label::Append{keys, msgs} => {
                let old_stack = pre.ephemeral->v;
                reveal(AllocationBranchStack::State::append_to_empty);
                AllocationBranch::build_next_preserves_inv(
                    old_stack.active_branch,
                    new_stack.active_branch,
                    crate::allocation_layer::AllocationBranch_v::BuildEvent::Initialize{addr: init_root, keys, msgs},
                    Set::empty(),
                    Set::empty(),
                );
                mini_allocator_allocate_preserves_all_aus(old_stack.active_branch.mini_allocator, init_root);
                assert(new_stack.wf());
                assert(new_stack.sealed_stack == old_stack.sealed_stack);
            }
            _ => { }
        }
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(ephemeral_internal_noop)]
    fn ephemeral_internal_noop_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_stack: AllocationBranchStack::State,
    ) {
        let old_stack = pre.ephemeral->v;
        reveal(AllocationBranchStack::State::internal_noop);
        assert(new_stack == old_stack);
        assert(new_stack.sealed_stack == old_stack.sealed_stack);
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(ephemeral_internal_grow)]
    fn ephemeral_internal_grow_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_stack: AllocationBranchStack::State,
        new_root_addr: Address,
    ) {
        let old_stack = pre.ephemeral->v;
        reveal(AllocationBranchStack::State::internal_grow);
        AllocationBranch::build_next_preserves_inv(
            old_stack.active_branch,
            new_stack.active_branch,
            crate::allocation_layer::AllocationBranch_v::BuildEvent::Grow{addr: new_root_addr},
            Set::empty(),
            Set::empty(),
        );
        mini_allocator_allocate_preserves_all_aus(old_stack.active_branch.mini_allocator, new_root_addr);
        assert(new_stack.wf());
        assert(new_stack.sealed_stack == old_stack.sealed_stack);
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(ephemeral_internal_split)]
    fn ephemeral_internal_split_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_stack: AllocationBranchStack::State,
        new_child_addr: Address,
        path: Path<Summary>,
        split_arg: SplitArg,
    ) {
        let old_stack = pre.ephemeral->v;
        reveal(AllocationBranchStack::State::internal_split);
        AllocationBranch::build_next_preserves_inv(
            old_stack.active_branch,
            new_stack.active_branch,
            crate::allocation_layer::AllocationBranch_v::BuildEvent::Split{
                addr: new_child_addr,
                path,
                split_arg,
            },
            Set::empty(),
            Set::empty(),
        );
        mini_allocator_allocate_preserves_all_aus(old_stack.active_branch.mini_allocator, new_child_addr);
        assert(new_stack.wf());
        assert(new_stack.sealed_stack == old_stack.sealed_stack);
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(ephemeral_internal_seal)]
    fn ephemeral_internal_seal_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_stack: AllocationBranchStack::State,
        aux_ptr: Pointer,
    ) {
        let old_stack = pre.ephemeral->v;
        reveal(AllocationBranchStack::State::internal_seal);
        let dealloc_aus = old_stack.active_branch.mini_allocator.removable_aus();
        let sealed_active = old_stack.active_branch.branch_seal(aux_ptr, dealloc_aus);
        let sealed_branch = sealed_active.branch.unwrap();
        AllocationBranch::build_next_preserves_inv(
            old_stack.active_branch,
            sealed_active,
            crate::allocation_layer::AllocationBranch_v::BuildEvent::Seal{aux_ptr},
            Set::empty(),
            dealloc_aus,
        );
        old_stack.sealed_stack.push_branch_preserves_wf(sealed_branch);
        new_branch_inv(Set::empty());
        assert(new_stack.wf());
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(ephemeral_internal_fill_au)]
    fn ephemeral_internal_fill_au_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_stack: AllocationBranchStack::State,
        aus: Set<AU>,
    ) {
        let old_stack = pre.ephemeral->v;
        reveal(AllocationBranchStack::State::internal_fill_au);
        AllocationBranch::build_next_preserves_inv(
            old_stack.active_branch,
            new_stack.active_branch,
            crate::allocation_layer::AllocationBranch_v::BuildEvent::AllocFill{},
            aus,
            Set::empty(),
        );
        mini_allocator_add_aus_preserves_all_aus(old_stack.active_branch.mini_allocator, aus);
        assert(new_stack.wf());
        assert(new_stack.sealed_stack == old_stack.sealed_stack);
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(freeze_map_internal)]
    fn freeze_map_internal_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(freeze_persistent_internal)]
    fn freeze_persistent_internal_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(commit_start)]
    fn commit_start_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(commit_complete)]
    fn commit_complete_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(crash)]
    fn crash_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
        assert(post.stack_compatible());
    }
}}

impl CrashAwareAllocationBranchStack::State {
    pub open spec fn wf(self) -> bool
    {
        &&& self.persistent.wf()
        &&& self.in_flight is Some ==> self.in_flight.unwrap().sealed_stack.wf()
        &&& self.ephemeral is Unknown ==> self.in_flight is None
        &&& self.ephemeral is Known ==> self.ephemeral->v.wf()
    }
}

}
