// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::map::*;

use verus_state_machines_macros::state_machine;

use crate::allocation_layer::AllocationBranch_v::{AllocationBranch, BranchNode, Summary};
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::LinkedBranch_v::{Path, SplitArg};
use crate::disk::GenericDisk_v::{AU, Address, Pointer, to_aus};
use crate::implementation::AllocationBranchStack_v::{
    mini_allocator_add_aus_preserves_all_aus, mini_allocator_allocate_preserves_all_aus,
    new_branch_inv, normalize_value, AllocationBranchStack, SealedAllocationBranchStack,
};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Message, Value};

verus! {

pub enum EphemeralAllocationBranchStack {
    Unknown,
    Known{ v: AllocationBranchStack::State },
}

pub struct FrozenAllocationBranchStack {
    pub sealed_stack: SealedAllocationBranchStack,
    pub branch_summary: Map<AU, Summary>,
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
    persistent_branch_summary: Map<AU, Summary>,
    persistent_seq_end: nat,
    free_aus: Set<AU>,
) -> AllocationBranchStack::State
{
    AllocationBranchStack::State{
        sealed_stack: persistent,
        branch_summary: persistent_branch_summary,
        active_branch: AllocationBranch::new(free_aus),
        seq_end: persistent_seq_end,
    }
}

state_machine!{ CrashAwareAllocationBranchStack {
    fields {
        pub persistent: SealedAllocationBranchStack,
        pub persistent_branch_summary: Map<AU, Summary>,
        pub persistent_seq_end: nat,
        pub ephemeral: EphemeralAllocationBranchStack,
        pub frozen: Option<FrozenAllocationBranchStack>,
    }

    pub enum Label {
        LoadEphemeral{ free_aus: Set<AU> },
        Query{ key: Key, value: Value },
        Append{ keys: Seq<Key>, msgs: Seq<Message> },
        Internal,
        CommitStart{ new_boundary_lsn: nat, frozen_stack: FrozenAllocationBranchStack },
        CommitComplete,
        Crash{ keep_in_flight: bool },
    }

    init!{ initialize() {
        init persistent = empty_sealed_stack();
        init persistent_branch_summary = Map::empty();
        init persistent_seq_end = 0;
        init ephemeral = EphemeralAllocationBranchStack::Unknown;
        init frozen = Option::None;
    }}

    transition!{ load_ephemeral(lbl: Label) {
        require let Label::LoadEphemeral{free_aus} = lbl;
        require pre.ephemeral is Unknown;
        require pre.frozen is None;
        let stack = load_stack(
            pre.persistent,
            pre.persistent_branch_summary,
            pre.persistent_seq_end,
            free_aus,
        );
        require stack.wf();
        update ephemeral = EphemeralAllocationBranchStack::Known{ v: stack };
    }}

    transition!{ query(lbl: Label, new_stack: AllocationBranchStack::State, msg: Message) {
        require let Label::Query{key, value} = lbl;
        require pre.ephemeral is Known;
        let old_stack = pre.ephemeral->v;
        require normalize_value(msg) == value;
        let stack_lbl = AllocationBranchStack::Label::QueryLabel{key, msg};
        require AllocationBranchStack::State::query_step(old_stack, new_stack, stack_lbl);
        update ephemeral = EphemeralAllocationBranchStack::Known{ v: new_stack };
    }}

    transition!{ append_to_active(
        lbl: Label,
        new_stack: AllocationBranchStack::State,
        path: Path<Summary>,
    ) {
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
        require let Label::Append{keys, msgs} = lbl;
        require pre.ephemeral is Known;
        let old_stack = pre.ephemeral->v;
        let stack_lbl = AllocationBranchStack::Label::AppendLabel{keys, msgs};
        require AllocationBranchStack::State::append_to_empty(old_stack, new_stack, stack_lbl, init_root);
        update ephemeral = EphemeralAllocationBranchStack::Known{ v: new_stack };
    }}

    transition!{ ephemeral_internal_noop(lbl: Label, new_stack: AllocationBranchStack::State) {
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
        loose_active_disk: BufferDisk<BranchNode>,
    ) {
        require lbl is Internal;
        require pre.ephemeral is Known;
        let old_stack = pre.ephemeral->v;
        require AllocationBranchStack::State::internal_seal(
            old_stack,
            new_stack,
            AllocationBranchStack::Label::InternalLabel,
            aux_ptr,
            loose_active_disk,
        );
        update ephemeral = EphemeralAllocationBranchStack::Known{ v: new_stack };
    }}

    transition!{ ephemeral_internal_fill_au(
        lbl: Label,
        new_stack: AllocationBranchStack::State,
        aus: Set<AU>,
    ) {
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
        require lbl is Internal;
        require pre.ephemeral is Known;
        let stack = pre.ephemeral->v;
        let sealed_stack = stack.freeze_snapshot();
        require AllocationBranchStack::State::freeze_as(
            stack,
            stack,
            AllocationBranchStack::Label::FreezeAsLabel{ sealed_stack },
        );
    }}

    transition!{ commit_start_ephemeral(lbl: Label) {
        require let Label::CommitStart{new_boundary_lsn, frozen_stack} = lbl;
        require pre.ephemeral is Known;
        require pre.frozen is None;
        require new_boundary_lsn == frozen_stack.seq_end;
        require frozen_stack.seq_end == pre.ephemeral->v.seq_end;
        require AllocationBranchStack::State::freeze_as(
            pre.ephemeral->v,
            pre.ephemeral->v,
            AllocationBranchStack::Label::FreezeAsLabel{ sealed_stack: frozen_stack.sealed_stack },
        );
        require frozen_stack.branch_summary == pre.ephemeral->v.branch_summary;
        update frozen = Option::Some(frozen_stack);
    }}

    transition!{ commit_start_persistent(lbl: Label) {
        require let Label::CommitStart{new_boundary_lsn, frozen_stack} = lbl;
        require pre.ephemeral is Known;
        require pre.frozen is None;
        require new_boundary_lsn == frozen_stack.seq_end;
        require frozen_stack.sealed_stack == pre.persistent;
        require frozen_stack.branch_summary == pre.persistent_branch_summary;
        require frozen_stack.seq_end == pre.persistent_seq_end;
        update frozen = Option::Some(frozen_stack);
    }}

    transition!{ commit_complete(lbl: Label) {
        require lbl is CommitComplete;
        require pre.frozen is Some;
        update persistent = pre.frozen.unwrap().sealed_stack;
        update persistent_branch_summary = pre.frozen.unwrap().branch_summary;
        update persistent_seq_end = pre.frozen.unwrap().seq_end;
        update frozen = Option::None;
    }}

    transition!{ crash(lbl: Label) {
        require let Label::Crash{keep_in_flight} = lbl;
        require keep_in_flight ==> pre.frozen is Some;
        update ephemeral = EphemeralAllocationBranchStack::Unknown;
        update frozen = Option::None;
        update persistent = if keep_in_flight {
            pre.frozen.unwrap().sealed_stack
        } else {
            pre.persistent
        };
        update persistent_branch_summary = if keep_in_flight {
            pre.frozen.unwrap().branch_summary
        } else {
            pre.persistent_branch_summary
        };
        update persistent_seq_end = if keep_in_flight {
            pre.frozen.unwrap().seq_end
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
        &&& self.frozen is Some ==> self.persistent_seq_end <= self.frozen.unwrap().seq_end
        &&& self.ephemeral is Known ==> self.persistent_seq_end <= self.ephemeral->v.seq_end
        &&& self.ephemeral is Known && self.frozen is Some
            ==> self.frozen.unwrap().seq_end <= self.ephemeral->v.seq_end
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) {
        assert(post.persistent.sealed_roots.to_set() =~= Set::<Address>::empty());
        assert(to_aus(post.persistent.sealed_roots.to_set()) =~= Set::<AU>::empty());
        assert(post.persistent_branch_summary.dom() =~= Set::<AU>::empty());
        assert(post.persistent_branch_summary.dom()
            =~= to_aus(post.persistent.sealed_roots.to_set()));
        assert(post.persistent.wf(post.persistent_branch_summary));
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(load_ephemeral)]
    fn load_ephemeral_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(query)]
    fn query_inductive(pre: Self, post: Self, lbl: Label, new_stack: AllocationBranchStack::State, msg: Message) {
        match lbl {
            Label::Query{key, value} => {
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
        loose_active_disk: BufferDisk<BranchNode>,
    ) {
        let old_stack = pre.ephemeral->v;
        reveal(AllocationBranchStack::State::internal_seal);
        reveal(AllocationBranchStack::State::next);
        reveal(AllocationBranchStack::State::next_by);
        assert(AllocationBranchStack::State::next_by(
            old_stack,
            new_stack,
            AllocationBranchStack::Label::InternalLabel,
            AllocationBranchStack::Step::internal_seal(aux_ptr, loose_active_disk),
        ));
        assert(AllocationBranchStack::State::next(
            old_stack,
            new_stack,
            AllocationBranchStack::Label::InternalLabel,
        ));
        AllocationBranchStack::State::inv_next(
            old_stack,
            new_stack,
            AllocationBranchStack::Label::InternalLabel,
        );
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

    #[inductive(commit_start_ephemeral)]
    fn commit_start_ephemeral_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(commit_start_persistent)]
    fn commit_start_persistent_inductive(pre: Self, post: Self, lbl: Label) {
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

    pub proof fn inv_next(pre: Self, post: Self, lbl: Label)
        requires
            pre.inv(),
            CrashAwareAllocationBranchStack::State::next(pre, post, lbl),
        ensures
            post.inv(),
    {
        reveal(CrashAwareAllocationBranchStack::State::next);
        reveal(CrashAwareAllocationBranchStack::State::next_by);

        let step = choose |step| CrashAwareAllocationBranchStack::State::next_by(pre, post, lbl, step);
        match step {
            CrashAwareAllocationBranchStack::Step::load_ephemeral() => {
                assert(CrashAwareAllocationBranchStack::State::load_ephemeral(pre, post, lbl)) by {
                    reveal(CrashAwareAllocationBranchStack::State::load_ephemeral);
                }
                CrashAwareAllocationBranchStack::State::load_ephemeral_inductive(pre, post, lbl);
            },
            CrashAwareAllocationBranchStack::Step::query(new_stack, msg) => {
                assert(CrashAwareAllocationBranchStack::State::query(pre, post, lbl, new_stack, msg)) by {
                    reveal(CrashAwareAllocationBranchStack::State::query);
                }
                CrashAwareAllocationBranchStack::State::query_inductive(pre, post, lbl, new_stack, msg);
            },
            CrashAwareAllocationBranchStack::Step::append_to_active(new_stack, path) => {
                assert(CrashAwareAllocationBranchStack::State::append_to_active(pre, post, lbl, new_stack, path)) by {
                    reveal(CrashAwareAllocationBranchStack::State::append_to_active);
                }
                CrashAwareAllocationBranchStack::State::append_to_active_inductive(pre, post, lbl, new_stack, path);
            },
            CrashAwareAllocationBranchStack::Step::append_to_empty(new_stack, init_root) => {
                assert(CrashAwareAllocationBranchStack::State::append_to_empty(pre, post, lbl, new_stack, init_root)) by {
                    reveal(CrashAwareAllocationBranchStack::State::append_to_empty);
                }
                CrashAwareAllocationBranchStack::State::append_to_empty_inductive(pre, post, lbl, new_stack, init_root);
            },
            CrashAwareAllocationBranchStack::Step::ephemeral_internal_noop(new_stack) => {
                assert(CrashAwareAllocationBranchStack::State::ephemeral_internal_noop(pre, post, lbl, new_stack)) by {
                    reveal(CrashAwareAllocationBranchStack::State::ephemeral_internal_noop);
                }
                CrashAwareAllocationBranchStack::State::ephemeral_internal_noop_inductive(pre, post, lbl, new_stack);
            },
            CrashAwareAllocationBranchStack::Step::ephemeral_internal_grow(new_stack, new_root_addr) => {
                assert(CrashAwareAllocationBranchStack::State::ephemeral_internal_grow(pre, post, lbl, new_stack, new_root_addr)) by {
                    reveal(CrashAwareAllocationBranchStack::State::ephemeral_internal_grow);
                }
                CrashAwareAllocationBranchStack::State::ephemeral_internal_grow_inductive(pre, post, lbl, new_stack, new_root_addr);
            },
            CrashAwareAllocationBranchStack::Step::ephemeral_internal_split(new_stack, new_child_addr, path, split_arg) => {
                assert(CrashAwareAllocationBranchStack::State::ephemeral_internal_split(pre, post, lbl, new_stack, new_child_addr, path, split_arg)) by {
                    reveal(CrashAwareAllocationBranchStack::State::ephemeral_internal_split);
                }
                CrashAwareAllocationBranchStack::State::ephemeral_internal_split_inductive(pre, post, lbl, new_stack, new_child_addr, path, split_arg);
            },
            CrashAwareAllocationBranchStack::Step::ephemeral_internal_seal(new_stack, aux_ptr, loose_active_disk) => {
                assert(CrashAwareAllocationBranchStack::State::ephemeral_internal_seal(pre, post, lbl, new_stack, aux_ptr, loose_active_disk)) by {
                    reveal(CrashAwareAllocationBranchStack::State::ephemeral_internal_seal);
                }
                CrashAwareAllocationBranchStack::State::ephemeral_internal_seal_inductive(pre, post, lbl, new_stack, aux_ptr, loose_active_disk);
            },
            CrashAwareAllocationBranchStack::Step::ephemeral_internal_fill_au(new_stack, aus) => {
                assert(CrashAwareAllocationBranchStack::State::ephemeral_internal_fill_au(pre, post, lbl, new_stack, aus)) by {
                    reveal(CrashAwareAllocationBranchStack::State::ephemeral_internal_fill_au);
                }
                CrashAwareAllocationBranchStack::State::ephemeral_internal_fill_au_inductive(pre, post, lbl, new_stack, aus);
            },
            CrashAwareAllocationBranchStack::Step::freeze_map_internal() => {
                assert(CrashAwareAllocationBranchStack::State::freeze_map_internal(pre, post, lbl)) by {
                    reveal(CrashAwareAllocationBranchStack::State::freeze_map_internal);
                }
                CrashAwareAllocationBranchStack::State::freeze_map_internal_inductive(pre, post, lbl);
            },
            CrashAwareAllocationBranchStack::Step::commit_start_ephemeral() => {
                assert(CrashAwareAllocationBranchStack::State::commit_start_ephemeral(pre, post, lbl)) by {
                    reveal(CrashAwareAllocationBranchStack::State::commit_start_ephemeral);
                }
                CrashAwareAllocationBranchStack::State::commit_start_ephemeral_inductive(pre, post, lbl);
            },
            CrashAwareAllocationBranchStack::Step::commit_start_persistent() => {
                assert(CrashAwareAllocationBranchStack::State::commit_start_persistent(pre, post, lbl)) by {
                    reveal(CrashAwareAllocationBranchStack::State::commit_start_persistent);
                }
                CrashAwareAllocationBranchStack::State::commit_start_persistent_inductive(pre, post, lbl);
            },
            CrashAwareAllocationBranchStack::Step::commit_complete() => {
                assert(CrashAwareAllocationBranchStack::State::commit_complete(pre, post, lbl)) by {
                    reveal(CrashAwareAllocationBranchStack::State::commit_complete);
                }
                CrashAwareAllocationBranchStack::State::commit_complete_inductive(pre, post, lbl);
            },
            CrashAwareAllocationBranchStack::Step::crash() => {
                assert(CrashAwareAllocationBranchStack::State::crash(pre, post, lbl)) by {
                    reveal(CrashAwareAllocationBranchStack::State::crash);
                }
                CrashAwareAllocationBranchStack::State::crash_inductive(pre, post, lbl);
            },
            CrashAwareAllocationBranchStack::Step::dummy_to_use_type_params(_) => {
                assert(false);
            },
        }
    }
}}

impl CrashAwareAllocationBranchStack::State {
    pub open spec fn wf(self) -> bool
    {
        &&& self.persistent.wf(self.persistent_branch_summary)
        &&& self.frozen is Some ==> self.frozen.unwrap().sealed_stack.wf(
            self.frozen.unwrap().branch_summary,
        )
        &&& self.ephemeral is Unknown ==> self.frozen is None
        &&& self.ephemeral is Known ==> self.ephemeral->v.wf()
    }

}

}
