// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;

use verus_state_machines_macros::state_machine;

use crate::allocation_layer::AllocationBranch_v::{AllocationBranch, BranchNode, Summary};
use crate::allocation_layer::AllocationBranchBetree_v::{
    branch_summary_insert_ensures, map_with_disjoint_values, summary_aus,
};
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::LinkedBranch_v::{LinkedBranch, Path, SplitArg};
use crate::betree::Utils_v::lemma_union_set_of_sets_subset;
use crate::disk::GenericDisk_v::{addrs_closed, set_addrs_disjoint_aus, AU, Address, Pointer};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{nop_delta, Message};

verus! {

pub open spec fn is_nop_message(msg: Message) -> bool
{
    msg == Message::Update{delta: nop_delta()}
}

pub open spec fn active_branch_query_or_nop(active_branch: AllocationBranch, key: Key) -> Message
{
    if active_branch.branch is Some {
        active_branch.branch_query(key)
    } else {
        Message::Update{delta: nop_delta()}
    }
}

pub open spec fn stack_wf(
    sealed_stack: SealedAllocationBranchStack,
    branch_summary: Map<AU, Summary>,
    active_branch: AllocationBranch,
    seq_end: nat,
) -> bool
{
    &&& sealed_stack.wf()
    &&& branch_summary == sealed_stack.branch_summary()
    &&& active_branch.inv()
    &&& !active_branch.sealed
    &&& summary_aus(branch_summary).disjoint(active_branch.mini_allocator.all_aus())
}

pub proof fn mini_allocator_add_aus_preserves_all_aus(mini_allocator: MiniAllocator, aus: Set<AU>)
    requires
        mini_allocator.wf(),
    ensures
        mini_allocator.add_aus(aus).all_aus() == mini_allocator.all_aus() + aus,
{
    assert forall |au: AU| #[trigger] mini_allocator.add_aus(aus).all_aus().contains(au)
        <==> (mini_allocator.all_aus() + aus).contains(au) by { };
}

pub proof fn mini_allocator_allocate_preserves_all_aus(mini_allocator: MiniAllocator, addr: Address)
    requires
        mini_allocator.wf(),
        mini_allocator.can_allocate(addr),
    ensures
        mini_allocator.allocate(addr).all_aus() == mini_allocator.all_aus(),
{
    assert forall |au: AU| #[trigger] mini_allocator.allocate(addr).all_aus().contains(au)
        <==> mini_allocator.all_aus().contains(au) by {
        if au == addr.au {
            assert(mini_allocator.all_aus().contains(au));
        }
    };
}

pub proof fn new_branch_inv(free_aus: Set<AU>)
    ensures
        AllocationBranch::new(free_aus).inv(),
        !AllocationBranch::new(free_aus).sealed,
        AllocationBranch::new(free_aus).mini_allocator.all_aus() == free_aus,
{
    assert(MiniAllocator::empty().wf());
    mini_allocator_add_aus_preserves_all_aus(MiniAllocator::empty(), free_aus);
    assert(AllocationBranch::new(free_aus).mini_allocator.all_aus() == free_aus);
    assert(AllocationBranch::new(free_aus).inv());
}

pub struct SealedAllocationBranchStack {
    pub sealed_roots: Seq<Address>,
    pub sealed_disk: BufferDisk<BranchNode>,
}

impl SealedAllocationBranchStack {
    pub open spec fn branch_summary(self) -> Map<AU, Summary>
    {
        self.sealed_disk.build_branch_summary(self.sealed_roots.to_set())
    }

    pub open spec fn wf(self) -> bool
    {
        &&& self.sealed_disk.sealed_branch_roots(self.sealed_roots.to_set())
        &&& set_addrs_disjoint_aus(self.sealed_roots.to_set())
        &&& map_with_disjoint_values(self.branch_summary())
        &&& addrs_closed(self.sealed_disk.entries.dom(), summary_aus(self.branch_summary()))
    }

    pub open spec fn sealed_branch_at(self, idx: nat) -> LinkedBranch<Summary>
        recommends idx < self.sealed_roots.len()
    {
        self.sealed_disk.get_branch(self.sealed_roots[idx as int])
    }

    pub open spec fn query_up_to(self, end: nat, key: Key) -> Message
        recommends end <= self.sealed_roots.len()
        decreases end
    {
        if end == 0 {
            Message::Update{delta: nop_delta()}
        } else {
            let msg = self.sealed_branch_at((end - 1) as nat).query(key);
            if is_nop_message(msg) {
                self.query_up_to((end - 1) as nat, key)
            } else {
                msg
            }
        }
    }

    pub open spec fn query(self, key: Key) -> Message
    {
        self.query_up_to(self.sealed_roots.len() as nat, key)
    }

    pub open spec fn push_branch(self, sealed_branch: LinkedBranch<Summary>) -> Self
    {
        SealedAllocationBranchStack{
            sealed_roots: self.sealed_roots.push(sealed_branch.root),
            sealed_disk: BufferDisk{
                entries: self.sealed_disk.entries.union_prefer_right(sealed_branch.disk_view.entries),
            },
        }
    }

    pub proof fn disk_wf(self)
        requires
            self.wf(),
        ensures
            self.sealed_disk.to_branch_disk().wf(),
    {
        if self.sealed_roots.len() == 0 {
            assert(self.branch_summary() == Map::<AU, Summary>::empty());
            assert(self.branch_summary().values() =~= Set::<Set<AU>>::empty());
            assert(summary_aus(self.branch_summary()) == Set::<AU>::empty());
            assert forall |addr: Address| #[trigger] self.sealed_disk.entries.contains_key(addr) implies false by {
                assert(self.sealed_disk.entries.dom().contains(addr));
                assert(addrs_closed(self.sealed_disk.entries.dom(), summary_aus(self.branch_summary())));
            }
            assert(self.sealed_disk.to_branch_disk().wf());
        } else {
            let root = self.sealed_roots[0];
            assert(self.sealed_roots.to_set().contains(root));
            assert(self.sealed_disk.get_branch(root).valid_sealed_branch());
        }
    }

    pub proof fn root_au_in_summary(self, root: Address)
        requires
            self.wf(),
            self.sealed_roots.to_set().contains(root),
        ensures
            self.branch_summary().contains_key(root.au),
            self.branch_summary()[root.au].contains(root.au),
            summary_aus(self.branch_summary()).contains(root.au),
    {
        let roots = self.sealed_roots.to_set();
        self.sealed_disk.build_branch_summary_finite(roots);
        self.sealed_disk.build_branch_summary_contains(roots, root);
        let branch = self.sealed_disk.get_branch(root);
        assert(branch.valid_sealed_branch());
        assert(branch.full_repr().contains(root));
        assert(self.branch_summary()[root.au] == branch.get_summary());
        assert(self.branch_summary().values().contains(self.branch_summary()[root.au]));
        lemma_union_set_of_sets_subset(self.branch_summary().values(), self.branch_summary()[root.au]);
    }

    pub proof fn push_branch_preserves_wf(self, sealed_branch: LinkedBranch<Summary>)
        requires
            self.wf(),
            sealed_branch.valid_sealed_branch(),
            sealed_branch.tight_disk_view_with_summary(),
            summary_aus(self.branch_summary()).disjoint(sealed_branch.get_summary()),
        ensures
            self.push_branch(sealed_branch).wf(),
            self.push_branch(sealed_branch).branch_summary()
                == self.branch_summary().insert(sealed_branch.root.au, sealed_branch.get_summary()),
    {
        let roots = self.sealed_roots.to_set();
        let post = self.push_branch(sealed_branch);
        let post_roots = roots + set!{sealed_branch.root};
        let pre_summary = self.branch_summary();
        let post_summary = pre_summary.insert(sealed_branch.root.au, sealed_branch.get_summary());

        self.disk_wf();
        assert(sealed_branch.disk_view.wf());
        assert(sealed_branch.full_repr().contains(sealed_branch.root));
        assert(sealed_branch.get_summary().contains(sealed_branch.root.au));

        assert(set_addrs_disjoint_aus(post_roots)) by {
            assert forall |a: Address, b: Address|
                post_roots.contains(a) && post_roots.contains(b) && a != b
                implies #[trigger] a.au != #[trigger] b.au
            by {
                if a != sealed_branch.root && b != sealed_branch.root {
                    assert(roots.contains(a) && roots.contains(b));
                } else {
                    let old_root = if a == sealed_branch.root { b } else { a };
                    self.root_au_in_summary(old_root);
                    if old_root.au == sealed_branch.root.au {
                        assert(summary_aus(pre_summary).contains(old_root.au));
                        assert(sealed_branch.get_summary().contains(old_root.au));
                    }
                }
            }
        }

        assert(self.sealed_disk.entries.dom().disjoint(sealed_branch.disk_view.entries.dom())) by {
            assert(sealed_branch.disk_view.entries.dom() =~= sealed_branch.full_repr());
            assert forall |addr: Address| #[trigger] self.sealed_disk.entries.dom().contains(addr)
                implies !sealed_branch.disk_view.entries.dom().contains(addr)
            by {
                if sealed_branch.disk_view.entries.dom().contains(addr) {
                    assert(summary_aus(pre_summary).contains(addr.au));
                    assert(sealed_branch.get_summary().contains(addr.au));
                }
            }
        }

        assert(post.sealed_disk.to_branch_disk().wf()) by {
            assert forall |addr: Address| #[trigger] post.sealed_disk.to_branch_disk().entries.contains_key(addr)
                implies post.sealed_disk.to_branch_disk().entries[addr].wf()
            by {
                if self.sealed_disk.entries.contains_key(addr) {
                    assert(self.sealed_disk.to_branch_disk().entries[addr].wf());
                } else {
                    assert(sealed_branch.disk_view.entries.contains_key(addr));
                    assert(sealed_branch.disk_view.entries[addr].wf());
                }
            }

            assert forall |addr: Address| #[trigger] post.sealed_disk.to_branch_disk().entries.contains_key(addr)
                implies post.sealed_disk.to_branch_disk().node_has_valid_child_address(
                    post.sealed_disk.to_branch_disk().entries[addr]
                )
            by {
                if self.sealed_disk.entries.contains_key(addr) {
                    assert(self.sealed_disk.to_branch_disk().node_has_valid_child_address(
                        self.sealed_disk.to_branch_disk().entries[addr]
                    ));
                    if post.sealed_disk.to_branch_disk().entries[addr] is Index {
                        assert forall |idx|
                            0 <= idx < post.sealed_disk.to_branch_disk().entries[addr]->children.len()
                            implies ({
                                let child = #[trigger] post.sealed_disk.to_branch_disk().entries[addr]->children[idx];
                                &&& post.sealed_disk.to_branch_disk().valid_address(child)
                                &&& !(post.sealed_disk.to_branch_disk().entries[child] is Auxiliary)
                            })
                        by {
                            let child = post.sealed_disk.to_branch_disk().entries[addr]->children[idx];
                            assert(self.sealed_disk.to_branch_disk().valid_address(child));
                            if sealed_branch.disk_view.entries.contains_key(child) {
                                assert(false);
                            }
                            assert(post.sealed_disk.to_branch_disk().valid_address(child));
                            assert(post.sealed_disk.to_branch_disk().entries[child]
                                == self.sealed_disk.to_branch_disk().entries[child]);
                            assert(!(post.sealed_disk.to_branch_disk().entries[child] is Auxiliary));
                        }
                    }
                } else {
                    assert(sealed_branch.disk_view.entries.contains_key(addr));
                    assert(sealed_branch.disk_view.node_has_valid_child_address(
                        sealed_branch.disk_view.entries[addr]
                    ));
                    if post.sealed_disk.to_branch_disk().entries[addr] is Index {
                        assert forall |idx|
                            0 <= idx < post.sealed_disk.to_branch_disk().entries[addr]->children.len()
                            implies ({
                                let child = #[trigger] post.sealed_disk.to_branch_disk().entries[addr]->children[idx];
                                &&& post.sealed_disk.to_branch_disk().valid_address(child)
                                &&& !(post.sealed_disk.to_branch_disk().entries[child] is Auxiliary)
                            })
                        by {
                            let child = post.sealed_disk.to_branch_disk().entries[addr]->children[idx];
                            assert(sealed_branch.disk_view.valid_address(child));
                            assert(post.sealed_disk.to_branch_disk().valid_address(child));
                            assert(post.sealed_disk.to_branch_disk().entries[child]
                                == sealed_branch.disk_view.entries[child]);
                            assert(!(post.sealed_disk.to_branch_disk().entries[child] is Auxiliary));
                        }
                    }
                }
            }
        }

        self.sealed_disk.build_branch_summary_insert(post.sealed_disk, roots, sealed_branch);
        self.sealed_disk.build_branch_summary_finite(roots);
        assert(!pre_summary.contains_key(sealed_branch.root.au)) by {
            if pre_summary.contains_key(sealed_branch.root.au) {
                let old_root = self.sealed_disk.build_branch_summary_get_addr(roots, sealed_branch.root.au);
                self.root_au_in_summary(old_root);
                assert(summary_aus(pre_summary).contains(sealed_branch.root.au));
                assert(sealed_branch.get_summary().contains(sealed_branch.root.au));
            }
        }
        branch_summary_insert_ensures(pre_summary, sealed_branch);
        assert(post.sealed_roots == self.sealed_roots + seq![sealed_branch.root]);
        assert(post.sealed_roots.to_set() =~= post_roots) by {
            assert forall |addr: Address| #[trigger] post.sealed_roots.to_set().contains(addr)
                <==> post_roots.contains(addr) by {
                if post.sealed_roots.to_set().contains(addr) {
                    let i = post.sealed_roots.index_of(addr);
                    if i < self.sealed_roots.len() {
                        assert(self.sealed_roots[i] == addr);
                        assert(self.sealed_roots.to_set().contains(addr));
                    } else {
                        assert(i == self.sealed_roots.len());
                        assert(post.sealed_roots[i] == addr);
                    }
                } else if post_roots.contains(addr) {
                    if addr == sealed_branch.root {
                        assert(post.sealed_roots[self.sealed_roots.len() as int] == addr);
                    } else {
                        assert(self.sealed_roots.to_set().contains(addr));
                        let i = self.sealed_roots.index_of(addr);
                        assert(self.sealed_roots[i] == addr);
                        assert(post.sealed_roots[i] == addr);
                    }
                }
            }
        }
        assert(post.branch_summary() == post_summary);
        assert(map_with_disjoint_values(post_summary));

        assert(addrs_closed(post.sealed_disk.entries.dom(), summary_aus(post_summary))) by {
            assert forall |addr: Address| #[trigger] post.sealed_disk.entries.dom().contains(addr)
                implies summary_aus(post_summary).contains(addr.au)
            by {
                if self.sealed_disk.entries.dom().contains(addr) {
                    assert(summary_aus(pre_summary).contains(addr.au));
                    assert(summary_aus(post_summary) == summary_aus(pre_summary) + sealed_branch.get_summary());
                } else {
                    assert(sealed_branch.disk_view.entries.dom().contains(addr));
                    assert(sealed_branch.disk_view.entries.dom() =~= sealed_branch.full_repr());
                    assert(sealed_branch.get_summary().contains(addr.au));
                    assert(summary_aus(post_summary) == summary_aus(pre_summary) + sealed_branch.get_summary());
                }
            }
        }

        assert(post.wf());
    }
}

state_machine!{ AllocationBranchStack {
    fields {
        pub sealed_stack: SealedAllocationBranchStack,
        pub branch_summary: Map<AU, Summary>,
        pub active_branch: AllocationBranch,
        pub seq_end: nat,
    }

    pub enum Label {
        QueryLabel{ key: Key, msg: Message },
        AppendLabel{ keys: Seq<Key>, msgs: Seq<Message> },
        FreezeAsLabel{ sealed_stack: SealedAllocationBranchStack },
        InternalLabel,
    }

    init!{ initialize(
        sealed_roots: Seq<Address>,
        sealed_disk: BufferDisk<BranchNode>,
        branch_summary: Map<AU, Summary>,
        init_aus: Set<AU>,
        seq_end: nat,
    ) {
        let sealed_stack = SealedAllocationBranchStack{ sealed_roots, sealed_disk };
        require sealed_stack.wf();
        require branch_summary == sealed_stack.branch_summary();
        require summary_aus(branch_summary).disjoint(init_aus);
        init sealed_stack = sealed_stack;
        init branch_summary = branch_summary;
        init active_branch = AllocationBranch::new(init_aus);
        init seq_end = seq_end;
    }}

    transition!{ query_step(lbl: Label) {
        require pre.wf();
        require let Label::QueryLabel{key, msg} = lbl;
        require msg == pre.query(key);
    }}

    transition!{ append_to_active(lbl: Label, path: Path<Summary>) {
        require pre.wf();
        require lbl is AppendLabel;
        require pre.active_branch.branch is Some;
        require pre.active_branch.can_append(lbl->keys, lbl->msgs, path);
        require forall |key: Key| #[trigger] lbl->keys.contains(key)
            ==> is_nop_message(pre.active_branch.branch_query(key));
        update active_branch = pre.active_branch.branch_append(lbl->keys, lbl->msgs, path);
        update seq_end = pre.seq_end + lbl->keys.len();
    }}

    transition!{ append_to_empty(lbl: Label, init_root: Address) {
        require pre.wf();
        require lbl is AppendLabel;
        require pre.active_branch.branch is None;
        require pre.active_branch.mini_allocator.can_allocate(init_root);
        require pre.active_branch.can_initialize(init_root, lbl->keys, lbl->msgs);
        update active_branch = pre.active_branch.branch_initialize(init_root, lbl->keys, lbl->msgs);
        update seq_end = pre.seq_end + lbl->keys.len();
    }}

    transition!{ freeze_as(lbl: Label) {
        require pre.wf();
        require let Label::FreezeAsLabel{sealed_stack: frozen_stack} = lbl;
        require frozen_stack.wf();
        require frozen_stack == pre.freeze_snapshot();
        require pre.active_branch.branch is None;
    }}

    transition!{ internal_noop(lbl: Label) {
        require pre.wf();
        require lbl is InternalLabel;
    }}

    transition!{ internal_grow(lbl: Label, new_root_addr: Address) {
        require pre.wf();
        require lbl is InternalLabel;
        require pre.active_branch.can_grow(new_root_addr);
        update active_branch = pre.active_branch.branch_grow(new_root_addr);
    }}

    transition!{ internal_split(lbl: Label, new_child_addr: Address, path: Path<Summary>, split_arg: SplitArg) {
        require pre.wf();
        require lbl is InternalLabel;
        require pre.active_branch.can_split(new_child_addr, path, split_arg);
        update active_branch = pre.active_branch.branch_split(new_child_addr, path, split_arg);
    }}

    transition!{ internal_seal(lbl: Label, aux_ptr: Pointer) {
        require pre.wf();
        require lbl is InternalLabel;
        let dealloc_aus = pre.active_branch.mini_allocator.removable_aus();
        require pre.active_branch.can_seal(aux_ptr, dealloc_aus);
        let sealed_active = pre.active_branch.branch_seal(aux_ptr, dealloc_aus);
        let sealed_branch = sealed_active.branch.unwrap();
        update sealed_stack = pre.sealed_stack.push_branch(sealed_branch);
        update branch_summary = pre.branch_summary.insert(
            sealed_branch.root.au,
            sealed_branch.get_summary(),
        );
        update active_branch = AllocationBranch::new(Set::empty());
    }}

    transition!{ internal_fill_au(lbl: Label, aus: Set<AU>) {
        require pre.wf();
        require lbl is InternalLabel;
        require pre.active_branch.can_fill(aus);
        require summary_aus(pre.branch_summary).disjoint(aus);
        update active_branch = pre.active_branch.mini_allocator_fill(aus);
    }}

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        self.wf()
    }

    #[inductive(initialize)]
    fn initialize_inductive(
        post: Self,
        sealed_roots: Seq<Address>,
        sealed_disk: BufferDisk<BranchNode>,
        branch_summary: Map<AU, Summary>,
        init_aus: Set<AU>,
        seq_end: nat,
    ) {
        new_branch_inv(init_aus);
        assert(post.wf());
    }

    #[inductive(query_step)]
    fn query_step_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
    }

    #[inductive(append_to_active)]
    fn append_to_active_inductive(pre: Self, post: Self, lbl: Label, path: Path<Summary>) {
        match lbl {
            Label::AppendLabel{keys, msgs} => {
                AllocationBranch::build_next_preserves_inv(
                    pre.active_branch,
                    post.active_branch,
                    crate::allocation_layer::AllocationBranch_v::BuildEvent::Append{keys, msgs, path},
                    Set::empty(),
                    Set::empty(),
                );
                assert(post.active_branch.mini_allocator == pre.active_branch.mini_allocator);
                assert(post.wf());
            }
            _ => { }
        }
    }

    #[inductive(append_to_empty)]
    fn append_to_empty_inductive(pre: Self, post: Self, lbl: Label, init_root: Address) {
        match lbl {
            Label::AppendLabel{keys, msgs} => {
                AllocationBranch::build_next_preserves_inv(
                    pre.active_branch,
                    post.active_branch,
                    crate::allocation_layer::AllocationBranch_v::BuildEvent::Initialize{addr: init_root, keys, msgs},
                    Set::empty(),
                    Set::empty(),
                );
                mini_allocator_allocate_preserves_all_aus(pre.active_branch.mini_allocator, init_root);
                assert(post.wf());
            }
            _ => { }
        }
    }

    #[inductive(freeze_as)]
    fn freeze_as_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
    }

    #[inductive(internal_noop)]
    fn internal_noop_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
    }

    #[inductive(internal_grow)]
    fn internal_grow_inductive(pre: Self, post: Self, lbl: Label, new_root_addr: Address) {
        AllocationBranch::build_next_preserves_inv(
            pre.active_branch,
            post.active_branch,
            crate::allocation_layer::AllocationBranch_v::BuildEvent::Grow{addr: new_root_addr},
            Set::empty(),
            Set::empty(),
        );
        mini_allocator_allocate_preserves_all_aus(pre.active_branch.mini_allocator, new_root_addr);
        assert(post.wf());
    }

    #[inductive(internal_split)]
    fn internal_split_inductive(pre: Self, post: Self, lbl: Label, new_child_addr: Address, path: Path<Summary>, split_arg: SplitArg) {
        AllocationBranch::build_next_preserves_inv(
            pre.active_branch,
            post.active_branch,
            crate::allocation_layer::AllocationBranch_v::BuildEvent::Split{
                addr: new_child_addr,
                path,
                split_arg,
            },
            Set::empty(),
            Set::empty(),
        );
        mini_allocator_allocate_preserves_all_aus(pre.active_branch.mini_allocator, new_child_addr);
        assert(post.wf());
    }

    #[inductive(internal_seal)]
    fn internal_seal_inductive(pre: Self, post: Self, lbl: Label, aux_ptr: Pointer) {
        let dealloc_aus = pre.active_branch.mini_allocator.removable_aus();
        let sealed_active = pre.active_branch.branch_seal(aux_ptr, dealloc_aus);
        let sealed_branch = sealed_active.branch.unwrap();
        AllocationBranch::build_next_preserves_inv(
            pre.active_branch,
            sealed_active,
            crate::allocation_layer::AllocationBranch_v::BuildEvent::Seal{aux_ptr},
            Set::empty(),
            dealloc_aus,
        );
        pre.sealed_stack.push_branch_preserves_wf(sealed_branch);
        new_branch_inv(Set::empty());
        assert(post.wf());
    }

    #[inductive(internal_fill_au)]
    fn internal_fill_au_inductive(pre: Self, post: Self, lbl: Label, aus: Set<AU>) {
        AllocationBranch::build_next_preserves_inv(
            pre.active_branch,
            post.active_branch,
            crate::allocation_layer::AllocationBranch_v::BuildEvent::AllocFill{},
            aus,
            Set::empty(),
        );
        mini_allocator_add_aus_preserves_all_aus(pre.active_branch.mini_allocator, aus);
        assert(post.wf());
    }
}}

impl AllocationBranchStack::State {
    pub open spec fn query(self, key: Key) -> Message
    {
        let active_msg = active_branch_query_or_nop(self.active_branch, key);
        if is_nop_message(active_msg) {
            self.sealed_stack.query(key)
        } else {
            active_msg
        }
    }

    pub open spec fn freeze_snapshot(self) -> SealedAllocationBranchStack
    {
        self.sealed_stack
    }

    pub open spec fn wf(self) -> bool
    {
        stack_wf(
            self.sealed_stack,
            self.branch_summary,
            self.active_branch,
            self.seq_end,
        )
    }
}

}
