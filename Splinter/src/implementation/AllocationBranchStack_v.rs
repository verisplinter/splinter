// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::map_lib::*;

use verus_state_machines_macros::state_machine;

use crate::allocation_layer::AllocationBranch_v::{AllocationBranch, BranchNode, Summary};
use crate::allocation_layer::AllocationBranchBetree_v::{
    branch_summary_insert_ensures, map_with_disjoint_values, summary_aus,
};
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::LinkedBranch_v::{LinkedBranch, Path, SplitArg};
use crate::betree::Utils_v::{
    lemma_union_set_of_sets_contains, lemma_union_set_of_sets_subset,
};
use crate::disk::GenericDisk_v::{
    addrs_closed, addrs_with_different_au, set_addrs_disjoint_aus, to_aus,
    to_aus_additive, to_aus_domain, to_aus_finite, to_aus_singleton, AU, Address,
    Pointer,
};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{default_value, nop_delta, Message, Value};

verus! {

pub open spec fn is_nop_message(msg: Message) -> bool
{
    msg == Message::Update{delta: nop_delta()}
}

pub open spec fn normalize_value(msg: Message) -> Value
{
    match msg {
        Message::Define{value} => value,
        Message::Update{delta} => Message::apply_delta(delta, default_value()),
    }
}

pub open spec fn query_message_merge(older: Message, newer: Message) -> Message
{
    older.merge(newer)
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
    &&& sealed_stack.wf(branch_summary)
    &&& active_branch.inv()
    &&& !active_branch.sealed
    &&& summary_aus(branch_summary).disjoint(active_branch.mini_allocator.all_aus())
}

pub open spec fn tight_branch_in_loose_disk(
    loose_disk: BufferDisk<BranchNode>,
    root: Address,
    summary: Summary,
    branch: LinkedBranch<Summary>,
) -> bool
{
    &&& branch.root == root
    &&& branch.valid_sealed_branch()
    &&& branch.tight_disk_view_with_summary()
    &&& branch.get_summary() == summary
    &&& branch.disk_view.entries <= loose_disk.entries
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
    pub open spec fn root_has_tight_branch(
        self,
        root: Address,
        summary: Summary,
    ) -> bool
    {
        exists |branch: LinkedBranch<Summary>|
            tight_branch_in_loose_disk(self.sealed_disk, root, summary, branch)
    }

    pub open spec fn tight_branch(
        self,
        root: Address,
        summary: Summary,
    ) -> LinkedBranch<Summary>
    {
        choose |branch: LinkedBranch<Summary>|
            tight_branch_in_loose_disk(self.sealed_disk, root, summary, branch)
    }

    pub open spec fn wf(self, branch_summary: Map<AU, Summary>) -> bool
    {
        &&& set_addrs_disjoint_aus(self.sealed_roots.to_set())
        &&& branch_summary.dom() == to_aus(self.sealed_roots.to_set())
        &&& map_with_disjoint_values(branch_summary)
        &&& forall |root: Address| #[trigger] self.sealed_roots.to_set().contains(root) ==> {
            &&& branch_summary.contains_key(root.au)
            &&& branch_summary[root.au].contains(root.au)
            &&& self.root_has_tight_branch(root, branch_summary[root.au])
        }
        &&& addrs_closed(self.sealed_disk.entries.dom(), summary_aus(branch_summary))
    }

    pub open spec fn sealed_branch_at(
        self,
        branch_summary: Map<AU, Summary>,
        idx: nat,
    ) -> LinkedBranch<Summary>
        recommends idx < self.sealed_roots.len()
    {
        let root = self.sealed_roots[idx as int];
        self.tight_branch(root, branch_summary[root.au])
    }

    pub open spec fn query_up_to(
        self,
        branch_summary: Map<AU, Summary>,
        end: nat,
        key: Key,
    ) -> Message
        recommends end <= self.sealed_roots.len()
        decreases end
    {
        if end == 0 {
            Message::Update{delta: nop_delta()}
        } else {
            let msg = self.sealed_branch_at(branch_summary, (end - 1) as nat).query(key);
            query_message_merge(self.query_up_to(branch_summary, (end - 1) as nat, key), msg)
        }
    }

    pub open spec fn query(self, branch_summary: Map<AU, Summary>, key: Key) -> Message
    {
        self.query_up_to(branch_summary, self.sealed_roots.len() as nat, key)
    }

    pub open spec fn push_branch(
        self,
        sealed_branch: LinkedBranch<Summary>,
        loose_active_disk: BufferDisk<BranchNode>,
    ) -> Self
    {
        SealedAllocationBranchStack{
            sealed_roots: self.sealed_roots.push(sealed_branch.root),
            sealed_disk: self.sealed_disk.merge_disk(loose_active_disk),
        }
    }

    pub proof fn root_au_in_summary(self, branch_summary: Map<AU, Summary>, root: Address)
        requires
            self.wf(branch_summary),
            self.sealed_roots.to_set().contains(root),
        ensures
            branch_summary.contains_key(root.au),
            branch_summary[root.au].contains(root.au),
            summary_aus(branch_summary).contains(root.au),
    {
        to_aus_finite(self.sealed_roots.to_set());
        assert(branch_summary.dom().finite());
        lemma_values_finite(branch_summary);
        assert(branch_summary.contains_value(branch_summary[root.au]));
        lemma_union_set_of_sets_subset(branch_summary.values(), branch_summary[root.au]);
    }

    pub proof fn tight_branch_facts(self, branch_summary: Map<AU, Summary>, root: Address)
        requires
            self.wf(branch_summary),
            self.sealed_roots.to_set().contains(root),
        ensures
            tight_branch_in_loose_disk(
                self.sealed_disk,
                root,
                branch_summary[root.au],
                self.tight_branch(root, branch_summary[root.au]),
            ),
            self.tight_branch(root, branch_summary[root.au]).root == root,
            self.tight_branch(root, branch_summary[root.au]).valid_sealed_branch(),
            self.tight_branch(root, branch_summary[root.au]).tight_disk_view_with_summary(),
            self.tight_branch(root, branch_summary[root.au]).get_summary() == branch_summary[root.au],
            self.tight_branch(root, branch_summary[root.au]).disk_view.entries <= self.sealed_disk.entries,
    {
        self.root_au_in_summary(branch_summary, root);
        assert(self.root_has_tight_branch(root, branch_summary[root.au]));
    }

    pub proof fn push_branch_preserves_wf(
        self,
        pre_summary: Map<AU, Summary>,
        sealed_branch: LinkedBranch<Summary>,
        loose_active_disk: BufferDisk<BranchNode>,
    )
        requires
            self.wf(pre_summary),
            tight_branch_in_loose_disk(
                loose_active_disk,
                sealed_branch.root,
                sealed_branch.get_summary(),
                sealed_branch,
            ),
            addrs_closed(loose_active_disk.entries.dom(), sealed_branch.get_summary()),
            summary_aus(pre_summary).disjoint(sealed_branch.get_summary()),
            !pre_summary.contains_key(sealed_branch.root.au),
        ensures
            self.push_branch(sealed_branch, loose_active_disk).wf(
                pre_summary.insert(sealed_branch.root.au, sealed_branch.get_summary())
            ),
    {
        let roots = self.sealed_roots.to_set();
        let post = self.push_branch(sealed_branch, loose_active_disk);
        let post_roots = roots + set!{sealed_branch.root};
        let post_summary = pre_summary.insert(sealed_branch.root.au, sealed_branch.get_summary());
        to_aus_finite(roots);
        assert(pre_summary.dom().finite());
        lemma_values_finite(pre_summary);

        assert(sealed_branch.full_repr().contains(sealed_branch.root));
        assert(sealed_branch.get_summary().contains(sealed_branch.root.au));

        assert(set_addrs_disjoint_aus(post_roots)) by {
            assert forall |a: Address, b: Address|
                post_roots.contains(a) && post_roots.contains(b) && a != b
                implies #[trigger] addrs_with_different_au(a, b)
            by {
                if a != sealed_branch.root && b != sealed_branch.root {
                    assert(roots.contains(a) && roots.contains(b));
                } else {
                    let old_root = if a == sealed_branch.root { b } else { a };
                    self.root_au_in_summary(pre_summary, old_root);
                    if old_root.au == sealed_branch.root.au {
                        assert(summary_aus(pre_summary).contains(old_root.au));
                        assert(sealed_branch.get_summary().contains(old_root.au));
                    }
                }
            }
        }

        assert(self.sealed_disk.entries.dom().disjoint(loose_active_disk.entries.dom())) by {
            assert forall |addr: Address| #[trigger] self.sealed_disk.entries.dom().contains(addr)
                implies !loose_active_disk.entries.dom().contains(addr)
            by {
                if loose_active_disk.entries.dom().contains(addr) {
                    assert(summary_aus(pre_summary).contains(addr.au));
                    assert(sealed_branch.get_summary().contains(addr.au));
                }
            }
        }

        assert(self.sealed_disk.is_sub_disk(post.sealed_disk)) by {
            assert forall |addr: Address| #[trigger] self.sealed_disk.entries.dom().contains(addr)
                implies post.sealed_disk.entries.dom().contains(addr)
                    && self.sealed_disk.entries[addr] == post.sealed_disk.entries[addr]
            by {
                assert(!loose_active_disk.entries.dom().contains(addr));
            }
        }

        assert(loose_active_disk.is_sub_disk(post.sealed_disk)) by {
            assert forall |addr: Address| #[trigger] loose_active_disk.entries.dom().contains(addr)
                implies post.sealed_disk.entries.dom().contains(addr)
                    && loose_active_disk.entries[addr] == post.sealed_disk.entries[addr]
            by {
                assert(!self.sealed_disk.entries.dom().contains(addr));
            }
        }

        to_aus_additive(roots, set!{sealed_branch.root});
        to_aus_singleton(sealed_branch.root);
        assert(post_roots == roots + set!{sealed_branch.root});
        branch_summary_insert_ensures(pre_summary, sealed_branch);
        assert(post_summary.dom() =~= pre_summary.dom() + set!{sealed_branch.root.au});
        assert(post_summary.dom() =~= to_aus(post_roots));
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
        assert(map_with_disjoint_values(post_summary));

        assert forall |root: Address| #[trigger] post.sealed_roots.to_set().contains(root)
            implies ({
                &&& post_summary.contains_key(root.au)
                &&& post_summary[root.au].contains(root.au)
                &&& post.root_has_tight_branch(root, post_summary[root.au])
            })
        by {
            if root == sealed_branch.root {
                assert(post_summary[root.au] == sealed_branch.get_summary());
                assert(tight_branch_in_loose_disk(
                    post.sealed_disk,
                    root,
                    post_summary[root.au],
                    sealed_branch,
                )) by {
                    assert(loose_active_disk.is_sub_disk(post.sealed_disk));
                    assert(sealed_branch.disk_view.entries <= loose_active_disk.entries);
                }
                assert(exists |branch: LinkedBranch<Summary>|
                    tight_branch_in_loose_disk(post.sealed_disk, root, post_summary[root.au], branch));
            } else {
                assert(roots.contains(root));
                assert(post_summary[root.au] == pre_summary[root.au]);
                let old_branch = self.tight_branch(root, pre_summary[root.au]);
                assert(tight_branch_in_loose_disk(
                    self.sealed_disk,
                    root,
                    pre_summary[root.au],
                    old_branch,
                ));
                assert(tight_branch_in_loose_disk(
                    post.sealed_disk,
                    root,
                    post_summary[root.au],
                    old_branch,
                )) by {
                    assert(self.sealed_disk.is_sub_disk(post.sealed_disk));
                    assert(old_branch.disk_view.entries <= self.sealed_disk.entries);
                }
                assert(exists |branch: LinkedBranch<Summary>|
                    tight_branch_in_loose_disk(post.sealed_disk, root, post_summary[root.au], branch));
            }
        }

        assert(addrs_closed(post.sealed_disk.entries.dom(), summary_aus(post_summary))) by {
            assert forall |addr: Address| #[trigger] post.sealed_disk.entries.dom().contains(addr)
                implies summary_aus(post_summary).contains(addr.au)
            by {
                if self.sealed_disk.entries.dom().contains(addr) {
                    assert(summary_aus(pre_summary).contains(addr.au));
                    assert(summary_aus(post_summary) == summary_aus(pre_summary) + sealed_branch.get_summary());
                } else {
                    assert(loose_active_disk.entries.dom().contains(addr));
                    assert(sealed_branch.get_summary().contains(addr.au));
                    assert(summary_aus(post_summary) == summary_aus(pre_summary) + sealed_branch.get_summary());
                }
            }
        }

        assert(post.wf(post_summary));
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
        require sealed_stack.wf(branch_summary);
        require summary_aus(branch_summary).disjoint(init_aus);
        init sealed_stack = sealed_stack;
        init branch_summary = branch_summary;
        init active_branch = AllocationBranch::new(init_aus);
        init seq_end = seq_end;
    }}

    transition!{ query_step(lbl: Label) {
        require let Label::QueryLabel{key, msg} = lbl;
        require msg == pre.query(key);
    }}

    transition!{ append_to_active(lbl: Label, path: Path<Summary>) {
        require lbl is AppendLabel;
        require pre.active_branch.branch is Some;
        require pre.active_branch.can_append(lbl->keys, lbl->msgs, path);
        require forall |key: Key| #[trigger] lbl->keys.contains(key)
            ==> is_nop_message(pre.active_branch.branch_query(key));
        let new_active = pre.active_branch.branch_append(lbl->keys, lbl->msgs, path);
        update active_branch = new_active;
        update seq_end = pre.seq_end + lbl->keys.len();
    }}

    transition!{ append_to_empty(lbl: Label, init_root: Address) {
        require lbl is AppendLabel;
        require pre.active_branch.branch is None;
        require pre.active_branch.mini_allocator.can_allocate(init_root);
        require pre.active_branch.can_initialize(init_root, lbl->keys, lbl->msgs);
        let new_active = pre.active_branch.branch_initialize(init_root, lbl->keys, lbl->msgs);
        update active_branch = new_active;
        update seq_end = pre.seq_end + lbl->keys.len();
    }}

    transition!{ freeze_as(lbl: Label) {
        require let Label::FreezeAsLabel{sealed_stack: frozen_stack} = lbl;
        require frozen_stack == pre.freeze_snapshot();
        require pre.active_branch.branch is None;
    }}

    transition!{ internal_noop(lbl: Label) {
        require lbl is InternalLabel;
    }}

    transition!{ internal_grow(lbl: Label, new_root_addr: Address) {
        require lbl is InternalLabel;
        require pre.active_branch.can_grow(new_root_addr);
        let new_active = pre.active_branch.branch_grow(new_root_addr);
        update active_branch = new_active;
    }}

    transition!{ internal_split(lbl: Label, new_child_addr: Address, path: Path<Summary>, split_arg: SplitArg) {
        require lbl is InternalLabel;
        require pre.active_branch.can_split(new_child_addr, path, split_arg);
        let new_active = pre.active_branch.branch_split(new_child_addr, path, split_arg);
        update active_branch = new_active;
    }}

    transition!{ internal_seal(lbl: Label, aux_ptr: Pointer, loose_active_disk: BufferDisk<BranchNode>) {
        require lbl is InternalLabel;
        let dealloc_aus = pre.active_branch.mini_allocator.removable_aus();
        require pre.active_branch.can_seal(aux_ptr, dealloc_aus);
        let sealed_active = pre.active_branch.branch_seal(aux_ptr, dealloc_aus);
        let sealed_branch = sealed_active.branch.unwrap();
        require tight_branch_in_loose_disk(
            loose_active_disk,
            sealed_branch.root,
            sealed_branch.get_summary(),
            sealed_branch,
        );
        require addrs_closed(loose_active_disk.entries.dom(), sealed_branch.get_summary());
        let next_active_allocator = pre.active_branch.mini_allocator
            .prune(sealed_branch.get_summary());
        update sealed_stack = pre.sealed_stack.push_branch(sealed_branch, loose_active_disk);
        update branch_summary = pre.branch_summary.insert(
            sealed_branch.root.au,
            sealed_branch.get_summary(),
        );
        update active_branch = AllocationBranch{
            sealed: false,
            branch: None,
            mini_allocator: next_active_allocator,
        };
    }}

    transition!{ internal_fill_au(lbl: Label, aus: Set<AU>) {
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
    fn internal_seal_inductive(pre: Self, post: Self, lbl: Label, aux_ptr: Pointer, loose_active_disk: BufferDisk<BranchNode>) {
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
        let roots = pre.sealed_stack.sealed_roots.to_set();
        to_aus_finite(roots);
        assert(pre.branch_summary.dom().finite());
        lemma_values_finite(pre.branch_summary);
        assert(sealed_branch.get_summary().contains(sealed_branch.root.au)) by {
            assert(sealed_branch.full_repr().contains(sealed_branch.root));
            assert(addrs_closed(sealed_branch.full_repr(), sealed_branch.get_summary()));
        }
        assert(!pre.branch_summary.contains_key(sealed_branch.root.au)) by {
            if pre.branch_summary.contains_key(sealed_branch.root.au) {
                assert(pre.branch_summary.values().contains(pre.branch_summary[sealed_branch.root.au]));
                lemma_union_set_of_sets_subset(
                    pre.branch_summary.values(),
                    pre.branch_summary[sealed_branch.root.au],
                );
                assert(summary_aus(pre.branch_summary).contains(sealed_branch.root.au));
                assert(!sealed_branch.get_summary().contains(sealed_branch.root.au));
            }
        }
        pre.sealed_stack.push_branch_preserves_wf(pre.branch_summary, sealed_branch, loose_active_disk);
        branch_summary_insert_ensures(pre.branch_summary, sealed_branch);
        pre.active_branch.mini_allocator.prune_preserves_wf(sealed_branch.get_summary());
        assert(post.active_branch.mini_allocator.all_aus()
            == pre.active_branch.mini_allocator.all_aus().difference(sealed_branch.get_summary()));
        assert(summary_aus(post.branch_summary)
            == summary_aus(pre.branch_summary) + sealed_branch.get_summary());
        assert(summary_aus(post.branch_summary).disjoint(post.active_branch.mini_allocator.all_aus())) by {
            assert forall |au: AU| #[trigger] summary_aus(post.branch_summary).contains(au)
                implies !post.active_branch.mini_allocator.all_aus().contains(au) by {
                if summary_aus(pre.branch_summary).contains(au) {
                    assert(!pre.active_branch.mini_allocator.all_aus().contains(au));
                } else {
                    assert(sealed_branch.get_summary().contains(au));
                }
            }
        }
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

    pub proof fn inv_next(pre: Self, post: Self, lbl: Label)
        requires
            pre.inv(),
            AllocationBranchStack::State::next(pre, post, lbl),
        ensures
            post.inv(),
    {
        reveal(AllocationBranchStack::State::next);
        reveal(AllocationBranchStack::State::next_by);

        let step = choose |step| AllocationBranchStack::State::next_by(pre, post, lbl, step);
        match step {
            AllocationBranchStack::Step::query_step() => {
                assert(AllocationBranchStack::State::query_step(pre, post, lbl)) by {
                    reveal(AllocationBranchStack::State::query_step);
                }
                AllocationBranchStack::State::query_step_inductive(pre, post, lbl);
            },
            AllocationBranchStack::Step::append_to_active(path) => {
                assert(AllocationBranchStack::State::append_to_active(pre, post, lbl, path)) by {
                    reveal(AllocationBranchStack::State::append_to_active);
                }
                AllocationBranchStack::State::append_to_active_inductive(pre, post, lbl, path);
            },
            AllocationBranchStack::Step::append_to_empty(init_root) => {
                assert(AllocationBranchStack::State::append_to_empty(pre, post, lbl, init_root)) by {
                    reveal(AllocationBranchStack::State::append_to_empty);
                }
                AllocationBranchStack::State::append_to_empty_inductive(pre, post, lbl, init_root);
            },
            AllocationBranchStack::Step::freeze_as() => {
                assert(AllocationBranchStack::State::freeze_as(pre, post, lbl)) by {
                    reveal(AllocationBranchStack::State::freeze_as);
                }
                AllocationBranchStack::State::freeze_as_inductive(pre, post, lbl);
            },
            AllocationBranchStack::Step::internal_noop() => {
                assert(AllocationBranchStack::State::internal_noop(pre, post, lbl)) by {
                    reveal(AllocationBranchStack::State::internal_noop);
                }
                AllocationBranchStack::State::internal_noop_inductive(pre, post, lbl);
            },
            AllocationBranchStack::Step::internal_grow(new_root_addr) => {
                assert(AllocationBranchStack::State::internal_grow(pre, post, lbl, new_root_addr)) by {
                    reveal(AllocationBranchStack::State::internal_grow);
                }
                AllocationBranchStack::State::internal_grow_inductive(pre, post, lbl, new_root_addr);
            },
            AllocationBranchStack::Step::internal_split(new_child_addr, path, split_arg) => {
                assert(AllocationBranchStack::State::internal_split(pre, post, lbl, new_child_addr, path, split_arg)) by {
                    reveal(AllocationBranchStack::State::internal_split);
                }
                AllocationBranchStack::State::internal_split_inductive(pre, post, lbl, new_child_addr, path, split_arg);
            },
            AllocationBranchStack::Step::internal_seal(aux_ptr, loose_active_disk) => {
                assert(AllocationBranchStack::State::internal_seal(pre, post, lbl, aux_ptr, loose_active_disk)) by {
                    reveal(AllocationBranchStack::State::internal_seal);
                }
                AllocationBranchStack::State::internal_seal_inductive(pre, post, lbl, aux_ptr, loose_active_disk);
            },
            AllocationBranchStack::Step::internal_fill_au(aus) => {
                assert(AllocationBranchStack::State::internal_fill_au(pre, post, lbl, aus)) by {
                    reveal(AllocationBranchStack::State::internal_fill_au);
                }
                AllocationBranchStack::State::internal_fill_au_inductive(pre, post, lbl, aus);
            },
            _ => {
                assert(post.inv());
            },
        }
    }
}}

impl AllocationBranchStack::State {
    pub open spec fn query(self, key: Key) -> Message
    {
        let active_msg = active_branch_query_or_nop(self.active_branch, key);
        query_message_merge(self.sealed_stack.query(self.branch_summary, key), active_msg)
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
