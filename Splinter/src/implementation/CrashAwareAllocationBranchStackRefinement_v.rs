// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::map::*;

use crate::abstract_system::AbstractCrashAwareMap_v::{
    AbstractCrashAwareMap, Ephemeral as AbstractEphemeral,
};
use crate::abstract_system::AbstractMap_v::AbstractMap;
use crate::abstract_system::StampedMap_v::{empty, StampedMap};
use crate::allocation_layer::AllocationBranch_v::Summary;
use crate::betree::LinkedBranch_v::{Path, SplitArg};
use crate::disk::GenericDisk_v::{AU, Address, Pointer};
use crate::implementation::AllocationBranchStack_v::{
    AllocationBranchStack, SealedAllocationBranchStack,
};
use crate::implementation::AllocationBranchStackRefinement_v::{
    active_branch_sparse_map, append_puts, buffer_kmmap_i,
};
use crate::implementation::CrashAwareAllocationBranchStack_v::{
    empty_sealed_stack, load_stack, CrashAwareAllocationBranchStack,
    EphemeralAllocationBranchStack, FrozenAllocationBranchStack,
};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::Message;
use crate::spec::TotalKMMap_t::TotalKMMap;

verus! {

pub open spec fn sealed_store_i(
    sealed_stack: SealedAllocationBranchStack,
    branch_summary: Map<AU, Summary>,
    seq_end: nat,
) -> StampedMap
{
    sealed_stack.abstract_map_i_at(branch_summary, seq_end).stamped_map
}

pub open spec fn optional_sealed_store_i(
    sealed_stack: Option<FrozenAllocationBranchStack>,
) -> Option<StampedMap>
{
    match sealed_stack {
        Option::None => Option::None,
        Option::Some{0: stack} => Option::Some(sealed_store_i(
            stack.sealed_stack,
            stack.branch_summary,
            stack.seq_end,
        )),
    }
}

impl EphemeralAllocationBranchStack {
    pub open spec fn abstract_i(self) -> AbstractEphemeral
    {
        match self {
            EphemeralAllocationBranchStack::Unknown => AbstractEphemeral::Unknown,
            EphemeralAllocationBranchStack::Known{v} =>
                AbstractEphemeral::Known{ v: v.abstract_map_i() },
        }
    }
}

impl CrashAwareAllocationBranchStack::State {
    pub open spec fn abstract_i(self) -> AbstractCrashAwareMap::State
    {
        AbstractCrashAwareMap::State{
            persistent: sealed_store_i(
                self.persistent,
                self.persistent_branch_summary,
                self.persistent_seq_end,
            ),
            ephemeral: self.ephemeral.abstract_i(),
            frozen: optional_sealed_store_i(self.frozen),
        }
    }

    pub open spec fn label_to_abstract_map(self, lbl: CrashAwareAllocationBranchStack::Label)
        -> AbstractCrashAwareMap::Label
    {
        match lbl {
            CrashAwareAllocationBranchStack::Label::LoadEphemeral{free_aus} =>
                AbstractCrashAwareMap::Label::LoadEphemeralFromPersistentLabel{
                    end_lsn: self.persistent_seq_end,
                },
            CrashAwareAllocationBranchStack::Label::Query{key, value} =>
                AbstractCrashAwareMap::Label::QueryLabel{
                    end_lsn: if self.ephemeral is Known { self.ephemeral->v.seq_end } else { 0 },
                    key,
                    value,
                },
            CrashAwareAllocationBranchStack::Label::Append{keys, msgs} =>
                AbstractCrashAwareMap::Label::PutRecordsLabel{
                    records: if self.ephemeral is Known {
                        append_puts(self.ephemeral->v.seq_end, keys, msgs)
                    } else {
                        append_puts(0, keys, msgs)
                    },
                },
            CrashAwareAllocationBranchStack::Label::Internal =>
                AbstractCrashAwareMap::Label::InternalLabel,
            CrashAwareAllocationBranchStack::Label::CommitStart{new_boundary_lsn, frozen_stack} =>
                AbstractCrashAwareMap::Label::CommitStartLabel{
                    new_boundary_lsn,
                    frozen_map: sealed_store_i(
                        frozen_stack.sealed_stack,
                        frozen_stack.branch_summary,
                        frozen_stack.seq_end,
                    ),
                },
            CrashAwareAllocationBranchStack::Label::CommitComplete =>
                AbstractCrashAwareMap::Label::CommitCompleteLabel,
            CrashAwareAllocationBranchStack::Label::Crash{keep_in_flight} =>
                AbstractCrashAwareMap::Label::CrashLabel{ keep_in_flight },
        }
    }

    proof fn empty_sealed_stack_refines_to_empty()
        ensures
            sealed_store_i(empty_sealed_stack(), Map::<AU, Summary>::empty(), 0) == empty(),
    {
        let stack = empty_sealed_stack();
        let branch_summary = Map::<AU, Summary>::empty();
        stack.kmmap_i_wf(branch_summary);
        assert(stack.sparse_map(branch_summary) == Map::<Key, Message>::empty());
        assert(stack.kmmap_i(branch_summary).0 =~= TotalKMMap::empty().0) by {
            assert forall |key: Key| #[trigger] stack.kmmap_i(branch_summary).0.contains_key(key)
                <==> TotalKMMap::empty().0.contains_key(key) by { }
            assert forall |key: Key| #[trigger] stack.kmmap_i(branch_summary).0.contains_key(key)
                implies stack.kmmap_i(branch_summary).0[key] == TotalKMMap::empty().0[key] by { }
        }
        assert(stack.kmmap_i(branch_summary) == TotalKMMap::empty());
    }

    proof fn load_stack_matches_persistent(
        persistent: SealedAllocationBranchStack,
        persistent_branch_summary: Map<AU, Summary>,
        persistent_seq_end: nat,
        free_aus: Set<AU>,
    )
        requires
            load_stack(persistent, persistent_branch_summary, persistent_seq_end, free_aus).wf(),
        ensures
            load_stack(
                persistent,
                persistent_branch_summary,
                persistent_seq_end,
                free_aus,
            ).abstract_map_i().stamped_map
                == persistent.abstract_map_i_at(
                    persistent_branch_summary,
                    persistent_seq_end,
                ).stamped_map,
    {
        let stack = load_stack(
            persistent,
            persistent_branch_summary,
            persistent_seq_end,
            free_aus,
        );
        assert(stack.active_branch.branch is None);
        assert(active_branch_sparse_map(stack.active_branch) == Map::<Key, Message>::empty());
        assert(stack.sparse_map() =~= persistent.sparse_map(persistent_branch_summary)) by {
            assert forall |key: Key| #[trigger] stack.sparse_map().contains_key(key)
                <==> persistent.sparse_map(persistent_branch_summary).contains_key(key) by { }
            assert forall |key: Key| #![auto] stack.sparse_map().contains_key(key)
                implies stack.sparse_map()[key] == persistent.sparse_map(persistent_branch_summary)[key] by { }
        }
        assert(stack.seq_end == persistent_seq_end);
        assert(stack.kmmap_i().0 =~= persistent.kmmap_i(persistent_branch_summary).0);
        assert(stack.kmmap_i() == persistent.kmmap_i(persistent_branch_summary));
    }

    pub proof fn init_refines(self)
        requires
            CrashAwareAllocationBranchStack::State::initialize(self),
        ensures
            AbstractCrashAwareMap::State::initialize(self.abstract_i()),
    {
        reveal(AbstractCrashAwareMap::State::init_by);
        Self::empty_sealed_stack_refines_to_empty();
        assert(AbstractCrashAwareMap::State::init_by(
            self.abstract_i(),
            AbstractCrashAwareMap::Config::initialize(),
        ));
    }

    pub proof fn load_ephemeral_refines(self, post: Self, lbl: CrashAwareAllocationBranchStack::Label)
        requires
            self.inv(),
            CrashAwareAllocationBranchStack::State::load_ephemeral(self, post, lbl),
        ensures
            AbstractCrashAwareMap::State::next(
                self.abstract_i(),
                post.abstract_i(),
                self.label_to_abstract_map(lbl),
            ),
    {
        reveal(AbstractCrashAwareMap::State::next);
        reveal(AbstractCrashAwareMap::State::next_by);
        reveal(AbstractMap::State::init_by);

        match lbl {
            CrashAwareAllocationBranchStack::Label::LoadEphemeral{free_aus} => {
                Self::load_stack_matches_persistent(
                    self.persistent,
                    self.persistent_branch_summary,
                    self.persistent_seq_end,
                    free_aus,
                );
                let new_map = load_stack(
                    self.persistent,
                    self.persistent_branch_summary,
                    self.persistent_seq_end,
                    free_aus,
                ).abstract_map_i();
                assert(new_map.stamped_map == self.abstract_i().persistent);
                assert(AbstractMap::State::init_by(
                    new_map,
                    AbstractMap::Config::initialize(self.abstract_i().persistent),
                ));
                assert(AbstractCrashAwareMap::State::next_by(
                    self.abstract_i(),
                    post.abstract_i(),
                    self.label_to_abstract_map(lbl),
                    AbstractCrashAwareMap::Step::load_ephemeral_from_persistent(),
                ));
            }
            _ => { }
        }
    }

    pub proof fn query_refines(
        self,
        post: Self,
        lbl: CrashAwareAllocationBranchStack::Label,
        new_stack: AllocationBranchStack::State,
        msg: Message,
    )
        requires
            self.inv(),
            CrashAwareAllocationBranchStack::State::query(self, post, lbl, new_stack, msg),
        ensures
            AbstractCrashAwareMap::State::next(
                self.abstract_i(),
                post.abstract_i(),
                self.label_to_abstract_map(lbl),
            ),
    {
        reveal(AbstractCrashAwareMap::State::next);
        reveal(AbstractCrashAwareMap::State::next_by);

        match lbl {
            CrashAwareAllocationBranchStack::Label::Query{key, value} => {
                let old_stack = self.ephemeral->v;
                let stack_lbl = AllocationBranchStack::Label::QueryLabel{key, msg};
                old_stack.query_refines(new_stack, stack_lbl);
                assert(value == crate::implementation::AllocationBranchStack_v::normalize_value(msg)) by {
                    reveal(CrashAwareAllocationBranchStack::State::query);
                }
                assert(AbstractCrashAwareMap::State::next_by(
                    self.abstract_i(),
                    post.abstract_i(),
                    self.label_to_abstract_map(lbl),
                    AbstractCrashAwareMap::Step::query(new_stack.abstract_map_i()),
                ));
            }
            _ => { }
        }
    }

    pub proof fn append_to_active_refines(
        self,
        post: Self,
        lbl: CrashAwareAllocationBranchStack::Label,
        new_stack: AllocationBranchStack::State,
        path: Path<Summary>,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareAllocationBranchStack::State::append_to_active(self, post, lbl, new_stack, path),
        ensures
            AbstractCrashAwareMap::State::next(
                self.abstract_i(),
                post.abstract_i(),
                self.label_to_abstract_map(lbl),
            ),
    {
        reveal(AbstractCrashAwareMap::State::next);
        reveal(AbstractCrashAwareMap::State::next_by);

        match lbl {
            CrashAwareAllocationBranchStack::Label::Append{keys, msgs} => {
                let old_stack = self.ephemeral->v;
                let stack_lbl = AllocationBranchStack::Label::AppendLabel{keys, msgs};
                old_stack.append_to_active_refines(new_stack, stack_lbl, path);
                assert(AbstractCrashAwareMap::State::next_by(
                    self.abstract_i(),
                    post.abstract_i(),
                    self.label_to_abstract_map(lbl),
                    AbstractCrashAwareMap::Step::put_records(new_stack.abstract_map_i()),
                ));
            }
            _ => { }
        }
    }

    pub proof fn append_to_empty_refines(
        self,
        post: Self,
        lbl: CrashAwareAllocationBranchStack::Label,
        new_stack: AllocationBranchStack::State,
        init_root: Address,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareAllocationBranchStack::State::append_to_empty(self, post, lbl, new_stack, init_root),
        ensures
            AbstractCrashAwareMap::State::next(
                self.abstract_i(),
                post.abstract_i(),
                self.label_to_abstract_map(lbl),
            ),
    {
        reveal(AbstractCrashAwareMap::State::next);
        reveal(AbstractCrashAwareMap::State::next_by);

        match lbl {
            CrashAwareAllocationBranchStack::Label::Append{keys, msgs} => {
                let old_stack = self.ephemeral->v;
                let stack_lbl = AllocationBranchStack::Label::AppendLabel{keys, msgs};
                old_stack.append_to_empty_refines(new_stack, stack_lbl, init_root);
                assert(AbstractCrashAwareMap::State::next_by(
                    self.abstract_i(),
                    post.abstract_i(),
                    self.label_to_abstract_map(lbl),
                    AbstractCrashAwareMap::Step::put_records(new_stack.abstract_map_i()),
                ));
            }
            _ => { }
        }
    }

    proof fn stack_internal_refines(
        self,
        post: Self,
        new_stack: AllocationBranchStack::State,
    )
        requires
            self.inv(),
            post.inv(),
            self.ephemeral is Known,
            post.ephemeral == (EphemeralAllocationBranchStack::Known{ v: new_stack }),
            self.label_to_abstract_map(CrashAwareAllocationBranchStack::Label::Internal)
                == AbstractCrashAwareMap::Label::InternalLabel,
            AbstractMap::State::next(
                self.ephemeral->v.abstract_map_i(),
                new_stack.abstract_map_i(),
                AbstractMap::Label::InternalLabel,
            ),
            post.persistent == self.persistent,
            post.persistent_branch_summary == self.persistent_branch_summary,
            post.persistent_seq_end == self.persistent_seq_end,
            post.frozen == self.frozen,
        ensures
            AbstractCrashAwareMap::State::next(
                self.abstract_i(),
                post.abstract_i(),
                AbstractCrashAwareMap::Label::InternalLabel,
            ),
    {
        reveal(AbstractCrashAwareMap::State::next);
        reveal(AbstractCrashAwareMap::State::next_by);
        assert(post.abstract_i().persistent == self.abstract_i().persistent);
        assert(post.abstract_i().frozen == self.abstract_i().frozen);
        assert(AbstractCrashAwareMap::State::next_by(
            self.abstract_i(),
            post.abstract_i(),
            AbstractCrashAwareMap::Label::InternalLabel,
            AbstractCrashAwareMap::Step::ephemeral_internal(new_stack.abstract_map_i()),
        ));
    }

    pub proof fn ephemeral_internal_noop_refines(
        self,
        post: Self,
        lbl: CrashAwareAllocationBranchStack::Label,
        new_stack: AllocationBranchStack::State,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareAllocationBranchStack::State::ephemeral_internal_noop(self, post, lbl, new_stack),
        ensures
            AbstractCrashAwareMap::State::next(self.abstract_i(), post.abstract_i(), self.label_to_abstract_map(lbl)),
    {
        let old_stack = self.ephemeral->v;
        old_stack.internal_noop_refines(new_stack, AllocationBranchStack::Label::InternalLabel);
        self.stack_internal_refines(post, new_stack);
    }

    pub proof fn ephemeral_internal_grow_refines(
        self,
        post: Self,
        lbl: CrashAwareAllocationBranchStack::Label,
        new_stack: AllocationBranchStack::State,
        new_root_addr: Address,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareAllocationBranchStack::State::ephemeral_internal_grow(
                self, post, lbl, new_stack, new_root_addr,
            ),
        ensures
            AbstractCrashAwareMap::State::next(self.abstract_i(), post.abstract_i(), self.label_to_abstract_map(lbl)),
    {
        let old_stack = self.ephemeral->v;
        old_stack.grow_refines(new_stack, AllocationBranchStack::Label::InternalLabel, new_root_addr);
        self.stack_internal_refines(post, new_stack);
    }

    pub proof fn ephemeral_internal_split_refines(
        self,
        post: Self,
        lbl: CrashAwareAllocationBranchStack::Label,
        new_stack: AllocationBranchStack::State,
        new_child_addr: Address,
        path: Path<Summary>,
        split_arg: SplitArg,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareAllocationBranchStack::State::ephemeral_internal_split(
                self, post, lbl, new_stack, new_child_addr, path, split_arg,
            ),
        ensures
            AbstractCrashAwareMap::State::next(self.abstract_i(), post.abstract_i(), self.label_to_abstract_map(lbl)),
    {
        let old_stack = self.ephemeral->v;
        old_stack.split_refines(
            new_stack,
            AllocationBranchStack::Label::InternalLabel,
            new_child_addr,
            path,
            split_arg,
        );
        self.stack_internal_refines(post, new_stack);
    }

    pub proof fn ephemeral_internal_seal_refines(
        self,
        post: Self,
        lbl: CrashAwareAllocationBranchStack::Label,
        new_stack: AllocationBranchStack::State,
        aux_ptr: Pointer,
        loose_active_disk: crate::betree::BufferDisk_v::BufferDisk<crate::allocation_layer::AllocationBranch_v::BranchNode>,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareAllocationBranchStack::State::ephemeral_internal_seal(
                self,
                post,
                lbl,
                new_stack,
                aux_ptr,
                loose_active_disk,
            ),
        ensures
            AbstractCrashAwareMap::State::next(self.abstract_i(), post.abstract_i(), self.label_to_abstract_map(lbl)),
    {
        let old_stack = self.ephemeral->v;
        old_stack.seal_refines(
            new_stack,
            AllocationBranchStack::Label::InternalLabel,
            aux_ptr,
            loose_active_disk,
        );
        self.stack_internal_refines(post, new_stack);
    }

    pub proof fn ephemeral_internal_fill_au_refines(
        self,
        post: Self,
        lbl: CrashAwareAllocationBranchStack::Label,
        new_stack: AllocationBranchStack::State,
        aus: Set<AU>,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareAllocationBranchStack::State::ephemeral_internal_fill_au(self, post, lbl, new_stack, aus),
        ensures
            AbstractCrashAwareMap::State::next(self.abstract_i(), post.abstract_i(), self.label_to_abstract_map(lbl)),
    {
        let old_stack = self.ephemeral->v;
        old_stack.fill_au_refines(new_stack, AllocationBranchStack::Label::InternalLabel, aus);
        self.stack_internal_refines(post, new_stack);
    }

    pub proof fn freeze_map_internal_refines(self, post: Self, lbl: CrashAwareAllocationBranchStack::Label)
        requires
            self.inv(),
            post.inv(),
            CrashAwareAllocationBranchStack::State::freeze_map_internal(self, post, lbl),
        ensures
            AbstractCrashAwareMap::State::next(self.abstract_i(), post.abstract_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(AbstractCrashAwareMap::State::next);
        reveal(AbstractCrashAwareMap::State::next_by);
        let stack = self.ephemeral->v;
        let sealed_stack = stack.freeze_snapshot();
        let stack_lbl = AllocationBranchStack::Label::FreezeAsLabel{ sealed_stack };
        stack.freeze_as_refines(stack, stack_lbl);
        assert(AbstractCrashAwareMap::State::next_by(
            self.abstract_i(),
            post.abstract_i(),
            self.label_to_abstract_map(lbl),
            AbstractCrashAwareMap::Step::freeze_map_internal(
                sealed_stack.abstract_map_i_at(stack.branch_summary, stack.seq_end).stamped_map,
                stack.abstract_map_i(),
            ),
        ));
    }

    pub proof fn commit_start_ephemeral_refines(self, post: Self, lbl: CrashAwareAllocationBranchStack::Label)
        requires
            self.inv(),
            post.inv(),
            CrashAwareAllocationBranchStack::State::commit_start_ephemeral(self, post, lbl),
        ensures
            AbstractCrashAwareMap::State::next(self.abstract_i(), post.abstract_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(AbstractCrashAwareMap::State::next);
        reveal(AbstractCrashAwareMap::State::next_by);
        reveal(CrashAwareAllocationBranchStack::State::commit_start_ephemeral);
        let stack = self.ephemeral->v;
        let frozen_stack = lbl->frozen_stack;
        let stack_lbl = AllocationBranchStack::Label::FreezeAsLabel{
            sealed_stack: frozen_stack.sealed_stack,
        };
        assert(AllocationBranchStack::State::freeze_as(stack, stack, stack_lbl));
        stack.freeze_as_refines(stack, stack_lbl);
        assert(sealed_store_i(
            frozen_stack.sealed_stack,
            frozen_stack.branch_summary,
            frozen_stack.seq_end,
        )
            == self.label_to_abstract_map(lbl)->frozen_map);
        assert(stack.abstract_map_i() == self.abstract_i().ephemeral->v);
        assert(AbstractCrashAwareMap::State::next_by(
            self.abstract_i(),
            post.abstract_i(),
            self.label_to_abstract_map(lbl),
            AbstractCrashAwareMap::Step::commit_start_ephemeral(),
        ));
    }

    pub proof fn commit_start_persistent_refines(self, post: Self, lbl: CrashAwareAllocationBranchStack::Label)
        requires
            self.inv(),
            post.inv(),
            CrashAwareAllocationBranchStack::State::commit_start_persistent(self, post, lbl),
        ensures
            AbstractCrashAwareMap::State::next(self.abstract_i(), post.abstract_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(AbstractCrashAwareMap::State::next);
        reveal(AbstractCrashAwareMap::State::next_by);
        reveal(CrashAwareAllocationBranchStack::State::commit_start_persistent);
        let frozen_stack = lbl->frozen_stack;
        assert(sealed_store_i(
            frozen_stack.sealed_stack,
            frozen_stack.branch_summary,
            frozen_stack.seq_end,
        )
            == self.abstract_i().persistent);
        assert(sealed_store_i(
            frozen_stack.sealed_stack,
            frozen_stack.branch_summary,
            frozen_stack.seq_end,
        )
            == self.label_to_abstract_map(lbl)->frozen_map);
        assert(AbstractCrashAwareMap::State::next_by(
            self.abstract_i(),
            post.abstract_i(),
            self.label_to_abstract_map(lbl),
            AbstractCrashAwareMap::Step::commit_start_persistent(),
        ));
    }

    pub proof fn commit_complete_refines(self, post: Self, lbl: CrashAwareAllocationBranchStack::Label)
        requires
            self.inv(),
            post.inv(),
            CrashAwareAllocationBranchStack::State::commit_complete(self, post, lbl),
        ensures
            AbstractCrashAwareMap::State::next(self.abstract_i(), post.abstract_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(AbstractCrashAwareMap::State::next);
        reveal(AbstractCrashAwareMap::State::next_by);
        assert(AbstractCrashAwareMap::State::next_by(
            self.abstract_i(),
            post.abstract_i(),
            self.label_to_abstract_map(lbl),
            AbstractCrashAwareMap::Step::commit_complete(),
        ));
    }

    pub proof fn crash_refines(self, post: Self, lbl: CrashAwareAllocationBranchStack::Label)
        requires
            self.inv(),
            post.inv(),
            CrashAwareAllocationBranchStack::State::crash(self, post, lbl),
        ensures
            AbstractCrashAwareMap::State::next(self.abstract_i(), post.abstract_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(AbstractCrashAwareMap::State::next);
        reveal(AbstractCrashAwareMap::State::next_by);
        assert(AbstractCrashAwareMap::State::next_by(
            self.abstract_i(),
            post.abstract_i(),
            self.label_to_abstract_map(lbl),
            AbstractCrashAwareMap::Step::crash(),
        ));
    }

    pub proof fn next_refines(self, post: Self, lbl: CrashAwareAllocationBranchStack::Label)
        requires
            self.inv(),
            post.inv(),
            CrashAwareAllocationBranchStack::State::next(self, post, lbl),
        ensures
            AbstractCrashAwareMap::State::next(self.abstract_i(), post.abstract_i(), self.label_to_abstract_map(lbl)),
    {
        reveal(CrashAwareAllocationBranchStack::State::next);
        reveal(CrashAwareAllocationBranchStack::State::next_by);

        let step = choose |step| CrashAwareAllocationBranchStack::State::next_by(self, post, lbl, step);
        match step {
            CrashAwareAllocationBranchStack::Step::load_ephemeral() => {
                self.load_ephemeral_refines(post, lbl);
            }
            CrashAwareAllocationBranchStack::Step::query(new_stack, msg) => {
                self.query_refines(post, lbl, new_stack, msg);
            }
            CrashAwareAllocationBranchStack::Step::append_to_active(new_stack, path) => {
                self.append_to_active_refines(post, lbl, new_stack, path);
            }
            CrashAwareAllocationBranchStack::Step::append_to_empty(new_stack, init_root) => {
                self.append_to_empty_refines(post, lbl, new_stack, init_root);
            }
            CrashAwareAllocationBranchStack::Step::ephemeral_internal_noop(new_stack) => {
                self.ephemeral_internal_noop_refines(post, lbl, new_stack);
            }
            CrashAwareAllocationBranchStack::Step::ephemeral_internal_grow(new_stack, new_root_addr) => {
                self.ephemeral_internal_grow_refines(post, lbl, new_stack, new_root_addr);
            }
            CrashAwareAllocationBranchStack::Step::ephemeral_internal_split(new_stack, new_child_addr, path, split_arg) => {
                self.ephemeral_internal_split_refines(post, lbl, new_stack, new_child_addr, path, split_arg);
            }
            CrashAwareAllocationBranchStack::Step::ephemeral_internal_seal(new_stack, aux_ptr, loose_active_disk) => {
                self.ephemeral_internal_seal_refines(
                    post,
                    lbl,
                    new_stack,
                    aux_ptr,
                    loose_active_disk,
                );
            }
            CrashAwareAllocationBranchStack::Step::ephemeral_internal_fill_au(new_stack, aus) => {
                self.ephemeral_internal_fill_au_refines(post, lbl, new_stack, aus);
            }
            CrashAwareAllocationBranchStack::Step::freeze_map_internal() => {
                self.freeze_map_internal_refines(post, lbl);
            }
            CrashAwareAllocationBranchStack::Step::commit_start_ephemeral() => {
                self.commit_start_ephemeral_refines(post, lbl);
            }
            CrashAwareAllocationBranchStack::Step::commit_start_persistent() => {
                self.commit_start_persistent_refines(post, lbl);
            }
            CrashAwareAllocationBranchStack::Step::commit_complete() => {
                self.commit_complete_refines(post, lbl);
            }
            CrashAwareAllocationBranchStack::Step::crash() => {
                self.crash_refines(post, lbl);
            }
            _ => { }
        }
    }
}

}
