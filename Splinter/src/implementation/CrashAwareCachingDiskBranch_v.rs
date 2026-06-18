// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Crash-aware wrapper for CachingDiskBranch.

#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::map::*;
use vstd::assert_seqs_equal;

use verus_state_machines_macros::state_machine;

use crate::disk::GenericDisk_v::{Address, AU};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Message, Value};
use crate::allocation_layer::AllocationBranchBetree_v::summary_aus;
use crate::implementation::AllocationBranchStack_v::{new_branch_inv, normalize_value};
use crate::implementation::CachingDiskBranch_v::*;
use crate::implementation::CachingDisk_v::CachingDisk;
use crate::implementation::CrashAwareAllocationBranchStack_v::{
    EphemeralAllocationBranchStack, FrozenAllocationBranchStack,
    CrashAwareAllocationBranchStack,
};

verus!{

pub enum EphemeralCachingDiskBranch {
    Unknown,
    Known{ v: CachingDiskBranch::State },
}

pub proof fn cdb_step_preserves_image_match(
    pre: CachingDiskBranch::State,
    post: CachingDiskBranch::State,
    lbl: CachingDiskBranch::Label,
    image: CachingDiskBranchImage,
)
    requires
        pre.inv(),
        image.sealed_roots.len() <= pre.sealed_roots.len(),
        pre.sealed_roots.subrange(0, image.sealed_roots.len() as int) == image.sealed_roots,
        pre.visible_image_for_metadata(CachingDiskBranchFrozenImage{
            sealed_roots: image.sealed_roots,
            seq_end: image.seq_end,
        }).sealed_stack_i() == image.sealed_stack_i(),
        CachingDiskBranch::State::next(pre, post, lbl),
    ensures
        image.sealed_roots.len() <= post.sealed_roots.len(),
        post.sealed_roots.subrange(0, image.sealed_roots.len() as int) == image.sealed_roots,
        post.visible_image_for_metadata(CachingDiskBranchFrozenImage{
            sealed_roots: image.sealed_roots,
            seq_end: image.seq_end,
        }).sealed_stack_i() == image.sealed_stack_i(),
{
    let frozen = CachingDiskBranchFrozenImage{
        sealed_roots: image.sealed_roots,
        seq_end: image.seq_end,
    };
    CachingDiskBranch::State::inv_next(pre, post, lbl);
    if pre.metadata_loaded {
        CachingDiskBranch::State::next_preserves_loaded_root_prefix(
            pre,
            post,
            lbl,
            image.sealed_roots,
        );
        pre.next_preserves_visible_prefix_image(post, lbl, frozen);
    } else {
        reveal(CachingDiskBranch::State::next);
        reveal(CachingDiskBranch::State::next_by);
        let step = choose |step: CachingDiskBranch::Step|
            CachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskBranch::Step::disk_internal(new_disk) => {
                reveal(CachingDiskBranch::State::disk_internal);
                CachingDisk::State::internal_visible_unchanged(pre.disk, post.disk);
                assert(post.sealed_roots == pre.sealed_roots);
                assert(post.visible_image_for_metadata(frozen)
                    == pre.visible_image_for_metadata(frozen));
            },
            CachingDiskBranch::Step::load_metadata(reads) => {
                reveal(CachingDiskBranch::State::load_metadata);
                assert(post.sealed_roots == pre.sealed_roots);
                assert(post.disk == pre.disk);
                assert(post.visible_image_for_metadata(frozen)
                    == pre.visible_image_for_metadata(frozen));
            },
            CachingDiskBranch::Step::internal_fill_au(aus, new_disk) => {
                reveal(CachingDiskBranch::State::internal_fill_au);
                assert(post.sealed_roots == pre.sealed_roots);
                assert(post.visible_image_for_metadata(frozen)
                    == pre.visible_image_for_metadata(frozen));
            },
            CachingDiskBranch::Step::internal_noop() => {
                reveal(CachingDiskBranch::State::internal_noop);
                assert(post == pre);
            },
            CachingDiskBranch::Step::freeze_prepared() => {
                reveal(CachingDiskBranch::State::freeze_prepared);
                assert(post == pre);
            },
            _ => {
                assert(false);
            },
        }
    }
}

state_machine!{ CrashAwareCachingDiskBranch {
    fields {
        pub persistent: CachingDiskBranchImage,
        pub ephemeral: EphemeralCachingDiskBranch,
        pub frozen: Option<CachingDiskBranchFrozenImage>,
        pub prepared: bool,
    }

    pub enum Label {
        LoadEphemeral,
        LoadMetadata{ root: Address, discovered_aus: Set<AU> },
        Query{ key: Key, value: Value },
        Append{ keys: Seq<Key>, msgs: Seq<Message> },
        Internal,
        InternalAlloc{ allocs: Set<AU>, deallocs: Set<AU> },
        CommitStart{ new_boundary_lsn: nat, sealed_roots: Seq<Address> },
        FreezePrepared,
        CommitComplete,
        Crash{ keep_in_flight: bool },
    }

    init!{ initialize() {
        init persistent = empty_caching_disk_branch_image();
        init ephemeral = EphemeralCachingDiskBranch::Unknown;
        init frozen = Option::None;
        init prepared = false;
    }}

    transition!{ load_ephemeral(lbl: Label, new_ephemeral: CachingDiskBranch::State) {
        require lbl is LoadEphemeral;
        require pre.ephemeral is Unknown;
        require CachingDiskBranch::State::initialize(new_ephemeral, pre.persistent);
        update ephemeral = EphemeralCachingDiskBranch::Known{
            v: new_ephemeral,
        };
    }}

    transition!{ load_metadata(lbl: Label, new_ephemeral: CachingDiskBranch::State) {
        require let Label::LoadMetadata{root, discovered_aus} = lbl;
        require pre.ephemeral is Known;
        require CachingDiskBranch::State::next(
            pre.ephemeral->v,
            new_ephemeral,
            CachingDiskBranch::Label::LoadMetadata{root, discovered_aus},
        );
        update ephemeral = EphemeralCachingDiskBranch::Known{
            v: new_ephemeral,
        };
    }}

    transition!{ query(lbl: Label, msg: Message) {
        require let Label::Query{key, value} = lbl;
        require pre.ephemeral is Known;
        require normalize_value(msg) == value;
        require CachingDiskBranch::State::next(pre.ephemeral->v, pre.ephemeral->v,
            CachingDiskBranch::Label::QueryLabel{key, msg});
    }}

    transition!{ append(lbl: Label, new_ephemeral: CachingDiskBranch::State) {
        require let Label::Append{keys, msgs} = lbl;
        require pre.ephemeral is Known;
        require CachingDiskBranch::State::next(pre.ephemeral->v, new_ephemeral,
            CachingDiskBranch::Label::AppendLabel{keys, msgs});
        update ephemeral = EphemeralCachingDiskBranch::Known{ v: new_ephemeral };
    }}

    transition!{ internal(lbl: Label, new_ephemeral: CachingDiskBranch::State) {
        require lbl is Internal;
        require pre.ephemeral is Known;
        require CachingDiskBranch::State::next(pre.ephemeral->v, new_ephemeral,  CachingDiskBranch::Label::Internal);
        update ephemeral = EphemeralCachingDiskBranch::Known{ v: new_ephemeral };
    }}

    transition!{ internal_alloc(lbl: Label, new_ephemeral: CachingDiskBranch::State) {
        require let Label::InternalAlloc{allocs, deallocs} = lbl;
        require pre.ephemeral is Known;
        require CachingDiskBranch::State::next(pre.ephemeral->v, new_ephemeral,
            CachingDiskBranch::Label::InternalAlloc{allocs, deallocs});
        update ephemeral = EphemeralCachingDiskBranch::Known{ v: new_ephemeral };
    }}

    transition!{ commit_start(lbl: Label) {
        require let Label::CommitStart{new_boundary_lsn, sealed_roots} = lbl;
        require pre.ephemeral is Known;
        require pre.frozen is None;
        let frozen = CachingDiskBranchFrozenImage{
            sealed_roots,
            seq_end: new_boundary_lsn,
        };
        require {
            ||| {
                &&& new_boundary_lsn == pre.persistent.seq_end
                &&& sealed_roots == pre.persistent.sealed_roots
            }
            ||| CachingDiskBranch::State::next(
                pre.ephemeral->v,
                pre.ephemeral->v,
                CachingDiskBranch::Label::FreezeAsLabel{image: frozen},
            )
        };

        update frozen = Option::Some(frozen);
    }}

    transition!{ freeze_prepared(lbl: Label) {
        require lbl is FreezePrepared;
        require pre.ephemeral is Known;
        require pre.frozen is Some;
        require !pre.prepared;
        let frozen = pre.frozen.unwrap();
        require CachingDiskBranch::State::next(
            pre.ephemeral->v,
            pre.ephemeral->v,
            CachingDiskBranch::Label::FreezePrepared{
                image: frozen,
            },
        );

        update prepared = true;
    }}

    transition!{ commit_complete(lbl: Label, prepared_image: CachingDiskBranchImage) {
        require lbl is CommitComplete;
        require pre.frozen is Some;
        require pre.prepared;
        require pre.ephemeral is Known;
        let frozen = pre.frozen.unwrap();
        require prepared_image.sealed_roots == frozen.sealed_roots;
        require prepared_image.seq_end == frozen.seq_end;
        require prepared_image.persistent == pre.ephemeral->v.disk.persistent;
        require CachingDiskBranch::State::next(
            pre.ephemeral->v,
            pre.ephemeral->v,
            CachingDiskBranch::Label::FreezePrepared{
                image: frozen,
            },
        );

        update persistent = prepared_image;
        update frozen = Option::None;
        update prepared = false;
    }}

    transition!{ crash(lbl: Label, prepared_image: CachingDiskBranchImage) {
        require let Label::Crash{keep_in_flight} = lbl;
        require keep_in_flight ==> pre.frozen is Some;
        require keep_in_flight ==> pre.prepared;
        require keep_in_flight ==> pre.ephemeral is Known;
        require keep_in_flight ==> prepared_image.sealed_roots == pre.frozen.unwrap().sealed_roots;
        require keep_in_flight ==> prepared_image.seq_end == pre.frozen.unwrap().seq_end;
        require keep_in_flight ==> prepared_image.persistent == pre.ephemeral->v.disk.persistent;
        require keep_in_flight ==> CachingDiskBranch::State::next(
            pre.ephemeral->v,
            pre.ephemeral->v,
            CachingDiskBranch::Label::FreezePrepared{
                image: pre.frozen.unwrap(),
            },
        );

        update ephemeral = EphemeralCachingDiskBranch::Unknown;
        update frozen = Option::None;
        update prepared = false;
        update persistent = if keep_in_flight {
            prepared_image
        } else {
            pre.persistent
        };
    }}

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.wf()
        &&& self.stack_compatible()
        &&& self.persistent_matches_ephemeral()
        &&& self.persistent.sealed_stack_i().wf()
        &&& self.frozen is None ==> !self.prepared
        &&& self.frozen is Some && self.ephemeral is Known ==> {
            ||| {
                &&& self.frozen.unwrap().sealed_roots == self.persistent.sealed_roots
                &&& self.frozen.unwrap().seq_end == self.persistent.seq_end
            }
            ||| {
                &&& self.ephemeral->v.metadata_loaded
                &&& self.frozen.unwrap().sealed_roots.len()
                    <= self.ephemeral->v.sealed_roots.len()
                &&& self.ephemeral->v.sealed_roots.subrange(
                    0,
                    self.frozen.unwrap().sealed_roots.len() as int,
                ) == self.frozen.unwrap().sealed_roots
            }
        }
        &&& self.prepared ==> self.frozen is Some
        &&& self.prepared ==> self.ephemeral is Known
        &&& self.prepared && self.ephemeral is Known && self.frozen is Some ==>
            self.frozen.unwrap().sealed_roots.len() <= self.ephemeral->v.persisted_root_count
    }

    #[invariant]
    pub open spec(checked) fn stack_compatible(self) -> bool {
        &&& self.frozen is Some ==> self.persistent.seq_end <= self.frozen.unwrap().seq_end
        &&& self.ephemeral is Known ==> self.persistent.seq_end <= self.ephemeral->v.seq_end
        &&& self.ephemeral is Known && self.frozen is Some
            ==> self.frozen.unwrap().seq_end <= self.ephemeral->v.seq_end
    }

    #[invariant]
    pub open spec(checked) fn persistent_matches_ephemeral(self) -> bool {
        self.ephemeral is Known ==> {
            let frozen = CachingDiskBranchFrozenImage{
                sealed_roots: self.persistent.sealed_roots,
                seq_end: self.persistent.seq_end,
            };
            &&& self.persistent.sealed_roots.len() <= self.ephemeral->v.sealed_roots.len()
            &&& self.ephemeral->v.sealed_roots.subrange(
                0,
                self.persistent.sealed_roots.len() as int,
            ) == self.persistent.sealed_roots
            &&& self.ephemeral->v.visible_image_for_metadata(frozen).sealed_stack_i()
                == self.persistent.sealed_stack_i()
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) {
        empty_caching_disk_branch_image_wf();
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(load_ephemeral)]
    fn load_ephemeral_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_ephemeral: CachingDiskBranch::State,
    ) {
        match lbl {
            Label::LoadEphemeral => {
                reveal(CrashAwareCachingDiskBranch::State::load_ephemeral);
                reveal(CachingDiskBranch::State::initialize);
                CachingDiskBranch::State::initialize_inductive(
                    new_ephemeral,
                    pre.persistent,
                );
                assert(post.ephemeral == EphemeralCachingDiskBranch::Known{v: new_ephemeral});
                assert(new_ephemeral == CachingDiskBranch::State::load_from_persistent(pre.persistent));
                assert(new_ephemeral.sealed_roots == pre.persistent.sealed_roots);
                assert(new_ephemeral.disk.persistent == pre.persistent.persistent);
                assert(new_ephemeral.persisted_root_count == pre.persistent.sealed_roots.len());
                assert_seqs_equal!(
                    post.ephemeral->v.sealed_roots.subrange(
                        0,
                        post.persistent.sealed_roots.len() as int,
                    ),
                    post.persistent.sealed_roots
                );
                let branch_lbl = CachingDiskBranch::Label::FreezePrepared{
                    image: CachingDiskBranchFrozenImage{
                        sealed_roots: pre.persistent.sealed_roots,
                        seq_end: pre.persistent.seq_end,
                    },
                };
                assert(CachingDiskBranch::State::next(
                    post.ephemeral->v,
                    post.ephemeral->v,
                    branch_lbl,
                )) by {
                    reveal(CachingDiskBranch::State::next);
                    reveal(CachingDiskBranch::State::next_by);
                    assert(CachingDiskBranch::State::freeze_prepared(
                        post.ephemeral->v,
                        post.ephemeral->v,
                        branch_lbl,
                    )) by {
                        reveal(CachingDiskBranch::State::freeze_prepared);
                    };
                    assert(CachingDiskBranch::State::next_by(
                        post.ephemeral->v,
                        post.ephemeral->v,
                        branch_lbl,
                        CachingDiskBranch::Step::freeze_prepared(),
                    ));
                };
                post.ephemeral->v.prepared_image_matches_visible_prefix(pre.persistent);
                assert_seqs_equal!(
                    post.ephemeral->v.sealed_roots.subrange(
                        0,
                        post.persistent.sealed_roots.len() as int,
                    ),
                    post.persistent.sealed_roots
                );
                assert(post.ephemeral->v.disk.inv());
                assert(post.ephemeral->v.inv());
            },
            _ => { }
        }
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(load_metadata)]
    fn load_metadata_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_ephemeral: CachingDiskBranch::State,
    ) {
        reveal(CrashAwareCachingDiskBranch::State::load_metadata);
        match lbl {
            Label::LoadMetadata{root, discovered_aus} => {
                let branch_lbl = CachingDiskBranch::Label::LoadMetadata{root, discovered_aus};
                CachingDiskBranch::State::inv_next(pre.ephemeral->v, new_ephemeral, branch_lbl);
                cdb_step_preserves_image_match(
                    pre.ephemeral->v,
                    post.ephemeral->v,
                    branch_lbl,
                    pre.persistent,
                );
                CachingDiskBranch::State::next_preserves_seq_end_lower_bound(
                    pre.ephemeral->v,
                    new_ephemeral,
                    branch_lbl,
                    pre.persistent.seq_end,
                );
                if pre.frozen is Some {
                    CachingDiskBranch::State::next_preserves_seq_end_lower_bound(
                        pre.ephemeral->v,
                        new_ephemeral,
                        branch_lbl,
                        pre.frozen.unwrap().seq_end,
                    );
                    if pre.prepared {
                        CachingDiskBranch::State::next_preserves_persisted_root_count_lower_bound(
                            pre.ephemeral->v,
                            new_ephemeral,
                            branch_lbl,
                            pre.frozen.unwrap().sealed_roots.len() as nat,
                        );
                    }
                    if !(pre.frozen.unwrap().sealed_roots == pre.persistent.sealed_roots
                        && pre.frozen.unwrap().seq_end == pre.persistent.seq_end) {
                        CachingDiskBranch::State::next_preserves_loaded_root_prefix(
                            pre.ephemeral->v,
                            new_ephemeral,
                            branch_lbl,
                            pre.frozen.unwrap().sealed_roots,
                        );
                    }
                }
            },
            _ => { }
        }
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(query)]
    fn query_inductive(pre: Self, post: Self, lbl: Label, msg: Message) {
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(append)]
    fn append_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskBranch::State) {
        reveal(CrashAwareCachingDiskBranch::State::append);
        let branch_lbl = CachingDiskBranch::Label::AppendLabel{
            keys: lbl.arrow_Append_keys(),
            msgs: lbl.arrow_Append_msgs(),
        };
        CachingDiskBranch::State::inv_next(pre.ephemeral->v, post.ephemeral->v, branch_lbl);
        cdb_step_preserves_image_match(
            pre.ephemeral->v,
            post.ephemeral->v,
            branch_lbl,
            pre.persistent,
        );
        CachingDiskBranch::State::next_preserves_seq_end_lower_bound(
            pre.ephemeral->v,
            post.ephemeral->v,
            branch_lbl,
            pre.persistent.seq_end,
        );
        if pre.frozen is Some {
            CachingDiskBranch::State::next_preserves_seq_end_lower_bound(
                pre.ephemeral->v,
                post.ephemeral->v,
                branch_lbl,
                pre.frozen.unwrap().seq_end,
            );
            if pre.prepared {
                CachingDiskBranch::State::next_preserves_persisted_root_count_lower_bound(
                    pre.ephemeral->v,
                    post.ephemeral->v,
                    branch_lbl,
                    pre.frozen.unwrap().sealed_roots.len() as nat,
                );
            }
            if !(pre.frozen.unwrap().sealed_roots == pre.persistent.sealed_roots
                && pre.frozen.unwrap().seq_end == pre.persistent.seq_end) {
                CachingDiskBranch::State::next_preserves_loaded_root_prefix(
                    pre.ephemeral->v,
                    post.ephemeral->v,
                    branch_lbl,
                    pre.frozen.unwrap().sealed_roots,
                );
            }
        }
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(internal)]
    fn internal_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskBranch::State) {
        reveal(CrashAwareCachingDiskBranch::State::internal);
        let branch_lbl = CachingDiskBranch::Label::Internal;
        CachingDiskBranch::State::inv_next(pre.ephemeral->v, post.ephemeral->v, branch_lbl);
        cdb_step_preserves_image_match(
            pre.ephemeral->v,
            post.ephemeral->v,
            branch_lbl,
            pre.persistent,
        );
        CachingDiskBranch::State::next_preserves_seq_end_lower_bound(
            pre.ephemeral->v,
            post.ephemeral->v,
            branch_lbl,
            pre.persistent.seq_end,
        );
        if pre.frozen is Some {
            CachingDiskBranch::State::next_preserves_seq_end_lower_bound(
                pre.ephemeral->v,
                post.ephemeral->v,
                branch_lbl,
                pre.frozen.unwrap().seq_end,
            );
            if pre.prepared {
                CachingDiskBranch::State::next_preserves_persisted_root_count_lower_bound(
                    pre.ephemeral->v,
                    post.ephemeral->v,
                    branch_lbl,
                    pre.frozen.unwrap().sealed_roots.len() as nat,
                );
            }
            if !(pre.frozen.unwrap().sealed_roots == pre.persistent.sealed_roots
                && pre.frozen.unwrap().seq_end == pre.persistent.seq_end) {
                CachingDiskBranch::State::next_preserves_loaded_root_prefix(
                    pre.ephemeral->v,
                    post.ephemeral->v,
                    branch_lbl,
                    pre.frozen.unwrap().sealed_roots,
                );
            }
        }
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(internal_alloc)]
    fn internal_alloc_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskBranch::State) {
        reveal(CrashAwareCachingDiskBranch::State::internal_alloc);
        let branch_lbl = CachingDiskBranch::Label::InternalAlloc{
            allocs: lbl.arrow_InternalAlloc_allocs(),
            deallocs: lbl.arrow_InternalAlloc_deallocs(),
        };
        CachingDiskBranch::State::inv_next(pre.ephemeral->v, post.ephemeral->v, branch_lbl);
        cdb_step_preserves_image_match(
            pre.ephemeral->v,
            post.ephemeral->v,
            branch_lbl,
            pre.persistent,
        );
        CachingDiskBranch::State::next_preserves_seq_end_lower_bound(
            pre.ephemeral->v,
            post.ephemeral->v,
            branch_lbl,
            pre.persistent.seq_end,
        );
        if pre.frozen is Some {
            CachingDiskBranch::State::next_preserves_seq_end_lower_bound(
                pre.ephemeral->v,
                post.ephemeral->v,
                branch_lbl,
                pre.frozen.unwrap().seq_end,
            );
            if pre.prepared {
                CachingDiskBranch::State::next_preserves_persisted_root_count_lower_bound(
                    pre.ephemeral->v,
                    post.ephemeral->v,
                    branch_lbl,
                    pre.frozen.unwrap().sealed_roots.len() as nat,
                );
            }
            if !(pre.frozen.unwrap().sealed_roots == pre.persistent.sealed_roots
                && pre.frozen.unwrap().seq_end == pre.persistent.seq_end) {
                CachingDiskBranch::State::next_preserves_loaded_root_prefix(
                    pre.ephemeral->v,
                    post.ephemeral->v,
                    branch_lbl,
                    pre.frozen.unwrap().sealed_roots,
                );
            }
        }
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(commit_start)]
    fn commit_start_inductive(pre: Self, post: Self, lbl: Label) {
        reveal(CrashAwareCachingDiskBranch::State::commit_start);
        match lbl {
            Label::CommitStart{new_boundary_lsn, sealed_roots} => {
                let frozen = CachingDiskBranchFrozenImage{
                    sealed_roots,
                    seq_end: new_boundary_lsn,
                };
                if !(post.frozen.unwrap().sealed_roots == post.persistent.sealed_roots
                    && post.frozen.unwrap().seq_end == post.persistent.seq_end) {
                    reveal(CachingDiskBranch::State::next);
                    reveal(CachingDiskBranch::State::next_by);
                    let branch_lbl = CachingDiskBranch::Label::FreezeAsLabel{image: frozen};
                    let step = choose |step: CachingDiskBranch::Step|
                        CachingDiskBranch::State::next_by(pre.ephemeral->v, pre.ephemeral->v, branch_lbl, step);
                    match step {
                        CachingDiskBranch::Step::freeze_as() => {
                            reveal(CachingDiskBranch::State::freeze_as);
                        },
                        _ => { assert(false); },
                    }
                    assert(sealed_roots == pre.ephemeral->v.sealed_roots);
                    assert(post.frozen.unwrap().sealed_roots == pre.ephemeral->v.sealed_roots);
                    assert(post.frozen.unwrap().sealed_roots.len()
                        == pre.ephemeral->v.sealed_roots.len());
                    assert(pre.ephemeral->v.sealed_roots.subrange(
                        0,
                        post.frozen.unwrap().sealed_roots.len() as int,
                    ) == post.frozen.unwrap().sealed_roots);
                }
            },
            _ => {}
        }
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(freeze_prepared)]
    fn freeze_prepared_inductive(pre: Self, post: Self, lbl: Label) {
        reveal(CrashAwareCachingDiskBranch::State::freeze_prepared);
        assert(post.prepared);
        let frozen = pre.frozen.unwrap();
        let branch_lbl = CachingDiskBranch::Label::FreezePrepared{
            image: frozen,
        };
        assert(CachingDiskBranch::State::next(
            pre.ephemeral->v,
            pre.ephemeral->v,
            branch_lbl,
        )) by {
            reveal(CachingDiskBranch::State::next);
            reveal(CachingDiskBranch::State::next_by);
            assert(CachingDiskBranch::State::freeze_prepared(
                pre.ephemeral->v,
                pre.ephemeral->v,
                branch_lbl,
            )) by {
                reveal(CachingDiskBranch::State::freeze_prepared);
            };
            assert(CachingDiskBranch::State::next_by(
                pre.ephemeral->v,
                pre.ephemeral->v,
                branch_lbl,
                CachingDiskBranch::Step::freeze_prepared(),
            ));
        };
        assert(frozen.sealed_roots.len() <= pre.ephemeral->v.persisted_root_count) by {
            reveal(CachingDiskBranch::State::next);
            reveal(CachingDiskBranch::State::next_by);
            let step = choose |step: CachingDiskBranch::Step|
                CachingDiskBranch::State::next_by(
                    pre.ephemeral->v,
                    pre.ephemeral->v,
                    branch_lbl,
                    step,
                );
            match step {
                CachingDiskBranch::Step::freeze_prepared() => {
                    reveal(CachingDiskBranch::State::freeze_prepared);
                },
                _ => { assert(false); },
            }
            assert(CachingDiskBranch::State::freeze_prepared(
                pre.ephemeral->v,
                pre.ephemeral->v,
                branch_lbl,
            ));
        }
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(commit_complete)]
    fn commit_complete_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        prepared_image: CachingDiskBranchImage,
    ) {
        reveal(CrashAwareCachingDiskBranch::State::commit_complete);
        pre.ephemeral->v.prepared_image_matches_visible_prefix(prepared_image);
        assert(prepared_image.sealed_stack_i().wf());
        assert(post.ephemeral->v.inv());
        assert(post.wf());
        assert(post.persistent.sealed_stack_i().wf());
        assert(post.stack_compatible());
    }

    #[inductive(crash)]
    fn crash_inductive(pre: Self, post: Self, lbl: Label, prepared_image: CachingDiskBranchImage) {
        if lbl.arrow_Crash_keep_in_flight() {
            pre.ephemeral->v.prepared_image_matches_visible_prefix(prepared_image);
            assert(prepared_image.sealed_stack_i().wf());
            assert(post.persistent.sealed_stack_i().wf());
        } else {
            assert(post.persistent == pre.persistent);
        }
        assert(post.wf());
        assert(post.stack_compatible());
    }

    pub proof fn inv_next(pre: Self, post: Self, lbl: Label)
        requires
            pre.inv(),
            CrashAwareCachingDiskBranch::State::next(pre, post, lbl),
        ensures
            post.inv(),
    {
        reveal(CrashAwareCachingDiskBranch::State::next);
        reveal(CrashAwareCachingDiskBranch::State::next_by);
        let step = choose |step| CrashAwareCachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CrashAwareCachingDiskBranch::Step::load_ephemeral(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::load_ephemeral(pre, post, lbl, new_ephemeral)) by {
                    reveal(CrashAwareCachingDiskBranch::State::load_ephemeral);
                }
                CrashAwareCachingDiskBranch::State::load_ephemeral_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskBranch::Step::load_metadata(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::load_metadata(pre, post, lbl, new_ephemeral)) by {
                    reveal(CrashAwareCachingDiskBranch::State::load_metadata);
                }
                CrashAwareCachingDiskBranch::State::load_metadata_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskBranch::Step::query(msg) => {
                assert(CrashAwareCachingDiskBranch::State::query(pre, post, lbl, msg)) by {
                    reveal(CrashAwareCachingDiskBranch::State::query);
                }
                CrashAwareCachingDiskBranch::State::query_inductive(pre, post, lbl, msg);
            },
            CrashAwareCachingDiskBranch::Step::append(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::append(pre, post, lbl, new_ephemeral)) by {
                    reveal(CrashAwareCachingDiskBranch::State::append);
                }
                CrashAwareCachingDiskBranch::State::append_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskBranch::Step::internal(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::internal(pre, post, lbl, new_ephemeral)) by {
                    reveal(CrashAwareCachingDiskBranch::State::internal);
                }
                CrashAwareCachingDiskBranch::State::internal_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskBranch::Step::internal_alloc(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::internal_alloc(pre, post, lbl, new_ephemeral)) by {
                    reveal(CrashAwareCachingDiskBranch::State::internal_alloc);
                }
                CrashAwareCachingDiskBranch::State::internal_alloc_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskBranch::Step::commit_start() => {
                assert(CrashAwareCachingDiskBranch::State::commit_start(pre, post, lbl)) by {
                    reveal(CrashAwareCachingDiskBranch::State::commit_start);
                }
                CrashAwareCachingDiskBranch::State::commit_start_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskBranch::Step::freeze_prepared() => {
                assert(CrashAwareCachingDiskBranch::State::freeze_prepared(pre, post, lbl)) by {
                    reveal(CrashAwareCachingDiskBranch::State::freeze_prepared);
                }
                CrashAwareCachingDiskBranch::State::freeze_prepared_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskBranch::Step::commit_complete(prepared_image) => {
                assert(CrashAwareCachingDiskBranch::State::commit_complete(pre, post, lbl, prepared_image)) by {
                    reveal(CrashAwareCachingDiskBranch::State::commit_complete);
                }
                CrashAwareCachingDiskBranch::State::commit_complete_inductive(pre, post, lbl, prepared_image);
            },
            CrashAwareCachingDiskBranch::Step::crash(prepared_image) => {
                assert(CrashAwareCachingDiskBranch::State::crash(pre, post, lbl, prepared_image)) by {
                    reveal(CrashAwareCachingDiskBranch::State::crash);
                }
                CrashAwareCachingDiskBranch::State::crash_inductive(pre, post, lbl, prepared_image);
            },
            _ => {
                assert(post.inv());
            },
        }
    }
}}

impl CrashAwareCachingDiskBranch::State {
    pub open spec fn wf(self) -> bool {
        &&& self.ephemeral is Unknown ==> self.frozen is None && !self.prepared
        &&& self.ephemeral is Known ==> self.ephemeral->v.inv()
    }

    pub proof fn load_metadata_preserves_full_accessible_aus(
        pre: Self,
        post: Self,
        root: Address,
        discovered_aus: Set<AU>,
    )
        requires
            pre.inv(),
            CrashAwareCachingDiskBranch::State::next(
                pre,
                post,
                CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus},
            ),
        ensures
            post.persistent == pre.persistent,
            post.frozen == pre.frozen,
            pre.ephemeral is Known,
            post.ephemeral is Known,
            post.ephemeral->v.full_accessible_aus()
                == pre.ephemeral->v.full_accessible_aus(),
    {
        let lbl = CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus};
        reveal(CrashAwareCachingDiskBranch::State::next);
        reveal(CrashAwareCachingDiskBranch::State::next_by);
        let step = choose |step| CrashAwareCachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CrashAwareCachingDiskBranch::Step::load_metadata(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::load_metadata(
                    pre,
                    post,
                    lbl,
                    new_ephemeral,
                )) by {
                    reveal(CrashAwareCachingDiskBranch::State::load_metadata);
                }
                CachingDiskBranch::State::load_metadata_preserves_full_accessible_aus(
                    pre.ephemeral->v,
                    new_ephemeral,
                    root,
                    discovered_aus,
                );
                assert(post.ephemeral->v == new_ephemeral);
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn load_metadata_accessible_aus_growth(
        pre: Self,
        post: Self,
        root: Address,
        discovered_aus: Set<AU>,
    )
        requires
            pre.inv(),
            CrashAwareCachingDiskBranch::State::next(
                pre,
                post,
                CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus},
            ),
        ensures
            post.persistent == pre.persistent,
            post.frozen == pre.frozen,
            pre.ephemeral is Known,
            post.ephemeral is Known,
            post.ephemeral->v.accessible_aus()
                <= pre.ephemeral->v.accessible_aus() + discovered_aus,
    {
        let lbl = CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus};
        reveal(CrashAwareCachingDiskBranch::State::next);
        reveal(CrashAwareCachingDiskBranch::State::next_by);
        let step = choose |step| CrashAwareCachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CrashAwareCachingDiskBranch::Step::load_metadata(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::load_metadata(
                    pre,
                    post,
                    lbl,
                    new_ephemeral,
                )) by {
                    reveal(CrashAwareCachingDiskBranch::State::load_metadata);
                }
                CachingDiskBranch::State::load_metadata_accessible_aus_growth(
                    pre.ephemeral->v,
                    new_ephemeral,
                    root,
                    discovered_aus,
                );
                assert(post.ephemeral->v == new_ephemeral);
            },
            _ => {
                assert(false);
            },
        }
    }
}

}
