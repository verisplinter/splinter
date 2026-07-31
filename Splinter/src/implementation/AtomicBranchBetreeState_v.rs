// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Atomic ownership boundary for the cached Betree and its recovery/sync
// control state.

#![allow(unused_imports)]

use vstd::prelude::*;
use verus_state_machines_macros::state_machine;

use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::betree::LinkedBetree_v::{
    PathAddrs, SplitAddrs, TwoAddrs,
};
use crate::betree::SplitRequest_v::SplitRequest;
use crate::disk::GenericDisk_v::{AU, Address};
use crate::implementation::CachedBranchBetree_v::{
    CachedAllocationBranch, CachedAllocationBranchEvent,
    CachedBranchBetree, FrozenBranchBetree, LoadedBetree,
    LoadedBetreePath, LoadedBetreeQueryReceipt,
};
use crate::implementation::CachedBranch_v::LoadedBranch;
use crate::implementation::CrashAwareCachingDiskBranchBetree_v::{
    BetreeMetadataRecoveryCore, BetreeMetadataRecoveryLabel,
    CachingDiskBranchBetreeMetadata,
    FrozenCachingDiskBranchBetree,
};
use crate::implementation::CachingDiskBranchBetree_v::{
    BranchBuildEvent, PageAccess, to_betree_nodes,
};
use crate::spec::AsyncDisk_t::RawPage;

verus! {

#[verifier::ext_equal]
pub struct AtomicBranchBetreeControl {
    pub metadata: CachingDiskBranchBetreeMetadata,
    pub recovery: BetreeMetadataRecoveryCore,
    pub persistent_aus: Set<AU>,
    pub installed: bool,
    pub loading: bool,
    pub metadata_loaded: bool,
    pub frozen: Option<FrozenCachingDiskBranchBetree>,
}

impl AtomicBranchBetreeControl {
    pub open spec fn empty() -> Self {
        let metadata = CachingDiskBranchBetreeMetadata::empty();
        Self {
            metadata,
            recovery: BetreeMetadataRecoveryCore::start(metadata),
            persistent_aus: Set::empty(),
            installed: false,
            loading: false,
            metadata_loaded: false,
            frozen: None,
        }
    }

    pub open spec fn install(
        metadata: CachingDiskBranchBetreeMetadata,
    ) -> Self {
        Self {
            metadata,
            recovery: BetreeMetadataRecoveryCore::start(metadata),
            persistent_aus: Set::empty(),
            installed: true,
            loading: false,
            metadata_loaded: false,
            frozen: None,
        }
    }

    pub open spec fn protected_aus(self) -> Set<AU> {
        self.persistent_aus + if self.frozen is Some {
            self.frozen.unwrap().aus
        } else {
            Set::empty()
        }
    }

    pub open spec fn reclaimable(
        self,
        deallocs: Set<AU>,
    ) -> Set<AU> {
        deallocs - self.protected_aus()
    }
}

pub open spec fn empty_cached_betree()
    -> CachedBranchBetree::State
{
    let metadata = CachingDiskBranchBetreeMetadata::empty();
    BetreeMetadataRecoveryCore::start(metadata)
        .loaded_betree(metadata)
}

state_machine! { AtomicBranchBetreeState {
    fields {
        pub betree: CachedBranchBetree::State,
        pub control: AtomicBranchBetreeControl,
    }

    pub enum Label {
        Internal,
        Betree {
            cached_op: CachedBranchBetree::Label,
        },
        Recover {
            recovery_op: BetreeMetadataRecoveryLabel,
        },
        RecoveryComplete,
        CommitStart {
            image: FrozenBranchBetree,
        },
        CommitPrepared,
        CommitComplete,
    }

    init! { initialize(
        metadata: CachingDiskBranchBetreeMetadata,
    ) {
        init betree = empty_cached_betree();
        init control = AtomicBranchBetreeControl::install(metadata);
    }}

    transition! { query(
        lbl: Label,
        receipt: LoadedBetreeQueryReceipt,
        betree_reads: LoadedBetree,
        branch_reads: LoadedBranch,
    ) {
        require let Label::Betree{cached_op} = lbl;
        require CachedBranchBetree::State::query(
            pre.betree,
            pre.betree,
            cached_op,
            receipt,
            betree_reads,
            branch_reads,
        );
    }}

    transition! { put(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
    ) {
        require let Label::Betree{cached_op} = lbl;
        require CachedBranchBetree::State::put(
            pre.betree,
            new_betree,
            cached_op,
        );
        update betree = new_betree;
    }}

    transition! { branch_begin(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
    ) {
        require let Label::Betree{cached_op} = lbl;
        require CachedBranchBetree::State::branch_begin(
            pre.betree,
            new_betree,
            cached_op,
        );
        update betree = new_betree;
    }}

    transition! { branch_build(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        idx: int,
        post_branch: CachedAllocationBranch,
        event: CachedAllocationBranchEvent,
    ) {
        require let Label::Betree{cached_op} = lbl;
        require CachedBranchBetree::State::branch_build(
            pre.betree,
            new_betree,
            cached_op,
            idx,
            post_branch,
            event,
        );
        update betree = new_betree;
    }}

    transition! { branch_abort(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        idx: int,
    ) {
        require let Label::Betree{cached_op} = lbl;
        require CachedBranchBetree::State::branch_abort(
            pre.betree,
            new_betree,
            cached_op,
            idx,
        );
        update betree = new_betree;
    }}

    transition! { flush_memtable(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        branch_idx: int,
        new_root_addr: Address,
        betree_reads: LoadedBetree,
        betree_writes: LoadedBetree,
        branch_reads: LoadedBranch,
    ) {
        require let Label::Betree{cached_op} = lbl;
        require CachedBranchBetree::State::flush_memtable(
            pre.betree,
            new_betree,
            cached_op,
            branch_idx,
            new_root_addr,
            betree_reads,
            betree_writes,
            branch_reads,
        );
        update betree = new_betree;
    }}

    transition! { grow(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_root_addr: Address,
        betree_writes: LoadedBetree,
    ) {
        require let Label::Betree{cached_op} = lbl;
        require CachedBranchBetree::State::grow(
            pre.betree,
            new_betree,
            cached_op,
            new_root_addr,
            betree_writes,
        );
        update betree = new_betree;
    }}

    transition! { split(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        path: LoadedBetreePath,
        request: SplitRequest,
        new_addrs: SplitAddrs,
        path_addrs: PathAddrs,
        betree_reads: LoadedBetree,
        betree_writes: LoadedBetree,
    ) {
        require let Label::Betree{cached_op} = lbl;
        require CachedBranchBetree::State::split(
            pre.betree,
            new_betree,
            cached_op,
            path,
            request,
            new_addrs,
            path_addrs,
            betree_reads,
            betree_writes,
        );
        update betree = new_betree;
    }}

    transition! { flush(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        path: LoadedBetreePath,
        child_idx: nat,
        buffer_gc: nat,
        new_addrs: TwoAddrs,
        path_addrs: PathAddrs,
        betree_reads: LoadedBetree,
        betree_writes: LoadedBetree,
    ) {
        require let Label::Betree{cached_op} = lbl;
        require CachedBranchBetree::State::flush(
            pre.betree,
            new_betree,
            cached_op,
            path,
            child_idx,
            buffer_gc,
            new_addrs,
            path_addrs,
            betree_reads,
            betree_writes,
        );
        update betree = new_betree;
    }}

    transition! { compact_begin(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        path: LoadedBetreePath,
        start: nat,
        end: nat,
        betree_reads: LoadedBetree,
    ) {
        require let Label::Betree{cached_op} = lbl;
        require CachedBranchBetree::State::compact_begin(
            pre.betree,
            new_betree,
            cached_op,
            path,
            start,
            end,
            betree_reads,
        );
        update betree = new_betree;
    }}

    transition! { compact_abort(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        input_idx: int,
    ) {
        require let Label::Betree{cached_op} = lbl;
        require CachedBranchBetree::State::compact_abort(
            pre.betree,
            new_betree,
            cached_op,
            input_idx,
        );
        update betree = new_betree;
    }}

    transition! { compact_complete(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        input_idx: int,
        branch_idx: int,
        path: LoadedBetreePath,
        start: nat,
        end: nat,
        new_node_addr: Address,
        path_addrs: PathAddrs,
        betree_reads: LoadedBetree,
        betree_writes: LoadedBetree,
        branch_reads: LoadedBranch,
    ) {
        require let Label::Betree{cached_op} = lbl;
        require CachedBranchBetree::State::compact_complete(
            pre.betree,
            new_betree,
            cached_op,
            input_idx,
            branch_idx,
            path,
            start,
            end,
            new_node_addr,
            path_addrs,
            betree_reads,
            betree_writes,
            branch_reads,
        );
        update betree = new_betree;
    }}

    transition! { internal_noop(lbl: Label) {
        require lbl is Internal;
        require CachedBranchBetree::State::internal_noop(
            pre.betree,
            pre.betree,
            CachedBranchBetree::Label::Internal,
        );
    }}

    transition! { recovery_begin(lbl: Label) {
        require lbl is Internal;
        require pre.control.installed;
        require !pre.control.loading;
        require !pre.control.metadata_loaded;

        update control = AtomicBranchBetreeControl {
            recovery: BetreeMetadataRecoveryCore::start(
                pre.control.metadata,
            ),
            loading: true,
            ..pre.control
        };
    }}

    transition! { recover(
        lbl: Label,
        new_recovery: BetreeMetadataRecoveryCore,
    ) {
        require let Label::Recover{recovery_op} = lbl;
        require pre.control.loading;
        require !pre.control.metadata_loaded;
        require BetreeMetadataRecoveryCore::next(
            pre.control.recovery,
            new_recovery,
            recovery_op,
        );

        update control = AtomicBranchBetreeControl {
            recovery: new_recovery,
            ..pre.control
        };
    }}

    transition! { recovery_complete(lbl: Label) {
        require lbl is RecoveryComplete;
        require pre.control.loading;
        require !pre.control.metadata_loaded;
        require pre.control.recovery.complete();
        let loaded = pre.control.recovery.loaded_betree(
            pre.control.metadata,
        );
        let discovered_aus = loaded.durable_aus();

        update betree = loaded;
        update control = AtomicBranchBetreeControl {
            persistent_aus: discovered_aus,
            loading: false,
            metadata_loaded: true,
            ..pre.control
        };
    }}

    transition! { commit_start(lbl: Label) {
        require let Label::CommitStart{image} = lbl;
        require pre.control.frozen is None;
        require pre.betree.compactors.len() == 0;
        require pre.betree.wip_branches.len() == 0;
        require CachedBranchBetree::State::freeze_as(
            pre.betree,
            pre.betree,
            CachedBranchBetree::Label::FreezeAs{image},
        );

        update control = AtomicBranchBetreeControl {
            frozen: Some(FrozenCachingDiskBranchBetree {
                metadata: CachingDiskBranchBetreeMetadata {
                    root: image.root,
                    seq_end: image.seq_end,
                },
                aus: pre.betree.durable_aus(),
            }),
            ..pre.control
        };
    }}

    transition! { commit_prepared(lbl: Label) {
        require lbl is CommitPrepared;
        require pre.control.frozen is Some;
    }}

    transition! { commit_complete(lbl: Label) {
        require lbl is CommitComplete;
        require pre.control.frozen is Some;
        let frozen = pre.control.frozen.unwrap();

        update control = AtomicBranchBetreeControl {
            metadata: frozen.metadata,
            persistent_aus: frozen.aus,
            frozen: None,
            ..pre.control
        };
    }}
}}

impl AtomicBranchBetreeState::State {
    pub open spec fn empty() -> Self {
        Self {
            betree: empty_cached_betree(),
            control: AtomicBranchBetreeControl::empty(),
        }
    }

    pub open spec fn metadata_loaded(self) -> bool {
        self.control.metadata_loaded
    }

    pub open spec fn protected_aus(self) -> Set<AU> {
        self.control.protected_aus()
    }

    pub open spec fn reclaimable(
        self,
        deallocs: Set<AU>,
    ) -> Set<AU> {
        self.control.reclaimable(deallocs)
    }

    pub open spec fn internal_access_next(
        pre: Self,
        post: Self,
        lbl: AtomicBranchBetreeState::Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    ) -> bool {
        match lbl {
            AtomicBranchBetreeState::Label::Recover{
                recovery_op,
            } => {
                &&& writes.is_empty()
                &&& match recovery_op {
                    BetreeMetadataRecoveryLabel::ReadBetree{
                        reads: recovery_reads,
                        ..
                    }
                    | BetreeMetadataRecoveryLabel::ReadBranchRoot{
                        reads: recovery_reads,
                        ..
                    }
                    | BetreeMetadataRecoveryLabel::ReadBranchAux{
                        reads: recovery_reads,
                        ..
                    } => recovery_reads == reads,
                    BetreeMetadataRecoveryLabel::DiskInternal =>
                        false,
                }
                &&& AtomicBranchBetreeState::State::recover(
                    pre,
                    post,
                    lbl,
                    post.control.recovery,
                )
            },
            AtomicBranchBetreeState::Label::Betree{
                cached_op,
            } => {
                &&& cached_op is Internal
                &&& pre.control.metadata_loaded
                &&& writes.is_empty()
                &&& exists |
                    path: LoadedBetreePath,
                    start: nat,
                    end: nat,
                | AtomicBranchBetreeState::State::compact_begin(
                    pre,
                    post,
                    lbl,
                    post.betree,
                    path,
                    start,
                    end,
                    to_betree_nodes(reads),
                )
            },
            _ => false,
        }
    }

    pub open spec fn internal_alloc_access_next_by(
        pre: Self,
        post: Self,
        allocs: Set<AU>,
        deallocs: Set<AU>,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        step: AtomicBranchBetreeState::Step,
        access: PageAccess,
    ) -> bool {
        let lbl = AtomicBranchBetreeState::Label::Betree {
            cached_op: CachedBranchBetree::Label::InternalAlloc {
                allocs,
                deallocs,
            },
        };
        &&& pre.control.metadata_loaded
        &&& AtomicBranchBetreeState::State::next_by(
            pre,
            post,
            lbl,
            step,
        )
        &&& access.reads() == reads
        &&& access.writes() == writes
        &&& match step {
                AtomicBranchBetreeState::Step::branch_begin(
                    _,
                ) => {
                    &&& allocs.is_empty()
                    &&& deallocs.is_empty()
                    &&& access == PageAccess::empty()
                },
                AtomicBranchBetreeState::Step::branch_build(
                    _,
                    _,
                    _,
                    cached_event,
                ) => {
                    &&& access.only_branch()
                    &&& exists |event: BranchBuildEvent|
                        event.cached_event(access) == cached_event
                },
                AtomicBranchBetreeState::Step::flush_memtable(
                    _,
                    _,
                    _,
                    betree_reads,
                    betree_writes,
                    branch_reads,
                ) => {
                    &&& access.wf()
                    &&& access.branch_writes.is_empty()
                    &&& access.loaded_betree_reads()
                        == betree_reads
                    &&& access.loaded_betree_writes()
                        == betree_writes
                    &&& access.loaded_branch_reads()
                        == branch_reads
                },
                AtomicBranchBetreeState::Step::grow(
                    _,
                    _,
                    betree_writes,
                ) => {
                    &&& access.only_betree()
                    &&& access.loaded_betree_writes()
                        == betree_writes
                },
                AtomicBranchBetreeState::Step::split(
                    _,
                    _,
                    _,
                    _,
                    _,
                    betree_reads,
                    betree_writes,
                ) => {
                    &&& access.only_betree()
                    &&& access.loaded_betree_reads()
                        == betree_reads
                    &&& access.loaded_betree_writes()
                        == betree_writes
                },
                AtomicBranchBetreeState::Step::flush(
                    _,
                    _,
                    _,
                    _,
                    _,
                    _,
                    betree_reads,
                    betree_writes,
                ) => {
                    &&& access.only_betree()
                    &&& access.loaded_betree_reads()
                        == betree_reads
                    &&& access.loaded_betree_writes()
                        == betree_writes
                },
                AtomicBranchBetreeState::Step::compact_complete(
                    _,
                    _,
                    _,
                    _,
                    _,
                    _,
                    _,
                    _,
                    betree_reads,
                    betree_writes,
                    branch_reads,
                ) => {
                    &&& access.wf()
                    &&& access.branch_writes.is_empty()
                    &&& access.loaded_betree_reads()
                        == betree_reads
                    &&& access.loaded_betree_writes()
                        == betree_writes
                    &&& access.loaded_branch_reads()
                        == branch_reads
                },
            _ => false,
        }
    }

    pub open spec fn internal_alloc_access_next(
        pre: Self,
        post: Self,
        allocs: Set<AU>,
        deallocs: Set<AU>,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    ) -> bool {
        exists |
            step: AtomicBranchBetreeState::Step,
            access: PageAccess,
        | AtomicBranchBetreeState::State::
            internal_alloc_access_next_by(
                pre,
                post,
                allocs,
                deallocs,
                reads,
                writes,
                step,
                access,
            )
    }

    ////////////////////////////////////////////////////////////////////////////
    // Utility proofs
    ////////////////////////////////////////////////////////////////////////////

    pub proof fn put_effect(
        pre: Self,
        post: Self,
        puts: MsgHistory,
    )
        requires
            AtomicBranchBetreeState::State::next(
                pre,
                post,
                AtomicBranchBetreeState::Label::Betree {
                    cached_op: CachedBranchBetree::Label::Put{puts},
                },
            ),
        ensures
            post.control == pre.control,
            CachedBranchBetree::State::put(
                pre.betree,
                post.betree,
                CachedBranchBetree::Label::Put{puts},
            ),
    {
        let lbl = AtomicBranchBetreeState::Label::Betree {
            cached_op: CachedBranchBetree::Label::Put{puts},
        };
        reveal(AtomicBranchBetreeState::State::next);
        reveal(AtomicBranchBetreeState::State::next_by);
        let step = choose |step| AtomicBranchBetreeState::State::next_by(
            pre,
            post,
            lbl,
            step,
        );
        match step {
            AtomicBranchBetreeState::Step::put(new_betree) => {
                assert(AtomicBranchBetreeState::State::put(
                    pre,
                    post,
                    lbl,
                    new_betree,
                )) by {
                    reveal(AtomicBranchBetreeState::State::put);
                }
            },
            _ => {
                assert(false);
            },
        }
    }
}

} // verus!
