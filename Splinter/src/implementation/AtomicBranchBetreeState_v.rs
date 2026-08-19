// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Atomic ownership boundary for the cached Betree and its recovery/sync
// control state.

#![allow(unused_imports)]

use vstd::prelude::*;
use verus_state_machines_macros::state_machine;

use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::abstract_system::StampedMap_v::LSN;
use crate::betree::LinkedBetree_v::{
    PathAddrs, SplitAddrs, TwoAddrs,
};
use crate::betree::SplitRequest_v::SplitRequest;
use crate::disk::GenericDisk_v::{AU, Address};
use crate::implementation::CachedBranchBetree_v::{
    CachedBranchBetree, FrozenBranchBetree, LoadedBetree,
    LoadedBetreePath, LoadedBetreeQueryReceipt,
};
use crate::implementation::CachedBulkBranch_v::{
    CachedBulkBranch, CachedBulkBranchEvent,
};
use crate::implementation::CachedBranch_v::LoadedBranch;
use crate::implementation::CrashAwareCachingDiskBranchBetree_v::{
    BetreeMetadataRecoveryCore, BetreeMetadataRecoveryLabel,
    CachingDiskBranchBetreeMetadata,
    FrozenCachingDiskBranchBetree,
};
use crate::implementation::CachingDiskBranchBetree_v::{
    BranchBuildEvent, PageAccess, to_betree_nodes, to_branch_nodes,
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

pub open spec fn recovery_page_access(
    recovery_op: BetreeMetadataRecoveryLabel,
) -> PageAccess {
    match recovery_op {
        BetreeMetadataRecoveryLabel::ReadBetree { reads, .. } =>
            PageAccess {
                betree_reads: reads,
                branch_reads: Map::empty(),
                betree_writes: Map::empty(),
                branch_writes: Map::empty(),
            },
        BetreeMetadataRecoveryLabel::ReadBranchRoot { reads, .. }
        | BetreeMetadataRecoveryLabel::ReadBranchAux { reads, .. } =>
            PageAccess {
                betree_reads: Map::empty(),
                branch_reads: reads,
                betree_writes: Map::empty(),
                branch_writes: Map::empty(),
            },
        BetreeMetadataRecoveryLabel::DiskInternal => PageAccess::empty(),
    }
}

state_machine! { AtomicBranchBetreeState {
    fields {
        pub betree: CachedBranchBetree::State,
        pub control: AtomicBranchBetreeControl,
    }

    pub enum Label {
        Internal,
        Query {
            end_lsn: LSN,
            key: crate::spec::KeyType_t::Key,
            value: crate::spec::Messages_t::Value,
            access: PageAccess,
        },
        Put {
            puts: MsgHistory,
        },
        InternalAccess {
            access: PageAccess,
        },
        InternalAllocAccess {
            allocs: Set<AU>,
            deallocs: Set<AU>,
            access: PageAccess,
        },
        RecoveryAccess {
            access: PageAccess,
        },
        RecoveryComplete {
            discovered_aus: Set<AU>,
        },
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
        require let Label::Query{
            end_lsn, key, value, access,
        } = lbl;
        require CachedBranchBetree::State::next(
            pre.betree,
            pre.betree,
            CachedBranchBetree::Label::Query {
                end_lsn,
                key,
                value,
                access: access.cached_access(),
            },
        );
    }}

    transition! { put(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
    ) {
        require let Label::Put{puts} = lbl;
        require CachedBranchBetree::State::next(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::Put{puts},
        );
        update betree = new_betree;
    }}

    transition! { branch_begin(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
    ) {
        require let Label::InternalAllocAccess{
            allocs, deallocs, access,
        } = lbl;
        require CachedBranchBetree::State::next(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAllocAccess {
                allocs,
                deallocs,
                access: access.cached_access(),
            },
        );
        update betree = new_betree;
    }}

    transition! { branch_build(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        idx: int,
        post_branch: CachedBulkBranch,
        event: CachedBulkBranchEvent,
    ) {
        require let Label::InternalAllocAccess{
            allocs, deallocs, access,
        } = lbl;
        require CachedBranchBetree::State::next(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAllocAccess {
                allocs,
                deallocs,
                access: access.cached_access(),
            },
        );
        update betree = new_betree;
    }}

    transition! { branch_fill(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        idx: int,
        post_branch: CachedBulkBranch,
    ) {
        require let Label::InternalAllocAccess{
            allocs, deallocs, access,
        } = lbl;
        require CachedBranchBetree::State::next(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAllocAccess {
                allocs,
                deallocs,
                access: access.cached_access(),
            },
        );
        update betree = new_betree;
    }}

    transition! { branch_abort(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        idx: int,
    ) {
        require let Label::InternalAllocAccess{
            allocs, deallocs, access,
        } = lbl;
        require CachedBranchBetree::State::next(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAllocAccess {
                allocs,
                deallocs,
                access: access.cached_access(),
            },
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
        require let Label::InternalAllocAccess{
            allocs, deallocs, access,
        } = lbl;
        require CachedBranchBetree::State::next(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAllocAccess {
                allocs,
                deallocs,
                access: access.cached_access(),
            },
        );
        update betree = new_betree;
    }}

    transition! { grow(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_root_addr: Address,
        betree_writes: LoadedBetree,
    ) {
        require let Label::InternalAllocAccess{
            allocs, deallocs, access,
        } = lbl;
        require CachedBranchBetree::State::next(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAllocAccess {
                allocs,
                deallocs,
                access: access.cached_access(),
            },
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
        require let Label::InternalAllocAccess{
            allocs, deallocs, access,
        } = lbl;
        require CachedBranchBetree::State::next(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAllocAccess {
                allocs,
                deallocs,
                access: access.cached_access(),
            },
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
        require let Label::InternalAllocAccess{
            allocs, deallocs, access,
        } = lbl;
        require CachedBranchBetree::State::next(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAllocAccess {
                allocs,
                deallocs,
                access: access.cached_access(),
            },
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
        require let Label::InternalAccess{access} = lbl;
        require CachedBranchBetree::State::next(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAccess {
                access: access.cached_access(),
            },
        );
        update betree = new_betree;
    }}

    transition! { compact_scan_page(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        input_idx: int,
        branch_reads: LoadedBranch,
    ) {
        require let Label::InternalAccess{access} = lbl;
        require CachedBranchBetree::State::next(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAccess {
                access: access.cached_access(),
            },
        );
        update betree = new_betree;
    }}

    transition! { compact_abort(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        input_idx: int,
    ) {
        require let Label::InternalAllocAccess{
            allocs, deallocs, access,
        } = lbl;
        require CachedBranchBetree::State::next(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAllocAccess {
                allocs,
                deallocs,
                access: access.cached_access(),
            },
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
    ) {
        require let Label::InternalAllocAccess{
            allocs, deallocs, access,
        } = lbl;
        require CachedBranchBetree::State::next(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAllocAccess {
                allocs,
                deallocs,
                access: access.cached_access(),
            },
        );
        update betree = new_betree;
    }}

    transition! { internal_noop(lbl: Label) {
        require lbl is Internal;
        require CachedBranchBetree::State::next(
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
        recovery_op: BetreeMetadataRecoveryLabel,
    ) {
        require let Label::RecoveryAccess{access} = lbl;
        require !(recovery_op is DiskInternal);
        require access == recovery_page_access(recovery_op);
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

    transition! { recover_internal(
        lbl: Label,
        new_recovery: BetreeMetadataRecoveryCore,
        recovery_op: BetreeMetadataRecoveryLabel,
    ) {
        require lbl is Internal;
        require recovery_op is DiskInternal;
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
        require let Label::RecoveryComplete{discovered_aus} = lbl;
        require pre.control.loading;
        require !pre.control.metadata_loaded;
        require pre.control.recovery.complete();
        let loaded = pre.control.recovery.loaded_betree(
            pre.control.metadata,
        );
        require discovered_aus == loaded.durable_aus();

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
        require CachedBranchBetree::State::next(
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

    ////////////////////////////////////////////////////////////////////////////
    // Utility proofs
    ////////////////////////////////////////////////////////////////////////////

    pub proof fn query_effect(
        pre: Self,
        end_lsn: LSN,
        key: crate::spec::KeyType_t::Key,
        value: crate::spec::Messages_t::Value,
        access: PageAccess,
    )
        requires AtomicBranchBetreeState::State::next(
            pre,
            pre,
            AtomicBranchBetreeState::Label::Query {
                end_lsn,
                key,
                value,
                access,
            },
        )
        ensures CachedBranchBetree::State::next(
            pre.betree,
            pre.betree,
            CachedBranchBetree::Label::Query {
                end_lsn,
                key,
                value,
                access: access.cached_access(),
            },
        ),
    {
        let lbl = AtomicBranchBetreeState::Label::Query {
            end_lsn,
            key,
            value,
            access,
        };
        reveal(AtomicBranchBetreeState::State::next);
        reveal(AtomicBranchBetreeState::State::next_by);
        let step = choose |step| AtomicBranchBetreeState::State::next_by(
            pre,
            pre,
            lbl,
            step,
        );
        match step {
            AtomicBranchBetreeState::Step::query(..) => {},
            _ => { assert(false); },
        }
    }

    pub proof fn put_effect(
        pre: Self,
        post: Self,
        puts: MsgHistory,
    )
        requires
            AtomicBranchBetreeState::State::next(
                pre,
                post,
                AtomicBranchBetreeState::Label::Put{puts},
            ),
        ensures
            post.control == pre.control,
            CachedBranchBetree::State::next(
                pre.betree,
                post.betree,
                CachedBranchBetree::Label::Put{puts},
            ),
    {
        let lbl = AtomicBranchBetreeState::Label::Put{puts};
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
                }
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn internal_access_effect(
        pre: Self,
        post: Self,
        access: PageAccess,
    )
        requires AtomicBranchBetreeState::State::next(
            pre,
            post,
            AtomicBranchBetreeState::Label::InternalAccess{access},
        )
        ensures
            post.control == pre.control,
            CachedBranchBetree::State::next(
                pre.betree,
                post.betree,
                CachedBranchBetree::Label::InternalAccess{
                    access: access.cached_access(),
                },
            ),
    {
        reveal(AtomicBranchBetreeState::State::next);
        reveal(AtomicBranchBetreeState::State::next_by);
        let step = choose |step: AtomicBranchBetreeState::Step|
            AtomicBranchBetreeState::State::next_by(
                pre,
                post,
                AtomicBranchBetreeState::Label::InternalAccess{access},
                step,
            );
        match step {
            AtomicBranchBetreeState::Step::compact_begin(..)
            | AtomicBranchBetreeState::Step::compact_scan_page(..) => {},
            _ => { assert(false); },
        }
    }

    pub proof fn internal_alloc_access_effect(
        pre: Self,
        post: Self,
        allocs: Set<AU>,
        deallocs: Set<AU>,
        access: PageAccess,
    )
        requires AtomicBranchBetreeState::State::next(
            pre,
            post,
            AtomicBranchBetreeState::Label::InternalAllocAccess{
                allocs, deallocs, access,
            },
        )
        ensures
            post.control == pre.control,
            CachedBranchBetree::State::next(
                pre.betree,
                post.betree,
                CachedBranchBetree::Label::InternalAllocAccess{
                    allocs,
                    deallocs,
                    access: access.cached_access(),
                },
            ),
    {
        reveal(AtomicBranchBetreeState::State::next);
        reveal(AtomicBranchBetreeState::State::next_by);
        let step = choose |step: AtomicBranchBetreeState::Step|
            AtomicBranchBetreeState::State::next_by(
                pre,
                post,
                AtomicBranchBetreeState::Label::InternalAllocAccess{
                    allocs, deallocs, access,
                },
                step,
            );
        match step {
            AtomicBranchBetreeState::Step::branch_begin(..)
            | AtomicBranchBetreeState::Step::branch_build(..)
            | AtomicBranchBetreeState::Step::branch_fill(..)
            | AtomicBranchBetreeState::Step::branch_abort(..)
            | AtomicBranchBetreeState::Step::flush_memtable(..)
            | AtomicBranchBetreeState::Step::grow(..)
            | AtomicBranchBetreeState::Step::split(..)
            | AtomicBranchBetreeState::Step::flush(..)
            | AtomicBranchBetreeState::Step::compact_abort(..)
            | AtomicBranchBetreeState::Step::compact_complete(..) => {},
            _ => { assert(false); },
        }
    }

}

impl AtomicBranchBetreeState::Label {
    pub open spec fn internal_access(self) -> Option<PageAccess> {
        match self {
            AtomicBranchBetreeState::Label::InternalAccess{access}
            | AtomicBranchBetreeState::Label::RecoveryAccess{access} => Some(access),
            _ => None,
        }
    }
}

} // verus!
