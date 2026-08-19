// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Coordination composition for the crash-aware caching-disk journal and
// crash-aware caching-disk Betree. This is the Betree counterpart of
// CrashAwareCachingDiskSystem and is kept parallel during migration.

#![allow(unused_imports)]

use vstd::prelude::*;

use verus_state_machines_macros::state_machine;

use crate::abstract_system::AbstractCrashAwareMap_v::
    AbstractCrashAwareMap;
use crate::abstract_system::AbstractCrashAwareJournal_v::
    AbstractCrashAwareJournal;
use crate::abstract_system::AbstractCrashAwareSystem_v::
    CoordinationSystem;
use crate::abstract_system::MsgHistory_v::{KeyedMessage, MsgHistory};
use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::{AU, Address, to_aus};
use crate::implementation::AbstractSuperblock_v::{
    AbstractSuperblockImage, empty_abstract_superblock_image,
    superblock_matches,
};
use crate::implementation::CachingDiskBranchBetree_v::{
    CachingDiskBranchBetree, PageAccess,
};
use crate::implementation::CrashAwareCachingDiskBranchBetree_v::{
    BetreeMetadataRecoveryLabel, CrashAwareCachingDiskBranchBetree,
    EphemeralCachingDiskBranchBetree, logical_allocs,
};
use crate::implementation::CrashAwareCachingDiskJournal_v::{
    CrashAwareCachingDiskJournal, EphemeralCachingDiskJournal,
};
use crate::implementation::SuperblockStore_v::SuperblockStore;
use crate::implementation::UnifiedCacheBetreeSystem_v::{
    betree_metadata_from_superblock, betree_superblock_image_wf,
};
use crate::spec::AsyncDisk_t::RawPage;
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::{
    AsyncMap, EphemeralState, Input, Output, Reply, Request, SyncReqId,
};
use crate::spec::Messages_t::Message;

verus! {

pub open spec fn branch_internal_label(
    lbl: CrashAwareCachingDiskBranchBetree::Label,
) -> bool {
    match lbl {
        CrashAwareCachingDiskBranchBetree::Label::RecoverMetadata{
            recovery_op:
                BetreeMetadataRecoveryLabel::DiskInternal,
        } => true,
        CrashAwareCachingDiskBranchBetree::Label::Ephemeral{
            op: CachingDiskBranchBetree::Label::Internal
                | CachingDiskBranchBetree::Label::InternalAccess{..},
            deallocs,
        } => deallocs.is_empty(),
        _ => false,
    }
}

state_machine! { CrashAwareCachingDiskBetreeSystem {
    fields {
        pub journal: CrashAwareCachingDiskJournal::State,
        pub branch: CrashAwareCachingDiskBranchBetree::State,
        pub progress: EphemeralState,
        pub sync_reqs: Map<SyncReqId, LSN>,
        pub superblockstore: SuperblockStore::State,
        pub free_aus: Set<AU>,
    }

    pub enum Label {
        Request{req: Request},
        Execute{req: Request, reply: Reply},
        Reply{reply: Reply},
        ReqSync{sync_req_id: SyncReqId},
        ReplySync{sync_req_id: SyncReqId},
        Sync,
        Crash,
        Noop,
    }

    init! { initialize(
        free_aus: Set<AU>,
        initial_superblock: RawPage,
        journal: CrashAwareCachingDiskJournal::State,
        branch: CrashAwareCachingDiskBranchBetree::State,
    ) {
        require Self::reserved_aus().disjoint(free_aus);
        require superblock_matches(
            initial_superblock,
            empty_abstract_superblock_image(),
        );
        require CrashAwareCachingDiskJournal::State::initialize(journal);
        require CrashAwareCachingDiskBranchBetree::State::initialize(branch);

        init journal = journal;
        init branch = branch;
        init progress = AsyncMap::State::init_ephemeral_state();
        init sync_reqs = Map::empty();
        init superblockstore = SuperblockStore::State {
            persistent: initial_superblock,
            in_flight: None,
            landed: false,
        };
        init free_aus = free_aus;
    }}

    transition! { accept_request(lbl: Label) {
        require let Label::Request{req} = lbl;
        require !pre.progress.requests.contains(req);

        update progress = EphemeralState {
            requests: pre.progress.requests.insert(req),
            ..pre.progress
        };
    }}

    transition! { deliver_reply(lbl: Label) {
        require let Label::Reply{reply} = lbl;
        require pre.progress.replies.contains(reply);

        update progress = EphemeralState {
            replies: pre.progress.replies.remove(reply),
            ..pre.progress
        };
    }}

    transition! { query(
        lbl: Label,
        new_branch: CrashAwareCachingDiskBranchBetree::State,
        access: PageAccess,
    ) {
        require let Label::Execute{req, reply} = lbl;
        require req.input is QueryInput;
        require reply.output is QueryOutput;
        require req.id == reply.id;
        require pre.progress.requests.contains(req);
        require !pre.progress.replies.contains(reply);
        let key = req.input.arrow_QueryInput_key();
        let value = reply.output.arrow_QueryOutput_value();
        require pre.journal.ephemeral is Known;
        require pre.journal.ephemeral->v.journal.status is Some;
        require pre.journal_lsn() == pre.branch_lsn();
        require CrashAwareCachingDiskBranchBetree::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranchBetree::Label::Ephemeral {
                op: CachingDiskBranchBetree::Label::Query {
                    end_lsn: pre.branch_lsn(),
                    key,
                    value,
                    access,
                },
                deallocs: Set::empty(),
            },
        );

        update branch = new_branch;
        update progress = EphemeralState {
            requests: pre.progress.requests.remove(req),
            replies: pre.progress.replies.insert(reply),
        };
    }}

    transition! { put(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranchBetree::State,
    ) {
        require let Label::Execute{req, reply} = lbl;
        require let Request{
            input: Input::PutInput{key, value},
            id: request_id,
        } = req;
        require let Reply{
            output: Output::PutOutput,
            id: reply_id,
        } = reply;
        require request_id == reply_id;
        require pre.progress.requests.contains(req);
        require !pre.progress.replies.contains(reply);
        let records = MsgHistory::singleton_at(
            pre.branch_lsn(),
            KeyedMessage {
                key,
                message: Message::Define{value},
            },
        );
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::Put{
                records,
            },
        );
        require CrashAwareCachingDiskBranchBetree::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranchBetree::Label::Ephemeral {
                op: CachingDiskBranchBetree::Label::Put{
                    puts: records,
                },
                deallocs: Set::empty(),
            },
        );

        update journal = new_journal;
        update branch = new_branch;
        update progress = EphemeralState {
            requests: pre.progress.requests.remove(req),
            replies: pre.progress.replies.insert(reply),
        };
    }}

    transition! { execute_noop(lbl: Label) {
        require let Label::Execute{req, reply} = lbl;
        require req.input is NoopInput;
        require reply.output is NoopOutput;
        require req.id == reply.id;
        require pre.progress.requests.contains(req);
        require !pre.progress.replies.contains(reply);

        update progress = EphemeralState {
            requests: pre.progress.requests.remove(req),
            replies: pre.progress.replies.insert(reply),
        };
    }}

    transition! { req_sync(lbl: Label) {
        require let Label::ReqSync{sync_req_id} = lbl;
        require pre.components_loaded();
        require !pre.sync_reqs.contains_key(sync_req_id);
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            pre.journal,
            CrashAwareCachingDiskJournal::Label::QueryEndLsn{
                end_lsn: pre.branch_lsn(),
            },
        );

        update sync_reqs =
            pre.sync_reqs.insert(sync_req_id, pre.branch_lsn());
    }}

    transition! { reply_sync(lbl: Label) {
        require let Label::ReplySync{sync_req_id} = lbl;
        require pre.components_loaded();
        require pre.sync_reqs.contains_key(sync_req_id);
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            pre.journal,
            CrashAwareCachingDiskJournal::Label::QueryLsnPersistence{
                sync_lsn: pre.sync_reqs[sync_req_id],
            },
        );

        update sync_reqs = pre.sync_reqs.remove(sync_req_id);
    }}

    transition! { journal_internal(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
    ) {
        require lbl is Noop;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::Internal,
        );

        update journal = new_journal;
    }}

    transition! { journal_observe_clean_aus(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        aus: Set<AU>,
    ) {
        require lbl is Noop;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::ObserveCleanAUs{aus},
        );

        update journal = new_journal;
    }}

    transition! { journal_load_ephemeral(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
    ) {
        require lbl is Noop;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::LoadEphemeral,
        );

        update journal = new_journal;
    }}

    transition! { journal_load_index(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        discovered_aus: Set<AU>,
    ) {
        require lbl is Noop;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::LoadIndex{
                discovered_aus,
            },
        );

        update journal = new_journal;
        update free_aus = pre.free_aus - discovered_aus;
    }}

    transition! { journal_internal_alloc(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        allocs: Set<AU>,
        deallocs: Set<AU>,
        prune_aus: Set<AU>,
    ) {
        require lbl is Noop;
        require pre.allocation_ready();
        require allocs <= pre.free_aus;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::InternalAlloc{
                allocs,
                deallocs,
                prune_aus,
            },
        );

        update journal = new_journal;
        update free_aus = (pre.free_aus - allocs) + deallocs;
    }}

    transition! { branch_load_ephemeral(
        lbl: Label,
        new_branch: CrashAwareCachingDiskBranchBetree::State,
    ) {
        require lbl is Noop;
        require CrashAwareCachingDiskBranchBetree::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranchBetree::Label::LoadEphemeral,
        );

        update branch = new_branch;
    }}

    transition! { branch_recover_metadata(
        lbl: Label,
        new_branch: CrashAwareCachingDiskBranchBetree::State,
        recovery_op: BetreeMetadataRecoveryLabel,
    ) {
        require lbl is Noop;
        require CrashAwareCachingDiskBranchBetree::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranchBetree::Label::RecoverMetadata{
                recovery_op,
            },
        );

        update branch = new_branch;
    }}

    transition! { branch_load_metadata(
        lbl: Label,
        new_branch: CrashAwareCachingDiskBranchBetree::State,
        discovered_aus: Set<AU>,
    ) {
        require lbl is Noop;
        require CrashAwareCachingDiskBranchBetree::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranchBetree::Label::LoadMetadata,
        );
        require new_branch.ephemeral is Known;
        require discovered_aus
            == new_branch.ephemeral->persistent_aus;

        update branch = new_branch;
        update free_aus = pre.free_aus - discovered_aus;
    }}

    transition! { branch_internal(
        lbl: Label,
        new_branch: CrashAwareCachingDiskBranchBetree::State,
        branch_lbl: CrashAwareCachingDiskBranchBetree::Label,
    ) {
        require lbl is Noop;
        require branch_internal_label(branch_lbl);
        require CrashAwareCachingDiskBranchBetree::State::next(
            pre.branch,
            new_branch,
            branch_lbl,
        );

        update branch = new_branch;
    }}

    transition! { component_internals(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranchBetree::State,
        branch_lbl: CrashAwareCachingDiskBranchBetree::Label,
    ) {
        require lbl is Noop;
        require branch_internal_label(branch_lbl);
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::Internal,
        );
        require CrashAwareCachingDiskBranchBetree::State::next(
            pre.branch,
            new_branch,
            branch_lbl,
        );

        update journal = new_journal;
        update branch = new_branch;
    }}

    transition! { branch_internal_alloc(
        lbl: Label,
        new_branch: CrashAwareCachingDiskBranchBetree::State,
        op: CachingDiskBranchBetree::Label,
        allocs: Set<AU>,
        deallocs: Set<AU>,
    ) {
        require lbl is Noop;
        require pre.allocation_ready();
        require op is InternalAllocAccess;
        require logical_allocs(op) == allocs;
        require allocs <= pre.free_aus;
        require CrashAwareCachingDiskBranchBetree::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranchBetree::Label::Ephemeral{
                op,
                deallocs,
            },
        );

        update branch = new_branch;
        update free_aus = (pre.free_aus - allocs) + deallocs;
    }}

    transition! { recover(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranchBetree::State,
        journal_records: MsgHistory,
        branch_records: MsgHistory,
    ) {
        require lbl is Noop;
        require journal_records.wf();
        require pre.branch_lsn() <= journal_records.seq_end;
        require branch_records
            == journal_records.maybe_discard_old(pre.branch_lsn());
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::ReadForRecovery{
                records: journal_records,
            },
        );
        require CrashAwareCachingDiskBranchBetree::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranchBetree::Label::Ephemeral{
                op: CachingDiskBranchBetree::Label::Put{
                    puts: branch_records,
                },
                deallocs: Set::empty(),
            },
        );

        update journal = new_journal;
        update branch = new_branch;
    }}

    transition! { journal_commit_start(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        superblock_image: AbstractSuperblockImage,
    ) {
        require lbl is Noop;
        require betree_superblock_image_wf(superblock_image);
        require pre.branch.ephemeral is Known;
        require betree_metadata_from_superblock(superblock_image)
            == pre.branch.persistent.metadata;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::CommitStart{
                new_boundary_lsn:
                    superblock_image.journal_snapshot.boundary_lsn,
                snapshot: superblock_image.journal_snapshot,
                seq_end: superblock_image.journal_seq_end,
            },
        );

        update journal = new_journal;
    }}

    transition! { store_commit_start(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranchBetree::State,
        superblock_image: AbstractSuperblockImage,
    ) {
        require lbl is Noop;
        require betree_superblock_image_wf(superblock_image);
        let metadata =
            betree_metadata_from_superblock(superblock_image);
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::CommitStart{
                new_boundary_lsn:
                    superblock_image.journal_snapshot.boundary_lsn,
                snapshot: superblock_image.journal_snapshot,
                seq_end: superblock_image.journal_seq_end,
            },
        );
        require CrashAwareCachingDiskBranchBetree::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranchBetree::Label::CommitStart{
                image:
                    crate::implementation::CachedBranchBetree_v::FrozenBranchBetree {
                        root: metadata.root,
                        seq_end: metadata.seq_end,
                    },
            },
        );

        update journal = new_journal;
        update branch = new_branch;
    }}

    transition! { journal_commit_prepared(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_superblock: SuperblockStore::State,
        raw_page: RawPage,
        superblock_image: AbstractSuperblockImage,
    ) {
        require lbl is Noop;
        require pre.journal.frozen is Some;
        require pre.branch.frozen is None;
        require superblock_image.journal_snapshot
            == pre.journal.frozen.unwrap().snapshot;
        require superblock_image.journal_seq_end
            == pre.journal.frozen.unwrap().seq_end;
        require betree_metadata_from_superblock(superblock_image)
            == pre.branch.persistent.metadata;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::CommitPrepared,
        );
        require superblock_matches(raw_page, superblock_image);
        require SuperblockStore::State::next(
            pre.superblockstore,
            new_superblock,
            SuperblockStore::Label::Write{raw: raw_page},
        );

        update journal = new_journal;
        update superblockstore = new_superblock;
    }}

    transition! { store_commit_prepared(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranchBetree::State,
        new_superblock: SuperblockStore::State,
        raw_page: RawPage,
        superblock_image: AbstractSuperblockImage,
    ) {
        require lbl is Noop;
        require pre.journal.frozen is Some;
        require pre.branch.frozen is Some;
        require superblock_image.journal_snapshot
            == pre.journal.frozen.unwrap().snapshot;
        require superblock_image.journal_seq_end
            == pre.journal.frozen.unwrap().seq_end;
        require betree_metadata_from_superblock(superblock_image)
            == pre.branch.frozen.unwrap().metadata;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::CommitPrepared,
        );
        require CrashAwareCachingDiskBranchBetree::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranchBetree::Label::CommitPrepared,
        );
        require superblock_matches(raw_page, superblock_image);
        require SuperblockStore::State::next(
            pre.superblockstore,
            new_superblock,
            SuperblockStore::Label::Write{raw: raw_page},
        );

        update journal = new_journal;
        update branch = new_branch;
        update superblockstore = new_superblock;
    }}

    transition! { superblock_write_lands(
        lbl: Label,
        new_superblock: SuperblockStore::State,
    ) {
        require lbl is Sync;
        require SuperblockStore::State::next(
            pre.superblockstore,
            new_superblock,
            SuperblockStore::Label::Land,
        );

        update superblockstore = new_superblock;
    }}

    transition! { journal_commit_complete(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_superblock: SuperblockStore::State,
        journal_discarded: Set<AU>,
    ) {
        require lbl is Noop;
        require pre.branch.frozen is None;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::CommitComplete{
                require_end: pre.branch_lsn(),
                discarded: journal_discarded,
            },
        );
        require SuperblockStore::State::next(
            pre.superblockstore,
            new_superblock,
            SuperblockStore::Label::Complete,
        );

        update journal = new_journal;
        update superblockstore = new_superblock;
        update free_aus = pre.free_aus + journal_discarded;
    }}

    transition! { store_commit_complete(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranchBetree::State,
        new_superblock: SuperblockStore::State,
        journal_discarded: Set<AU>,
        branch_discarded: Set<AU>,
    ) {
        require lbl is Noop;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::CommitComplete{
                require_end: pre.branch_lsn(),
                discarded: journal_discarded,
            },
        );
        require CrashAwareCachingDiskBranchBetree::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranchBetree::Label::CommitComplete{
                deallocs: branch_discarded,
            },
        );
        require SuperblockStore::State::next(
            pre.superblockstore,
            new_superblock,
            SuperblockStore::Label::Complete,
        );

        update journal = new_journal;
        update branch = new_branch;
        update superblockstore = new_superblock;
        update free_aus =
            pre.free_aus + journal_discarded + branch_discarded;
    }}

    transition! { crash(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranchBetree::State,
        new_superblock: SuperblockStore::State,
        new_free_aus: Set<AU>,
        keep_in_flight: bool,
    ) {
        require lbl is Crash;
        require keep_in_flight == pre.superblockstore.landed;
        let branch_keep_in_flight =
            keep_in_flight && pre.branch.prepared is Some;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::Crash{
                keep_in_flight,
            },
        );
        require CrashAwareCachingDiskBranchBetree::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranchBetree::Label::Crash{
                keep_in_flight: branch_keep_in_flight,
            },
        );
        require SuperblockStore::State::next(
            pre.superblockstore,
            new_superblock,
            SuperblockStore::Label::Crash,
        );

        update journal = new_journal;
        update branch = new_branch;
        update superblockstore = new_superblock;
        update progress = AsyncMap::State::init_ephemeral_state();
        update sync_reqs = Map::empty();
        update free_aus = new_free_aus - Self::reserved_aus();
    }}

    transition! { noop(lbl: Label) {
        require lbl is Noop;
    }}

    pub open spec fn journal_lsn(self) -> LSN {
        if self.journal.ephemeral is Known
            && self.journal.ephemeral->v.journal.status is Some
        {
            self.journal.ephemeral->v.journal.seq_end()
        } else {
            self.journal.persistent.metadata().seq_end
        }
    }

    pub open spec fn branch_lsn(self) -> LSN {
        match self.branch.ephemeral {
            EphemeralCachingDiskBranchBetree::Known{v, ..} =>
                v.betree.memtable.seq_end,
            _ => self.branch.persistent.metadata.seq_end,
        }
    }

    pub open spec fn journal_allocation_ready(self) -> bool {
        &&& self.journal.ephemeral is Known
        &&& self.journal.ephemeral->v.journal.status is Some
    }

    pub open spec fn branch_allocation_ready(self) -> bool {
        self.branch.ephemeral is Known
    }

    pub open spec fn allocation_ready(self) -> bool {
        self.journal_allocation_ready()
            && self.branch_allocation_ready()
    }

    pub open spec fn reserved_aus() -> Set<AU> {
        set![
            crate::implementation::DiskLayout_v::
                spec_superblock_addr().au
        ]
    }

    pub open spec fn commit_started(self) -> bool {
        self.journal.frozen is Some
    }

    pub open spec fn superblock_inflight(self) -> bool {
        self.commit_started() && !self.superblockstore.landed
    }

    pub open spec fn superblock_landed(self) -> bool {
        self.commit_started() && self.superblockstore.landed
    }

    pub open spec fn map_i(self) -> AbstractCrashAwareMap::State {
        let raw = self.branch.i_abstract();
        let sync_adjusted = if self.journal.frozen is Some
            && self.branch.frozen is None
        {
            AbstractCrashAwareMap::State {
                frozen: Some(raw.persistent),
                ..raw
            }
        } else {
            raw
        };
        if self.components_loaded() {
            sync_adjusted
        } else {
            AbstractCrashAwareMap::State {
                ephemeral:
                    crate::abstract_system::AbstractCrashAwareMap_v::
                        Ephemeral::Unknown,
                ..sync_adjusted
            }
        }
    }

    pub open spec fn journal_i(
        self,
    ) -> AbstractCrashAwareJournal::State {
        let raw = self.journal.i_abstract();
        if self.components_loaded() {
            raw
        } else {
            AbstractCrashAwareJournal::State {
                ephemeral:
                    crate::abstract_system::AbstractCrashAwareJournal_v::
                        Ephemeral::Unknown,
                ..raw
            }
        }
    }

    pub open spec fn components_loaded(self) -> bool {
        &&& self.journal.ephemeral is Known
        &&& !(self.branch.ephemeral is Unknown)
    }

    pub open spec fn coordination_i(
        self,
    ) -> CoordinationSystem::State {
        CoordinationSystem::State {
            journal: self.journal_i(),
            mapadt: self.map_i(),
            progress: self.progress,
            sync_reqs: self.sync_reqs,
            superblock_in_flight: self.superblock_inflight(),
            superblock_landed: self.superblock_landed(),
        }
    }
}}

} // verus!
