// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Coordination refinement for the crash-aware caching-disk Betree system.

#![allow(unused_imports)]
#![allow(unused_variables)]

use vstd::prelude::*;

use crate::abstract_system::AbstractCrashAwareJournal_v::{
    AbstractCrashAwareJournal, Ephemeral as AbstractJournalEphemeral,
};
use crate::abstract_system::AbstractCrashAwareMap_v::{
    AbstractCrashAwareMap, Ephemeral as AbstractMapEphemeral,
};
use crate::abstract_system::AbstractCrashAwareSystem_v::
    CoordinationSystem;
use crate::abstract_system::AbstractCrashAwareSystemRefinement_v::*;
use crate::abstract_system::AbstractJournal_v::AbstractJournal;
use crate::abstract_system::AbstractMap_v::AbstractMap;
use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::implementation::CachingDiskBranchBetree_v::{
    CachingDiskBranchBetree, PageAccess,
};
use crate::implementation::CrashAwareCachingDiskBetreeSystem_v::
    CrashAwareCachingDiskBetreeSystem;
use crate::implementation::SuperblockStore_v::
    SuperblockStore;
use crate::implementation::CrashAwareCachingDiskBranchBetree_v::{
    BetreeMetadataRecoveryLabel, CrashAwareCachingDiskBranchBetree,
    EphemeralCachingDiskBranchBetree,
};
use crate::implementation::
    CrashAwareCachingDiskBranchBetreeRefinement_v::*;
use crate::implementation::CrashAwareCachingDiskJournal_v::
    CrashAwareCachingDiskJournal;
use crate::implementation::CrashAwareCachingDiskJournalRefinement_v::*;
use crate::implementation::CachingDiskJournal_v::CachingDiskJournal;
use crate::implementation::CachedJournal_v::CachedJournal;
use crate::implementation::AbstractSuperblock_v::AbstractSuperblockImage;
use crate::disk::GenericDisk_v::AU;
use crate::spec::AsyncDisk_t::RawPage;
use crate::spec::MapSpec_t::{
    AsyncMap, CrashTolerantAsyncMap,
};

verus! {

pub open spec fn caching_disk_betree_system_i(
    model: CrashAwareCachingDiskBetreeSystem::State,
) -> CoordinationSystem::State {
    model.coordination_i()
}

pub open spec fn caching_disk_betree_system_ctam_i(
    model: CrashAwareCachingDiskBetreeSystem::State,
) -> CrashTolerantAsyncMap::State {
    caching_disk_betree_system_i(model).i()
}

pub open spec fn caching_disk_betree_system_lbl_i(
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
) -> CrashTolerantAsyncMap::Label {
    match lbl {
        CrashAwareCachingDiskBetreeSystem::Label::Request{req} =>
            CrashTolerantAsyncMap::Label::OperateOp {
                base_op: AsyncMap::Label::RequestOp{req},
            },
        CrashAwareCachingDiskBetreeSystem::Label::Execute{
            req,
            reply,
        } =>
            CrashTolerantAsyncMap::Label::OperateOp {
                base_op: AsyncMap::Label::ExecuteOp{req, reply},
            },
        CrashAwareCachingDiskBetreeSystem::Label::Reply{reply} =>
            CrashTolerantAsyncMap::Label::OperateOp {
                base_op: AsyncMap::Label::ReplyOp{reply},
            },
        CrashAwareCachingDiskBetreeSystem::Label::ReqSync{
            sync_req_id,
        } =>
            CrashTolerantAsyncMap::Label::ReqSyncOp{sync_req_id},
        CrashAwareCachingDiskBetreeSystem::Label::ReplySync{
            sync_req_id,
        } =>
            CrashTolerantAsyncMap::Label::ReplySyncOp{sync_req_id},
        CrashAwareCachingDiskBetreeSystem::Label::Sync =>
            CrashTolerantAsyncMap::Label::SyncOp{},
        CrashAwareCachingDiskBetreeSystem::Label::Crash =>
            CrashTolerantAsyncMap::Label::CrashOp{},
        CrashAwareCachingDiskBetreeSystem::Label::Noop =>
            CrashTolerantAsyncMap::Label::Noop{},
    }
}

pub open spec fn partial_components_match_persistent(
    model: CrashAwareCachingDiskBetreeSystem::State,
) -> bool {
    !model.components_loaded() ==> {
        &&& model.journal.ephemeral is Known ==>
            model.journal.i_abstract().ephemeral->v.journal
                == model.journal.i_abstract().persistent
        &&& !(model.branch.ephemeral is Unknown) ==>
            model.branch.i_abstract().ephemeral->v.stamped_map
                == model.branch.i_abstract().persistent
        &&& model.journal.i_abstract().frozen is None
        &&& model.branch.i_abstract().frozen is None
    }
}

pub open spec fn refinement_inv(
    model: CrashAwareCachingDiskBetreeSystem::State,
) -> bool {
    &&& model.journal.refinement_inv()
    &&& model.branch.refinement_inv()
    &&& model.superblockstore.inv()
    &&& partial_components_match_persistent(model)
    &&& !model.sync_reqs.dom().is_empty()
        ==> model.components_loaded()
    &&& (model.superblockstore.in_flight is Some
        || model.superblockstore.landed)
        ==> model.commit_started()
    &&& model.branch.frozen is Some
        ==> model.journal.frozen is Some
    &&& model.branch.prepared is Some
        ==> model.journal.prepared
    &&& (model.superblockstore.in_flight is Some
        || model.superblockstore.landed)
        && model.branch.frozen is Some
        ==> model.branch.prepared is Some
}

pub open spec fn journal_non_commit_label(
    lbl: CrashAwareCachingDiskJournal::Label,
) -> bool {
    &&& !(lbl is CommitStart)
    &&& !(lbl is CommitPrepared)
    &&& !(lbl is CommitComplete)
    &&& !(lbl is Crash)
}

proof fn journal_non_commit_preserves_protocol(
    pre: CrashAwareCachingDiskJournal::State,
    post: CrashAwareCachingDiskJournal::State,
    lbl: CrashAwareCachingDiskJournal::Label,
)
    requires
        journal_non_commit_label(lbl),
        CrashAwareCachingDiskJournal::State::next(pre, post, lbl),
    ensures
        post.frozen == pre.frozen,
        post.prepared == pre.prepared,
{
    reveal(CrashAwareCachingDiskJournal::State::next);
    reveal(CrashAwareCachingDiskJournal::State::next_by);
    let step = choose |step: CrashAwareCachingDiskJournal::Step|
        CrashAwareCachingDiskJournal::State::next_by(
            pre,
            post,
            lbl,
            step,
        );
    match step {
        CrashAwareCachingDiskJournal::Step::load_ephemeral() => {
        }
        CrashAwareCachingDiskJournal::Step::read_for_recovery() => {
        }
        CrashAwareCachingDiskJournal::Step::query_end_lsn() => {
        }
        CrashAwareCachingDiskJournal::Step::put(new_ephemeral) => {
        }
        CrashAwareCachingDiskJournal::Step::
            query_lsn_persistence() => {
        }
        CrashAwareCachingDiskJournal::Step::load_index(
            new_ephemeral,
        ) => {
        }
        CrashAwareCachingDiskJournal::Step::observe_clean_aus(
            new_ephemeral,
        ) => {
        }
        CrashAwareCachingDiskJournal::Step::internal(
            new_ephemeral,
        ) => {
        }
        CrashAwareCachingDiskJournal::Step::internal_alloc(
            new_ephemeral,
        ) => {
        }
        CrashAwareCachingDiskJournal::Step::commit_start()
        | CrashAwareCachingDiskJournal::Step::commit_prepared()
        | CrashAwareCachingDiskJournal::Step::commit_complete(_)
        | CrashAwareCachingDiskJournal::Step::crash() => {
            assert(false);
        }
        CrashAwareCachingDiskJournal::Step::
            dummy_to_use_type_params(_) => {
            assert(false);
        }
    }
}

pub open spec fn branch_non_commit_label(
    lbl: CrashAwareCachingDiskBranchBetree::Label,
) -> bool {
    &&& !(lbl is CommitStart)
    &&& !(lbl is CommitPrepared)
    &&& !(lbl is CommitComplete)
    &&& !(lbl is Crash)
}

proof fn branch_non_commit_preserves_protocol(
    pre: CrashAwareCachingDiskBranchBetree::State,
    post: CrashAwareCachingDiskBranchBetree::State,
    lbl: CrashAwareCachingDiskBranchBetree::Label,
)
    requires
        branch_non_commit_label(lbl),
        CrashAwareCachingDiskBranchBetree::State::next(
            pre,
            post,
            lbl,
        ),
    ensures
        post.frozen == pre.frozen,
        post.prepared == pre.prepared,
{
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
    let step = choose |step:
        CrashAwareCachingDiskBranchBetree::Step|
        CrashAwareCachingDiskBranchBetree::State::next_by(
            pre,
            post,
            lbl,
            step,
        );
    match step {
        CrashAwareCachingDiskBranchBetree::Step::load_ephemeral(
            initial_disk,
        ) => {
        }
        CrashAwareCachingDiskBranchBetree::Step::recover_metadata(
            new_recovery,
        ) => {
        }
        CrashAwareCachingDiskBranchBetree::Step::load_metadata() => {
        }
        CrashAwareCachingDiskBranchBetree::Step::ephemeral_step(
            new_ephemeral,
        ) => {
        }
        CrashAwareCachingDiskBranchBetree::Step::commit_start()
        | CrashAwareCachingDiskBranchBetree::Step::
            commit_prepared(_)
        | CrashAwareCachingDiskBranchBetree::Step::
            commit_complete(_)
        | CrashAwareCachingDiskBranchBetree::Step::crash() => {
            assert(false);
        }
        CrashAwareCachingDiskBranchBetree::Step::
            dummy_to_use_type_params(_) => {
            assert(false);
        }
    }
}

proof fn abstract_journal_internal_stutters(
    pre: AbstractCrashAwareJournal::State,
    post: AbstractCrashAwareJournal::State,
)
    requires
        AbstractCrashAwareJournal::State::next(
            pre,
            post,
            AbstractCrashAwareJournal::Label::InternalLabel,
        ),
    ensures
        post == pre,
{
    reveal(AbstractCrashAwareJournal::State::next);
    reveal(AbstractCrashAwareJournal::State::next_by);
    let step = choose |step: AbstractCrashAwareJournal::Step|
        AbstractCrashAwareJournal::State::next_by(
            pre,
            post,
            AbstractCrashAwareJournal::Label::InternalLabel,
            step,
        );
    match step {
        AbstractCrashAwareJournal::Step::internal(new_journal) => {
            reveal(AbstractJournal::State::next);
            reveal(AbstractJournal::State::next_by);
            let journal_step = choose |journal_step: AbstractJournal::Step|
                AbstractJournal::State::next_by(
                    pre.ephemeral->v,
                    new_journal,
                    AbstractJournal::Label::InternalLabel,
                    journal_step,
                );
            match journal_step {
                AbstractJournal::Step::internal() => {
                }
                _ => {
                    assert(false);
                }
            }
        }
        _ => {
            assert(false);
        }
    }
}

proof fn abstract_map_internal_stutters(
    pre: AbstractCrashAwareMap::State,
    post: AbstractCrashAwareMap::State,
)
    requires
        AbstractCrashAwareMap::State::next(
            pre,
            post,
            AbstractCrashAwareMap::Label::InternalLabel,
        ),
    ensures
        post == pre,
{
    reveal(AbstractCrashAwareMap::State::next);
    reveal(AbstractCrashAwareMap::State::next_by);
    let step = choose |step: AbstractCrashAwareMap::Step|
        AbstractCrashAwareMap::State::next_by(
            pre,
            post,
            AbstractCrashAwareMap::Label::InternalLabel,
            step,
        );
    match step {
        AbstractCrashAwareMap::Step::freeze_map_internal(
            frozen_map,
            new_map,
        ) => {
        }
        AbstractCrashAwareMap::Step::ephemeral_internal(new_map) => {
            abstract_internal_stutters(pre.ephemeral->v, new_map);
        }
        _ => {
            assert(false);
        }
    }
}

proof fn abstract_journal_load_facts(
    pre: AbstractCrashAwareJournal::State,
    post: AbstractCrashAwareJournal::State,
)
    requires
        AbstractCrashAwareJournal::State::next(
            pre,
            post,
            AbstractCrashAwareJournal::Label::
                LoadEphemeralFromPersistentLabel,
        ),
    ensures
        post.persistent == pre.persistent,
        post.frozen == pre.frozen,
        post.ephemeral is Known,
        post.ephemeral->v.journal == pre.persistent,
{
    reveal(AbstractCrashAwareJournal::State::next);
    reveal(AbstractCrashAwareJournal::State::next_by);
    let step = choose |step: AbstractCrashAwareJournal::Step|
        AbstractCrashAwareJournal::State::next_by(
            pre,
            post,
            AbstractCrashAwareJournal::Label::
                LoadEphemeralFromPersistentLabel,
            step,
        );
    match step {
        AbstractCrashAwareJournal::Step::
            load_ephemeral_from_persistent(new_journal) => {
            reveal(AbstractJournal::State::init_by);
        }
        _ => {
            assert(false);
        }
    }
}

proof fn abstract_map_load_facts(
    pre: AbstractCrashAwareMap::State,
    post: AbstractCrashAwareMap::State,
    end_lsn: crate::abstract_system::StampedMap_v::LSN,
)
    requires
        AbstractCrashAwareMap::State::next(
            pre,
            post,
            AbstractCrashAwareMap::Label::
                LoadEphemeralFromPersistentLabel{end_lsn},
        ),
    ensures
        post.persistent == pre.persistent,
        post.frozen == pre.frozen,
        post.ephemeral is Known,
        post.ephemeral->v.stamped_map == pre.persistent,
{
    reveal(AbstractCrashAwareMap::State::next);
    reveal(AbstractCrashAwareMap::State::next_by);
    let step = choose |step: AbstractCrashAwareMap::Step|
        AbstractCrashAwareMap::State::next_by(
            pre,
            post,
            AbstractCrashAwareMap::Label::
                LoadEphemeralFromPersistentLabel{end_lsn},
            step,
        );
    match step {
        AbstractCrashAwareMap::Step::
            load_ephemeral_from_persistent() => {
        }
        _ => {
            assert(false);
        }
    }
}

proof fn abstract_crashaware_query_stutters(
    pre: AbstractCrashAwareMap::State,
    post: AbstractCrashAwareMap::State,
    lbl: AbstractCrashAwareMap::Label,
)
    requires
        lbl is QueryLabel,
        AbstractCrashAwareMap::State::next(pre, post, lbl),
    ensures
        post == pre,
{
    reveal(AbstractCrashAwareMap::State::next);
    reveal(AbstractCrashAwareMap::State::next_by);
    let step = choose |step: AbstractCrashAwareMap::Step|
        AbstractCrashAwareMap::State::next_by(
            pre,
            post,
            lbl,
            step,
        );
    match step {
        AbstractCrashAwareMap::Step::query(new_map) => {
            abstract_query_stutters(
                pre.ephemeral->v,
                new_map,
                AbstractMap::Label::QueryLabel {
                    end_lsn: lbl.arrow_QueryLabel_end_lsn(),
                    key: lbl.arrow_QueryLabel_key(),
                    value: lbl.arrow_QueryLabel_value(),
                },
            );
        }
        _ => {
            assert(false);
        }
    }
}

proof fn abstract_crashaware_query_exposes_map_step(
    pre: AbstractCrashAwareMap::State,
    post: AbstractCrashAwareMap::State,
    lbl: AbstractCrashAwareMap::Label,
)
    requires
        lbl is QueryLabel,
        AbstractCrashAwareMap::State::next(pre, post, lbl),
    ensures
        AbstractMap::State::next(
            pre.ephemeral->v,
            post.ephemeral->v,
            AbstractMap::Label::QueryLabel {
                end_lsn: lbl.arrow_QueryLabel_end_lsn(),
                key: lbl.arrow_QueryLabel_key(),
                value: lbl.arrow_QueryLabel_value(),
            },
        ),
{
    reveal(AbstractCrashAwareMap::State::next);
    reveal(AbstractCrashAwareMap::State::next_by);
    let step = choose |step: AbstractCrashAwareMap::Step|
        AbstractCrashAwareMap::State::next_by(
            pre,
            post,
            lbl,
            step,
        );
    match step {
        AbstractCrashAwareMap::Step::query(new_map) => {
            abstract_query_stutters(
                pre.ephemeral->v,
                new_map,
                AbstractMap::Label::QueryLabel {
                    end_lsn:
                        lbl.arrow_QueryLabel_end_lsn(),
                    key: lbl.arrow_QueryLabel_key(),
                    value: lbl.arrow_QueryLabel_value(),
                },
            );
        }
        _ => {
            assert(false);
        }
    }
}

proof fn abstract_crashaware_put_exposes_map_step(
    pre: AbstractCrashAwareMap::State,
    post: AbstractCrashAwareMap::State,
    records: MsgHistory,
)
    requires
        AbstractCrashAwareMap::State::next(
            pre,
            post,
            AbstractCrashAwareMap::Label::PutRecordsLabel{
                records,
            },
        ),
    ensures
        AbstractMap::State::next(
            pre.ephemeral->v,
            post.ephemeral->v,
            AbstractMap::Label::PutLabel{puts: records},
        ),
{
    reveal(AbstractCrashAwareMap::State::next);
    reveal(AbstractCrashAwareMap::State::next_by);
    let step = choose |step: AbstractCrashAwareMap::Step|
        AbstractCrashAwareMap::State::next_by(
            pre,
            post,
            AbstractCrashAwareMap::Label::PutRecordsLabel{
                records,
            },
            step,
        );
    match step {
        AbstractCrashAwareMap::Step::put_records(new_map) => {
        }
        _ => {
            assert(false);
        }
    }
}

proof fn coordination_noop(
    pre: CoordinationSystem::State,
    post: CoordinationSystem::State,
    lbl: CoordinationSystem::Label,
)
    requires
        pre == post,
        lbl->ctam_label is Noop,
    ensures
        CoordinationSystem::State::next(pre, post, lbl),
{
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    assert(CoordinationSystem::State::next_by(
        pre,
        post,
        lbl,
        CoordinationSystem::Step::noop(),
    ));
}

proof fn journal_internal_step_stutters(
    pre: CrashAwareCachingDiskJournal::State,
    post: CrashAwareCachingDiskJournal::State,
    lbl: CrashAwareCachingDiskJournal::Label,
)
    requires
        pre.refinement_inv(),
        CrashAwareCachingDiskJournal::State::next(pre, post, lbl),
        pre.label_i_abstract(post, lbl) is InternalLabel,
    ensures
        post.refinement_inv(),
        post.i_abstract() == pre.i_abstract(),
        journal_non_commit_label(lbl) ==>
            post.frozen == pre.frozen
                && post.prepared == pre.prepared,
{
    pre.next_refines_abstract(post, lbl);
    if journal_non_commit_label(lbl) {
        journal_non_commit_preserves_protocol(pre, post, lbl);
    }
    abstract_journal_internal_stutters(
        pre.i_abstract(),
        post.i_abstract(),
    );
}

proof fn branch_internal_step_stutters(
    pre: CrashAwareCachingDiskBranchBetree::State,
    post: CrashAwareCachingDiskBranchBetree::State,
    lbl: CrashAwareCachingDiskBranchBetree::Label,
)
    requires
        pre.refinement_inv(),
        CrashAwareCachingDiskBranchBetree::State::next(
            pre,
            post,
            lbl,
        ),
        pre.label_i_abstract(post, lbl) is InternalLabel,
    ensures
        post.refinement_inv(),
        post.i_abstract() == pre.i_abstract(),
        branch_non_commit_label(lbl) ==>
            post.frozen == pre.frozen
                && post.prepared == pre.prepared,
{
    pre.next_refines(post, lbl);
    if branch_non_commit_label(lbl) {
        branch_non_commit_preserves_protocol(pre, post, lbl);
    }
    abstract_map_internal_stutters(
        pre.i_abstract(),
        post.i_abstract(),
    );
}

proof fn journal_load_ephemeral_facts(
    pre: CrashAwareCachingDiskJournal::State,
    post: CrashAwareCachingDiskJournal::State,
)
    requires
        CrashAwareCachingDiskJournal::State::next(
            pre,
            post,
            CrashAwareCachingDiskJournal::Label::LoadEphemeral,
        ),
    ensures
        pre.ephemeral is Unknown,
        post.ephemeral is Known,
        post.frozen == pre.frozen,
        post.prepared == pre.prepared,
{
    reveal(CrashAwareCachingDiskJournal::State::next);
    reveal(CrashAwareCachingDiskJournal::State::next_by);
    let step = choose |step: CrashAwareCachingDiskJournal::Step|
        CrashAwareCachingDiskJournal::State::next_by(
            pre,
            post,
            CrashAwareCachingDiskJournal::Label::LoadEphemeral,
            step,
        );
    match step {
        CrashAwareCachingDiskJournal::Step::load_ephemeral() => {
        }
        _ => {
            assert(false);
        }
    }
}

proof fn branch_load_ephemeral_facts(
    pre: CrashAwareCachingDiskBranchBetree::State,
    post: CrashAwareCachingDiskBranchBetree::State,
)
    requires
        CrashAwareCachingDiskBranchBetree::State::next(
            pre,
            post,
            CrashAwareCachingDiskBranchBetree::Label::LoadEphemeral,
        ),
    ensures
        pre.ephemeral is Unknown,
        post.ephemeral is Loading,
        post.persistent == pre.persistent,
        post.frozen == pre.frozen,
        post.prepared == pre.prepared,
{
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
    let step = choose |step: CrashAwareCachingDiskBranchBetree::Step|
        CrashAwareCachingDiskBranchBetree::State::next_by(
            pre,
            post,
            CrashAwareCachingDiskBranchBetree::Label::LoadEphemeral,
            step,
        );
    match step {
        CrashAwareCachingDiskBranchBetree::Step::load_ephemeral(
            initial_disk,
        ) => {
        }
        _ => {
            assert(false);
        }
    }
}

proof fn branch_ephemeral_step_facts(
    pre: CrashAwareCachingDiskBranchBetree::State,
    post: CrashAwareCachingDiskBranchBetree::State,
    lbl: CrashAwareCachingDiskBranchBetree::Label,
)
    requires
        lbl is Ephemeral,
        CrashAwareCachingDiskBranchBetree::State::next(
            pre,
            post,
            lbl,
        ),
    ensures
        pre.ephemeral is Known,
        post.ephemeral is Known,
        post.persistent == pre.persistent,
        post.frozen == pre.frozen,
        post.prepared == pre.prepared,
{
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
    let step = choose |step: CrashAwareCachingDiskBranchBetree::Step|
        CrashAwareCachingDiskBranchBetree::State::next_by(
            pre,
            post,
            lbl,
            step,
        );
    match step {
        CrashAwareCachingDiskBranchBetree::Step::ephemeral_step(
            new_ephemeral,
        ) => {
        }
        _ => {
            assert(false);
        }
    }
}

proof fn journal_query_end_self(
    journal: CrashAwareCachingDiskJournal::State,
    end_lsn: crate::abstract_system::StampedMap_v::LSN,
)
    requires
        journal.refinement_inv(),
        journal.ephemeral is Known,
        journal.ephemeral->v.journal.status is Some,
        journal.ephemeral->v.journal.seq_end() == end_lsn,
    ensures
        CrashAwareCachingDiskJournal::State::next(
            journal,
            journal,
            CrashAwareCachingDiskJournal::Label::QueryEndLsn{
                end_lsn,
            },
        ),
        AbstractCrashAwareJournal::State::next(
            journal.i_abstract(),
            journal.i_abstract(),
            AbstractCrashAwareJournal::Label::QueryEndLsnLabel{
                end_lsn,
            },
        ),
{
    let cached = journal.ephemeral->v.journal;
    assert(CachedJournal::State::next(
        cached,
        cached,
        CachedJournal::Label::QueryEndLsn{end_lsn},
    )) by {
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        assert(CachedJournal::State::next_by(
            cached,
            cached,
            CachedJournal::Label::QueryEndLsn{end_lsn},
            CachedJournal::Step::query_end_lsn(),
        ));
    }
    assert(CachingDiskJournal::State::next(
        journal.ephemeral->v,
        journal.ephemeral->v,
        CachingDiskJournal::Label::QueryEndLsn{end_lsn},
    )) by {
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        assert(CachingDiskJournal::State::next_by(
            journal.ephemeral->v,
            journal.ephemeral->v,
            CachingDiskJournal::Label::QueryEndLsn{end_lsn},
            CachingDiskJournal::Step::query_end_lsn(),
        ));
    }
    assert(CrashAwareCachingDiskJournal::State::next(
        journal,
        journal,
        CrashAwareCachingDiskJournal::Label::QueryEndLsn{
            end_lsn,
        },
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next);
        reveal(CrashAwareCachingDiskJournal::State::next_by);
        assert(CrashAwareCachingDiskJournal::State::next_by(
            journal,
            journal,
            CrashAwareCachingDiskJournal::Label::QueryEndLsn{
                end_lsn,
            },
            CrashAwareCachingDiskJournal::Step::query_end_lsn(),
        ));
    }
    journal.next_refines_abstract(
        journal,
        CrashAwareCachingDiskJournal::Label::QueryEndLsn{
            end_lsn,
        },
    );
}

proof fn journal_put_step_facts(
    pre: CrashAwareCachingDiskJournal::State,
    post: CrashAwareCachingDiskJournal::State,
    records: MsgHistory,
)
    requires
        CrashAwareCachingDiskJournal::State::next(
            pre,
            post,
            CrashAwareCachingDiskJournal::Label::Put{records},
        ),
    ensures
        pre.ephemeral is Known,
        post.ephemeral is Known,
        post.persistent == pre.persistent,
        post.frozen == pre.frozen,
        post.prepared == pre.prepared,
{
    reveal(CrashAwareCachingDiskJournal::State::next);
    reveal(CrashAwareCachingDiskJournal::State::next_by);
    let step = choose |step: CrashAwareCachingDiskJournal::Step|
        CrashAwareCachingDiskJournal::State::next_by(
            pre,
            post,
            CrashAwareCachingDiskJournal::Label::Put{records},
            step,
        );
    match step {
        CrashAwareCachingDiskJournal::Step::put(new_ephemeral) => {
        }
        _ => {
            assert(false);
        }
    }
}

proof fn journal_recovery_read_facts(
    pre: CrashAwareCachingDiskJournal::State,
    post: CrashAwareCachingDiskJournal::State,
    records: MsgHistory,
)
    requires
        CrashAwareCachingDiskJournal::State::next(
            pre,
            post,
            CrashAwareCachingDiskJournal::Label::
                ReadForRecovery{records},
        ),
    ensures
        pre.ephemeral is Known,
        post == pre,
{
    reveal(CrashAwareCachingDiskJournal::State::next);
    reveal(CrashAwareCachingDiskJournal::State::next_by);
    let step = choose |step: CrashAwareCachingDiskJournal::Step|
        CrashAwareCachingDiskJournal::State::next_by(
            pre,
            post,
            CrashAwareCachingDiskJournal::Label::
                ReadForRecovery{records},
            step,
        );
    match step {
        CrashAwareCachingDiskJournal::Step::
            read_for_recovery() => {
        }
        _ => {
            assert(false);
        }
    }
}

proof fn journal_commit_prepared_facts(
    pre: CrashAwareCachingDiskJournal::State,
    post: CrashAwareCachingDiskJournal::State,
)
    requires
        CrashAwareCachingDiskJournal::State::next(
            pre,
            post,
            CrashAwareCachingDiskJournal::Label::CommitPrepared,
        ),
    ensures
        post.persistent == pre.persistent,
        post.ephemeral == pre.ephemeral,
        post.frozen == pre.frozen,
        post.prepared,
{
    reveal(CrashAwareCachingDiskJournal::State::next);
    reveal(CrashAwareCachingDiskJournal::State::next_by);
    let step = choose |step: CrashAwareCachingDiskJournal::Step|
        CrashAwareCachingDiskJournal::State::next_by(
            pre,
            post,
            CrashAwareCachingDiskJournal::Label::CommitPrepared,
            step,
        );
    match step {
        CrashAwareCachingDiskJournal::Step::commit_prepared() => {
        }
        _ => {
            assert(false);
        }
    }
}

proof fn journal_commit_start_facts(
    pre: CrashAwareCachingDiskJournal::State,
    post: CrashAwareCachingDiskJournal::State,
    lbl: CrashAwareCachingDiskJournal::Label,
)
    requires
        lbl is CommitStart,
        CrashAwareCachingDiskJournal::State::next(
            pre,
            post,
            lbl,
        ),
    ensures
        pre.frozen is None,
        post.frozen is Some,
        post.persistent == pre.persistent,
        post.ephemeral is Known,
        pre.label_i_abstract(post, lbl)
            == (AbstractCrashAwareJournal::Label::CommitStartLabel {
                new_boundary_lsn:
                    lbl.arrow_CommitStart_new_boundary_lsn(),
                frozen_journal:
                    post.i_abstract().frozen.unwrap(),
            }),
{
    reveal(CrashAwareCachingDiskJournal::State::next);
    reveal(CrashAwareCachingDiskJournal::State::next_by);
    let step = choose |step: CrashAwareCachingDiskJournal::Step|
        CrashAwareCachingDiskJournal::State::next_by(
            pre,
            post,
            lbl,
            step,
        );
    match step {
        CrashAwareCachingDiskJournal::Step::commit_start() => {
        }
        _ => {
            assert(false);
        }
    }
}

proof fn branch_commit_start_facts(
    pre: CrashAwareCachingDiskBranchBetree::State,
    post: CrashAwareCachingDiskBranchBetree::State,
    lbl: CrashAwareCachingDiskBranchBetree::Label,
)
    requires
        lbl is CommitStart,
        CrashAwareCachingDiskBranchBetree::State::next(
            pre,
            post,
            lbl,
        ),
    ensures
        pre.frozen is None,
        post.frozen is Some,
        post.persistent == pre.persistent,
        post.ephemeral == pre.ephemeral,
        pre.prepared is None,
        post.prepared is None,
{
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
    let step = choose |step: CrashAwareCachingDiskBranchBetree::Step|
        CrashAwareCachingDiskBranchBetree::State::next_by(
            pre,
            post,
            lbl,
            step,
        );
    match step {
        CrashAwareCachingDiskBranchBetree::Step::commit_start() => {
        }
        _ => {
            assert(false);
        }
    }
}

proof fn branch_commit_prepared_facts(
    pre: CrashAwareCachingDiskBranchBetree::State,
    post: CrashAwareCachingDiskBranchBetree::State,
)
    requires
        CrashAwareCachingDiskBranchBetree::State::next(
            pre,
            post,
            CrashAwareCachingDiskBranchBetree::Label::CommitPrepared,
        ),
    ensures
        post.persistent == pre.persistent,
        post.ephemeral == pre.ephemeral,
        post.frozen == pre.frozen,
        post.prepared is Some,
{
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
    let step = choose |step: CrashAwareCachingDiskBranchBetree::Step|
        CrashAwareCachingDiskBranchBetree::State::next_by(
            pre,
            post,
            CrashAwareCachingDiskBranchBetree::Label::CommitPrepared,
            step,
        );
    match step {
        CrashAwareCachingDiskBranchBetree::Step::commit_prepared(
            image,
        ) => {
        }
        _ => {
            assert(false);
        }
    }
}

proof fn journal_commit_complete_facts(
    pre: CrashAwareCachingDiskJournal::State,
    post: CrashAwareCachingDiskJournal::State,
    lbl: CrashAwareCachingDiskJournal::Label,
)
    requires
        lbl is CommitComplete,
        CrashAwareCachingDiskJournal::State::next(pre, post, lbl),
    ensures
        pre.frozen is Some,
        post.frozen is None,
        post.ephemeral is Known,
        !post.prepared,
{
    reveal(CrashAwareCachingDiskJournal::State::next);
    reveal(CrashAwareCachingDiskJournal::State::next_by);
    let step = choose |step: CrashAwareCachingDiskJournal::Step|
        CrashAwareCachingDiskJournal::State::next_by(
            pre,
            post,
            lbl,
            step,
        );
    match step {
        CrashAwareCachingDiskJournal::Step::commit_complete(
            new_ephemeral,
        ) => {
        }
        _ => {
            assert(false);
        }
    }
}

proof fn branch_commit_complete_facts(
    pre: CrashAwareCachingDiskBranchBetree::State,
    post: CrashAwareCachingDiskBranchBetree::State,
    lbl: CrashAwareCachingDiskBranchBetree::Label,
)
    requires
        lbl is CommitComplete,
        CrashAwareCachingDiskBranchBetree::State::next(
            pre,
            post,
            lbl,
        ),
    ensures
        pre.frozen is Some,
        post.frozen is None,
        post.ephemeral is Known,
        post.prepared is None,
{
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
    let step = choose |step:
        CrashAwareCachingDiskBranchBetree::Step|
        CrashAwareCachingDiskBranchBetree::State::next_by(
            pre,
            post,
            lbl,
            step,
        );
    match step {
        CrashAwareCachingDiskBranchBetree::Step::commit_complete(
            discarded,
        ) => {
        }
        _ => {
            assert(false);
        }
    }
}

proof fn superblock_write_facts(
    pre: SuperblockStore::State,
    post: SuperblockStore::State,
    raw: crate::spec::AsyncDisk_t::RawPage,
)
    requires
        pre.inv(),
        SuperblockStore::State::next(
            pre,
            post,
            SuperblockStore::Label::Write{raw},
        ),
    ensures
        !pre.landed,
        post.landed == pre.landed,
{
    reveal(SuperblockStore::State::next);
    reveal(SuperblockStore::State::next_by);
    let step = choose |step: SuperblockStore::Step|
        SuperblockStore::State::next_by(
            pre,
            post,
            SuperblockStore::Label::Write{raw},
            step,
        );
    match step {
        SuperblockStore::Step::write() => {
        }
        _ => {
            assert(false);
        }
    }
}

proof fn superblock_land_facts(
    pre: SuperblockStore::State,
    post: SuperblockStore::State,
)
    requires
        pre.inv(),
        SuperblockStore::State::next(
            pre,
            post,
            SuperblockStore::Label::Land,
        ),
    ensures
        !pre.landed,
        post.landed,
{
    reveal(SuperblockStore::State::next);
    reveal(SuperblockStore::State::next_by);
    let step = choose |step: SuperblockStore::Step|
        SuperblockStore::State::next_by(
            pre,
            post,
            SuperblockStore::Label::Land,
            step,
        );
    match step {
        SuperblockStore::Step::land() => {
        }
        _ => {
            assert(false);
        }
    }
}

proof fn superblock_crash_facts(
    pre: SuperblockStore::State,
    post: SuperblockStore::State,
)
    requires
        SuperblockStore::State::next(
            pre,
            post,
            SuperblockStore::Label::Crash,
        ),
    ensures
        !post.landed,
{
    reveal(SuperblockStore::State::next);
    reveal(SuperblockStore::State::next_by);
    let step = choose |step: SuperblockStore::Step|
        SuperblockStore::State::next_by(
            pre,
            post,
            SuperblockStore::Label::Crash,
            step,
        );
    match step {
        SuperblockStore::Step::crash() => {
        }
        _ => {
            assert(false);
        }
    }
}

proof fn journal_crash_facts(
    pre: CrashAwareCachingDiskJournal::State,
    post: CrashAwareCachingDiskJournal::State,
    keep_in_flight: bool,
)
    requires
        CrashAwareCachingDiskJournal::State::next(
            pre,
            post,
            CrashAwareCachingDiskJournal::Label::Crash{
                keep_in_flight,
            },
        ),
    ensures
        post.ephemeral is Unknown,
        post.frozen is None,
        !post.prepared,
{
    reveal(CrashAwareCachingDiskJournal::State::next);
    reveal(CrashAwareCachingDiskJournal::State::next_by);
    let step = choose |step: CrashAwareCachingDiskJournal::Step|
        CrashAwareCachingDiskJournal::State::next_by(
            pre,
            post,
            CrashAwareCachingDiskJournal::Label::Crash{
                keep_in_flight,
            },
            step,
        );
    match step {
        CrashAwareCachingDiskJournal::Step::crash() => {
        }
        _ => {
            assert(false);
        }
    }
}

proof fn branch_crash_facts(
    pre: CrashAwareCachingDiskBranchBetree::State,
    post: CrashAwareCachingDiskBranchBetree::State,
    keep_in_flight: bool,
)
    requires
        CrashAwareCachingDiskBranchBetree::State::next(
            pre,
            post,
            CrashAwareCachingDiskBranchBetree::Label::Crash{
                keep_in_flight,
            },
        ),
    ensures
        post.ephemeral is Unknown,
        post.frozen is None,
        post.prepared is None,
        keep_in_flight ==> pre.prepared is Some,
        post.persistent == if keep_in_flight {
            pre.prepared.unwrap()
        } else {
            pre.persistent
        },
{
    reveal(CrashAwareCachingDiskBranchBetree::State::next);
    reveal(CrashAwareCachingDiskBranchBetree::State::next_by);
    let step = choose |step: CrashAwareCachingDiskBranchBetree::Step|
        CrashAwareCachingDiskBranchBetree::State::next_by(
            pre,
            post,
            CrashAwareCachingDiskBranchBetree::Label::Crash{
                keep_in_flight,
            },
            step,
        );
    match step {
        CrashAwareCachingDiskBranchBetree::Step::crash() => {
        }
        _ => {
            assert(false);
        }
    }
}

proof fn branch_lsn_matches_map_i(
    model: CrashAwareCachingDiskBetreeSystem::State,
)
    requires
        model.branch.refinement_inv(),
        model.components_loaded(),
    ensures
        model.coordination_i().mapadt.i().seq_end
            == model.branch_lsn(),
{
    if model.branch.ephemeral is Known {
        assert(model.branch.ephemeral->v.refinement_inv());
        model.branch.ephemeral->v.i_abstract_seq_end();
    } else {
        assert(model.branch.persistent.valid());
        model.branch.persistent.i_abstract_seq_end();
    }
}

proof fn accept_request_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
)
    requires
        CrashAwareCachingDiskBetreeSystem::State::accept_request(
            pre,
            post,
            lbl,
        ),
    ensures
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    assert(CoordinationSystem::State::next_by(
        pre.coordination_i(),
        post.coordination_i(),
        CoordinationSystem::Label::Label {
            ctam_label: caching_disk_betree_system_lbl_i(lbl),
        },
        CoordinationSystem::Step::accept_request(),
    ));
}

proof fn deliver_reply_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
)
    requires
        CrashAwareCachingDiskBetreeSystem::State::deliver_reply(
            pre,
            post,
            lbl,
        ),
    ensures
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    assert(CoordinationSystem::State::next_by(
        pre.coordination_i(),
        post.coordination_i(),
        CoordinationSystem::Label::Label {
            ctam_label: caching_disk_betree_system_lbl_i(lbl),
        },
        CoordinationSystem::Step::deliver_reply(),
    ));
}

proof fn execute_noop_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
)
    requires
        CrashAwareCachingDiskBetreeSystem::State::execute_noop(
            pre,
            post,
            lbl,
        ),
    ensures
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    assert(CoordinationSystem::State::next_by(
        pre.coordination_i(),
        post.coordination_i(),
        CoordinationSystem::Label::Label {
            ctam_label: caching_disk_betree_system_lbl_i(lbl),
        },
        CoordinationSystem::Step::execute_noop(),
    ));
}

proof fn noop_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
)
    requires
        CrashAwareCachingDiskBetreeSystem::State::noop(
            pre,
            post,
            lbl,
        ),
    ensures
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    coordination_noop(
        pre.coordination_i(),
        post.coordination_i(),
        CoordinationSystem::Label::Label {
            ctam_label: caching_disk_betree_system_lbl_i(lbl),
        },
    );
}

#[verifier::spinoff_prover]
proof fn journal_commit_complete_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    new_superblock: SuperblockStore::State,
    journal_discarded: Set<AU>,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::journal_commit_complete(
            pre,
            post,
            lbl,
            new_journal,
            new_superblock,
            journal_discarded,
        ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    let journal_lbl =
        CrashAwareCachingDiskJournal::Label::CommitComplete {
            require_end: pre.branch_lsn(),
            discarded: journal_discarded,
    };
    pre.journal.next_refines_abstract(new_journal, journal_lbl);
    journal_commit_complete_facts(
        pre.journal,
        new_journal,
        journal_lbl,
    );
    SuperblockStore::State::inv_next(
        pre.superblockstore,
        new_superblock,
        SuperblockStore::Label::Complete,
    );
    reveal(SuperblockStore::State::next);
    reveal(SuperblockStore::State::next_by);
    let cpre = pre.coordination_i();
    let cpost = post.coordination_i();
    let clbl = CoordinationSystem::Label::Label {
        ctam_label: caching_disk_betree_system_lbl_i(lbl),
    };
    branch_lsn_matches_map_i(pre);
    assert(cpre.mapadt.frozen == Some(cpre.mapadt.persistent));
    assert(cpost.mapadt.persistent == cpre.mapadt.persistent);
    assert(cpost.mapadt.frozen is None);
    assert(AbstractCrashAwareMap::State::next(
        cpre.mapadt,
        cpost.mapadt,
        AbstractCrashAwareMap::Label::CommitCompleteLabel,
    )) by {
        reveal(AbstractCrashAwareMap::State::next);
        reveal(AbstractCrashAwareMap::State::next_by);
        assert(AbstractCrashAwareMap::State::next_by(
            cpre.mapadt,
            cpost.mapadt,
            AbstractCrashAwareMap::Label::CommitCompleteLabel,
            AbstractCrashAwareMap::Step::commit_complete(),
        ));
    }
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::commit_complete(
            cpost.mapadt,
            cpost.journal,
        ),
    ));
}

#[verifier::spinoff_prover]
proof fn store_commit_complete_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    new_branch: CrashAwareCachingDiskBranchBetree::State,
    new_superblock: SuperblockStore::State,
    journal_discarded: Set<AU>,
    branch_discarded: Set<AU>,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::store_commit_complete(
            pre,
            post,
            lbl,
            new_journal,
            new_branch,
            new_superblock,
            journal_discarded,
            branch_discarded,
        ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    let journal_lbl =
        CrashAwareCachingDiskJournal::Label::CommitComplete {
            require_end: pre.branch_lsn(),
            discarded: journal_discarded,
        };
    let branch_lbl =
        CrashAwareCachingDiskBranchBetree::Label::CommitComplete {
            deallocs: branch_discarded,
    };
    pre.journal.next_refines_abstract(new_journal, journal_lbl);
    pre.branch.next_refines(new_branch, branch_lbl);
    journal_commit_complete_facts(
        pre.journal,
        new_journal,
        journal_lbl,
    );
    branch_commit_complete_facts(
        pre.branch,
        new_branch,
        branch_lbl,
    );
    SuperblockStore::State::inv_next(
        pre.superblockstore,
        new_superblock,
        SuperblockStore::Label::Complete,
    );
    reveal(SuperblockStore::State::next);
    reveal(SuperblockStore::State::next_by);
    let cpre = pre.coordination_i();
    let cpost = post.coordination_i();
    let clbl = CoordinationSystem::Label::Label {
        ctam_label: caching_disk_betree_system_lbl_i(lbl),
    };
    assert(cpre.journal == pre.journal.i_abstract());
    assert(cpost.journal == new_journal.i_abstract());
    assert(cpre.mapadt == pre.branch.i_abstract());
    assert(cpost.mapadt == new_branch.i_abstract());
    branch_lsn_matches_map_i(pre);
    assert(pre.journal.label_i_abstract(
        new_journal,
        journal_lbl,
    ) == AbstractCrashAwareJournal::Label::CommitCompleteLabel {
        require_end: cpre.mapadt.i().seq_end,
    });
    assert(pre.branch.label_i_abstract(
        new_branch,
        branch_lbl,
    ) == AbstractCrashAwareMap::Label::CommitCompleteLabel);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::commit_complete(
            cpost.mapadt,
            cpost.journal,
        ),
    ));
}

#[verifier::spinoff_prover]
proof fn journal_commit_start_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    superblock_image: AbstractSuperblockImage,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::journal_commit_start(
            pre,
            post,
            lbl,
            new_journal,
            superblock_image,
        ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    let journal_lbl =
        CrashAwareCachingDiskJournal::Label::CommitStart {
            new_boundary_lsn:
                superblock_image.journal_snapshot.boundary_lsn,
            snapshot: superblock_image.journal_snapshot,
            seq_end: superblock_image.journal_seq_end,
        };
    pre.journal.next_refines_abstract(new_journal, journal_lbl);
    journal_commit_start_facts(
        pre.journal,
        new_journal,
        journal_lbl,
    );
    pre.branch.persistent.i_abstract_seq_end();
    let cpre = pre.coordination_i();
    let cpost = post.coordination_i();
    let clbl = CoordinationSystem::Label::Label {
        ctam_label: caching_disk_betree_system_lbl_i(lbl),
    };
    let map_lbl =
        AbstractCrashAwareMap::Label::CommitStartLabel {
            new_boundary_lsn:
                superblock_image.journal_snapshot.boundary_lsn,
            frozen_map: cpre.mapadt.persistent,
        };
    assert(pre.branch.frozen is None);
    assert(post.branch.frozen is None);
    assert(post.journal.frozen is Some);
    assert(cpost.journal == new_journal.i_abstract());
    assert(pre.journal.label_i_abstract(
        new_journal,
        journal_lbl,
    ) == (AbstractCrashAwareJournal::Label::CommitStartLabel {
        new_boundary_lsn:
            superblock_image.journal_snapshot.boundary_lsn,
        frozen_journal: cpost.journal.frozen.unwrap(),
    }));
    assert(cpre.mapadt.persistent
        == pre.branch.i_abstract().persistent);
    assert(cpost.mapadt.frozen
        == Some(pre.branch.i_abstract().persistent));
    assert(cpost.mapadt.frozen
        == Some(cpre.mapadt.persistent));
    assert(AbstractCrashAwareMap::State::next(
        cpre.mapadt,
        cpost.mapadt,
        map_lbl,
    )) by {
        reveal(AbstractCrashAwareMap::State::next);
        reveal(AbstractCrashAwareMap::State::next_by);
        assert(AbstractCrashAwareMap::State::next_by(
            cpre.mapadt,
            cpost.mapadt,
            map_lbl,
            AbstractCrashAwareMap::Step::
                commit_start_persistent(),
        ));
    }
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::commit_start(
            superblock_image.journal_snapshot.boundary_lsn,
            cpost.journal.frozen.unwrap(),
            cpost.mapadt.frozen.unwrap(),
            cpost.journal,
            cpost.mapadt,
        ),
    ));
}

#[verifier::spinoff_prover]
proof fn store_commit_start_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    new_branch: CrashAwareCachingDiskBranchBetree::State,
    superblock_image: AbstractSuperblockImage,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::store_commit_start(
            pre,
            post,
            lbl,
            new_journal,
            new_branch,
            superblock_image,
        ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    let metadata =
        crate::implementation::UnifiedCacheBetreeSystem_v::
            betree_metadata_from_superblock(superblock_image);
    let journal_lbl =
        CrashAwareCachingDiskJournal::Label::CommitStart {
            new_boundary_lsn:
                superblock_image.journal_snapshot.boundary_lsn,
            snapshot: superblock_image.journal_snapshot,
            seq_end: superblock_image.journal_seq_end,
        };
    let branch_lbl =
        CrashAwareCachingDiskBranchBetree::Label::CommitStart {
            image:
                crate::implementation::CachedBranchBetree_v::
                    FrozenBranchBetree {
                        root: metadata.root,
                        seq_end: metadata.seq_end,
                    },
        };
    pre.journal.next_refines_abstract(new_journal, journal_lbl);
    pre.branch.next_refines(new_branch, branch_lbl);
    journal_commit_start_facts(
        pre.journal,
        new_journal,
        journal_lbl,
    );
    branch_commit_start_facts(
        pre.branch,
        new_branch,
        branch_lbl,
    );
    let cpre = pre.coordination_i();
    let cpost = post.coordination_i();
    let clbl = CoordinationSystem::Label::Label {
        ctam_label: caching_disk_betree_system_lbl_i(lbl),
    };
    assert(cpost.journal == new_journal.i_abstract());
    assert(cpost.mapadt == new_branch.i_abstract());
    assert(pre.journal.label_i_abstract(
        new_journal,
        journal_lbl,
    ) == (AbstractCrashAwareJournal::Label::CommitStartLabel {
        new_boundary_lsn:
            superblock_image.journal_snapshot.boundary_lsn,
        frozen_journal: cpost.journal.frozen.unwrap(),
    }));
    assert(pre.branch.label_i_abstract(
        new_branch,
        branch_lbl,
    ) == (AbstractCrashAwareMap::Label::CommitStartLabel {
        new_boundary_lsn:
            superblock_image.journal_snapshot.boundary_lsn,
        frozen_map: cpost.mapadt.frozen.unwrap(),
    }));
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::commit_start(
            superblock_image.journal_snapshot.boundary_lsn,
            cpost.journal.frozen.unwrap(),
            cpost.mapadt.frozen.unwrap(),
            cpost.journal,
            cpost.mapadt,
        ),
    ));
}

#[verifier::spinoff_prover]
proof fn crash_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    new_branch: CrashAwareCachingDiskBranchBetree::State,
    new_superblock: SuperblockStore::State,
    new_free_aus: Set<AU>,
    keep_in_flight: bool,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::crash(
            pre,
            post,
            lbl,
            new_journal,
            new_branch,
            new_superblock,
            new_free_aus,
            keep_in_flight,
        ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    let journal_lbl =
        CrashAwareCachingDiskJournal::Label::Crash {
            keep_in_flight,
        };
    let branch_keep_in_flight =
        keep_in_flight && pre.branch.prepared is Some;
    let branch_lbl =
        CrashAwareCachingDiskBranchBetree::Label::Crash {
            keep_in_flight: branch_keep_in_flight,
        };
    pre.journal.next_refines_abstract(new_journal, journal_lbl);
    pre.branch.next_refines(new_branch, branch_lbl);
    journal_crash_facts(
        pre.journal,
        new_journal,
        keep_in_flight,
    );
    branch_crash_facts(
        pre.branch,
        new_branch,
        branch_keep_in_flight,
    );
    let cpre = pre.coordination_i();
    let cpost = post.coordination_i();
    let clbl = CoordinationSystem::Label::Label {
        ctam_label: caching_disk_betree_system_lbl_i(lbl),
    };
    assert(pre.superblockstore.landed
        ==> pre.commit_started());
    assert(cpre.superblock_landed
        == pre.superblockstore.landed);
    assert(keep_in_flight == cpre.superblock_landed);
    assert(cpost.journal == new_journal.i_abstract());
    assert(cpost.mapadt == new_branch.i_abstract());
    if keep_in_flight {
        if pre.branch.frozen is Some {
            assert(pre.branch.prepared is Some);
            assert(branch_keep_in_flight);
            assert(cpre.mapadt == pre.branch.i_abstract());
        } else {
            assert(!branch_keep_in_flight);
            assert(cpre.mapadt.frozen
                == Some(cpre.mapadt.persistent));
            assert(cpost.mapadt.persistent
                == cpre.mapadt.persistent);
        }
    } else {
        assert(!branch_keep_in_flight);
        assert(cpost.mapadt.persistent
            == cpre.mapadt.persistent);
    }
    assert(AbstractCrashAwareJournal::State::next(
        cpre.journal,
        cpost.journal,
        AbstractCrashAwareJournal::Label::CrashLabel {
            keep_in_flight,
        },
    )) by {
        reveal(AbstractCrashAwareJournal::State::next);
        reveal(AbstractCrashAwareJournal::State::next_by);
        assert(AbstractCrashAwareJournal::State::next_by(
            cpre.journal,
            cpost.journal,
            AbstractCrashAwareJournal::Label::CrashLabel {
                keep_in_flight,
            },
            AbstractCrashAwareJournal::Step::crash(),
        ));
    }
    assert(AbstractCrashAwareMap::State::next(
        cpre.mapadt,
        cpost.mapadt,
        AbstractCrashAwareMap::Label::CrashLabel {
            keep_in_flight,
        },
    )) by {
        reveal(AbstractCrashAwareMap::State::next);
        reveal(AbstractCrashAwareMap::State::next_by);
        assert(AbstractCrashAwareMap::State::next_by(
            cpre.mapadt,
            cpost.mapadt,
            AbstractCrashAwareMap::Label::CrashLabel {
                keep_in_flight,
            },
            AbstractCrashAwareMap::Step::crash(),
        ));
    }
    reveal(SuperblockStore::State::next);
    reveal(SuperblockStore::State::next_by);
    superblock_crash_facts(
        pre.superblockstore,
        new_superblock,
    );
    SuperblockStore::State::inv_next(
        pre.superblockstore,
        new_superblock,
        SuperblockStore::Label::Crash,
    );
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::crash(
            new_journal.i_abstract(),
            new_branch.i_abstract(),
        ),
    ));
}

#[verifier::spinoff_prover]
proof fn query_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_branch: CrashAwareCachingDiskBranchBetree::State,
    access: PageAccess,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::query(
            pre,
            post,
            lbl,
            new_branch,
            access,
        ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    assert(lbl is Execute);
    let req = lbl.arrow_Execute_req();
    let reply = lbl.arrow_Execute_reply();
    let key = req.input.arrow_QueryInput_key();
    let value = reply.output.arrow_QueryOutput_value();
    let branch_lbl =
        CrashAwareCachingDiskBranchBetree::Label::Ephemeral {
            op: CachingDiskBranchBetree::Label::Query {
                end_lsn: pre.branch_lsn(),
                key,
                value,
                access,
            },
            deallocs: Set::empty(),
        };
    pre.branch.next_refines(new_branch, branch_lbl);
    abstract_crashaware_query_exposes_map_step(
        pre.branch.i_abstract(),
        new_branch.i_abstract(),
        pre.branch.label_i_abstract(
            new_branch,
            branch_lbl,
        ),
    );
    abstract_crashaware_query_stutters(
        pre.branch.i_abstract(),
        new_branch.i_abstract(),
        pre.branch.label_i_abstract(
            new_branch,
            branch_lbl,
        ),
    );
    branch_ephemeral_step_facts(
        pre.branch,
        new_branch,
        branch_lbl,
    );
    assert(pre.branch.ephemeral->v.refinement_inv());
    pre.branch.ephemeral->v.i_abstract_seq_end();
    assert(pre.branch.ephemeral->v.i_abstract()
        .stamped_map.seq_end == pre.branch_lsn());
    assert(pre.journal.ephemeral->v.journal.seq_end()
        == pre.branch_lsn());
    branch_lsn_matches_map_i(pre);
    journal_query_end_self(
        pre.journal,
        pre.branch_lsn(),
    );
    let cpre = pre.coordination_i();
    let cpost = post.coordination_i();
    let clbl = CoordinationSystem::Label::Label {
        ctam_label: caching_disk_betree_system_lbl_i(lbl),
    };
    let map_lbl =
        AbstractCrashAwareMap::Label::QueryLabel {
            end_lsn: pre.branch_lsn(),
            key,
            value,
        };
    assert(cpost.mapadt == cpre.mapadt);
    assert(AbstractCrashAwareMap::State::next(
        cpre.mapadt,
        cpost.mapadt,
        map_lbl,
    )) by {
        reveal(AbstractCrashAwareMap::State::next);
        reveal(AbstractCrashAwareMap::State::next_by);
        assert(AbstractMap::State::next(
            cpre.mapadt.ephemeral->v,
            cpre.mapadt.ephemeral->v,
            AbstractMap::Label::QueryLabel {
                end_lsn: pre.branch_lsn(),
                key,
                value,
            },
        ));
        assert(AbstractCrashAwareMap::State::next_by(
            cpre.mapadt,
            cpost.mapadt,
            map_lbl,
            AbstractCrashAwareMap::Step::query(
                cpre.mapadt.ephemeral->v,
            ),
        ));
    }
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::query(
            cpost.journal,
            cpost.mapadt,
        ),
    ));
    assert(refinement_inv(post));
}

#[verifier::spinoff_prover]
proof fn put_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    new_branch: CrashAwareCachingDiskBranchBetree::State,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::put(
            pre,
            post,
            lbl,
            new_journal,
            new_branch,
        ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    assert(lbl is Execute);
    let req = lbl.arrow_Execute_req();
    let records = MsgHistory::singleton_at(
        pre.branch_lsn(),
        crate::abstract_system::MsgHistory_v::KeyedMessage {
            key: req.input.arrow_PutInput_key(),
            message:
                crate::spec::Messages_t::Message::Define {
                    value: req.input.arrow_PutInput_value(),
                },
        },
    );
    let journal_lbl =
        CrashAwareCachingDiskJournal::Label::Put{records};
    let branch_lbl =
        CrashAwareCachingDiskBranchBetree::Label::Ephemeral {
            op: CachingDiskBranchBetree::Label::Put{
                puts: records,
            },
            deallocs: Set::empty(),
        };
    pre.journal.next_refines_abstract(
        new_journal,
        journal_lbl,
    );
    journal_put_step_facts(
        pre.journal,
        new_journal,
        records,
    );
    pre.branch.next_refines(new_branch, branch_lbl);
    abstract_crashaware_put_exposes_map_step(
        pre.branch.i_abstract(),
        new_branch.i_abstract(),
        records,
    );
    branch_ephemeral_step_facts(
        pre.branch,
        new_branch,
        branch_lbl,
    );
    assert(pre.branch.ephemeral->v.refinement_inv());
    pre.branch.ephemeral->v.i_abstract_seq_end();
    assert(pre.branch.ephemeral->v.i_abstract()
        .stamped_map.seq_end == pre.branch_lsn());
    branch_lsn_matches_map_i(pre);
    let cpre = pre.coordination_i();
    let cpost = post.coordination_i();
    let clbl = CoordinationSystem::Label::Label {
        ctam_label: caching_disk_betree_system_lbl_i(lbl),
    };
    let map_lbl =
        AbstractCrashAwareMap::Label::PutRecordsLabel {
            records,
        };
    assert(AbstractCrashAwareMap::State::next(
        cpre.mapadt,
        cpost.mapadt,
        map_lbl,
    )) by {
        reveal(AbstractCrashAwareMap::State::next);
        reveal(AbstractCrashAwareMap::State::next_by);
        assert(cpre.mapadt.ephemeral
            == pre.branch.i_abstract().ephemeral);
        assert(cpost.mapadt.ephemeral
            == new_branch.i_abstract().ephemeral);
        assert(AbstractCrashAwareMap::State::next_by(
            cpre.mapadt,
            cpost.mapadt,
            map_lbl,
            AbstractCrashAwareMap::Step::put_records(
                new_branch.i_abstract().ephemeral->v,
            ),
        ));
    }
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::put(
            cpost.journal,
            cpost.mapadt,
        ),
    ));
    assert(refinement_inv(post));
}

#[verifier::spinoff_prover]
proof fn journal_load_ephemeral_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::
            journal_load_ephemeral(
                pre,
                post,
                lbl,
                new_journal,
            ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    let journal_lbl =
        CrashAwareCachingDiskJournal::Label::LoadEphemeral;
    pre.journal.next_refines_abstract(
        new_journal,
        journal_lbl,
    );
    abstract_journal_load_facts(
        pre.journal.i_abstract(),
        new_journal.i_abstract(),
    );
    journal_load_ephemeral_facts(
        pre.journal,
        new_journal,
    );
    if post.components_loaded() {
        let cpre = pre.coordination_i();
        let cpost = post.coordination_i();
        let clbl = CoordinationSystem::Label::Label {
            ctam_label: caching_disk_betree_system_lbl_i(lbl),
        };
        assert(pre.branch.i_abstract().ephemeral is Known);
        assert(pre.branch.i_abstract().ephemeral->v.stamped_map
            == pre.branch.i_abstract().persistent);
        assert(AbstractMap::State::init_by(
            pre.branch.i_abstract().ephemeral->v,
            AbstractMap::Config::initialize(
                pre.branch.i_abstract().persistent,
            ),
        )) by {
            reveal(AbstractMap::State::init_by);
        }
        assert(AbstractCrashAwareMap::State::next(
            cpre.mapadt,
            cpost.mapadt,
            AbstractCrashAwareMap::Label::
                LoadEphemeralFromPersistentLabel {
                    end_lsn: cpre.mapadt.persistent.seq_end,
                },
        )) by {
            reveal(AbstractCrashAwareMap::State::next);
            reveal(AbstractCrashAwareMap::State::next_by);
            assert(AbstractCrashAwareMap::State::next_by(
                cpre.mapadt,
                cpost.mapadt,
                AbstractCrashAwareMap::Label::
                    LoadEphemeralFromPersistentLabel {
                        end_lsn: cpre.mapadt.persistent.seq_end,
                    },
                AbstractCrashAwareMap::Step::
                    load_ephemeral_from_persistent(),
            ));
        }
        reveal(CoordinationSystem::State::next);
        reveal(CoordinationSystem::State::next_by);
        assert(CoordinationSystem::State::next_by(
            cpre,
            cpost,
            clbl,
            CoordinationSystem::Step::
                load_ephemeral_from_persistent(
                    new_journal.i_abstract(),
                    pre.branch.i_abstract(),
                ),
        ));
    } else {
        assert(post.coordination_i() == pre.coordination_i());
        coordination_noop(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        );
    }
    assert(refinement_inv(post));
}

#[verifier::spinoff_prover]
proof fn branch_load_ephemeral_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_branch: CrashAwareCachingDiskBranchBetree::State,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::
            branch_load_ephemeral(
                pre,
                post,
                lbl,
                new_branch,
            ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    let branch_lbl =
        CrashAwareCachingDiskBranchBetree::Label::LoadEphemeral;
    pre.branch.next_refines(new_branch, branch_lbl);
    abstract_map_load_facts(
        pre.branch.i_abstract(),
        new_branch.i_abstract(),
        pre.branch.persistent_i().seq_end,
    );
    branch_load_ephemeral_facts(
        pre.branch,
        new_branch,
    );
    if post.components_loaded() {
        let cpre = pre.coordination_i();
        let cpost = post.coordination_i();
        let clbl = CoordinationSystem::Label::Label {
            ctam_label: caching_disk_betree_system_lbl_i(lbl),
        };
        assert(pre.journal.i_abstract().ephemeral is Known);
        assert(pre.journal.i_abstract().ephemeral->v.journal
            == pre.journal.i_abstract().persistent);
        pre.journal.persistent_i_wf();
        assert(AbstractJournal::State::init_by(
            pre.journal.i_abstract().ephemeral->v,
            AbstractJournal::Config::initialize(
                pre.journal.i_abstract().persistent,
            ),
        )) by {
            reveal(AbstractJournal::State::init_by);
        }
        assert(AbstractCrashAwareJournal::State::next(
            cpre.journal,
            cpost.journal,
            AbstractCrashAwareJournal::Label::
                LoadEphemeralFromPersistentLabel,
        )) by {
            reveal(AbstractCrashAwareJournal::State::next);
            reveal(AbstractCrashAwareJournal::State::next_by);
            assert(AbstractCrashAwareJournal::State::next_by(
                cpre.journal,
                cpost.journal,
                AbstractCrashAwareJournal::Label::
                    LoadEphemeralFromPersistentLabel,
                AbstractCrashAwareJournal::Step::
                    load_ephemeral_from_persistent(
                        pre.journal.i_abstract().ephemeral->v,
                    ),
            ));
        }
        reveal(CoordinationSystem::State::next);
        reveal(CoordinationSystem::State::next_by);
        assert(CoordinationSystem::State::next_by(
            cpre,
            cpost,
            clbl,
            CoordinationSystem::Step::
                load_ephemeral_from_persistent(
                    pre.journal.i_abstract(),
                    new_branch.i_abstract(),
                ),
        ));
    } else {
        assert(post.journal == pre.journal);
        assert(post.coordination_i() == pre.coordination_i());
        coordination_noop(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        );
    }
    assert(refinement_inv(post));
}

#[verifier::spinoff_prover]
proof fn recover_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    new_branch: CrashAwareCachingDiskBranchBetree::State,
    journal_records: MsgHistory,
    branch_records: MsgHistory,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::recover(
            pre,
            post,
            lbl,
            new_journal,
            new_branch,
            journal_records,
            branch_records,
        ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    let journal_lbl =
        CrashAwareCachingDiskJournal::Label::ReadForRecovery {
            records: journal_records,
        };
    let branch_lbl =
        CrashAwareCachingDiskBranchBetree::Label::Ephemeral {
            op: CachingDiskBranchBetree::Label::Put {
                puts: branch_records,
            },
            deallocs: Set::empty(),
        };
    pre.journal.next_refines_abstract(
        new_journal,
        journal_lbl,
    );
    journal_recovery_read_facts(
        pre.journal,
        new_journal,
        journal_records,
    );
    pre.branch.next_refines(new_branch, branch_lbl);
    abstract_crashaware_put_exposes_map_step(
        pre.branch.i_abstract(),
        new_branch.i_abstract(),
        branch_records,
    );
    branch_ephemeral_step_facts(
        pre.branch,
        new_branch,
        branch_lbl,
    );
    branch_lsn_matches_map_i(pre);
    let cpre = pre.coordination_i();
    let cpost = post.coordination_i();
    let clbl = CoordinationSystem::Label::Label {
        ctam_label: caching_disk_betree_system_lbl_i(lbl),
    };
    assert(cpost.journal == cpre.journal);
    pre.journal.ephemeral_i_wf();
    journal_records.maybe_discard_old_is_subseq(
        pre.branch_lsn(),
    );
    assert(journal_records.includes_subseq(branch_records));
    assert(cpre.journal.ephemeral->v.journal
        .includes_subseq(journal_records)) by {
        reveal(AbstractCrashAwareJournal::State::next);
        reveal(AbstractCrashAwareJournal::State::next_by);
        let journal_step =
            choose |journal_step: AbstractCrashAwareJournal::Step|
                AbstractCrashAwareJournal::State::next_by(
                    cpre.journal,
                    cpre.journal,
                    AbstractCrashAwareJournal::Label::
                        ReadForRecoveryLabel {
                            records: journal_records,
                        },
                    journal_step,
                );
        match journal_step {
            AbstractCrashAwareJournal::Step::
                read_for_recovery() => {
                reveal(AbstractJournal::State::next);
                reveal(AbstractJournal::State::next_by);
                let inner = choose |inner: AbstractJournal::Step|
                    AbstractJournal::State::next_by(
                        cpre.journal.ephemeral->v,
                        cpre.journal.ephemeral->v,
                        AbstractJournal::Label::
                            ReadForRecoveryLabel {
                                messages: journal_records,
                            },
                        inner,
                    );
                match inner {
                    AbstractJournal::Step::read_for_recovery() => {
                    }
                    _ => {
                        assert(false);
                    }
                }
            }
            _ => {
                assert(false);
            }
        }
    }
    assert(cpre.journal.ephemeral->v.journal
        .includes_subseq(branch_records));
    assert(AbstractCrashAwareJournal::State::next(
        cpre.journal,
        cpost.journal,
        AbstractCrashAwareJournal::Label::
            ReadForRecoveryLabel {
                records: branch_records,
            },
    )) by {
        reveal(AbstractCrashAwareJournal::State::next);
        reveal(AbstractCrashAwareJournal::State::next_by);
        reveal(AbstractJournal::State::next);
        reveal(AbstractJournal::State::next_by);
        assert(AbstractJournal::State::next_by(
            cpre.journal.ephemeral->v,
            cpre.journal.ephemeral->v,
            AbstractJournal::Label::ReadForRecoveryLabel {
                messages: branch_records,
            },
            AbstractJournal::Step::read_for_recovery(),
        ));
        assert(AbstractCrashAwareJournal::State::next_by(
            cpre.journal,
            cpost.journal,
            AbstractCrashAwareJournal::Label::
                ReadForRecoveryLabel {
                    records: branch_records,
                },
            AbstractCrashAwareJournal::Step::
                read_for_recovery(),
        ));
    }
    assert(AbstractCrashAwareMap::State::next(
        cpre.mapadt,
        cpost.mapadt,
        AbstractCrashAwareMap::Label::PutRecordsLabel {
            records: branch_records,
        },
    )) by {
        reveal(AbstractCrashAwareMap::State::next);
        reveal(AbstractCrashAwareMap::State::next_by);
        assert(AbstractCrashAwareMap::State::next_by(
            cpre.mapadt,
            cpost.mapadt,
            AbstractCrashAwareMap::Label::PutRecordsLabel {
                records: branch_records,
            },
            AbstractCrashAwareMap::Step::put_records(
                cpost.mapadt.ephemeral->v,
            ),
        ));
    }
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::recover(
            cpost.journal,
            cpost.mapadt,
            branch_records,
        ),
    ));
    assert(refinement_inv(post));
}

#[verifier::spinoff_prover]
proof fn req_sync_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::req_sync(
            pre,
            post,
            lbl,
        ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    let journal_lbl =
        CrashAwareCachingDiskJournal::Label::QueryEndLsn {
            end_lsn: pre.branch_lsn(),
        };
    pre.journal.next_refines_abstract(
        pre.journal,
        journal_lbl,
    );
    branch_lsn_matches_map_i(pre);
    let cpre = pre.coordination_i();
    let cpost = post.coordination_i();
    let clbl = CoordinationSystem::Label::Label {
        ctam_label: caching_disk_betree_system_lbl_i(lbl),
    };
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::req_sync(
            pre.journal.i_abstract(),
        ),
    ));
    assert(refinement_inv(post));
}

#[verifier::spinoff_prover]
proof fn reply_sync_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::reply_sync(
            pre,
            post,
            lbl,
        ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    assert(lbl is ReplySync);
    let sync_req_id = lbl.arrow_ReplySync_sync_req_id();
    let journal_lbl =
        CrashAwareCachingDiskJournal::Label::QueryLsnPersistence {
            sync_lsn: pre.sync_reqs[sync_req_id],
        };
    pre.journal.next_refines_abstract(
        pre.journal,
        journal_lbl,
    );
    let cpre = pre.coordination_i();
    let cpost = post.coordination_i();
    let clbl = CoordinationSystem::Label::Label {
        ctam_label: caching_disk_betree_system_lbl_i(lbl),
    };
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::reply_sync(
            pre.journal.i_abstract(),
        ),
    ));
    assert(refinement_inv(post));
}

#[verifier::spinoff_prover]
proof fn journal_commit_prepared_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    new_superblock: SuperblockStore::State,
    raw_page: RawPage,
    superblock_image: AbstractSuperblockImage,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::
            journal_commit_prepared(
                pre,
                post,
                lbl,
                new_journal,
                new_superblock,
                raw_page,
                superblock_image,
            ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    journal_internal_step_stutters(
        pre.journal,
        new_journal,
        CrashAwareCachingDiskJournal::Label::CommitPrepared,
    );
    journal_commit_prepared_facts(
        pre.journal,
        new_journal,
    );
    superblock_write_facts(
        pre.superblockstore,
        new_superblock,
        raw_page,
    );
    SuperblockStore::State::inv_next(
        pre.superblockstore,
        new_superblock,
        SuperblockStore::Label::Write{raw: raw_page},
    );
    assert(post.coordination_i() == pre.coordination_i());
    coordination_noop(
        pre.coordination_i(),
        post.coordination_i(),
        CoordinationSystem::Label::Label {
            ctam_label: caching_disk_betree_system_lbl_i(lbl),
        },
    );
    assert(refinement_inv(post));
}

#[verifier::spinoff_prover]
proof fn store_commit_prepared_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    new_branch: CrashAwareCachingDiskBranchBetree::State,
    new_superblock: SuperblockStore::State,
    raw_page: RawPage,
    superblock_image: AbstractSuperblockImage,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::
            store_commit_prepared(
                pre,
                post,
                lbl,
                new_journal,
                new_branch,
                new_superblock,
                raw_page,
                superblock_image,
            ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    journal_internal_step_stutters(
        pre.journal,
        new_journal,
        CrashAwareCachingDiskJournal::Label::CommitPrepared,
    );
    branch_internal_step_stutters(
        pre.branch,
        new_branch,
        CrashAwareCachingDiskBranchBetree::Label::CommitPrepared,
    );
    journal_commit_prepared_facts(
        pre.journal,
        new_journal,
    );
    branch_commit_prepared_facts(
        pre.branch,
        new_branch,
    );
    superblock_write_facts(
        pre.superblockstore,
        new_superblock,
        raw_page,
    );
    SuperblockStore::State::inv_next(
        pre.superblockstore,
        new_superblock,
        SuperblockStore::Label::Write{raw: raw_page},
    );
    assert(post.coordination_i() == pre.coordination_i());
    coordination_noop(
        pre.coordination_i(),
        post.coordination_i(),
        CoordinationSystem::Label::Label {
            ctam_label: caching_disk_betree_system_lbl_i(lbl),
        },
    );
    assert(refinement_inv(post));
}

#[verifier::spinoff_prover]
proof fn superblock_write_lands_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_superblock: SuperblockStore::State,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::
            superblock_write_lands(
                pre,
                post,
                lbl,
                new_superblock,
            ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    let cpre = pre.coordination_i();
    let cpost = post.coordination_i();
    let clbl = CoordinationSystem::Label::Label {
        ctam_label: caching_disk_betree_system_lbl_i(lbl),
    };
    reveal(SuperblockStore::State::next);
    reveal(SuperblockStore::State::next_by);
    superblock_land_facts(
        pre.superblockstore,
        new_superblock,
    );
    SuperblockStore::State::inv_next(
        pre.superblockstore,
        new_superblock,
        SuperblockStore::Label::Land,
    );
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::superblock_write_lands(),
    ));
    assert(refinement_inv(post));
}

#[verifier::spinoff_prover]
proof fn journal_internal_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::journal_internal(
            pre,
            post,
            lbl,
            new_journal,
        ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    journal_internal_step_stutters(
        pre.journal,
        new_journal,
        CrashAwareCachingDiskJournal::Label::Internal,
    );
    assert(post.coordination_i() == pre.coordination_i());
    coordination_noop(
        pre.coordination_i(),
        post.coordination_i(),
        CoordinationSystem::Label::Label {
            ctam_label: caching_disk_betree_system_lbl_i(lbl),
        },
    );
    assert(refinement_inv(post));
}

#[verifier::spinoff_prover]
proof fn journal_observe_clean_aus_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    aus: Set<AU>,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::
            journal_observe_clean_aus(
                pre,
                post,
                lbl,
                new_journal,
                aus,
            ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    journal_internal_step_stutters(
        pre.journal,
        new_journal,
        CrashAwareCachingDiskJournal::Label::ObserveCleanAUs{aus},
    );
    assert(post.coordination_i() == pre.coordination_i());
    coordination_noop(
        pre.coordination_i(),
        post.coordination_i(),
        CoordinationSystem::Label::Label {
            ctam_label: caching_disk_betree_system_lbl_i(lbl),
        },
    );
    assert(refinement_inv(post));
}

#[verifier::spinoff_prover]
proof fn journal_load_index_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    discovered_aus: Set<AU>,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::journal_load_index(
            pre,
            post,
            lbl,
            new_journal,
            discovered_aus,
        ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    journal_internal_step_stutters(
        pre.journal,
        new_journal,
        CrashAwareCachingDiskJournal::Label::LoadIndex {
            discovered_aus,
        },
    );
    assert(post.coordination_i() == pre.coordination_i());
    coordination_noop(
        pre.coordination_i(),
        post.coordination_i(),
        CoordinationSystem::Label::Label {
            ctam_label: caching_disk_betree_system_lbl_i(lbl),
        },
    );
    assert(refinement_inv(post));
}

#[verifier::spinoff_prover]
proof fn journal_internal_alloc_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    prune_aus: Set<AU>,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::
            journal_internal_alloc(
                pre,
                post,
                lbl,
                new_journal,
                allocs,
                deallocs,
                prune_aus,
            ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    journal_internal_step_stutters(
        pre.journal,
        new_journal,
        CrashAwareCachingDiskJournal::Label::InternalAlloc {
            allocs,
            deallocs,
            prune_aus,
        },
    );
    assert(post.coordination_i() == pre.coordination_i());
    coordination_noop(
        pre.coordination_i(),
        post.coordination_i(),
        CoordinationSystem::Label::Label {
            ctam_label: caching_disk_betree_system_lbl_i(lbl),
        },
    );
    assert(refinement_inv(post));
}

#[verifier::spinoff_prover]
proof fn branch_recover_metadata_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_branch: CrashAwareCachingDiskBranchBetree::State,
    recovery_op: BetreeMetadataRecoveryLabel,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::
            branch_recover_metadata(
                pre,
                post,
                lbl,
                new_branch,
                recovery_op,
            ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    branch_internal_step_stutters(
        pre.branch,
        new_branch,
        CrashAwareCachingDiskBranchBetree::Label::
            RecoverMetadata{recovery_op},
    );
    assert(post.coordination_i() == pre.coordination_i());
    coordination_noop(
        pre.coordination_i(),
        post.coordination_i(),
        CoordinationSystem::Label::Label {
            ctam_label: caching_disk_betree_system_lbl_i(lbl),
        },
    );
    assert(refinement_inv(post));
}

#[verifier::spinoff_prover]
proof fn branch_load_metadata_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_branch: CrashAwareCachingDiskBranchBetree::State,
    discovered_aus: Set<AU>,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::
            branch_load_metadata(
                pre,
                post,
                lbl,
                new_branch,
                discovered_aus,
            ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    branch_internal_step_stutters(
        pre.branch,
        new_branch,
        CrashAwareCachingDiskBranchBetree::Label::LoadMetadata,
    );
    assert(post.coordination_i() == pre.coordination_i());
    coordination_noop(
        pre.coordination_i(),
        post.coordination_i(),
        CoordinationSystem::Label::Label {
            ctam_label: caching_disk_betree_system_lbl_i(lbl),
        },
    );
    assert(refinement_inv(post));
}

#[verifier::spinoff_prover]
proof fn branch_internal_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_branch: CrashAwareCachingDiskBranchBetree::State,
    branch_lbl: CrashAwareCachingDiskBranchBetree::Label,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::branch_internal(
            pre,
            post,
            lbl,
            new_branch,
            branch_lbl,
        ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    branch_internal_step_stutters(
        pre.branch,
        new_branch,
        branch_lbl,
    );
    assert(post.coordination_i() == pre.coordination_i());
    coordination_noop(
        pre.coordination_i(),
        post.coordination_i(),
        CoordinationSystem::Label::Label {
            ctam_label: caching_disk_betree_system_lbl_i(lbl),
        },
    );
    assert(refinement_inv(post));
}

#[verifier::spinoff_prover]
proof fn component_internals_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    new_branch: CrashAwareCachingDiskBranchBetree::State,
    branch_lbl: CrashAwareCachingDiskBranchBetree::Label,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::
            component_internals(
                pre,
                post,
                lbl,
                new_journal,
                new_branch,
                branch_lbl,
            ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    journal_internal_step_stutters(
        pre.journal,
        new_journal,
        CrashAwareCachingDiskJournal::Label::Internal,
    );
    branch_internal_step_stutters(
        pre.branch,
        new_branch,
        branch_lbl,
    );
    assert(post.coordination_i() == pre.coordination_i());
    coordination_noop(
        pre.coordination_i(),
        post.coordination_i(),
        CoordinationSystem::Label::Label {
            ctam_label: caching_disk_betree_system_lbl_i(lbl),
        },
    );
    assert(refinement_inv(post));
}

#[verifier::spinoff_prover]
proof fn branch_internal_alloc_refines(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
    new_branch: CrashAwareCachingDiskBranchBetree::State,
    op: CachingDiskBranchBetree::Label,
    allocs: Set<AU>,
    deallocs: Set<AU>,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::
            branch_internal_alloc(
                pre,
                post,
                lbl,
                new_branch,
                op,
                allocs,
                deallocs,
            ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    let branch_lbl =
        CrashAwareCachingDiskBranchBetree::Label::Ephemeral {
            op,
            deallocs,
        };
    branch_internal_step_stutters(
        pre.branch,
        new_branch,
        branch_lbl,
    );
    assert(post.coordination_i() == pre.coordination_i());
    coordination_noop(
        pre.coordination_i(),
        post.coordination_i(),
        CoordinationSystem::Label::Label {
            ctam_label: caching_disk_betree_system_lbl_i(lbl),
        },
    );
    assert(refinement_inv(post));
}

#[verifier::spinoff_prover]
pub proof fn next_refines_coordination(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
)
    requires
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::next(
            pre,
            post,
            lbl,
        ),
    ensures
        refinement_inv(post),
        CoordinationSystem::State::next(
            pre.coordination_i(),
            post.coordination_i(),
            CoordinationSystem::Label::Label {
                ctam_label: caching_disk_betree_system_lbl_i(lbl),
            },
        ),
{
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);
    reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
    let step = choose |step: CrashAwareCachingDiskBetreeSystem::Step|
        CrashAwareCachingDiskBetreeSystem::State::next_by(
            pre,
            post,
            lbl,
            step,
        );
    match step {
        CrashAwareCachingDiskBetreeSystem::Step::accept_request() => {
            accept_request_refines(pre, post, lbl);
            assert(refinement_inv(post));
        }
        CrashAwareCachingDiskBetreeSystem::Step::deliver_reply() => {
            deliver_reply_refines(pre, post, lbl);
            assert(refinement_inv(post));
        }
        CrashAwareCachingDiskBetreeSystem::Step::execute_noop() => {
            execute_noop_refines(pre, post, lbl);
            assert(refinement_inv(post));
        }
        CrashAwareCachingDiskBetreeSystem::Step::noop() => {
            noop_refines(pre, post, lbl);
            assert(refinement_inv(post));
        }
        CrashAwareCachingDiskBetreeSystem::Step::journal_internal(
            new_journal,
        ) => {
            journal_internal_refines(
                pre,
                post,
                lbl,
                new_journal,
            );
        }
        CrashAwareCachingDiskBetreeSystem::Step::journal_observe_clean_aus(
            new_journal,
            aus,
        ) => {
            journal_observe_clean_aus_refines(
                pre,
                post,
                lbl,
                new_journal,
                aus,
            );
        }
        CrashAwareCachingDiskBetreeSystem::Step::journal_load_index(
            new_journal,
            discovered_aus,
        ) => {
            journal_load_index_refines(
                pre,
                post,
                lbl,
                new_journal,
                discovered_aus,
            );
        }
        CrashAwareCachingDiskBetreeSystem::Step::journal_internal_alloc(
            new_journal,
            allocs,
            deallocs,
            prune_aus,
        ) => {
            journal_internal_alloc_refines(
                pre,
                post,
                lbl,
                new_journal,
                allocs,
                deallocs,
                prune_aus,
            );
        }
        CrashAwareCachingDiskBetreeSystem::Step::branch_recover_metadata(
            new_branch,
            recovery_op,
        ) => {
            branch_recover_metadata_refines(
                pre,
                post,
                lbl,
                new_branch,
                recovery_op,
            );
        }
        CrashAwareCachingDiskBetreeSystem::Step::branch_load_metadata(
            new_branch,
            discovered_aus,
        ) => {
            branch_load_metadata_refines(
                pre,
                post,
                lbl,
                new_branch,
                discovered_aus,
            );
        }
        CrashAwareCachingDiskBetreeSystem::Step::branch_internal(
            new_branch,
            branch_lbl,
        ) => {
            branch_internal_refines(
                pre,
                post,
                lbl,
                new_branch,
                branch_lbl,
            );
        }
        CrashAwareCachingDiskBetreeSystem::Step::component_internals(
            new_journal,
            new_branch,
            branch_lbl,
        ) => {
            component_internals_refines(
                pre,
                post,
                lbl,
                new_journal,
                new_branch,
                branch_lbl,
            );
        }
        CrashAwareCachingDiskBetreeSystem::Step::branch_internal_alloc(
            new_branch,
            op,
            allocs,
            deallocs,
        ) => {
            branch_internal_alloc_refines(
                pre,
                post,
                lbl,
                new_branch,
                op,
                allocs,
                deallocs,
            );
        }
        CrashAwareCachingDiskBetreeSystem::Step::journal_load_ephemeral(
            new_journal,
        ) => {
            journal_load_ephemeral_refines(
                pre,
                post,
                lbl,
                new_journal,
            );
        }
        CrashAwareCachingDiskBetreeSystem::Step::branch_load_ephemeral(
            new_branch,
        ) => {
            branch_load_ephemeral_refines(
                pre,
                post,
                lbl,
                new_branch,
            );
        }
        CrashAwareCachingDiskBetreeSystem::Step::query(
            new_branch,
            access,
        ) => {
            query_refines(pre, post, lbl, new_branch, access);
        }
        CrashAwareCachingDiskBetreeSystem::Step::put(
            new_journal,
            new_branch,
        ) => {
            put_refines(
                pre,
                post,
                lbl,
                new_journal,
                new_branch,
            );
        }
        CrashAwareCachingDiskBetreeSystem::Step::req_sync() => {
            req_sync_refines(pre, post, lbl);
        }
        CrashAwareCachingDiskBetreeSystem::Step::reply_sync() => {
            reply_sync_refines(pre, post, lbl);
        }
        CrashAwareCachingDiskBetreeSystem::Step::recover(
            new_journal,
            new_branch,
            journal_records,
            branch_records,
        ) => {
            recover_refines(
                pre,
                post,
                lbl,
                new_journal,
                new_branch,
                journal_records,
                branch_records,
            );
        }
        CrashAwareCachingDiskBetreeSystem::Step::journal_commit_start(
            new_journal,
            superblock_image,
        ) => {
            journal_commit_start_refines(
                pre,
                post,
                lbl,
                new_journal,
                superblock_image,
            );
            assert(refinement_inv(post));
        }
        CrashAwareCachingDiskBetreeSystem::Step::store_commit_start(
            new_journal,
            new_branch,
            superblock_image,
        ) => {
            store_commit_start_refines(
                pre,
                post,
                lbl,
                new_journal,
                new_branch,
                superblock_image,
            );
            assert(refinement_inv(post));
        }
        CrashAwareCachingDiskBetreeSystem::Step::journal_commit_prepared(
            new_journal,
            new_superblock,
            raw_page,
            superblock_image,
        ) => {
            journal_commit_prepared_refines(
                pre,
                post,
                lbl,
                new_journal,
                new_superblock,
                raw_page,
                superblock_image,
            );
        }
        CrashAwareCachingDiskBetreeSystem::Step::store_commit_prepared(
            new_journal,
            new_branch,
            new_superblock,
            raw_page,
            superblock_image,
        ) => {
            store_commit_prepared_refines(
                pre,
                post,
                lbl,
                new_journal,
                new_branch,
                new_superblock,
                raw_page,
                superblock_image,
            );
        }
        CrashAwareCachingDiskBetreeSystem::Step::superblock_write_lands(
            new_superblock,
        ) => {
            superblock_write_lands_refines(
                pre,
                post,
                lbl,
                new_superblock,
            );
        }
        CrashAwareCachingDiskBetreeSystem::Step::journal_commit_complete(
            new_journal,
            new_superblock,
            journal_discarded,
        ) => {
            journal_commit_complete_refines(
                pre,
                post,
                lbl,
                new_journal,
                new_superblock,
                journal_discarded,
            );
            assert(refinement_inv(post));
        }
        CrashAwareCachingDiskBetreeSystem::Step::store_commit_complete(
            new_journal,
            new_branch,
            new_superblock,
            journal_discarded,
            branch_discarded,
        ) => {
            store_commit_complete_refines(
                pre,
                post,
                lbl,
                new_journal,
                new_branch,
                new_superblock,
                journal_discarded,
                branch_discarded,
            );
            assert(refinement_inv(post));
        }
        CrashAwareCachingDiskBetreeSystem::Step::crash(
            new_journal,
            new_branch,
            new_superblock,
            new_free_aus,
            keep_in_flight,
        ) => {
            crash_refines(
                pre,
                post,
                lbl,
                new_journal,
                new_branch,
                new_superblock,
                new_free_aus,
                keep_in_flight,
            );
            assert(refinement_inv(post));
        }
        _ => {
            assert(false);
        }
    }
}

pub proof fn init_refines_ctam(
    model: CrashAwareCachingDiskBetreeSystem::State,
)
    requires
        CrashAwareCachingDiskBetreeSystem::State::init(model),
    ensures
        refinement_inv(model),
        model.coordination_i().inv(),
        CrashTolerantAsyncMap::State::init(
            caching_disk_betree_system_ctam_i(model),
        ),
{
    reveal(CrashAwareCachingDiskBetreeSystem::State::init);
    reveal(CrashAwareCachingDiskBetreeSystem::State::init_by);


    let config = choose |config:
        CrashAwareCachingDiskBetreeSystem::Config|
        CrashAwareCachingDiskBetreeSystem::State::init_by(
            model,
            config,
        );
    match config {
        CrashAwareCachingDiskBetreeSystem::Config::initialize(
            free_aus,
            initial_superblock,
            journal,
            branch,
        ) => {
            journal.init_refines();
            branch.init_refines();
            assert(refinement_inv(model));
            let c = model.coordination_i();
            AbstractCrashAwareJournal::show::initialize(
                journal.i_abstract(),
            );
            AbstractCrashAwareMap::show::initialize(
                branch.i_abstract(),
            );
            assert(CoordinationSystem::State::initialize(c, c)) by {
            }
            assert(CoordinationSystem::State::init_by(
                c,
                CoordinationSystem::Config::initialize(c),
            )) by {
                reveal(CoordinationSystem::State::init_by);

            }
            assert(CoordinationSystem::State::init(c)) by {
                reveal(CoordinationSystem::State::init);

            }
            lemma_init_refines(c);
        }
        CrashAwareCachingDiskBetreeSystem::Config::
            dummy_to_use_type_params(_) => {
            assert(false);
        }
    }
}

pub proof fn next_refines_ctam(
    pre: CrashAwareCachingDiskBetreeSystem::State,
    post: CrashAwareCachingDiskBetreeSystem::State,
    lbl: CrashAwareCachingDiskBetreeSystem::Label,
)
    requires
        refinement_inv(pre),
        pre.coordination_i().inv(),
        CrashAwareCachingDiskBetreeSystem::State::next(
            pre,
            post,
            lbl,
        ),
    ensures
        refinement_inv(post),
        post.coordination_i().inv(),
        CrashTolerantAsyncMap::State::next(
            caching_disk_betree_system_ctam_i(pre),
            caching_disk_betree_system_ctam_i(post),
            caching_disk_betree_system_lbl_i(lbl),
        ),
{
    let cpre = pre.coordination_i();
    let cpost = post.coordination_i();
    let clbl = CoordinationSystem::Label::Label {
        ctam_label: caching_disk_betree_system_lbl_i(lbl),
    };
    next_refines_coordination(pre, post, lbl);
    next_refines(cpre, cpost, clbl);
}

} // verus!
