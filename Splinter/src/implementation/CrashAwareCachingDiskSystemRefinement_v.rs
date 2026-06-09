// Refinement for the branch-aware CrashAwareCachingDiskSystem.
//
// CrashAwareCachingDiskSystem is a clean composition of CrashAwareCachingDiskJournal
// and CrashAwareCachingDiskBranch.

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::assert_maps_equal;

use crate::abstract_system::AbstractCrashAwareJournal_v::AbstractCrashAwareJournal;
use crate::abstract_system::AbstractJournal_v::AbstractJournal;
use crate::abstract_system::AbstractCrashAwareMap_v::AbstractCrashAwareMap;
use crate::abstract_system::AbstractCrashAwareSystem_v::CoordinationSystem;
use crate::abstract_system::AbstractCrashAwareSystemRefinement_v::*;
use crate::abstract_system::MsgHistory_v::{KeyedMessage, MsgHistory};
use crate::allocation_layer::AllocationJournal_v::JournalImage;
use crate::implementation::CrashAwareCachingDiskBranchRefinement_v::*;
use crate::implementation::CrashAwareCachingDiskJournalRefinement_v::*;
use crate::implementation::AllocationBranchStackRefinement_v::{append_puts, append_puts_wf};
use crate::implementation::CrashAwareCachingDiskSystem_v::{CrashAwareCachingDiskSystem, SuperblockStore};
use crate::implementation::CrashAwareCachingDiskBranch_v::CrashAwareCachingDiskBranch;
use crate::implementation::CachingDiskBranch_v::{
    CachingDiskBranch, CachingDiskBranchImage, empty_caching_disk_branch_image,
    empty_caching_disk_branch_image_wf, to_branch_nodes,
};
use crate::implementation::CrashAwareCachingDiskJournal_v::{
    CachingDiskJournalImage, CrashAwareCachingDiskJournal,
};
use crate::implementation::CachingDiskJournal_v::CachingDiskJournal;
use crate::implementation::CachingDisk_v::CachingDiskRawPage as RawPage;
use crate::implementation::CachedJournal_v::CachedJournal;
use crate::implementation::CachedBranch_v::{CachedBranch, loaded_append_ready};
use crate::implementation::AbstractSuperblock_v::AbstractSuperblockImage;
use crate::disk::GenericDisk_v::{AU, Address};
use crate::spec::MapSpec_t::{AsyncMap, CrashTolerantAsyncMap};
use crate::spec::Messages_t::Message;

verus!{

pub closed spec fn caching_disk_system_coordination_i(model: CrashAwareCachingDiskSystem::State) -> CoordinationSystem::State
{
    model.coordination_i()
}

pub closed spec fn caching_disk_system_i(model: CrashAwareCachingDiskSystem::State) -> CrashTolerantAsyncMap::State
{
    caching_disk_system_coordination_i(model).i()
}

proof fn caching_disk_system_commit_flags_unchanged(pre: CrashAwareCachingDiskSystem::State, post: CrashAwareCachingDiskSystem::State)
    requires
        post.journal.frozen == pre.journal.frozen,
        post.branch.frozen == pre.branch.frozen,
        post.superblockstore == pre.superblockstore,
    ensures
        caching_disk_system_coordination_i(post).superblock_in_flight
            == caching_disk_system_coordination_i(pre).superblock_in_flight,
        caching_disk_system_coordination_i(post).superblock_landed
            == caching_disk_system_coordination_i(pre).superblock_landed,
{
    reveal(caching_disk_system_coordination_i);
    assert(post.commit_started() == pre.commit_started());
}

pub open spec fn caching_disk_system_i_lbl(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
) -> CrashTolerantAsyncMap::Label
{
    match lbl {
        CrashAwareCachingDiskSystem::Label::Request{req} =>
            CrashTolerantAsyncMap::Label::OperateOp{
                base_op: AsyncMap::Label::RequestOp{req},
            },
        CrashAwareCachingDiskSystem::Label::Execute{req, reply} =>
            CrashTolerantAsyncMap::Label::OperateOp{
                base_op: AsyncMap::Label::ExecuteOp{req, reply},
            },
        CrashAwareCachingDiskSystem::Label::Reply{reply} =>
            CrashTolerantAsyncMap::Label::OperateOp{
                base_op: AsyncMap::Label::ReplyOp{reply},
            },
        CrashAwareCachingDiskSystem::Label::ReqSync{sync_req_id} =>
            CrashTolerantAsyncMap::Label::ReqSyncOp{sync_req_id},
        CrashAwareCachingDiskSystem::Label::ReplySync{sync_req_id} =>
            CrashTolerantAsyncMap::Label::ReplySyncOp{sync_req_id},
        CrashAwareCachingDiskSystem::Label::Sync =>
            CrashTolerantAsyncMap::Label::SyncOp{},
        CrashAwareCachingDiskSystem::Label::Crash =>
            CrashTolerantAsyncMap::Label::CrashOp{},
        CrashAwareCachingDiskSystem::Label::Noop =>
            CrashTolerantAsyncMap::Label::Noop{},
    }
}

proof fn branch_lsn_matches_coordination_map(model: CrashAwareCachingDiskSystem::State)
    requires
        model.coordination_i().mapadt.ephemeral is Known,
    ensures
        model.coordination_i().mapadt.i().seq_end == model.branch_lsn(),
{
    assert(model.branch.ephemeral is Known) by {
        if !(model.branch.ephemeral is Known) {
            assert(model.branch.i().ephemeral is Unknown);
            assert(model.branch.i().abstract_i().ephemeral is Unknown);
            assert(model.coordination_i().mapadt.ephemeral is Unknown);
            assert(false);
        }
    };
    let branch_state = model.branch.ephemeral->v;
    let stack_state = branch_state.i();
    assert(model.branch.i().ephemeral is Known);
    assert(model.branch.i().ephemeral->v == stack_state);
    assert(model.branch.i().abstract_i().ephemeral is Known);
    assert(model.branch.i().abstract_i().ephemeral->v == stack_state.abstract_map_i());
    assert(model.coordination_i().mapadt == model.branch.i().abstract_i());
    assert(model.coordination_i().mapadt.i() == stack_state.abstract_map_i().stamped_map);
    assert(stack_state.abstract_map_i().stamped_map.seq_end == stack_state.seq_end);
    assert(stack_state.seq_end == branch_state.seq_end);
    assert(model.branch_lsn() == branch_state.seq_end);
}

proof fn journal_step_preserves_frozen(
    pre: CrashAwareCachingDiskJournal::State,
    post: CrashAwareCachingDiskJournal::State,
    lbl: CrashAwareCachingDiskJournal::Label,
)
    requires
        CrashAwareCachingDiskJournal::State::next(pre, post, lbl),
        lbl is Internal || lbl is LoadIndex || lbl is InternalAlloc || lbl is CommitPrepared,
    ensures
        post.frozen == pre.frozen,
{
    reveal(CrashAwareCachingDiskJournal::State::next);
    reveal(CrashAwareCachingDiskJournal::State::next_by);
    let step = choose |step| CrashAwareCachingDiskJournal::State::next_by(
        pre,
        post,
        lbl,
        step,
    );
    match step {
        CrashAwareCachingDiskJournal::Step::load_index(new_ephemeral) => {
            reveal(CrashAwareCachingDiskJournal::State::load_index);
        },
        CrashAwareCachingDiskJournal::Step::internal(new_ephemeral) => {
            reveal(CrashAwareCachingDiskJournal::State::internal);
        },
        CrashAwareCachingDiskJournal::Step::internal_alloc(new_ephemeral) => {
            reveal(CrashAwareCachingDiskJournal::State::internal_alloc);
        },
        CrashAwareCachingDiskJournal::Step::commit_prepared() => {
            reveal(CrashAwareCachingDiskJournal::State::commit_prepared);
        },
        _ => { assert(false); },
    }
}

proof fn branch_step_preserves_frozen(
    pre: CrashAwareCachingDiskBranch::State,
    post: CrashAwareCachingDiskBranch::State,
    lbl: CrashAwareCachingDiskBranch::Label,
)
    requires
        CrashAwareCachingDiskBranch::State::next(pre, post, lbl),
        lbl is Internal || lbl is LoadMetadata || lbl is InternalAlloc || lbl is FreezePrepared,
    ensures
        post.frozen == pre.frozen,
{
    reveal(CrashAwareCachingDiskBranch::State::next);
    reveal(CrashAwareCachingDiskBranch::State::next_by);
    let step = choose |step| CrashAwareCachingDiskBranch::State::next_by(
        pre,
        post,
        lbl,
        step,
    );
    match step {
        CrashAwareCachingDiskBranch::Step::load_metadata(new_ephemeral) => {
            reveal(CrashAwareCachingDiskBranch::State::load_metadata);
        },
        CrashAwareCachingDiskBranch::Step::internal(new_ephemeral) => {
            reveal(CrashAwareCachingDiskBranch::State::internal);
        },
        CrashAwareCachingDiskBranch::Step::internal_alloc(new_ephemeral) => {
            reveal(CrashAwareCachingDiskBranch::State::internal_alloc);
        },
        CrashAwareCachingDiskBranch::Step::freeze_prepared() => {
            reveal(CrashAwareCachingDiskBranch::State::freeze_prepared);
        },
        _ => { assert(false); },
    }
}

proof fn accept_request_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
)
    requires
        CrashAwareCachingDiskSystem::State::accept_request(pre, post, lbl),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::accept_request);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};
    assert(CoordinationSystem::State::accept_request(cpre, cpost, clbl)) by {
        reveal(CoordinationSystem::State::accept_request);
    }
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::accept_request(),
    ));
}

proof fn deliver_reply_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
)
    requires
        CrashAwareCachingDiskSystem::State::deliver_reply(pre, post, lbl),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::deliver_reply);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};
    assert(CoordinationSystem::State::deliver_reply(cpre, cpost, clbl)) by {
        reveal(CoordinationSystem::State::deliver_reply);
    }
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::deliver_reply(),
    ));
}

proof fn execute_noop_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
)
    requires
        CrashAwareCachingDiskSystem::State::execute_noop(pre, post, lbl),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::execute_noop);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};
    assert(CoordinationSystem::State::execute_noop(cpre, cpost, clbl)) by {
        reveal(CoordinationSystem::State::execute_noop);
    }
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::execute_noop(),
    ));
}

proof fn noop_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
)
    requires
        CrashAwareCachingDiskSystem::State::noop(pre, post, lbl),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::noop);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};
    assert(CoordinationSystem::State::noop(cpre, cpost, clbl)) by {
        reveal(CoordinationSystem::State::noop);
    }
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::noop(),
    ));
}

proof fn query_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
    new_branch: CrashAwareCachingDiskBranch::State,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskSystem::State::query(pre, post, lbl, new_branch),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::query);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};

    match lbl {
        CrashAwareCachingDiskSystem::Label::Execute{req, reply} => {
            let key = req.input.arrow_QueryInput_key();
            let value = reply.output.arrow_QueryOutput_value();
            let branch_lbl = CrashAwareCachingDiskBranch::Label::Query{key, value};

            assert(post.journal == pre.journal);
            assert(new_branch == pre.branch) by {
                reveal(CrashAwareCachingDiskBranch::State::next);
                reveal(CrashAwareCachingDiskBranch::State::next_by);
                let branch_step = choose |step| CrashAwareCachingDiskBranch::State::next_by(
                    pre.branch,
                    new_branch,
                    branch_lbl,
                    step,
                );
                match branch_step {
                    CrashAwareCachingDiskBranch::Step::query(branch_msg) => {
                        reveal(CrashAwareCachingDiskBranch::State::query);
                    },
                    _ => { assert(false); },
                }
            };
            assert(pre.branch.ephemeral is Known && new_branch.frozen == pre.branch.frozen) by {
                reveal(CrashAwareCachingDiskBranch::State::next);
                reveal(CrashAwareCachingDiskBranch::State::next_by);
                let branch_step = choose |step| CrashAwareCachingDiskBranch::State::next_by(
                    pre.branch,
                    new_branch,
                    branch_lbl,
                    step,
                );
                match branch_step {
                    CrashAwareCachingDiskBranch::Step::query(branch_msg) => {
                        reveal(CrashAwareCachingDiskBranch::State::query);
                    },
                    _ => { assert(false); },
                }
            };
            assert(pre.branch.ephemeral is Known);
            assert(pre.branch.i().ephemeral is Known);
            assert(pre.branch.i().abstract_i().ephemeral is Known);
            assert(cpre.mapadt == pre.branch.i().abstract_i());
            assert(cpre.mapadt.ephemeral is Known);
            pre.branch.next_refines_to_abstract_map(new_branch, branch_lbl);
            branch_lsn_matches_coordination_map(pre);
            assert(cpre.mapadt.i().seq_end == pre.branch_lsn());
            assert(pre.journal.ephemeral is Known);
            assert(pre.journal.ephemeral->v.journal.status is Some);
            assert(pre.journal_lsn() == pre.branch_lsn());
            assert(cpre.journal == pre.journal.i_abstract());
            let journal_lbl = CrashAwareCachingDiskJournal::Label::QueryEndLsn{
                end_lsn: cpre.mapadt.i().seq_end,
            };
            assert(CrashAwareCachingDiskJournal::State::next(
                pre.journal,
                pre.journal,
                journal_lbl,
            )) by {
                reveal(CrashAwareCachingDiskJournal::State::next);
                reveal(CrashAwareCachingDiskJournal::State::next_by);
                reveal(CrashAwareCachingDiskJournal::State::query_end_lsn);
                reveal(CachingDiskJournal::State::next);
                reveal(CachingDiskJournal::State::next_by);
                reveal(CachingDiskJournal::State::query_end_lsn);
                reveal(CachedJournal::State::next);
                reveal(CachedJournal::State::next_by);
                reveal(CachedJournal::State::query_end_lsn);
                assert(CachedJournal::State::query_end_lsn(
                    pre.journal.ephemeral->v.journal,
                    pre.journal.ephemeral->v.journal,
                    CachedJournal::Label::QueryEndLsn{end_lsn: cpre.mapadt.i().seq_end},
                ));
                assert(CachedJournal::State::next_by(
                    pre.journal.ephemeral->v.journal,
                    pre.journal.ephemeral->v.journal,
                    CachedJournal::Label::QueryEndLsn{end_lsn: cpre.mapadt.i().seq_end},
                    CachedJournal::Step::query_end_lsn(),
                ));
                assert(CachedJournal::State::next(
                    pre.journal.ephemeral->v.journal,
                    pre.journal.ephemeral->v.journal,
                    CachedJournal::Label::QueryEndLsn{end_lsn: cpre.mapadt.i().seq_end},
                ));
                assert(CachingDiskJournal::State::query_end_lsn(
                    pre.journal.ephemeral->v,
                    pre.journal.ephemeral->v,
                    CachingDiskJournal::Label::QueryEndLsn{end_lsn: cpre.mapadt.i().seq_end},
                ));
                assert(CachingDiskJournal::State::next_by(
                    pre.journal.ephemeral->v,
                    pre.journal.ephemeral->v,
                    CachingDiskJournal::Label::QueryEndLsn{end_lsn: cpre.mapadt.i().seq_end},
                    CachingDiskJournal::Step::query_end_lsn(),
                ));
                assert(CachingDiskJournal::State::next(
                    pre.journal.ephemeral->v,
                    pre.journal.ephemeral->v,
                    CachingDiskJournal::Label::QueryEndLsn{end_lsn: cpre.mapadt.i().seq_end},
                ));
                assert(CrashAwareCachingDiskJournal::State::query_end_lsn(
                    pre.journal,
                    pre.journal,
                    journal_lbl,
                )) by {
                }
                assert(CrashAwareCachingDiskJournal::State::next_by(
                    pre.journal,
                    pre.journal,
                    journal_lbl,
                    CrashAwareCachingDiskJournal::Step::query_end_lsn(),
                ));
            };
            pre.journal.next_refines_abstract(pre.journal, journal_lbl);
            assert(CoordinationSystem::State::query(
                cpre,
                cpost,
                clbl,
                pre.journal.i_abstract(),
                new_branch.abstract_i(),
            )) by {
                reveal(CoordinationSystem::State::query);
            }
            assert(CoordinationSystem::State::next_by(
                cpre,
                cpost,
                clbl,
                CoordinationSystem::Step::query(
                    pre.journal.i_abstract(),
                    new_branch.abstract_i(),
                ),
            ));
        },
        _ => { assert(false); }
    }
}

proof fn put_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    new_branch: CrashAwareCachingDiskBranch::State,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskSystem::State::put(pre, post, lbl, new_journal, new_branch),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::put);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};

    match lbl {
        CrashAwareCachingDiskSystem::Label::Execute{req, reply} => {
            let key = req.input.arrow_PutInput_key();
            let value = req.input.arrow_PutInput_value();
            let msg = Message::Define{value};
            let keyed_message = KeyedMessage{key, message: msg};
            let singleton = MsgHistory::singleton_at(pre.branch_lsn(), keyed_message);
            let journal_lbl = CrashAwareCachingDiskJournal::Label::Put{records: singleton};
            let branch_lbl = CrashAwareCachingDiskBranch::Label::Append{
                keys: seq![key],
                msgs: seq![msg],
            };

            CrashAwareCachingDiskJournal::State::inv_next(pre.journal, new_journal, journal_lbl);
            reveal(CrashAwareCachingDiskJournal::State::next);
            reveal(CrashAwareCachingDiskJournal::State::next_by);
            let journal_step = choose |step| CrashAwareCachingDiskJournal::State::next_by(
                pre.journal,
                new_journal,
                journal_lbl,
                step,
            );
            match journal_step {
                CrashAwareCachingDiskJournal::Step::put(new_ephemeral) => {
                    assert(CrashAwareCachingDiskJournal::State::put(
                        pre.journal,
                        new_journal,
                        journal_lbl,
                        new_ephemeral,
                    )) by {
                        reveal(CrashAwareCachingDiskJournal::State::put);
                    }
                    pre.journal.put_refines(new_journal, journal_lbl, new_ephemeral);
                    pre.journal.allocation_next_refines_abstract(new_journal, journal_lbl);
                    assert(new_journal.frozen == pre.journal.frozen);
                },
                _ => { assert(false); },
            }
            pre.branch.next_refines_to_abstract_map(new_branch, branch_lbl);
            assert(pre.branch.ephemeral is Known && new_branch.frozen == pre.branch.frozen) by {
                reveal(CrashAwareCachingDiskBranch::State::next);
                reveal(CrashAwareCachingDiskBranch::State::next_by);
                let branch_step = choose |step| CrashAwareCachingDiskBranch::State::next_by(
                    pre.branch,
                    new_branch,
                    branch_lbl,
                    step,
                );
                match branch_step {
                    CrashAwareCachingDiskBranch::Step::append(new_ephemeral) => {
                        reveal(CrashAwareCachingDiskBranch::State::append);
                        assert(new_branch.frozen == pre.branch.frozen);
                    },
                    _ => { assert(false); },
                }
            }
            assert(new_branch.frozen == pre.branch.frozen);
            assert(post.superblockstore == pre.superblockstore);
            assert(post.journal.frozen == pre.journal.frozen);
            assert(post.branch.frozen == pre.branch.frozen);
            caching_disk_system_commit_flags_unchanged(pre, post);
            assert(cpost.superblock_landed == cpre.superblock_landed);
            assert(cpost.superblock_in_flight == cpre.superblock_in_flight);
            assert(pre.branch.i().ephemeral is Known);
            assert(pre.branch.i().abstract_i().ephemeral is Known);
            assert(cpre.mapadt == pre.branch.i().abstract_i());
            assert(cpre.mapadt.ephemeral is Known);
            branch_lsn_matches_coordination_map(pre);
            assert(cpre.mapadt.i().seq_end == pre.branch_lsn());
            let puts = append_puts(cpre.mapadt.i().seq_end, seq![key], seq![msg]);
            assert(puts == singleton) by {
                assert(cpre.mapadt.i().seq_end == pre.branch_lsn());
                assert(seq![key].len() == seq![msg].len());
                assert(seq![key].len() == 1);
                assert(puts.seq_start == singleton.seq_start);
                assert(puts.seq_end == singleton.seq_end);
                assert_maps_equal!(puts.msgs, singleton.msgs, lsn => {
                    if puts.msgs.contains_key(lsn) {
                        assert(lsn == cpre.mapadt.i().seq_end);
                        assert(lsn == pre.branch_lsn());
                        assert(puts.msgs[lsn] == singleton.msgs[lsn]);
                    }
                    if singleton.msgs.contains_key(lsn) {
                        assert(lsn == pre.branch_lsn());
                        assert(lsn == cpre.mapadt.i().seq_end);
                        assert(puts.msgs.contains_key(lsn));
                        assert(puts.msgs[lsn] == singleton.msgs[lsn]);
                    }
                });
            };
            assert(CoordinationSystem::State::put(
                cpre,
                cpost,
                clbl,
                new_journal.i_abstract(),
                new_branch.abstract_i(),
            )) by {
                reveal(CoordinationSystem::State::put);
            }
            assert(CoordinationSystem::State::next_by(
                cpre,
                cpost,
                clbl,
                CoordinationSystem::Step::put(
                    new_journal.i_abstract(),
                    new_branch.abstract_i(),
                ),
            ));
        },
        _ => { assert(false); }
    }
}

proof fn req_sync_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskSystem::State::req_sync(pre, post, lbl),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::req_sync);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};

    match lbl {
        CrashAwareCachingDiskSystem::Label::ReqSync{sync_req_id} => {
            let journal_lbl = CrashAwareCachingDiskJournal::Label::QueryEndLsn{
                end_lsn: pre.branch_lsn(),
            };
            assert(CrashAwareCachingDiskJournal::State::query_end_lsn(
                pre.journal,
                pre.journal,
                journal_lbl,
            )) by {
                reveal(CrashAwareCachingDiskJournal::State::next);
                reveal(CrashAwareCachingDiskJournal::State::next_by);
                let journal_step = choose |step| CrashAwareCachingDiskJournal::State::next_by(
                    pre.journal,
                    pre.journal,
                    journal_lbl,
                    step,
                );
                match journal_step {
                    CrashAwareCachingDiskJournal::Step::query_end_lsn() => {
                        reveal(CrashAwareCachingDiskJournal::State::query_end_lsn);
                    },
                    _ => { assert(false); },
                }
            };
            reveal(CrashAwareCachingDiskJournal::State::query_end_lsn);
            assert(pre.journal.ephemeral is Known);
            assert(pre.journal.i().ephemeral is Known);
            assert(pre.journal.i_abstract().ephemeral is Known);
            assert(cpre.journal == pre.journal.i_abstract());
            assert(cpre.journal.ephemeral is Known);
            assert(pre.branch.ephemeral is Known);
            assert(cpre.mapadt.ephemeral is Known);
            pre.journal.next_refines_abstract(pre.journal, journal_lbl);
            branch_lsn_matches_coordination_map(pre);
            assert(cpre.mapadt.i().seq_end == pre.branch_lsn());
            assert(CoordinationSystem::State::req_sync(
                cpre,
                cpost,
                clbl,
                pre.journal.i_abstract(),
            )) by {
                reveal(CoordinationSystem::State::req_sync);
            }
            assert(CoordinationSystem::State::next_by(
                cpre,
                cpost,
                clbl,
                CoordinationSystem::Step::req_sync(pre.journal.i_abstract()),
            ));
        },
        _ => { assert(false); }
    }
}

proof fn reply_sync_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskSystem::State::reply_sync(pre, post, lbl),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::reply_sync);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};

    match lbl {
        CrashAwareCachingDiskSystem::Label::ReplySync{sync_req_id} => {
            let journal_lbl = CrashAwareCachingDiskJournal::Label::QueryLsnPersistence{
                sync_lsn: pre.sync_reqs[sync_req_id],
            };
            assert(CrashAwareCachingDiskJournal::State::query_lsn_persistence(
                pre.journal,
                pre.journal,
                journal_lbl,
            )) by {
                reveal(CrashAwareCachingDiskJournal::State::next);
                reveal(CrashAwareCachingDiskJournal::State::next_by);
                let journal_step = choose |step| CrashAwareCachingDiskJournal::State::next_by(
                    pre.journal,
                    pre.journal,
                    journal_lbl,
                    step,
                );
                match journal_step {
                    CrashAwareCachingDiskJournal::Step::query_lsn_persistence() => {
                        reveal(CrashAwareCachingDiskJournal::State::query_lsn_persistence);
                    },
                    _ => { assert(false); },
                }
            };
            reveal(CrashAwareCachingDiskJournal::State::query_lsn_persistence);
            pre.journal.next_refines_abstract(pre.journal, journal_lbl);
            assert(CoordinationSystem::State::reply_sync(
                cpre,
                cpost,
                clbl,
                pre.journal.i_abstract(),
            )) by {
                reveal(CoordinationSystem::State::reply_sync);
            }
            assert(CoordinationSystem::State::next_by(
                cpre,
                cpost,
                clbl,
                CoordinationSystem::Step::reply_sync(pre.journal.i_abstract()),
            ));
        },
        _ => { assert(false); }
    }
}

proof fn journal_next_crash_is_crash(
    pre: CrashAwareCachingDiskJournal::State,
    post: CrashAwareCachingDiskJournal::State,
    lbl: CrashAwareCachingDiskJournal::Label,
)
    requires
        CrashAwareCachingDiskJournal::State::next(pre, post, lbl),
        lbl is Crash,
    ensures
        exists |prepared_image: CachingDiskJournalImage|
            CrashAwareCachingDiskJournal::State::crash(pre, post, lbl, prepared_image),
{
    reveal(CrashAwareCachingDiskJournal::State::next);
    reveal(CrashAwareCachingDiskJournal::State::next_by);
    let step = choose |step| CrashAwareCachingDiskJournal::State::next_by(pre, post, lbl, step);
    match step {
        CrashAwareCachingDiskJournal::Step::crash(prepared_image) => {
            reveal(CrashAwareCachingDiskJournal::State::crash);
        },
        _ => { assert(false); },
    }
}

proof fn branch_next_crash_is_crash(
    pre: CrashAwareCachingDiskBranch::State,
    post: CrashAwareCachingDiskBranch::State,
    lbl: CrashAwareCachingDiskBranch::Label,
)
    requires
        CrashAwareCachingDiskBranch::State::next(pre, post, lbl),
        lbl is Crash,
    ensures
        exists |prepared_image: CachingDiskBranchImage|
            CrashAwareCachingDiskBranch::State::crash(pre, post, lbl, prepared_image),
{
    reveal(CrashAwareCachingDiskBranch::State::next);
    reveal(CrashAwareCachingDiskBranch::State::next_by);
    let step = choose |step| CrashAwareCachingDiskBranch::State::next_by(pre, post, lbl, step);
    match step {
        CrashAwareCachingDiskBranch::Step::crash(prepared_image) => {
            reveal(CrashAwareCachingDiskBranch::State::crash);
        },
        _ => { assert(false); },
    }
}

proof fn journal_crash_refines_abstract_light(
    pre: CrashAwareCachingDiskJournal::State,
    post: CrashAwareCachingDiskJournal::State,
    keep_in_flight: bool,
    prepared_image: CachingDiskJournalImage,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskJournal::State::crash(
            pre,
            post,
            CrashAwareCachingDiskJournal::Label::Crash{keep_in_flight},
            prepared_image,
        ),
    ensures
        AbstractCrashAwareJournal::State::next(
            pre.i_abstract(),
            post.i_abstract(),
            AbstractCrashAwareJournal::Label::CrashLabel{keep_in_flight},
        ),
{
    let lbl = CrashAwareCachingDiskJournal::Label::Crash{keep_in_flight};
    assert(CrashAwareCachingDiskJournal::State::next_by(
        pre,
        post,
        lbl,
        CrashAwareCachingDiskJournal::Step::crash(prepared_image),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next_by);
    }
    assert(CrashAwareCachingDiskJournal::State::next(pre, post, lbl)) by {
        reveal(CrashAwareCachingDiskJournal::State::next);
    }
    pre.next_refines_abstract(post, lbl);
}

proof fn branch_crash_refines_abstract_light(
    pre: CrashAwareCachingDiskBranch::State,
    post: CrashAwareCachingDiskBranch::State,
    keep_in_flight: bool,
    prepared_image: CachingDiskBranchImage,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskBranch::State::crash(
            pre,
            post,
            CrashAwareCachingDiskBranch::Label::Crash{keep_in_flight},
            prepared_image,
        ),
    ensures
        AbstractCrashAwareMap::State::next(
            pre.abstract_i(),
            post.abstract_i(),
            AbstractCrashAwareMap::Label::CrashLabel{keep_in_flight},
        ),
{
    let lbl = CrashAwareCachingDiskBranch::Label::Crash{keep_in_flight};
    assert(CrashAwareCachingDiskBranch::State::next_by(
        pre,
        post,
        lbl,
        CrashAwareCachingDiskBranch::Step::crash(prepared_image),
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next_by);
    }
    assert(CrashAwareCachingDiskBranch::State::next(pre, post, lbl)) by {
        reveal(CrashAwareCachingDiskBranch::State::next);
    }
    pre.next_refines_to_abstract_map(post, lbl);
}

proof fn crash_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    new_branch: CrashAwareCachingDiskBranch::State,
    new_superblock: SuperblockStore::State,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskSystem::State::crash(pre, post, lbl, new_journal, new_branch, new_superblock),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::crash);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};
    let keep_in_flight = pre.superblockstore.landed;
    let journal_lbl = CrashAwareCachingDiskJournal::Label::Crash{keep_in_flight};
    let branch_lbl = CrashAwareCachingDiskBranch::Label::Crash{keep_in_flight};
    journal_next_crash_is_crash(pre.journal, new_journal, journal_lbl);
    branch_next_crash_is_crash(pre.branch, new_branch, branch_lbl);
    let prepared_journal_image = choose |prepared_image: CachingDiskJournalImage|
        CrashAwareCachingDiskJournal::State::crash(
            pre.journal,
            new_journal,
            journal_lbl,
            prepared_image,
        );
    let prepared_branch_image = choose |prepared_image: CachingDiskBranchImage|
        CrashAwareCachingDiskBranch::State::crash(
            pre.branch,
            new_branch,
            branch_lbl,
            prepared_image,
        );
    journal_crash_refines_abstract_light(
        pre.journal,
        new_journal,
        keep_in_flight,
        prepared_journal_image,
    );
    branch_crash_refines_abstract_light(
        pre.branch,
        new_branch,
        keep_in_flight,
        prepared_branch_image,
    );
    assert(new_superblock.in_flight is None && !new_superblock.landed) by {
        reveal(SuperblockStore::State::next);
        reveal(SuperblockStore::State::next_by);
        assert(SuperblockStore::State::next_by(
            pre.superblockstore,
            new_superblock,
            SuperblockStore::Label::Crash,
            SuperblockStore::Step::crash(),
        ));
        reveal(SuperblockStore::State::crash);
    }
    assert(cpost.superblock_in_flight == false);
    assert(cpre.superblock_landed == keep_in_flight);
    assert(CoordinationSystem::State::crash(
        cpre,
        cpost,
        clbl,
        new_journal.i_abstract(),
        new_branch.abstract_i(),
    )) by {
        reveal(CoordinationSystem::State::crash);
    }
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::crash(
            new_journal.i_abstract(),
            new_branch.abstract_i(),
        ),
    ));
}

proof fn recover_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    new_branch: CrashAwareCachingDiskBranch::State,
    records: crate::abstract_system::MsgHistory_v::MsgHistory,
    keys: Seq<crate::spec::KeyType_t::Key>,
    msgs: Seq<Message>,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskSystem::State::recover(pre, post, lbl, new_journal, new_branch, records, keys, msgs),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::recover);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};
    let journal_lbl = CrashAwareCachingDiskJournal::Label::ReadForRecovery{records};
    let branch_lbl = CrashAwareCachingDiskBranch::Label::Append{keys, msgs};

    assert(CrashAwareCachingDiskJournal::State::read_for_recovery(
        pre.journal,
        new_journal,
        journal_lbl,
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next);
        reveal(CrashAwareCachingDiskJournal::State::next_by);
        let journal_step = choose |step| CrashAwareCachingDiskJournal::State::next_by(
            pre.journal,
            new_journal,
            journal_lbl,
            step,
        );
        match journal_step {
            CrashAwareCachingDiskJournal::Step::read_for_recovery() => {
                reveal(CrashAwareCachingDiskJournal::State::read_for_recovery);
            },
            _ => { assert(false); },
        }
    };
    reveal(CrashAwareCachingDiskJournal::State::read_for_recovery);
    assert(new_journal == pre.journal);
    assert(cpre.journal == pre.journal.i_abstract());
    assert(cpre.mapadt == pre.branch.i().abstract_i());
    pre.journal.next_refines_abstract(new_journal, journal_lbl);
    pre.branch.next_refines_to_abstract_map(new_branch, branch_lbl);
    assert(new_branch.frozen == pre.branch.frozen && new_branch.ephemeral is Known && keys.len() == msgs.len()) by {
        reveal(CrashAwareCachingDiskBranch::State::next);
        reveal(CrashAwareCachingDiskBranch::State::next_by);
        let branch_step = choose |step| CrashAwareCachingDiskBranch::State::next_by(
            pre.branch,
            new_branch,
            branch_lbl,
            step,
        );
        match branch_step {
            CrashAwareCachingDiskBranch::Step::append(new_ephemeral) => {
                reveal(CrashAwareCachingDiskBranch::State::append);
                let active_lbl = CachingDiskBranch::Label::AppendLabel{keys, msgs};
                assert(CachingDiskBranch::State::next(
                    pre.branch.ephemeral->v,
                    new_ephemeral,
                    active_lbl,
                ));
                assert(keys.len() == msgs.len()) by {
                    reveal(CachingDiskBranch::State::next);
                    reveal(CachingDiskBranch::State::next_by);
                    reveal(CachedBranch::State::next);
                    reveal(CachedBranch::State::next_by);
                    let active_step = choose |step| CachingDiskBranch::State::next_by(
                        pre.branch.ephemeral->v,
                        new_ephemeral,
                        active_lbl,
                        step,
                    );
                    match active_step {
                        CachingDiskBranch::Step::append(new_disk, new_active_branch, receipt, init_root, reads, writes) => {
                            reveal(CachingDiskBranch::State::append);
                            let read_nodes = to_branch_nodes(reads);
                            let write_nodes = to_branch_nodes(writes);
                            if pre.branch.ephemeral->v.active_branch.root is Some {
                                let branch_lbl = CachedBranch::Label::Append{
                                    mini_allocator: pre.branch.ephemeral->v.mini_allocator,
                                    receipt,
                                    keys,
                                    msgs,
                                    read_nodes,
                                    write_nodes,
                                };
                                assert(CachedBranch::State::next(
                                    pre.branch.ephemeral->v.active_branch,
                                    new_active_branch,
                                    branch_lbl,
                                ));
                                let cached_step = choose |step|
                                    CachedBranch::State::next_by(
                                        pre.branch.ephemeral->v.active_branch,
                                        new_active_branch,
                                        branch_lbl,
                                        step,
                                    );
                                match cached_step {
                                    CachedBranch::Step::append_step() => {
                                        reveal(CachedBranch::State::append_step);
                                        assert(loaded_append_ready(receipt, read_nodes, keys, msgs));
                                    },
                                    _ => { assert(false); },
                                }
                            } else {
                                assert(init_root is Some);
                                let branch_lbl = CachedBranch::Label::Initialize{
                                    mini_allocator: pre.branch.ephemeral->v.mini_allocator,
                                    init_root: init_root.unwrap(),
                                    keys,
                                    msgs,
                                    write_nodes,
                                };
                                assert(CachedBranch::State::next(
                                    pre.branch.ephemeral->v.active_branch,
                                    new_active_branch,
                                    branch_lbl,
                                ));
                                let cached_step = choose |step|
                                    CachedBranch::State::next_by(
                                        pre.branch.ephemeral->v.active_branch,
                                        new_active_branch,
                                        branch_lbl,
                                        step,
                                    );
                                match cached_step {
                                    CachedBranch::Step::initialize_branch() => {
                                        reveal(CachedBranch::State::initialize_branch);
                                    },
                                    _ => { assert(false); },
                                }
                            }
                        },
                        _ => { assert(false); },
                    }
                };
            },
            _ => { assert(false); },
        }
    };
    assert(keys.len() == msgs.len());
    assert(cpost.superblock_landed == cpre.superblock_landed);
    assert(pre.branch.ephemeral is Known) by {
        reveal(CrashAwareCachingDiskBranch::State::next);
        reveal(CrashAwareCachingDiskBranch::State::next_by);
        let branch_step = choose |step| CrashAwareCachingDiskBranch::State::next_by(
            pre.branch,
            new_branch,
            branch_lbl,
            step,
        );
        match branch_step {
            CrashAwareCachingDiskBranch::Step::append(new_ephemeral) => {
                reveal(CrashAwareCachingDiskBranch::State::append);
            },
            _ => { assert(false); },
        }
    };
    assert(cpre.mapadt.ephemeral is Known);
    branch_lsn_matches_coordination_map(pre);
    assert(records == append_puts(pre.branch_lsn(), keys, msgs));
    assert(records == append_puts(cpre.mapadt.i().seq_end, keys, msgs));
    append_puts_wf(cpre.mapadt.i().seq_end, keys, msgs);
    assert(records.wf());
    assert(CoordinationSystem::State::recover(
        cpre,
        cpost,
        clbl,
        new_journal.i_abstract(),
        new_branch.abstract_i(),
        records,
    )) by {
        reveal(CoordinationSystem::State::recover);
    }
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::recover(
            new_journal.i_abstract(),
            new_branch.abstract_i(),
            records,
        ),
    ));
}

proof fn journal_internal_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskSystem::State::journal_internal(pre, post, lbl, new_journal),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::journal_internal);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};
    let journal_lbl = CrashAwareCachingDiskJournal::Label::Internal;

    pre.journal.next_refines_abstract(new_journal, journal_lbl);
    assert(post.journal == new_journal);
    journal_step_preserves_frozen(pre.journal, new_journal, journal_lbl);
    assert(post.journal.frozen == pre.journal.frozen);
    assert(post.branch.frozen == pre.branch.frozen);
    assert(post.superblockstore == pre.superblockstore);
    caching_disk_system_commit_flags_unchanged(pre, post);
    assert(CoordinationSystem::State::journal_internal(
        cpre,
        cpost,
        clbl,
        new_journal.i_abstract(),
    )) by {
        reveal(CoordinationSystem::State::journal_internal);
    }
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::journal_internal(new_journal.i_abstract()),
    ));
}

proof fn journal_load_index_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    discovered_aus: Set<AU>,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskSystem::State::journal_load_index(
            pre,
            post,
            lbl,
            new_journal,
            discovered_aus,
        ),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::journal_load_index);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};
    let journal_lbl = CrashAwareCachingDiskJournal::Label::LoadIndex{discovered_aus};

    pre.journal.next_refines_abstract(new_journal, journal_lbl);
    assert(post.journal == new_journal);
    journal_step_preserves_frozen(pre.journal, new_journal, journal_lbl);
    assert(post.journal.frozen == pre.journal.frozen);
    assert(post.branch.frozen == pre.branch.frozen);
    assert(post.superblockstore == pre.superblockstore);
    caching_disk_system_commit_flags_unchanged(pre, post);
    assert(CoordinationSystem::State::journal_internal(
        cpre,
        cpost,
        clbl,
        new_journal.i_abstract(),
    )) by {
        reveal(CoordinationSystem::State::journal_internal);
    }
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::journal_internal(new_journal.i_abstract()),
    ));
}

proof fn journal_internal_alloc_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    prune_aus: Set<AU>,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskSystem::State::journal_internal_alloc(
            pre,
            post,
            lbl,
            new_journal,
            allocs,
            deallocs,
            prune_aus,
        ),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::journal_internal_alloc);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};
    let journal_lbl = CrashAwareCachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus};

    pre.journal.next_refines_abstract(new_journal, journal_lbl);
    assert(post.journal == new_journal);
    journal_step_preserves_frozen(pre.journal, new_journal, journal_lbl);
    assert(post.journal.frozen == pre.journal.frozen);
    assert(post.branch.frozen == pre.branch.frozen);
    assert(post.superblockstore == pre.superblockstore);
    caching_disk_system_commit_flags_unchanged(pre, post);
    assert(CoordinationSystem::State::journal_internal(
        cpre,
        cpost,
        clbl,
        new_journal.i_abstract(),
    )) by {
        reveal(CoordinationSystem::State::journal_internal);
    }
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::journal_internal(new_journal.i_abstract()),
    ));
}

proof fn map_internal_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
    new_branch: CrashAwareCachingDiskBranch::State,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskSystem::State::map_internal(pre, post, lbl, new_branch),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::map_internal);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};
    let branch_lbl = CrashAwareCachingDiskBranch::Label::Internal;

    pre.branch.next_refines_to_abstract_map(new_branch, branch_lbl);
    branch_step_preserves_frozen(pre.branch, new_branch, branch_lbl);
    assert(post.journal.frozen == pre.journal.frozen);
    assert(post.branch.frozen == pre.branch.frozen);
    assert(post.superblockstore == pre.superblockstore);
    caching_disk_system_commit_flags_unchanged(pre, post);
    assert(CoordinationSystem::State::map_internal(
        cpre,
        cpost,
        clbl,
        new_branch.abstract_i(),
    )) by {
        reveal(CoordinationSystem::State::map_internal);
    }
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::map_internal(new_branch.abstract_i()),
    ));
}

proof fn map_load_metadata_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
    new_branch: CrashAwareCachingDiskBranch::State,
    root: Address,
    discovered_aus: Set<AU>,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskSystem::State::map_load_metadata(
            pre,
            post,
            lbl,
            new_branch,
            root,
            discovered_aus,
        ),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::map_load_metadata);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};
    let branch_lbl = CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus};

    pre.branch.next_refines_to_abstract_map(new_branch, branch_lbl);
    branch_step_preserves_frozen(pre.branch, new_branch, branch_lbl);
    assert(post.journal.frozen == pre.journal.frozen);
    assert(post.branch.frozen == pre.branch.frozen);
    assert(post.superblockstore == pre.superblockstore);
    caching_disk_system_commit_flags_unchanged(pre, post);
    assert(CoordinationSystem::State::map_internal(
        cpre,
        cpost,
        clbl,
        new_branch.abstract_i(),
    )) by {
        reveal(CoordinationSystem::State::map_internal);
    }
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::map_internal(new_branch.abstract_i()),
    ));
}

proof fn map_internal_alloc_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
    new_branch: CrashAwareCachingDiskBranch::State,
    allocs: Set<AU>,
    deallocs: Set<AU>,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskSystem::State::map_internal_alloc(
            pre,
            post,
            lbl,
            new_branch,
            allocs,
            deallocs,
        ),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::map_internal_alloc);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};
    let branch_lbl = CrashAwareCachingDiskBranch::Label::InternalAlloc{allocs, deallocs};

    pre.branch.next_refines_to_abstract_map(new_branch, branch_lbl);
    branch_step_preserves_frozen(pre.branch, new_branch, branch_lbl);
    assert(post.journal.frozen == pre.journal.frozen);
    assert(post.branch.frozen == pre.branch.frozen);
    assert(post.superblockstore == pre.superblockstore);
    caching_disk_system_commit_flags_unchanged(pre, post);
    assert(CoordinationSystem::State::map_internal(
        cpre,
        cpost,
        clbl,
        new_branch.abstract_i(),
    )) by {
        reveal(CoordinationSystem::State::map_internal);
    }
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::map_internal(new_branch.abstract_i()),
    ));
}

proof fn commit_prepared_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    new_branch: CrashAwareCachingDiskBranch::State,
    new_superblock: SuperblockStore::State,
    raw_page: RawPage,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskSystem::State::commit_prepared(
            pre,
            post,
            lbl,
            new_journal,
            new_branch,
            new_superblock,
            raw_page,
        ),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::commit_prepared);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};

    assert(pre.commit_started());
    journal_step_preserves_frozen(pre.journal, new_journal, CrashAwareCachingDiskJournal::Label::CommitPrepared);
    branch_step_preserves_frozen(pre.branch, new_branch, CrashAwareCachingDiskBranch::Label::FreezePrepared);
    assert(post.journal == new_journal);
    assert(post.branch == new_branch);
    assert(post.commit_started() == pre.commit_started());
    assert(CrashAwareCachingDiskJournal::State::commit_prepared(
        pre.journal,
        new_journal,
        CrashAwareCachingDiskJournal::Label::CommitPrepared,
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next);
        reveal(CrashAwareCachingDiskJournal::State::next_by);
        let step = choose |step| CrashAwareCachingDiskJournal::State::next_by(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::CommitPrepared,
            step,
        );
        match step {
            CrashAwareCachingDiskJournal::Step::commit_prepared() => {},
            _ => { assert(false); },
        }
    }
    CrashAwareCachingDiskJournal::State::inv_next(
        pre.journal,
        new_journal,
        CrashAwareCachingDiskJournal::Label::CommitPrepared,
    );
    pre.journal.commit_prepared_refines(
        new_journal,
        CrashAwareCachingDiskJournal::Label::CommitPrepared,
    );
    assert(CrashAwareCachingDiskBranch::State::freeze_prepared(
        pre.branch,
        new_branch,
        CrashAwareCachingDiskBranch::Label::FreezePrepared,
    )) by {
        reveal(CrashAwareCachingDiskBranch::State::next);
        reveal(CrashAwareCachingDiskBranch::State::next_by);
        let step = choose |step| CrashAwareCachingDiskBranch::State::next_by(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranch::Label::FreezePrepared,
            step,
        );
        match step {
            CrashAwareCachingDiskBranch::Step::freeze_prepared() => {},
            _ => { assert(false); },
        }
    }
    CrashAwareCachingDiskBranch::State::inv_next(
        pre.branch,
        new_branch,
        CrashAwareCachingDiskBranch::Label::FreezePrepared,
    );
    pre.branch.freeze_prepared_preserves_i(new_branch);
    assert(!pre.superblockstore.landed) by {
        reveal(SuperblockStore::State::next);
        reveal(SuperblockStore::State::next_by);
        let store_step = choose |step| SuperblockStore::State::next_by(
            pre.superblockstore,
            new_superblock,
            SuperblockStore::Label::Write{raw: raw_page},
            step,
        );
        match store_step {
            SuperblockStore::Step::write() => {
                reveal(SuperblockStore::State::write);
            },
            _ => { assert(false); },
        }
    }
    assert(post.superblockstore == new_superblock);
    assert(!post.superblockstore.landed) by {
        reveal(SuperblockStore::State::next);
        reveal(SuperblockStore::State::next_by);
        let store_step = choose |step| SuperblockStore::State::next_by(
            pre.superblockstore,
            new_superblock,
            SuperblockStore::Label::Write{raw: raw_page},
            step,
        );
        match store_step {
            SuperblockStore::Step::write() => {
                reveal(SuperblockStore::State::write);
            },
            _ => { assert(false); },
        }
    }
    assert(cpre.superblock_in_flight == true);
    assert(cpost.superblock_in_flight == true);
    assert(cpre.superblock_landed == false);
    assert(cpost.superblock_landed == false);
    assert(new_journal.i() == pre.journal.i());
    assert(new_journal.i_abstract() == pre.journal.i_abstract());
    assert(new_branch.i() == pre.branch.i());
    assert(new_branch.abstract_i() == pre.branch.abstract_i());
    assert(cpre.journal == cpost.journal);
    assert(cpre.mapadt == cpost.mapadt);
    assert(cpre == cpost) by {
        reveal(caching_disk_system_coordination_i);
    }
    assert(CoordinationSystem::State::noop(cpre, cpost, clbl)) by {
        reveal(CoordinationSystem::State::noop);
    }
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::noop(),
    ));
}

proof fn load_ephemeral_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    new_branch: CrashAwareCachingDiskBranch::State,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskSystem::State::load_ephemeral_from_persistent(
            pre,
            post,
            lbl,
            new_journal,
            new_branch,
        ),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::load_ephemeral_from_persistent);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};
    let journal_lbl = CrashAwareCachingDiskJournal::Label::LoadEphemeral;
    let branch_lbl = CrashAwareCachingDiskBranch::Label::LoadEphemeral;

    pre.journal.next_refines_abstract(new_journal, journal_lbl);
    pre.branch.next_refines_to_abstract_map(new_branch, branch_lbl);
    assert(new_journal.frozen == pre.journal.frozen) by {
        reveal(CrashAwareCachingDiskJournal::State::next);
        reveal(CrashAwareCachingDiskJournal::State::next_by);
        let journal_step = choose |step| CrashAwareCachingDiskJournal::State::next_by(
            pre.journal,
            new_journal,
            journal_lbl,
            step,
        );
        match journal_step {
            CrashAwareCachingDiskJournal::Step::load_ephemeral() => {
                reveal(CrashAwareCachingDiskJournal::State::load_ephemeral);
            },
            _ => { assert(false); },
        }
    }
    assert(new_branch.frozen == pre.branch.frozen) by {
        reveal(CrashAwareCachingDiskBranch::State::next);
        reveal(CrashAwareCachingDiskBranch::State::next_by);
        let branch_step = choose |step| CrashAwareCachingDiskBranch::State::next_by(
            pre.branch,
            new_branch,
            branch_lbl,
            step,
        );
        match branch_step {
            CrashAwareCachingDiskBranch::Step::load_ephemeral(new_ephemeral) => {
                reveal(CrashAwareCachingDiskBranch::State::load_ephemeral);
            },
            _ => { assert(false); },
        }
    }
    assert(post.journal.frozen == pre.journal.frozen);
    assert(post.branch.frozen == pre.branch.frozen);
    assert(post.superblockstore == pre.superblockstore);
    caching_disk_system_commit_flags_unchanged(pre, post);
    assert(CoordinationSystem::State::load_ephemeral_from_persistent(
        cpre,
        cpost,
        clbl,
        new_journal.i_abstract(),
        new_branch.abstract_i(),
    )) by {
        reveal(CoordinationSystem::State::load_ephemeral_from_persistent);
    }
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::load_ephemeral_from_persistent(
            new_journal.i_abstract(),
            new_branch.abstract_i(),
        ),
    ));
}

proof fn commit_start_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    new_branch: CrashAwareCachingDiskBranch::State,
    superblock_image: AbstractSuperblockImage,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskSystem::State::commit_start(
            pre,
            post,
            lbl,
            new_journal,
            new_branch,
            superblock_image,
        ),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::commit_start);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};
    let new_boundary_lsn = superblock_image.branch_seq_end;
    let journal_lbl = CrashAwareCachingDiskJournal::Label::CommitStart{
        new_boundary_lsn,
        snapshot: superblock_image.journal_snapshot,
        seq_end: superblock_image.journal_seq_end,
    };
    let branch_lbl = CrashAwareCachingDiskBranch::Label::CommitStart{
        new_boundary_lsn,
        sealed_roots: superblock_image.branch_roots,
    };

    pre.journal.next_refines_abstract(new_journal, journal_lbl);
    pre.branch.next_refines_to_abstract_map(new_branch, branch_lbl);
    assert(pre.journal.frozen is None && new_journal.frozen is Some) by {
        reveal(CrashAwareCachingDiskJournal::State::next);
        reveal(CrashAwareCachingDiskJournal::State::next_by);
        let journal_step = choose |step| CrashAwareCachingDiskJournal::State::next_by(
            pre.journal,
            new_journal,
            journal_lbl,
            step,
        );
        match journal_step {
            CrashAwareCachingDiskJournal::Step::commit_start() => {
                reveal(CrashAwareCachingDiskJournal::State::commit_start);
            },
            _ => { assert(false); },
        }
    }
    assert(pre.branch.frozen is None && new_branch.frozen is Some) by {
        reveal(CrashAwareCachingDiskBranch::State::next);
        reveal(CrashAwareCachingDiskBranch::State::next_by);
        let branch_step = choose |step| CrashAwareCachingDiskBranch::State::next_by(
            pre.branch,
            new_branch,
            branch_lbl,
            step,
        );
        match branch_step {
            CrashAwareCachingDiskBranch::Step::commit_start() => {
                reveal(CrashAwareCachingDiskBranch::State::commit_start);
            },
            _ => { assert(false); },
        }
    }
    assert(!pre.commit_started());
    assert(!pre.superblockstore.landed);
    assert(post.commit_started());
    assert(post.superblockstore == pre.superblockstore);
    assert(!post.superblockstore.landed);
    assert(cpre.superblock_in_flight == false);
    assert(cpre.superblock_landed == false);
    assert(cpost.superblock_in_flight == true);
    assert(cpost.superblock_landed == false);
    assert(new_journal.i_abstract().frozen is Some) by {
        reveal(CrashAwareCachingDiskJournal::State::next);
        reveal(CrashAwareCachingDiskJournal::State::next_by);
        let journal_step = choose |step| CrashAwareCachingDiskJournal::State::next_by(
            pre.journal,
            new_journal,
            journal_lbl,
            step,
        );
        match journal_step {
            CrashAwareCachingDiskJournal::Step::commit_start() => {
                reveal(CrashAwareCachingDiskJournal::State::commit_start);
            },
            _ => { assert(false); },
        }
    }
    assert(new_branch.abstract_i().frozen is Some) by {
        reveal(CrashAwareCachingDiskBranch::State::next);
        reveal(CrashAwareCachingDiskBranch::State::next_by);
        let branch_step = choose |step| CrashAwareCachingDiskBranch::State::next_by(
            pre.branch,
            new_branch,
            branch_lbl,
            step,
        );
        match branch_step {
            CrashAwareCachingDiskBranch::Step::commit_start() => {
                reveal(CrashAwareCachingDiskBranch::State::commit_start);
            },
            _ => { assert(false); },
        }
    }
    let frozen_journal = new_journal.i_abstract().frozen.unwrap();
    let frozen_map = new_branch.abstract_i().frozen.unwrap();
    assert(pre.journal.label_i_abstract(new_journal, journal_lbl)
        == AbstractCrashAwareJournal::Label::CommitStartLabel{
            new_boundary_lsn,
            frozen_journal,
        });
    assert(pre.branch.label_to_abstract_map(new_branch, branch_lbl)
        == AbstractCrashAwareMap::Label::CommitStartLabel{
            new_boundary_lsn,
            frozen_map,
        });
    assert(CoordinationSystem::State::commit_start(
        cpre,
        cpost,
        clbl,
        new_boundary_lsn,
        frozen_journal,
        frozen_map,
        new_journal.i_abstract(),
        new_branch.abstract_i(),
    )) by {
        reveal(CoordinationSystem::State::commit_start);
    }
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::commit_start(
            new_boundary_lsn,
            frozen_journal,
            frozen_map,
            new_journal.i_abstract(),
            new_branch.abstract_i(),
        ),
    ));
}

proof fn superblock_write_lands_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
    new_superblock: SuperblockStore::State,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskSystem::State::superblock_write_lands(pre, post, lbl, new_superblock),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::superblock_write_lands);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};

    assert(new_superblock.in_flight is None && new_superblock.landed) by {
        reveal(SuperblockStore::State::next);
        reveal(SuperblockStore::State::next_by);
        assert(SuperblockStore::State::next_by(
            pre.superblockstore,
            new_superblock,
            SuperblockStore::Label::Land,
            SuperblockStore::Step::land(),
        ));
        reveal(SuperblockStore::State::land);
    }
    assert(pre.superblockstore.in_flight is Some) by {
        reveal(SuperblockStore::State::next);
        reveal(SuperblockStore::State::next_by);
        assert(SuperblockStore::State::next_by(
            pre.superblockstore,
            new_superblock,
            SuperblockStore::Label::Land,
            SuperblockStore::Step::land(),
        ));
        reveal(SuperblockStore::State::land);
    }
    assert(cpre.superblock_in_flight == true);
    assert(cpost.superblock_in_flight == false);
    assert(cpost.superblock_landed == true);
    assert(CoordinationSystem::State::superblock_write_lands(cpre, cpost, clbl)) by {
        reveal(CoordinationSystem::State::superblock_write_lands);
    }
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::superblock_write_lands(),
    ));
}

proof fn commit_complete_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
    new_journal: CrashAwareCachingDiskJournal::State,
    new_branch: CrashAwareCachingDiskBranch::State,
    new_superblock: SuperblockStore::State,
    discarded: Set<AU>,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskSystem::State::commit_complete(
            pre,
            post,
            lbl,
            new_journal,
            new_branch,
            new_superblock,
            discarded,
        ),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::commit_complete);
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(caching_disk_system_coordination_i);

    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};
    let journal_lbl = CrashAwareCachingDiskJournal::Label::CommitComplete{
        require_end: pre.branch_lsn(),
        discarded,
    };
    let branch_lbl = CrashAwareCachingDiskBranch::Label::CommitComplete;

    pre.journal.next_refines_abstract(new_journal, journal_lbl);
    pre.branch.next_refines_to_abstract_map(new_branch, branch_lbl);
    assert(new_superblock.in_flight is None && new_superblock.landed == false) by {
        reveal(SuperblockStore::State::next);
        reveal(SuperblockStore::State::next_by);
        assert(SuperblockStore::State::next_by(
            pre.superblockstore,
            new_superblock,
            SuperblockStore::Label::Complete,
            SuperblockStore::Step::complete(),
        ));
        reveal(SuperblockStore::State::complete);
    }
    assert(pre.superblockstore.landed) by {
        reveal(SuperblockStore::State::next);
        reveal(SuperblockStore::State::next_by);
        assert(SuperblockStore::State::next_by(
            pre.superblockstore,
            new_superblock,
            SuperblockStore::Label::Complete,
            SuperblockStore::Step::complete(),
        ));
        reveal(SuperblockStore::State::complete);
    }
    assert(cpre.superblock_landed == true) by {
        reveal(caching_disk_system_coordination_i);
    }
    assert(cpre.superblock_in_flight == false);
    assert(new_journal.frozen is None) by {
        reveal(CrashAwareCachingDiskJournal::State::next);
        reveal(CrashAwareCachingDiskJournal::State::next_by);
        let journal_step = choose |step| CrashAwareCachingDiskJournal::State::next_by(
            pre.journal,
            new_journal,
            journal_lbl,
            step,
        );
        match journal_step {
            CrashAwareCachingDiskJournal::Step::commit_complete(new_ephemeral, prepared_image) => {
                reveal(CrashAwareCachingDiskJournal::State::commit_complete);
            },
            _ => { assert(false); },
        }
    }
    assert(new_branch.frozen is None) by {
        reveal(CrashAwareCachingDiskBranch::State::next);
        reveal(CrashAwareCachingDiskBranch::State::next_by);
        let branch_step = choose |step| CrashAwareCachingDiskBranch::State::next_by(
            pre.branch,
            new_branch,
            branch_lbl,
            step,
        );
        match branch_step {
            CrashAwareCachingDiskBranch::Step::commit_complete(prepared_image) => {
                reveal(CrashAwareCachingDiskBranch::State::commit_complete);
            },
            _ => { assert(false); },
        }
    }
    assert(post.journal == new_journal);
    assert(post.branch == new_branch);
    assert(!post.commit_started());
    assert(cpost.superblock_landed == false);
    assert(cpost.superblock_in_flight == false) by {
        reveal(caching_disk_system_coordination_i);
    }
    assert(cpre.mapadt.ephemeral is Known) by {
        reveal(CrashAwareCachingDiskBranch::State::next);
        reveal(CrashAwareCachingDiskBranch::State::next_by);
        let branch_step = choose |step| CrashAwareCachingDiskBranch::State::next_by(
            pre.branch,
            new_branch,
            branch_lbl,
            step,
        );
        match branch_step {
            CrashAwareCachingDiskBranch::Step::commit_complete(prepared_image) => {
                reveal(CrashAwareCachingDiskBranch::State::commit_complete);
            },
            _ => { assert(false); },
        }
    }
    branch_lsn_matches_coordination_map(pre);
    assert(CoordinationSystem::State::commit_complete(
        cpre,
        cpost,
        clbl,
        new_branch.abstract_i(),
        new_journal.i_abstract(),
    )) by {
        reveal(CoordinationSystem::State::commit_complete);
    }
    assert(CoordinationSystem::State::next_by(
        cpre,
        cpost,
        clbl,
        CoordinationSystem::Step::commit_complete(
            new_branch.abstract_i(),
            new_journal.i_abstract(),
        ),
    ));
}

pub proof fn init_refines_ctam(model: CrashAwareCachingDiskSystem::State)
    requires
        CrashAwareCachingDiskSystem::State::init(model),
    ensures
        model.inv(),
        CrashTolerantAsyncMap::State::init(caching_disk_system_i(model)),
{
    reveal(CrashAwareCachingDiskSystem::State::init);
    reveal(CrashAwareCachingDiskSystem::State::init_by);
    reveal(caching_disk_system_coordination_i);

    let config = choose |config| CrashAwareCachingDiskSystem::State::init_by(model, config);
    match config {
        CrashAwareCachingDiskSystem::Config::initialize(free_aus, initial_superblock, journal, branch) => {
            assert(CrashAwareCachingDiskSystem::State::initialize(
                model,
                free_aus,
                initial_superblock,
                journal,
                branch,
            )) by {
                reveal(CrashAwareCachingDiskSystem::State::initialize);
            }
            reveal(CrashAwareCachingDiskSystem::State::initialize);
            assert(model.journal == journal);
            assert(model.branch == branch);
            reveal(CrashAwareCachingDiskJournal::State::initialize);
            JournalImage::empty_is_valid_image();
            assert(journal.persistent == CachingDiskJournalImage::empty());
            assert(journal.persistent.i() == JournalImage::empty());
            assert(journal.persistent.wf());
            assert(journal.inv());
            reveal(CrashAwareCachingDiskBranch::State::initialize);
            empty_caching_disk_branch_image_wf();
            assert(branch.persistent == empty_caching_disk_branch_image());
            assert(branch.persistent.stack_wf());
            assert(branch.inv());
            assert(model.journal.inv());
            assert(model.branch.inv());
            assert(model.components_wf());
            CrashAwareCachingDiskSystem::State::initialize_inductive(
                model,
                free_aus,
                initial_superblock,
                journal,
                branch,
            );
            assert(model.inv());
            journal.init_refines_abstract();
            branch.init_refines_to_abstract_map();
            CrashAwareCachingDiskJournal::show::initialize(journal);
            CrashAwareCachingDiskBranch::show::initialize(branch);
            AbstractCrashAwareJournal::show::initialize(journal.i_abstract());
            AbstractCrashAwareMap::show::initialize(branch.abstract_i());
            CrashAwareCachingDiskSystem::show::initialize(model, free_aus, initial_superblock, journal, branch);

            let c = caching_disk_system_coordination_i(model);
            assert(CoordinationSystem::State::initialize(c, c)) by {
                reveal(CoordinationSystem::State::initialize);
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
        },
        CrashAwareCachingDiskSystem::Config::dummy_to_use_type_params(_) => {
            assert(false);
        },
    }
}

pub proof fn next_refines_coordination(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
)
    requires
        pre.inv(),
        CrashAwareCachingDiskSystem::State::next(pre, post, lbl),
    ensures
        CoordinationSystem::State::next(
            caching_disk_system_coordination_i(pre),
            caching_disk_system_coordination_i(post),
            CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)},
        ),
{
    reveal(CrashAwareCachingDiskSystem::State::next);
    reveal(CrashAwareCachingDiskSystem::State::next_by);
    let step = choose |step| CrashAwareCachingDiskSystem::State::next_by(pre, post, lbl, step);

    match step {
        CrashAwareCachingDiskSystem::Step::accept_request() => {
            assert(CrashAwareCachingDiskSystem::State::accept_request(pre, post, lbl)) by {
                reveal(CrashAwareCachingDiskSystem::State::accept_request);
            }
            accept_request_refines_coordination(pre, post, lbl);
        },
        CrashAwareCachingDiskSystem::Step::deliver_reply() => {
            assert(CrashAwareCachingDiskSystem::State::deliver_reply(pre, post, lbl)) by {
                reveal(CrashAwareCachingDiskSystem::State::deliver_reply);
            }
            deliver_reply_refines_coordination(pre, post, lbl);
        },
        CrashAwareCachingDiskSystem::Step::execute_noop() => {
            assert(CrashAwareCachingDiskSystem::State::execute_noop(pre, post, lbl)) by {
                reveal(CrashAwareCachingDiskSystem::State::execute_noop);
            }
            execute_noop_refines_coordination(pre, post, lbl);
        },
        CrashAwareCachingDiskSystem::Step::query(new_branch) => {
            assert(CrashAwareCachingDiskSystem::State::query(pre, post, lbl, new_branch)) by {
                reveal(CrashAwareCachingDiskSystem::State::query);
            }
            query_refines_coordination(pre, post, lbl, new_branch);
        },
        CrashAwareCachingDiskSystem::Step::put(new_journal, new_branch) => {
            assert(CrashAwareCachingDiskSystem::State::put(pre, post, lbl, new_journal, new_branch)) by {
                reveal(CrashAwareCachingDiskSystem::State::put);
            }
            put_refines_coordination(pre, post, lbl, new_journal, new_branch);
        },
        CrashAwareCachingDiskSystem::Step::req_sync() => {
            assert(CrashAwareCachingDiskSystem::State::req_sync(pre, post, lbl)) by {
                reveal(CrashAwareCachingDiskSystem::State::req_sync);
            }
            req_sync_refines_coordination(pre, post, lbl);
        },
        CrashAwareCachingDiskSystem::Step::reply_sync() => {
            assert(CrashAwareCachingDiskSystem::State::reply_sync(pre, post, lbl)) by {
                reveal(CrashAwareCachingDiskSystem::State::reply_sync);
            }
            reply_sync_refines_coordination(pre, post, lbl);
        },
        CrashAwareCachingDiskSystem::Step::journal_internal(new_journal) => {
            assert(CrashAwareCachingDiskSystem::State::journal_internal(pre, post, lbl, new_journal)) by {
                reveal(CrashAwareCachingDiskSystem::State::journal_internal);
            }
            journal_internal_refines_coordination(pre, post, lbl, new_journal);
        },
        CrashAwareCachingDiskSystem::Step::journal_load_index(new_journal, discovered_aus) => {
            assert(CrashAwareCachingDiskSystem::State::journal_load_index(
                pre,
                post,
                lbl,
                new_journal,
                discovered_aus,
            )) by {
                reveal(CrashAwareCachingDiskSystem::State::journal_load_index);
            }
            journal_load_index_refines_coordination(pre, post, lbl, new_journal, discovered_aus);
        },
        CrashAwareCachingDiskSystem::Step::journal_internal_alloc(new_journal, allocs, deallocs, prune_aus) => {
            assert(CrashAwareCachingDiskSystem::State::journal_internal_alloc(
                pre,
                post,
                lbl,
                new_journal,
                allocs,
                deallocs,
                prune_aus,
            )) by {
                reveal(CrashAwareCachingDiskSystem::State::journal_internal_alloc);
            }
            journal_internal_alloc_refines_coordination(pre, post, lbl, new_journal, allocs, deallocs, prune_aus);
        },
        CrashAwareCachingDiskSystem::Step::map_internal(new_branch) => {
            assert(CrashAwareCachingDiskSystem::State::map_internal(pre, post, lbl, new_branch)) by {
                reveal(CrashAwareCachingDiskSystem::State::map_internal);
            }
            map_internal_refines_coordination(pre, post, lbl, new_branch);
        },
        CrashAwareCachingDiskSystem::Step::map_load_metadata(new_branch, root, discovered_aus) => {
            assert(CrashAwareCachingDiskSystem::State::map_load_metadata(
                pre,
                post,
                lbl,
                new_branch,
                root,
                discovered_aus,
            )) by {
                reveal(CrashAwareCachingDiskSystem::State::map_load_metadata);
            }
            map_load_metadata_refines_coordination(
                pre,
                post,
                lbl,
                new_branch,
                root,
                discovered_aus,
            );
        },
        CrashAwareCachingDiskSystem::Step::map_internal_alloc(new_branch, allocs, deallocs) => {
            assert(CrashAwareCachingDiskSystem::State::map_internal_alloc(
                pre,
                post,
                lbl,
                new_branch,
                allocs,
                deallocs,
            )) by {
                reveal(CrashAwareCachingDiskSystem::State::map_internal_alloc);
            }
            map_internal_alloc_refines_coordination(
                pre,
                post,
                lbl,
                new_branch,
                allocs,
                deallocs,
            );
        },
        CrashAwareCachingDiskSystem::Step::load_ephemeral_from_persistent(
            new_journal,
            new_branch,
        ) => {
            assert(CrashAwareCachingDiskSystem::State::load_ephemeral_from_persistent(
                pre,
                post,
                lbl,
                new_journal,
                new_branch,
            )) by {
                reveal(CrashAwareCachingDiskSystem::State::load_ephemeral_from_persistent);
            }
            load_ephemeral_refines_coordination(pre, post, lbl, new_journal, new_branch);
        },
        CrashAwareCachingDiskSystem::Step::recover(new_journal, new_branch, records, keys, msgs) => {
            assert(CrashAwareCachingDiskSystem::State::recover(
                pre,
                post,
                lbl,
                new_journal,
                new_branch,
                records,
                keys,
                msgs,
            )) by {
                reveal(CrashAwareCachingDiskSystem::State::recover);
            }
            recover_refines_coordination(pre, post, lbl, new_journal, new_branch, records, keys, msgs);
        },
        CrashAwareCachingDiskSystem::Step::commit_start(
            new_journal,
            new_branch,
            superblock_image,
        ) => {
            assert(CrashAwareCachingDiskSystem::State::commit_start(
                pre,
                post,
                lbl,
                new_journal,
                new_branch,
                superblock_image,
            )) by {
                reveal(CrashAwareCachingDiskSystem::State::commit_start);
            }
            commit_start_refines_coordination(
                pre,
                post,
                lbl,
                new_journal,
                new_branch,
                superblock_image,
            );
        },
        CrashAwareCachingDiskSystem::Step::commit_prepared(new_journal, new_branch, new_superblock, raw_page) => {
            assert(CrashAwareCachingDiskSystem::State::commit_prepared(
                pre,
                post,
                lbl,
                new_journal,
                new_branch,
                new_superblock,
                raw_page,
            )) by {
                reveal(CrashAwareCachingDiskSystem::State::commit_prepared);
            }
            commit_prepared_refines_coordination(
                pre,
                post,
                lbl,
                new_journal,
                new_branch,
                new_superblock,
                raw_page,
            );
        },
        CrashAwareCachingDiskSystem::Step::superblock_write_lands(new_superblock) => {
            assert(CrashAwareCachingDiskSystem::State::superblock_write_lands(
                pre,
                post,
                lbl,
                new_superblock,
            )) by {
                reveal(CrashAwareCachingDiskSystem::State::superblock_write_lands);
            }
            superblock_write_lands_refines_coordination(pre, post, lbl, new_superblock);
        },
        CrashAwareCachingDiskSystem::Step::commit_complete(
            new_journal,
            new_branch,
            new_superblock,
            discarded,
        ) => {
            assert(CrashAwareCachingDiskSystem::State::commit_complete(
                pre,
                post,
                lbl,
                new_journal,
                new_branch,
                new_superblock,
                discarded,
            )) by {
                reveal(CrashAwareCachingDiskSystem::State::commit_complete);
            }
            commit_complete_refines_coordination(
                pre,
                post,
                lbl,
                new_journal,
                new_branch,
                new_superblock,
                discarded,
            );
        },
        CrashAwareCachingDiskSystem::Step::crash(new_journal, new_branch, new_superblock) => {
            assert(CrashAwareCachingDiskSystem::State::crash(
                pre,
                post,
                lbl,
                new_journal,
                new_branch,
                new_superblock,
            )) by {
                reveal(CrashAwareCachingDiskSystem::State::crash);
            }
            crash_refines_coordination(pre, post, lbl, new_journal, new_branch, new_superblock);
        },
        CrashAwareCachingDiskSystem::Step::noop() => {
            assert(CrashAwareCachingDiskSystem::State::noop(pre, post, lbl)) by {
                reveal(CrashAwareCachingDiskSystem::State::noop);
            }
            noop_refines_coordination(pre, post, lbl);
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn next_refines_ctam(
    pre: CrashAwareCachingDiskSystem::State,
    post: CrashAwareCachingDiskSystem::State,
    lbl: CrashAwareCachingDiskSystem::Label,
)
    requires
        pre.inv(),
        caching_disk_system_coordination_i(pre).inv(),
        CrashAwareCachingDiskSystem::State::next(pre, post, lbl),
    ensures
        CrashTolerantAsyncMap::State::next(caching_disk_system_i(pre), caching_disk_system_i(post), caching_disk_system_i_lbl(pre, post, lbl)),
{
    let cpre = caching_disk_system_coordination_i(pre);
    let cpost = caching_disk_system_coordination_i(post);
    let clbl = CoordinationSystem::Label::Label{ctam_label: caching_disk_system_i_lbl(pre, post, lbl)};

    next_refines_coordination(pre, post, lbl);
    next_refines(cpre, cpost, clbl);
}

}
