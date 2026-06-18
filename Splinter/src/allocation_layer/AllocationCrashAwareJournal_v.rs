// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::prelude::*;
use verus_state_machines_macros::state_machine;

use crate::abstract_system::MsgHistory_v::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::{AU};
use crate::allocation_layer::AllocationJournal_v::*;
use crate::allocation_layer::MiniAllocator_v::*;

verus! {

pub enum Ephemeral
{
    Unknown,
    Known{v: AllocationJournal::State}
}

impl Ephemeral {
    pub open spec(checked) fn wf(self) -> bool
    {
      self is Known ==> self->v.wf()
    }
}

impl JournalImage {
    pub open spec(checked) fn init_by(self, aj: AllocationJournal::State) -> bool 
    {
        &&& self.valid_image()
        &&& AllocationJournal::State::initialize(aj, self)
        &&& aj.mini_allocator.wf()
        &&& aj.mini_allocator.curr is None
        &&& aj.mini_allocator.all_aus().disjoint(self.accessible_aus())
    }
}

// valid image
state_machine!{AllocationCrashAwareJournal{
    fields {
      pub persistent: JournalImage,
      pub ephemeral: Ephemeral,
      pub frozen: Option<JournalMetadata>
    }

    init!{
        initialize() {
            init persistent = JournalImage::empty();
            init ephemeral = Ephemeral::Unknown;
            init frozen = Option::None;
      }
    }

    pub enum Label
    {
        LoadEphemeralFromPersistent,
        ReadForRecovery{ records: MsgHistory },
        QueryEndLsn{ end_lsn: LSN },
        Put{ records: MsgHistory },
        Internal{allocs: Set<AU>, deallocs: Set<AU>},
        QueryLsnPersistence{ sync_lsn: LSN },
        CommitStart{ new_boundary_lsn: LSN, frozen_journal: JournalMetadata },
        CommitComplete{ require_end: LSN, discarded: Set<AU> },
        Crash{ keep_in_flight: bool },
    }

    pub open spec(checked) fn fresh_label(self, lbl: Label) -> bool
        recommends lbl is Internal ==> self.ephemeral is Known
    {
        lbl is Internal ==> {
            &&& lbl->allocs.disjoint(self.persistent.accessible_aus())
            &&& lbl->allocs.disjoint(self.ephemeral->v.accessible_aus())
        }
    }

    transition!{
        load_ephemeral_from_persistent(lbl: Label, new_journal: AllocationJournal::State) {
            require lbl is LoadEphemeralFromPersistent;
            require pre.ephemeral is Unknown;
            require pre.persistent.init_by(new_journal);
            update ephemeral = Ephemeral::Known{ v: new_journal };
        }
    }

    transition!{
        read_for_recovery(lbl: Label) {
            require lbl is ReadForRecovery;
            require pre.ephemeral is Known;
            require AllocationJournal::State::next(
                pre.ephemeral->v, 
                pre.ephemeral->v, 
                AllocationJournal::Label::ReadForRecovery{ messages: lbl.arrow_ReadForRecovery_records() }
            );
        }
    }

    transition!{
        query_end_lsn(lbl: Label) {
            require lbl is QueryEndLsn;
            require pre.ephemeral is Known;
            require AllocationJournal::State::next(
                pre.ephemeral->v, 
                pre.ephemeral->v, 
                AllocationJournal::Label::QueryEndLsn{ end_lsn: lbl->end_lsn },
            );
        }
    }

    transition!{
        put(lbl: Label, new_journal: AllocationJournal::State) {
            require lbl is Put;
            require pre.ephemeral is Known;
            require AllocationJournal::State::next(
                pre.ephemeral->v, 
                new_journal, 
                AllocationJournal::Label::Put{ messages: lbl.arrow_Put_records() },
            );
            update ephemeral = Ephemeral::Known{ v: new_journal };
        }
    }

    transition!{
        internal(lbl: Label, new_journal: AllocationJournal::State) {
            require lbl is Internal;
            require pre.ephemeral is Known;
            require pre.fresh_label(lbl);
            require AllocationJournal::State::next(
                pre.ephemeral->v, 
                new_journal, 
                AllocationJournal::Label::InternalAllocations{ allocs: lbl->allocs, deallocs: lbl.arrow_Internal_deallocs() }
            );
            require pre.frozen is Some ==> {
                &&& new_journal.frozen_metadata_valid(pre.frozen.unwrap())
                &&& new_journal.frozen_image(pre.frozen.unwrap())
                    == pre.ephemeral->v.frozen_image(pre.frozen.unwrap())
            };
            update ephemeral = Ephemeral::Known{ v: new_journal };
        }
    }

    transition!{
        query_lsn_persistence(lbl: Label) {
            require lbl is QueryLsnPersistence;
            require lbl->sync_lsn <= pre.persistent.tj.seq_end();
        }
    }

    transition!{
        commit_start(lbl: Label) {
            require lbl is CommitStart;
            require pre.ephemeral is Known;
            require pre.frozen is None;
            let frozen_journal = lbl->frozen_journal;
            require AllocationJournal::State::next(
                pre.ephemeral->v,
                pre.ephemeral->v,
                AllocationJournal::Label::FreezeForCommit{frozen_journal},
            );
            // Frozen journal stitches to frozen map
            require frozen_journal.boundary_lsn == lbl->new_boundary_lsn;
            // Journal doesn't go backwards
            require pre.persistent.tj.seq_end() <= lbl->new_boundary_lsn;
            update frozen = Option::Some(frozen_journal);
        }
    }

    transition!{
        commit_complete(lbl: Label, new_journal: AllocationJournal::State, frozen_image: JournalImage) {
            require lbl is CommitComplete;
            require pre.ephemeral is Known;
            require pre.frozen is Some;
            require pre.ephemeral->v.acceptable_frozen_image(pre.frozen.unwrap(), frozen_image);

            // upon a successful write to super block, we truncate ephemeral 
            // journal to line up with the beginning of the newly persisted journal
            // another option would be to truncate the ephemeral journal to the 
            // end of persitent journal, but this means that to reason about the
            // full system, we will need to reason about persistent tree,
            // persistent journal stitched at the front of the ephemeral journal.
            // since there's no runtime cost to track ephemeral journal as a 
            // superset of persistent journal, that's what we do
            require AllocationJournal::State::next(
                pre.ephemeral->v, 
                new_journal,
                AllocationJournal::Label::DiscardOld{
                    start_lsn: pre.frozen.unwrap().boundary_lsn,
                    require_end: lbl->require_end,
                    // where do we specify which aus are in deallocs?
                    deallocs: lbl->discarded,
                },
            );
            
            // Watch the `update` keyword!
            update persistent = frozen_image;
            update ephemeral = Ephemeral::Known{ v: new_journal };
            update frozen = Option::None;
        }
    }

    transition!{
        crash(lbl: Label) {
            require lbl is Crash;
            require lbl->keep_in_flight ==> pre.frozen is Some;
            require lbl->keep_in_flight ==> pre.ephemeral is Known;
            update ephemeral = Ephemeral::Unknown;
            update frozen = Option::None;
            update persistent = if lbl->keep_in_flight {
                pre.ephemeral->v.frozen_image(pre.frozen.unwrap())
            } else {
                pre.persistent
            };
        }
    }

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.ephemeral is Unknown ==> self.frozen is None
        &&& self.ephemeral is Known ==> self.ephemeral->v.inv()
        &&& self.ephemeral is Known ==> self.ephemeral->v.semantic_inv()
        &&& self.frozen is Some ==> {
            &&& self.ephemeral is Known
            &&& self.ephemeral->v.frozen_metadata_valid(self.frozen.unwrap())
        }
        &&& self.persistent.valid_image()
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) {
        JournalImage::empty_is_valid_image();
    }
   
    #[inductive(load_ephemeral_from_persistent)]
    fn load_ephemeral_from_persistent_inductive(pre: Self, post: Self, lbl: Label, new_journal: AllocationJournal::State) 
    {
        AllocationJournal::State::initialize_inductive(new_journal, pre.persistent);
        AllocationJournal::State::initialize_semantic_inv(new_journal, pre.persistent);
    }
   
    #[inductive(read_for_recovery)]
    fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label) 
    { 
    }
   
    #[inductive(query_end_lsn)]
    fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label) 
    { 
    }
   
    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label, new_journal: AllocationJournal::State) 
    {
        let aj_lbl = AllocationJournal::Label::Put{messages: lbl.arrow_Put_records()};
        AllocationJournal::State::next_refines(pre.ephemeral->v, new_journal, aj_lbl);
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);
        assert(AllocationJournal::State::next_by(
            pre.ephemeral->v,
            new_journal,
            aj_lbl,
            AllocationJournal::Step::put(),
        ));
        if pre.frozen is Some {
            AllocationJournal::State::put_preserves_frozen_metadata(
                pre.ephemeral->v,
                new_journal,
                aj_lbl,
                pre.frozen.unwrap(),
            );
        }
    }
   
    #[inductive(internal)]
    fn internal_inductive(pre: Self, post: Self, lbl: Label, new_journal: AllocationJournal::State) 
    {
        let aj_lbl = AllocationJournal::Label::InternalAllocations{ allocs: lbl->allocs, deallocs: lbl.arrow_Internal_deallocs() };
        AllocationJournal::State::next_refines(pre.ephemeral->v, post.ephemeral->v, aj_lbl);
    }
   
    #[inductive(query_lsn_persistence)]
    fn query_lsn_persistence_inductive(pre: Self, post: Self, lbl: Label) 
    {
    }

    #[inductive(commit_start)]
    fn commit_start_inductive(pre: Self, post: Self, lbl: Label)
    {
        let pre_ephemeral = pre.ephemeral->v;
        let aj_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: lbl->frozen_journal};
        assert(AllocationJournal::State::next(pre_ephemeral, pre_ephemeral, aj_lbl));
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);
        assert(AllocationJournal::State::next_by(
            pre_ephemeral,
            pre_ephemeral,
            aj_lbl,
            AllocationJournal::Step::freeze_for_commit(),
        ));
        AllocationJournal::State::frozen_journal_is_valid_image(pre_ephemeral, pre_ephemeral, aj_lbl);
    }
   
    #[inductive(commit_complete)]
    fn commit_complete_inductive(pre: Self, post: Self, lbl: Label, new_journal: AllocationJournal::State, frozen_image: JournalImage)
    {
        assert(pre.ephemeral->v.frozen_metadata_valid(pre.frozen.unwrap()));
        let freeze_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: pre.frozen.unwrap()};
        assert(AllocationJournal::State::next(pre.ephemeral->v, pre.ephemeral->v, freeze_lbl)) by {
            reveal(AllocationJournal::State::next);
            reveal(AllocationJournal::State::next_by);
            assert(AllocationJournal::State::next_by(
                pre.ephemeral->v,
                pre.ephemeral->v,
                freeze_lbl,
                AllocationJournal::Step::freeze_for_commit(),
            ));
        }
        AllocationJournal::State::frozen_journal_is_valid_image(
            pre.ephemeral->v,
            pre.ephemeral->v,
            freeze_lbl,
        );
        assert(frozen_image.valid_image());
        assert(post.ephemeral is Known ==> post.ephemeral->v.refinement_inv()) by {
            let alloc_lbl = AllocationJournal::Label::DiscardOld{ 
                start_lsn: pre.frozen.unwrap().boundary_lsn,
                require_end: lbl->require_end,
                deallocs: lbl->discarded,
            };
            AllocationJournal::State::next_refines(pre.ephemeral->v,
                post.ephemeral->v, alloc_lbl);
        }
        assert(post.ephemeral is Known ==> post.ephemeral->v.inv());
        assert(post.ephemeral is Known ==> post.ephemeral->v.semantic_inv());
    }
   
    #[inductive(crash)]
    fn crash_inductive(pre: Self, post: Self, lbl: Label)
    {
        if lbl->keep_in_flight {
            let freeze_lbl = AllocationJournal::Label::FreezeForCommit{
                frozen_journal: pre.frozen.unwrap(),
            };
            assert(AllocationJournal::State::next(pre.ephemeral->v, pre.ephemeral->v, freeze_lbl)) by {
                reveal(AllocationJournal::State::next);
                reveal(AllocationJournal::State::next_by);
                assert(AllocationJournal::State::next_by(
                    pre.ephemeral->v,
                    pre.ephemeral->v,
                    freeze_lbl,
                    AllocationJournal::Step::freeze_for_commit(),
                ));
            }
            AllocationJournal::State::frozen_journal_is_valid_image(
                pre.ephemeral->v,
                pre.ephemeral->v,
                freeze_lbl,
            );
        }
    }

    pub proof fn inv_next(pre: Self, post: Self, lbl: Label)
        requires
            pre.inv(),
            AllocationCrashAwareJournal::State::next(pre, post, lbl),
        ensures
            post.inv(),
    {
        reveal(AllocationCrashAwareJournal::State::next);
        reveal(AllocationCrashAwareJournal::State::next_by);

        let step = choose |step| AllocationCrashAwareJournal::State::next_by(pre, post, lbl, step);
        match step {
            AllocationCrashAwareJournal::Step::load_ephemeral_from_persistent(new_journal) => {
                assert(AllocationCrashAwareJournal::State::load_ephemeral_from_persistent(pre, post, lbl, new_journal)) by {
                    reveal(AllocationCrashAwareJournal::State::load_ephemeral_from_persistent);
                }
                AllocationCrashAwareJournal::State::load_ephemeral_from_persistent_inductive(pre, post, lbl, new_journal);
            },
            AllocationCrashAwareJournal::Step::read_for_recovery() => {
                assert(AllocationCrashAwareJournal::State::read_for_recovery(pre, post, lbl)) by {
                    reveal(AllocationCrashAwareJournal::State::read_for_recovery);
                }
                AllocationCrashAwareJournal::State::read_for_recovery_inductive(pre, post, lbl);
            },
            AllocationCrashAwareJournal::Step::query_end_lsn() => {
                assert(AllocationCrashAwareJournal::State::query_end_lsn(pre, post, lbl)) by {
                    reveal(AllocationCrashAwareJournal::State::query_end_lsn);
                }
                AllocationCrashAwareJournal::State::query_end_lsn_inductive(pre, post, lbl);
            },
            AllocationCrashAwareJournal::Step::put(new_journal) => {
                assert(AllocationCrashAwareJournal::State::put(pre, post, lbl, new_journal)) by {
                    reveal(AllocationCrashAwareJournal::State::put);
                }
                AllocationCrashAwareJournal::State::put_inductive(pre, post, lbl, new_journal);
            },
            AllocationCrashAwareJournal::Step::internal(new_journal) => {
                assert(AllocationCrashAwareJournal::State::internal(pre, post, lbl, new_journal)) by {
                    reveal(AllocationCrashAwareJournal::State::internal);
                }
                AllocationCrashAwareJournal::State::internal_inductive(pre, post, lbl, new_journal);
            },
            AllocationCrashAwareJournal::Step::query_lsn_persistence() => {
                assert(AllocationCrashAwareJournal::State::query_lsn_persistence(pre, post, lbl)) by {
                    reveal(AllocationCrashAwareJournal::State::query_lsn_persistence);
                }
                AllocationCrashAwareJournal::State::query_lsn_persistence_inductive(pre, post, lbl);
            },
            AllocationCrashAwareJournal::Step::commit_start() => {
                assert(AllocationCrashAwareJournal::State::commit_start(pre, post, lbl)) by {
                    reveal(AllocationCrashAwareJournal::State::commit_start);
                }
                AllocationCrashAwareJournal::State::commit_start_inductive(pre, post, lbl);
            },
            AllocationCrashAwareJournal::Step::commit_complete(new_journal, frozen_image) => {
                assert(AllocationCrashAwareJournal::State::commit_complete(pre, post, lbl, new_journal, frozen_image)) by {
                    reveal(AllocationCrashAwareJournal::State::commit_complete);
                }
                AllocationCrashAwareJournal::State::commit_complete_inductive(pre, post, lbl, new_journal, frozen_image);
            },
            AllocationCrashAwareJournal::Step::crash() => {
                assert(AllocationCrashAwareJournal::State::crash(pre, post, lbl)) by {
                    reveal(AllocationCrashAwareJournal::State::crash);
                }
                AllocationCrashAwareJournal::State::crash_inductive(pre, post, lbl);
            },
            AllocationCrashAwareJournal::Step::dummy_to_use_type_params(_) => {
                assert(false);
            },
        }
    }

  }} // state_machine
} // verus
