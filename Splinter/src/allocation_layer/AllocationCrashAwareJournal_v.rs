// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::prelude::*;
use verus_state_machines_macros::state_machine;

use crate::abstract_system::MsgHistory_v::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::{AU};
use crate::allocation_layer::AllocationJournal_v::*;
use crate::allocation_layer::MiniAllocator_v::*;
use crate::journal::LinkedJournal_v::TruncatedJournal;

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
      pub persistent: JournalMetadata,
      pub persistent_image: Option<JournalImage>,
      pub ephemeral: Ephemeral,
      pub frozen: Option<JournalMetadata>
    }

    init!{
        initialize() {
            init persistent = JournalMetadata::empty();
            init persistent_image = Option::Some(JournalImage::empty());
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

    pub open spec fn image_matches_metadata(image: JournalImage, metadata: JournalMetadata) -> bool
    {
        &&& image.first == metadata.first
        &&& image.tj.freshest_rec == metadata.freshest_rec
        &&& image.tj.disk_view.boundary_lsn == metadata.boundary_lsn
        &&& image.tj.seq_end() == metadata.seq_end
    }

    pub open spec(checked) fn persistent_image_view(self) -> JournalImage
        recommends self.persistent_image is Some || self.ephemeral is Known
    {
        if self.persistent_image is Some {
            self.persistent_image.unwrap()
        } else {
            self.ephemeral->v.frozen_image(self.persistent)
        }
    }

    pub open spec(checked) fn acceptable_persistent_image(self, image: JournalImage) -> bool
        recommends self.persistent_image is Some || self.ephemeral is Known
    {
        if self.persistent_image is Some {
            image == self.persistent_image.unwrap()
        } else {
            self.ephemeral->v.acceptable_frozen_image(self.persistent, image)
        }
    }

    pub open spec(checked) fn fresh_label(self, lbl: Label) -> bool
        recommends lbl is Internal ==> self.ephemeral is Known
    {
        lbl is Internal ==> {
            &&& lbl->allocs.disjoint(self.persistent_image_view().accessible_aus())
            &&& lbl->allocs.disjoint(self.ephemeral->v.accessible_aus())
        }
    }

    transition!{
        load_ephemeral_from_persistent(lbl: Label, new_journal: AllocationJournal::State) {
            require lbl is LoadEphemeralFromPersistent;
            require pre.ephemeral is Unknown;
            require pre.persistent_image is Some;
            require pre.persistent_image.unwrap().init_by(new_journal);
            update ephemeral = Ephemeral::Known{ v: new_journal };
            update persistent_image = Option::None;
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
            require pre.persistent_image is None ==> {
                &&& new_journal.frozen_metadata_valid(pre.persistent)
                &&& new_journal.frozen_image(pre.persistent).tight_tj()
                    == pre.ephemeral->v.frozen_image(pre.persistent).tight_tj()
            };
            require pre.frozen is Some ==> {
                &&& new_journal.frozen_metadata_valid(pre.frozen.unwrap())
                &&& new_journal.frozen_image(pre.frozen.unwrap()).tight_tj()
                    == pre.ephemeral->v.frozen_image(pre.frozen.unwrap()).tight_tj()
            };
            update ephemeral = Ephemeral::Known{ v: new_journal };
        }
    }

    transition!{
        query_lsn_persistence(lbl: Label) {
            require lbl is QueryLsnPersistence;
            require lbl->sync_lsn <= pre.persistent.seq_end;
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
            require pre.persistent.seq_end <= frozen_journal.seq_end;
            update frozen = Option::Some(frozen_journal);
        }
    }

    transition!{
        commit_complete(lbl: Label, new_journal: AllocationJournal::State) {
            require lbl is CommitComplete;
            require pre.ephemeral is Known;
            require pre.frozen is Some;

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
            require new_journal.frozen_metadata_valid(pre.frozen.unwrap());
            require new_journal.frozen_image(pre.frozen.unwrap())
                == pre.ephemeral->v.frozen_image(pre.frozen.unwrap());
            
            // Watch the `update` keyword!
            update persistent = pre.frozen.unwrap();
            update ephemeral = Ephemeral::Known{ v: new_journal };
            update frozen = Option::None;
        }
    }

    transition!{
        crash(lbl: Label, persistent_image: JournalImage) {
            require lbl is Crash;
            require lbl->keep_in_flight ==> pre.frozen is Some;
            require lbl->keep_in_flight ==> pre.ephemeral is Known;
            let persistent_metadata =
                if lbl->keep_in_flight { pre.frozen.unwrap() } else { pre.persistent };
            require Self::image_matches_metadata(persistent_image, persistent_metadata);
            require persistent_image.valid_image();
            require if lbl->keep_in_flight {
                pre.ephemeral->v.acceptable_frozen_image(pre.frozen.unwrap(), persistent_image)
            } else {
                pre.acceptable_persistent_image(persistent_image)
            };
            update ephemeral = Ephemeral::Unknown;
            update frozen = Option::None;
            update persistent = persistent_metadata;
            update persistent_image = Option::Some(persistent_image);
        }
    }

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.ephemeral is Unknown ==> self.frozen is None
        &&& self.ephemeral is Unknown <==> self.persistent_image is Some
        &&& self.persistent_image is Some ==> {
            let image = self.persistent_image.unwrap();
            &&& image.valid_image()
            &&& Self::image_matches_metadata(image, self.persistent)
        }
        &&& self.ephemeral is Known ==> self.ephemeral->v.inv()
        &&& self.ephemeral is Known ==> self.ephemeral->v.semantic_inv()
        &&& self.ephemeral is Known && self.persistent_image is None ==> {
            self.ephemeral->v.frozen_metadata_valid(self.persistent)
        }
        &&& self.frozen is Some ==> {
            &&& self.ephemeral is Known
            &&& self.ephemeral->v.frozen_metadata_valid(self.frozen.unwrap())
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) {
        JournalImage::empty_is_valid_image();
    }
   
    #[inductive(load_ephemeral_from_persistent)]
    fn load_ephemeral_from_persistent_inductive(pre: Self, post: Self, lbl: Label, new_journal: AllocationJournal::State) 
    {
        let image = pre.persistent_image.unwrap();
        let tight = image.tight_tj();
        let first = image.first;
        AllocationJournal::State::initialize_inductive(new_journal, image);
        AllocationJournal::State::initialize_semantic_inv(new_journal, image);
        AllocationJournal::State::initialize_tj_matches(new_journal, image);
        image.valid_image_implies_tight_valid_image();
        image.valid_image_implies_tight_seq_bounds();
        tight.build_lsn_au_index_from_first_ensures(first);
        reveal(TruncatedJournal::au_domain_valid);
        assert(new_journal.lsn_au_index == tight.build_lsn_au_index_from_first(first));
        if pre.persistent.freshest_rec is Some {
            let root = pre.persistent.freshest_rec.unwrap();
            let last_lsn = (pre.persistent.seq_end - 1) as nat;
            assert(tight.seq_start() <= last_lsn);
            assert(last_lsn < tight.seq_end());
            assert(new_journal.lsn_au_index.contains_key(last_lsn));
            assert(image.tj.freshest_rec == pre.persistent.freshest_rec);
            assert(tight.freshest_rec == pre.persistent.freshest_rec);
            assert(tight.disk_view.entries.contains_key(root));
            assert(tight.disk_view.entries[root] == image.tj.disk_view.entries[root]);
            assert(tight.disk_view.entries[root].message_seq.contains(last_lsn));
            assert(tight.disk_view.addr_supports_lsn(root, last_lsn));
            let index = tight.build_lsn_au_index_from_first(first);
            tight.disk_view.addr_supports_lsn_consistent_with_index(index, last_lsn, root);
            assert(index[last_lsn] == root.au);
            assert(new_journal.lsn_au_index[last_lsn] == root.au);
        }
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
    fn commit_complete_inductive(pre: Self, post: Self, lbl: Label, new_journal: AllocationJournal::State)
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
    fn crash_inductive(pre: Self, post: Self, lbl: Label, persistent_image: JournalImage)
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
            AllocationCrashAwareJournal::Step::commit_complete(new_journal) => {
                assert(AllocationCrashAwareJournal::State::commit_complete(pre, post, lbl, new_journal)) by {
                    reveal(AllocationCrashAwareJournal::State::commit_complete);
                }
                AllocationCrashAwareJournal::State::commit_complete_inductive(pre, post, lbl, new_journal);
            },
            AllocationCrashAwareJournal::Step::crash(persistent_image) => {
                assert(AllocationCrashAwareJournal::State::crash(pre, post, lbl, persistent_image)) by {
                    reveal(AllocationCrashAwareJournal::State::crash);
                }
                AllocationCrashAwareJournal::State::crash_inductive(pre, post, lbl, persistent_image);
            },
            AllocationCrashAwareJournal::Step::dummy_to_use_type_params(_) => {
                assert(false);
            },
        }
    }

  }} // state_machine
} // verus
