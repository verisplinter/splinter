// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
use vstd::prelude::*;

use crate::abstract_system::AbstractCrashAwareJournal_v;
use crate::abstract_system::AbstractCrashAwareJournal_v::AbstractCrashAwareJournal;
use crate::abstract_system::AbstractJournal_v::AbstractJournal;
use crate::abstract_system::MsgHistory_v::*;
use crate::allocation_layer::AllocationCrashAwareJournal_v::*;
use crate::allocation_layer::AllocationJournal_v::{
    AllocationJournal, JournalMetadata, JournalImage, maps_agree_on,
};
use crate::allocation_layer::LikesJournal_v::LikesJournal;
use crate::journal::LinkedJournal_v::{LinkedJournal, TruncatedJournal};
use crate::journal::PagedJournal_v::{JournalRecord, PagedJournal};

// Refines Allocation Journal => Abstract Journal
// Refines Allocation Crash Aware Journal => Abstract Crash Aware Journal

verus!{

impl AllocationJournal::Label{
    pub open spec fn i_abstract(self) -> AbstractJournal::Label
    {   
        LikesJournal::State::lbl_i(self.i()).i().i()
    }
}

impl AllocationJournal::State{
    pub proof fn initialized_i_abstract_journal_matches_image(self, image: JournalImage)
    requires
        AllocationJournal::State::initialize(self, image),
    ensures
        self.i_abstract().journal == image.i(),
    {
        self.init_refines_abstract(image);
        AllocationJournal::State::initialize_tj_matches(self, image);
        image.valid_image_implies_tight_valid_image();
        image.i_wf();
        let tight = image.tight_tj();
        let empty = MsgHistory::empty_history_at(tight.seq_end());
        let base = tight.i().i();
        assert(self.tj() == tight);
        assert(self.unmarshalled_tail == empty);
        assert(empty.wf());
        assert(base.wf());
        assert(base.seq_end == tight.seq_end());
        assert(empty.seq_start == base.seq_end);
        assert(base.can_concat(empty));
        base.concat_lemma(empty);
        assert(base.concat(empty) == base);
        assert(image.i() == base);
        let likes = self.i();
        assert(likes.journal.truncated_journal == tight);
        assert(likes.journal.unmarshalled_tail == empty);
        assert(likes.journal.truncated_journal.decodable());
        let linked = likes.i();
        assert(linked == likes.journal);
        assert(linked.truncated_journal == tight);
        assert(linked.unmarshalled_tail == empty);
        assert(linked.wf());
        assert(linked.truncated_journal.disk_view.acyclic());
        linked.iwf();
        let paged = linked.i();
        assert(paged.truncated_journal == tight.i());
        assert(paged.unmarshalled_tail == empty);
        assert(paged.i().journal == base.concat(empty));
        assert(self.i_abstract() == paged.i());
        assert(self.i_abstract().journal == base.concat(empty));
        assert(self.i_abstract().journal == image.i());
    }

    pub proof fn i_inv(self)
        requires
            self.refinement_inv(),
        ensures
            self.i().inv(),
    {
        self.tj_inherits_semantic_structure();
        assert(self.i().journal.truncated_journal == self.tj());
        assert(self.i().journal.unmarshalled_tail == self.unmarshalled_tail);
        assert(self.i().journal.wf());
        assert(self.i().journal.truncated_journal.decodable());
        assert(self.i().lsn_addr_index == self.tj().build_lsn_addr_index());
        assert(self.i().inv());
    }

    pub open spec fn label_i_abstract(self, lbl: AllocationJournal::Label) -> AbstractJournal::Label
    {
        LikesJournal::State::lbl_i(self.label_i(lbl)).i().i()
    }

    pub open spec fn i_abstract(self) -> AbstractJournal::State
    {
        self.i().i().i().i()
    }

    // refines to abstract journal
    pub proof fn init_refines_abstract(self, image: JournalImage)
    requires
        Self::initialize(self, image)
    ensures
        AbstractJournal::State::initialize(self.i_abstract(), self.i_abstract().journal)
    {
        self.init_refines(image);
        self.i().init_refines(self.tj());
        self.i().i().init_refines(self.tj());
        self.i().i().i().init_refines(self.tj().i());
    }

    // refines to abstract journal
    pub proof fn next_refines_abstract(self, post: Self, lbl: AllocationJournal::Label)
    requires
        self.refinement_inv(),
        post.refinement_inv(),
        Self::next(self, post, lbl)
    ensures
        AbstractJournal::State::next(self.i_abstract(), post.i_abstract(), self.label_i_abstract(lbl))
    {
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);
        reveal(AbstractJournal::State::next);
        reveal(AbstractJournal::State::next_by);

        self.next_refines(post, lbl); // alloc refines to likes

        let likes = self.i();
        let likes_post = post.i();
        let likes_lbl = self.label_i(lbl);
        self.i_inv();
        post.i_inv();

        likes.next_refines(likes_post, likes_lbl); // likes refines to linked

        let linked = likes.i();
        let linked_post = likes_post.i();
        let linked_lbl = LikesJournal::State::lbl_i(likes_lbl);
        likes.i_inv();
        likes_post.i_inv();

        linked.next_refines(linked_post, linked_lbl); // linked refines to paged

        linked.truncated_journal.iwf();
        linked_post.truncated_journal.iwf();
        
        let paged = linked.i();
        let paged_post = linked_post.i();
        let paged_lbl = linked_lbl.i();
        linked.i_wf();
        linked_post.i_wf();

        paged.next_refines(paged_post, paged_lbl); // paged refines to abstract
    }
}

impl LikesJournal::State {
    pub proof fn i_inv(self)
        requires
            self.inv(),
        ensures
            self.i().inv(),
    {
        assert(self.i() == self.journal);
        assert(self.journal.wf());
        assert(self.journal.truncated_journal.decodable());
        assert(self.i().inv());
    }
}

impl LinkedJournal::State {
    pub proof fn i_wf(self)
        requires
            self.inv(),
        ensures
            self.i().wf(),
    {
        assert(self.wf());
        assert(self.truncated_journal.decodable());
        self.truncated_journal.iwf();
        assert(self.i().truncated_journal == self.truncated_journal.i());
        assert(self.i().unmarshalled_tail == self.unmarshalled_tail);
        assert(self.i().wf());
    }
}

impl JournalImage{
    pub open spec fn i(self) -> MsgHistory
    {
        self.tight_tj().i().i()
    }

    pub proof fn i_wf(self)
    requires
        self.valid_image(),
    ensures
        self.i().wf(),
        self.i().seq_start == self.tight_tj().seq_start(),
        self.i().seq_end == self.tight_tj().seq_end(),
        self.i().seq_start == self.tj.seq_start(),
        self.i().seq_end == self.tj.seq_end(),
    {
        self.valid_image_implies_tight_valid_image();
        self.valid_image_implies_tight_seq_bounds();
        let tight = self.tight_tj();
        tight.iwf();
        JournalRecord::i_lemma_forall();
        assert(self.i().wf());
        assert(self.i().seq_start == self.tight_tj().seq_start());
        assert(self.i().seq_end == self.tight_tj().seq_end());
        assert(self.i().seq_start == self.tj.seq_start());
        assert(self.i().seq_end == self.tj.seq_end());
    }

    pub proof fn tight_i_matches(self)
    requires
        self.valid_image(),
    ensures
        self.i() == self.tight_tj().i().i(),
    {
        assert(self.i() == self.tight_tj().i().i());
    }
}

impl JournalMetadata {
    pub open spec fn i(self, journal: AllocationJournal::State) -> MsgHistory
    {
        journal.frozen_image(self).i()
    }
}

impl Ephemeral{
    pub open spec fn i(self) -> AbstractCrashAwareJournal_v::Ephemeral
    {
        if self is Unknown {
            AbstractCrashAwareJournal_v::Ephemeral::Unknown
        } else {
            AbstractCrashAwareJournal_v::Ephemeral::Known{
                v: self->v.i_abstract()
            }
        }
    }
}

impl AllocationCrashAwareJournal::Label{
    pub open spec fn i(self) -> AbstractCrashAwareJournal::Label
    {
        match self {
            Self::LoadEphemeralFromPersistent => 
                AbstractCrashAwareJournal::Label::LoadEphemeralFromPersistentLabel,
            Self::ReadForRecovery{records} =>
                AbstractCrashAwareJournal::Label::ReadForRecoveryLabel{records},
            Self::QueryEndLsn{end_lsn} =>
                AbstractCrashAwareJournal::Label::QueryEndLsnLabel{end_lsn},
            Self::Put{records} =>
                AbstractCrashAwareJournal::Label::PutLabel{records},
            Self::Internal{allocs, deallocs} =>
                AbstractCrashAwareJournal::Label::InternalLabel,
            Self::QueryLsnPersistence{sync_lsn} =>
                AbstractCrashAwareJournal::Label::QueryLsnPersistenceLabel{sync_lsn},
            Self::CommitStart{ new_boundary_lsn, frozen_journal } =>
                arbitrary(),
            Self::CommitComplete{ require_end, discarded } =>
                AbstractCrashAwareJournal::Label::CommitCompleteLabel{require_end},
            Self::Crash{ keep_in_flight } => AbstractCrashAwareJournal::Label::CrashLabel{ keep_in_flight },
        }
    }
}

impl AllocationCrashAwareJournal::State{
    pub proof fn persistent_image_view_i_wf(self)
    requires
        self.inv(),
    ensures
        self.persistent_image_view().valid_image(),
        self.persistent_image_view().i().wf(),
        self.persistent_image_view().i().seq_end == self.persistent.seq_end,
    {
        let image = self.persistent_image_view();
        if self.persistent_image is Some {
            assert(image.valid_image());
            assert(AllocationCrashAwareJournal::State::image_matches_metadata(image, self.persistent));
            image.i_wf();
        } else {
            let aj = self.ephemeral->v;
            let freeze_lbl = AllocationJournal::Label::FreezeForCommit{
                frozen_journal: self.persistent,
            };
            assert(AllocationJournal::State::next(aj, aj, freeze_lbl)) by {
                reveal(AllocationJournal::State::next);
                reveal(AllocationJournal::State::next_by);
                assert(AllocationJournal::State::next_by(
                    aj,
                    aj,
                    freeze_lbl,
                    AllocationJournal::Step::freeze_for_commit(),
                ));
            }
            AllocationJournal::State::frozen_journal_is_valid_image(aj, aj, freeze_lbl);
            assert(image == aj.frozen_image(self.persistent));
            image.i_wf();
        }
    }

    pub open spec fn label_i(self, lbl: AllocationCrashAwareJournal::Label) -> AbstractCrashAwareJournal::Label
    {
        match lbl {
            AllocationCrashAwareJournal::Label::CommitStart{new_boundary_lsn, frozen_journal} =>
                if self.ephemeral is Known {
                    AbstractCrashAwareJournal::Label::CommitStartLabel{
                        new_boundary_lsn,
                        frozen_journal: frozen_journal.i(self.ephemeral->v),
                    }
                } else {
                    arbitrary()
                },
            _ => lbl.i(),
        }
    }

    pub open spec fn i(self) -> AbstractCrashAwareJournal::State 
    {
        let i_frozen =
            if self.frozen is None { None }
            else if self.ephemeral is Known { Some(self.frozen.unwrap().i(self.ephemeral->v)) }
            else { arbitrary() };

        AbstractCrashAwareJournal::State{
            persistent: self.persistent_image_view().i(),
            ephemeral: self.ephemeral.i(),
            frozen: i_frozen,
        }
    }

    pub proof fn load_ephemeral_from_persistent_refines(self, post: Self, 
        lbl: AllocationCrashAwareJournal::Label, new_journal: AllocationJournal::State)
    requires
        self.inv(),
        post.inv(),
        Self::load_ephemeral_from_persistent(self, post, lbl, new_journal)
    ensures
        AbstractCrashAwareJournal::State::next_by(self.i(), post.i(), self.label_i(lbl),
            AbstractCrashAwareJournal::Step::load_ephemeral_from_persistent(new_journal.i_abstract()))
    {
        reveal(AbstractCrashAwareJournal::State::next_by);
        reveal(AbstractJournal::State::init_by);

        let persistent = self.persistent_image.unwrap();
        persistent.i_wf();
        new_journal.init_refines_abstract(persistent);
        AllocationJournal::State::initialize_tj_matches(new_journal, persistent);
        new_journal.initialized_i_abstract_journal_matches_image(persistent);
        assert(new_journal.tj() == persistent.tight_tj());
        let freeze_lbl = AllocationJournal::Label::FreezeForCommit{
            frozen_journal: post.persistent,
        };
        assert(AllocationJournal::State::next(new_journal, new_journal, freeze_lbl)) by {
            reveal(AllocationJournal::State::next);
            reveal(AllocationJournal::State::next_by);
            assert(AllocationJournal::State::next_by(
                new_journal,
                new_journal,
                freeze_lbl,
                AllocationJournal::Step::freeze_for_commit(),
            ));
        }
        assert(new_journal.acceptable_frozen_image(post.persistent, persistent)) by {
            assert(persistent.valid_image());
            assert(AllocationCrashAwareJournal::State::image_matches_metadata(persistent, post.persistent));
            assert(new_journal.disk_view == persistent.tj.disk_view);
            let tight_index = persistent.tight_tj().build_lsn_au_index_from_first(persistent.first);
            assert(new_journal.lsn_au_index == tight_index);
            assert(persistent.tj.disk_view.domain_au_bounded_wrt_index(tight_index));
            assert(persistent.tj.disk_view.entries.dom()
                <= new_journal.frozen_loose_domain(post.persistent)) by {
                assert forall |addr: crate::disk::GenericDisk_v::Address|
                    #[trigger] persistent.tj.disk_view.entries.dom().contains(addr)
                    implies new_journal.frozen_loose_domain(post.persistent).contains(addr) by {
                    assert(tight_index.values().contains(addr.au));
                    assert(new_journal.lsn_au_index.values().contains(addr.au));
                    let lsn = choose |lsn: nat| {
                        &&& new_journal.lsn_au_index.contains_key(lsn)
                        &&& new_journal.lsn_au_index[lsn] == addr.au
                    };
                    assert(tight_index.contains_key(lsn));
                    persistent.tight_tj().build_lsn_au_index_from_first_ensures(persistent.first);
                    reveal(TruncatedJournal::au_domain_valid);
                    assert(persistent.tight_tj().seq_start() <= lsn < persistent.tight_tj().seq_end());
                    persistent.valid_image_implies_tight_seq_bounds();
                    assert(post.persistent.boundary_lsn <= lsn < post.persistent.seq_end);
                    assert(new_journal.frozen_lsns(post.persistent).contains(lsn));
                    assert(new_journal.frozen_lsn_au_index(post.persistent).contains_key(lsn));
                    assert(new_journal.frozen_lsn_au_index(post.persistent)[lsn] == addr.au);
                    assert(new_journal.frozen_lsn_au_index(post.persistent).values().contains(addr.au));
                }
            }
            assert(maps_agree_on(
                new_journal.frozen_prefix_domain(post.persistent),
                persistent.tj.disk_view.entries,
                new_journal.disk_view.entries,
            ));
        }
        AllocationJournal::State::acceptable_frozen_image_matches_frozen_image(
            new_journal,
            post.persistent,
            persistent,
        );
        assert(post.persistent_image is None);
        assert(post.persistent_image_view() == new_journal.frozen_image(post.persistent));
        assert(post.persistent_image_view().i() == persistent.i());
        assert(post.i().persistent.wf());
        assert(post.i().persistent == persistent.i());
        assert(new_journal.i_abstract().journal == persistent.i());
        assert(new_journal.i_abstract().journal == post.i().persistent);
        assert(AbstractJournal::State::init_by(
            new_journal.i_abstract(),
            AbstractJournal::Config::initialize(post.i().persistent),
        )) by {
            reveal(AbstractJournal::State::init_by);
            reveal(AbstractJournal::State::initialize);
        }
    }

    pub proof fn read_for_recovery_refines(self, post: Self, lbl: AllocationCrashAwareJournal::Label)
    requires
        self.inv(),
        post.inv(),
        Self::read_for_recovery(self, post, lbl)
    ensures
        AbstractCrashAwareJournal::State::next_by(self.i(), post.i(), self.label_i(lbl), AbstractCrashAwareJournal::Step::read_for_recovery())
    {
        reveal(AbstractCrashAwareJournal::State::next_by);

        let aj = self.ephemeral->v;
        let alloc_lbl = AllocationJournal::Label::ReadForRecovery{messages: lbl.arrow_ReadForRecovery_records()};
        aj.next_refines_abstract(aj, alloc_lbl);
    }

    pub proof fn query_end_lsn_refines(self, post: Self, lbl: AllocationCrashAwareJournal::Label)
    requires
        self.inv(),
        post.inv(),
        Self::query_end_lsn(self, post, lbl)
    ensures
        AbstractCrashAwareJournal::State::next_by(self.i(), post.i(), self.label_i(lbl), AbstractCrashAwareJournal::Step::query_end_lsn())
    {
        reveal(AbstractCrashAwareJournal::State::next_by);

        let aj = self.ephemeral->v;
        let alloc_lbl = AllocationJournal::Label::QueryEndLsn{end_lsn: lbl->end_lsn };
        aj.next_refines_abstract(aj, alloc_lbl);
    }

    pub proof fn put_refines(self, post: Self, lbl: AllocationCrashAwareJournal::Label, 
        new_journal: AllocationJournal::State)
    requires
        self.inv(),
        post.inv(),
        Self::put(self, post, lbl, new_journal)
    ensures
        AbstractCrashAwareJournal::State::next_by(self.i(), post.i(), self.label_i(lbl),
            AbstractCrashAwareJournal::Step::put(new_journal.i_abstract()))
    {
        reveal(AbstractCrashAwareJournal::State::next_by);

        let aj = self.ephemeral->v;
        let alloc_lbl = AllocationJournal::Label::Put{messages: lbl.arrow_Put_records() };
        aj.next_refines_abstract(new_journal, alloc_lbl);
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);
        assert(AllocationJournal::State::next_by(
            aj,
            new_journal,
            alloc_lbl,
            AllocationJournal::Step::put(),
        ));
        if self.frozen is Some {
            AllocationJournal::State::put_preserves_frozen_metadata(
                aj,
                new_journal,
                alloc_lbl,
                self.frozen.unwrap(),
            );
            assert(post.i().frozen == self.i().frozen);
        }
    }

    pub proof fn internal_refines(self, post: Self, lbl: AllocationCrashAwareJournal::Label, 
        new_journal: AllocationJournal::State)
    requires
        self.inv(),
        post.inv(),
        Self::internal(self, post, lbl, new_journal)
    ensures
        AbstractCrashAwareJournal::State::next_by(self.i(), post.i(), self.label_i(lbl),
            AbstractCrashAwareJournal::Step::internal(new_journal.i_abstract()))
    {
        reveal(AbstractCrashAwareJournal::State::next_by);

        let aj = self.ephemeral->v;
        let alloc_lbl = AllocationJournal::Label::InternalAllocations{
            allocs: lbl->allocs,
            deallocs: lbl.arrow_Internal_deallocs(),
        };
        aj.next_refines_abstract(new_journal, alloc_lbl);
        assert(post.i().persistent == self.i().persistent) by {
            if self.persistent_image is Some {
                assert(post.persistent_image == self.persistent_image);
            } else {
                assert(new_journal.frozen_image(self.persistent).tight_tj()
                    == aj.frozen_image(self.persistent).tight_tj());
                assert(new_journal.frozen_image(self.persistent).i()
                    == aj.frozen_image(self.persistent).i());
            }
        }
        if self.frozen is Some {
            assert(new_journal.frozen_image(self.frozen.unwrap()).tight_tj()
                == aj.frozen_image(self.frozen.unwrap()).tight_tj());
            assert(new_journal.frozen_image(self.frozen.unwrap()).i()
                == aj.frozen_image(self.frozen.unwrap()).i());
            assert(post.i().frozen == self.i().frozen);
        }
    }

    pub proof fn commit_start_refines(self, post: Self, lbl: AllocationCrashAwareJournal::Label)
    requires
        self.inv(),
        post.inv(),
        Self::commit_start(self, post, lbl)
    ensures
        AbstractCrashAwareJournal::State::next_by(self.i(), post.i(), self.label_i(lbl),
            AbstractCrashAwareJournal::Step::commit_start())
    {
        reveal(AbstractCrashAwareJournal::State::next_by);

        let aj = self.ephemeral->v;
        let frozen_metadata = lbl->frozen_journal;
        let frozen_journal = aj.frozen_image(frozen_metadata);
        let alloc_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: frozen_metadata};
        AllocationJournal::State::frozen_journal_is_valid_image(aj, aj, alloc_lbl);
        frozen_journal.i_wf();
        frozen_journal.tight_i_matches();
        assert(aj.frozen_metadata_valid(frozen_metadata));
        assert(frozen_journal.tj.disk_view.boundary_lsn == frozen_metadata.boundary_lsn);
        assert(frozen_journal.tj.seq_start() == frozen_metadata.boundary_lsn);
        assert(self.i().frozen is None);

        assert(AllocationJournal::State::next(aj, aj, alloc_lbl));
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);
        let alloc_step = choose |step|
            AllocationJournal::State::next_by(aj, aj, alloc_lbl, step);
        assert(AllocationJournal::State::next_by(aj, aj, alloc_lbl, alloc_step));
        match alloc_step {
            AllocationJournal::Step::freeze_for_commit() => {},
            _ => { assert(false); },
        }
        aj.freeze_for_commit_refines(aj, alloc_lbl);
        aj.next_refines_abstract(aj, alloc_lbl);
        assert(self.i().ephemeral->v == aj.i_abstract());
        let abstract_lbl = aj.label_i_abstract(alloc_lbl);
        assert(abstract_lbl == AbstractJournal::Label::FreezeForCommitLabel{
            frozen_journal: frozen_journal.i(),
        });
        reveal(AbstractJournal::State::next);
        reveal(AbstractJournal::State::next_by);
        assert(aj.i_abstract().journal.includes_subseq(frozen_journal.i()));
        assert(self.i().ephemeral->v.journal == aj.i_abstract().journal);
        assert(self.i().ephemeral->v.journal.includes_subseq(frozen_journal.i()));
        assert(AbstractJournal::State::next_by(
            self.i().ephemeral->v,
            self.i().ephemeral->v,
            AbstractJournal::Label::FreezeForCommitLabel{frozen_journal: frozen_journal.i()},
            AbstractJournal::Step::freeze_for_commit(),
        ));

        assert(self.i().frozen is None);
        self.persistent_image_view_i_wf();
        assert(self.i().persistent.seq_end <= lbl->new_boundary_lsn);
        assert(post.i().frozen == Some(frozen_journal.i()));
        assert(AbstractCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(lbl),
            AbstractCrashAwareJournal::Step::commit_start(),
        ));
    }

    pub proof fn commit_complete_refines(self, post: Self, lbl: AllocationCrashAwareJournal::Label, 
        new_journal: AllocationJournal::State)
    requires
        self.inv(),
        post.inv(),
        Self::commit_complete(self, post, lbl, new_journal)
    ensures
        AbstractCrashAwareJournal::State::next_by(self.i(), post.i(), self.label_i(lbl),
            AbstractCrashAwareJournal::Step::commit_complete(new_journal.i_abstract()))
    {
        reveal(AbstractCrashAwareJournal::State::next_by);

        let freeze_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: self.frozen.unwrap()};
        assert(AllocationJournal::State::next(self.ephemeral->v, self.ephemeral->v, freeze_lbl)) by {
            reveal(AllocationJournal::State::next);
            reveal(AllocationJournal::State::next_by);
            assert(AllocationJournal::State::next_by(
                self.ephemeral->v,
                self.ephemeral->v,
                freeze_lbl,
                AllocationJournal::Step::freeze_for_commit(),
            ));
        }
        AllocationJournal::State::frozen_journal_is_valid_image(
            self.ephemeral->v,
            self.ephemeral->v,
            freeze_lbl,
        );
        let frozen_image = self.ephemeral->v.frozen_image(self.frozen.unwrap());
        frozen_image.i_wf();

        assert(self.i().frozen == Some(frozen_image.i()));
        assert(frozen_image.tj.seq_start() == self.i().frozen.unwrap().seq_start);
        assert(post.persistent == self.frozen.unwrap());
        assert(post.persistent_image is None);
        assert(post.ephemeral->v.frozen_image(post.persistent) == frozen_image);
        assert(post.i().persistent == frozen_image.i());

        let aj = self.ephemeral->v;
        let alloc_lbl = AllocationJournal::Label::DiscardOld{ 
            start_lsn: self.frozen.unwrap().boundary_lsn,
            require_end: lbl->require_end,
            deallocs: lbl->discarded,
        };
        aj.next_refines_abstract(new_journal, alloc_lbl);
    }

    pub proof fn next_refines(self, post: Self, lbl: AllocationCrashAwareJournal::Label)
    requires 
        self.inv(),
        post.inv(),
        Self::next(self, post, lbl)
    ensures
        AbstractCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(lbl))
    {
        reveal(AllocationCrashAwareJournal::State::next_by);  // unfortunate defaults
        reveal(AllocationCrashAwareJournal::State::next);
        reveal(AbstractCrashAwareJournal::State::next_by);
        reveal(AbstractCrashAwareJournal::State::next);

        let step = choose |step| AllocationCrashAwareJournal::State::next_by(self, post, lbl, step);
        match step {
            AllocationCrashAwareJournal::Step::load_ephemeral_from_persistent(new_journal) => {
                self.load_ephemeral_from_persistent_refines(post, lbl, new_journal);
            },
            AllocationCrashAwareJournal::Step::read_for_recovery() => {
                self.read_for_recovery_refines(post, lbl);
            },
            AllocationCrashAwareJournal::Step::query_end_lsn() => {
                self.query_end_lsn_refines(post, lbl);
            },
            AllocationCrashAwareJournal::Step::put(new_journal) => {
                self.put_refines(post, lbl, new_journal);
            },
            AllocationCrashAwareJournal::Step::internal(new_journal) => {
                self.internal_refines(post, lbl, new_journal);
            },
            AllocationCrashAwareJournal::Step::query_lsn_persistence() => {
                self.persistent_image_view_i_wf();
                assert( AbstractCrashAwareJournal::State::next_by(self.i(), post.i(), self.label_i(lbl),
                    AbstractCrashAwareJournal::Step::query_lsn_persistence()) ); // witness
            },
            AllocationCrashAwareJournal::Step::commit_start() => {
                self.commit_start_refines(post, lbl);
            },
            AllocationCrashAwareJournal::Step::commit_complete(new_journal) => {
                self.commit_complete_refines(post, lbl, new_journal);
            },
            AllocationCrashAwareJournal::Step::crash(persistent_image) => {
                if lbl->keep_in_flight {
                    let freeze_lbl = AllocationJournal::Label::FreezeForCommit{
                        frozen_journal: self.frozen.unwrap(),
                    };
                    assert(AllocationJournal::State::next(self.ephemeral->v, self.ephemeral->v, freeze_lbl)) by {
                        reveal(AllocationJournal::State::next);
                        reveal(AllocationJournal::State::next_by);
                        assert(AllocationJournal::State::next_by(
                            self.ephemeral->v,
                            self.ephemeral->v,
                            freeze_lbl,
                            AllocationJournal::Step::freeze_for_commit(),
                        ));
                    }
                    AllocationJournal::State::frozen_journal_is_valid_image(
                        self.ephemeral->v,
                        self.ephemeral->v,
                        freeze_lbl,
                    );
                    AllocationJournal::State::acceptable_frozen_image_matches_frozen_image(
                        self.ephemeral->v,
                        self.frozen.unwrap(),
                        persistent_image,
                    );
                    persistent_image.i_wf();
                    assert(self.i().frozen == Some(persistent_image.i()));
                    assert(post.i().persistent == persistent_image.i());
                } else {
                    persistent_image.i_wf();
                    if self.persistent_image is Some {
                        assert(persistent_image == self.persistent_image.unwrap());
                        assert(self.persistent_image_view() == persistent_image);
                    } else {
                        let freeze_lbl = AllocationJournal::Label::FreezeForCommit{
                            frozen_journal: self.persistent,
                        };
                        assert(AllocationJournal::State::next(self.ephemeral->v, self.ephemeral->v, freeze_lbl)) by {
                            reveal(AllocationJournal::State::next);
                            reveal(AllocationJournal::State::next_by);
                            assert(AllocationJournal::State::next_by(
                                self.ephemeral->v,
                                self.ephemeral->v,
                                freeze_lbl,
                                AllocationJournal::Step::freeze_for_commit(),
                            ));
                        }
                        AllocationJournal::State::acceptable_frozen_image_matches_frozen_image(
                            self.ephemeral->v,
                            self.persistent,
                            persistent_image,
                        );
                    }
                    assert(post.i().persistent == persistent_image.i());
                }
                assert( AbstractCrashAwareJournal::State::next_by(self.i(), post.i(), self.label_i(lbl),
                    AbstractCrashAwareJournal::Step::crash()) ); // witness
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn init_refines(self)
    requires Self::initialize(self)
    ensures AbstractCrashAwareJournal::State::initialize(self.i())
    {
        TruncatedJournal::mkfs_ensures();
        JournalImage::empty_is_valid_image();
        let empty = JournalImage::empty();
        assert(empty.tight_tj() == TruncatedJournal::mkfs());
        empty.i_wf();
        assert(empty.i() == MsgHistory::empty_history_at(0));
        assert(MsgHistory::empty_history_at(0) == MsgHistory{ msgs: Map::empty(), seq_start: 0, seq_end: 0});
    }
}

} // verus
