// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Composed refinement from AllocationJournal to AbstractJournal.

use vstd::prelude::*;

use crate::abstract_system::AbstractJournal_v::AbstractJournal;
use crate::abstract_system::MsgHistory_v::*;
use crate::allocation_layer::AllocationJournal_v::{
    AllocationJournal, JournalImage,
};
use crate::allocation_layer::AllocationJournalRefinement_v::*;
use crate::allocation_layer::LikesJournal_v::LikesJournal;
use crate::allocation_layer::LikesJournalRefinement_v::*;
use crate::journal::LinkedJournal_v::{LinkedJournal, TruncatedJournal};
use crate::journal::LinkedJournalRefinement_v::*;
use crate::journal::PagedJournal_v::{JournalRecord, PagedJournal};
use crate::journal::PagedJournalRefinement_v::*;

verus!{

impl AllocationJournal::Label {
    pub open spec fn i_abstract(self) -> AbstractJournal::Label {
        LikesJournal::State::lbl_i(self.i()).i().i()
    }
}

impl AllocationJournal::State {
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

    pub open spec fn label_i_abstract(self, lbl: AllocationJournal::Label) -> AbstractJournal::Label {
        LikesJournal::State::lbl_i(self.label_i(lbl)).i().i()
    }

    pub open spec fn i_abstract(self) -> AbstractJournal::State {
        self.i().i().i().i()
    }

    pub proof fn i_abstract_seq_bounds(self)
        requires self.refinement_inv(),
        ensures
            self.i_abstract().journal.seq_start == self.tj().seq_start(),
            self.i_abstract().journal.seq_end == self.seq_end(),
    {
        self.i_inv();
        self.i().i_inv();
        self.i().i().i_wf();
        JournalRecord::i_lemma_forall();
        let linked = self.i().i();
        let paged = linked.i();
        let base = paged.truncated_journal.i();
        assert(linked.truncated_journal == self.tj());
        assert(paged.truncated_journal == self.tj().i());
        assert(base.seq_start == self.tj().seq_start());
        assert(base.can_concat(paged.unmarshalled_tail));
    }

    pub proof fn init_refines_abstract(self, image: JournalImage)
        requires
            Self::initialize(self, image),
        ensures
            AbstractJournal::State::initialize(self.i_abstract(), self.i_abstract().journal),
    {
        self.init_refines(image);
        self.i().init_refines(self.tj());
        self.i().i().init_refines(self.tj());
        self.i().i().i().init_refines(self.tj().i());
    }

    pub proof fn next_refines_abstract(self, post: Self, lbl: AllocationJournal::Label)
        requires
            self.refinement_inv(),
            post.refinement_inv(),
            Self::next(self, post, lbl),
        ensures
            AbstractJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(lbl),
            ),
    {
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);
        reveal(AbstractJournal::State::next);
        reveal(AbstractJournal::State::next_by);

        self.next_refines(post, lbl);

        let likes = self.i();
        let likes_post = post.i();
        let likes_lbl = self.label_i(lbl);
        self.i_inv();
        post.i_inv();

        likes.next_refines(likes_post, likes_lbl);

        let linked = likes.i();
        let linked_post = likes_post.i();
        let linked_lbl = LikesJournal::State::lbl_i(likes_lbl);
        likes.i_inv();
        likes_post.i_inv();

        linked.next_refines(linked_post, linked_lbl);

        linked.truncated_journal.iwf();
        linked_post.truncated_journal.iwf();

        let paged = linked.i();
        let paged_post = linked_post.i();
        let paged_lbl = linked_lbl.i();
        linked.i_wf();
        linked_post.i_wf();

        paged.next_refines(paged_post, paged_lbl);
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

impl JournalImage {
    pub open spec fn i(self) -> MsgHistory {
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

} // verus!
