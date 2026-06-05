// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
use vstd::prelude::*;

use crate::abstract_system::AbstractCrashAwareJournal_v;
use crate::abstract_system::AbstractCrashAwareJournal_v::AbstractCrashAwareJournal;
use crate::abstract_system::AbstractJournal_v::AbstractJournal;
use crate::abstract_system::MsgHistory_v::*;
use crate::allocation_layer::AllocationCrashAwareJournal_v::*;
use crate::allocation_layer::AllocationJournal_v::{AllocationJournal, JournalImage};
use crate::allocation_layer::LikesJournal_v::LikesJournal;
use crate::journal::LinkedJournal_v::{LinkedJournal, TruncatedJournal};
use crate::journal::PagedJournal_v::JournalRecord;

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
    pub open spec fn i_abstract(self) -> AbstractJournal::State
    {
        self.i().i().i().i()
    }

    // refines to abstract journal
    pub proof fn init_refines_abstract(self, journal: LinkedJournal::State, image: JournalImage)
    requires
        Self::initialize(self, journal, image)
    ensures
        AbstractJournal::State::initialize(self.i_abstract(), self.i_abstract().journal)
    {
        self.init_refines(journal, image);
        self.i().init_refines(image.tj);
        self.i().i().init_refines(image.tj);
        self.i().i().i().init_refines(image.tj.i());
    }

    // refines to abstract journal
    pub proof fn next_refines_abstract(self, post: Self, lbl: AllocationJournal::Label)
    requires
        self.inv(),
        post.inv(),
        Self::next(self, post, lbl)
    ensures
        AbstractJournal::State::next(self.i_abstract(), post.i_abstract(), lbl.i_abstract())
    {
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);
        reveal(AbstractJournal::State::next);
        reveal(AbstractJournal::State::next_by);

        self.next_refines(post, lbl); // alloc refines to likes

        let likes = self.i();
        let likes_post = post.i();
        let likes_lbl = lbl.i();

        likes.next_refines(likes_post, likes_lbl); // likes refines to linked

        let linked = likes.i();
        let linked_post = likes_post.i();
        let linked_lbl = LikesJournal::State::lbl_i(likes_lbl);

        linked.next_refines(linked_post, linked_lbl); // linked refines to paged

        linked.truncated_journal.iwf();
        linked_post.truncated_journal.iwf();
        
        let paged = linked.i();
        let paged_post = linked_post.i();
        let paged_lbl = linked_lbl.i();

        paged.next_refines(paged_post, paged_lbl); // paged refines to abstract
    }
}

impl JournalImage{
    pub open spec fn i(self) -> MsgHistory
    {
        self.tj.i().i()
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
                AbstractCrashAwareJournal::Label::CommitStartLabel{
                    new_boundary_lsn,
                    frozen_journal: frozen_journal.i(),
                },
            Self::CommitComplete{ require_end, discarded } =>
                AbstractCrashAwareJournal::Label::CommitCompleteLabel{require_end},
            Self::Crash{ keep_in_flight } => AbstractCrashAwareJournal::Label::CrashLabel{ keep_in_flight },
        }
    }
}

impl AllocationCrashAwareJournal::State{
    pub open spec fn i(self) -> AbstractCrashAwareJournal::State 
    {
        let i_frozen =
            if self.frozen is None { None }
            else { Some(self.frozen.unwrap().i()) };

        AbstractCrashAwareJournal::State{
            persistent: self.persistent.i(),
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
        AbstractCrashAwareJournal::State::next_by(self.i(), post.i(), lbl.i(), 
            AbstractCrashAwareJournal::Step::load_ephemeral_from_persistent(new_journal.i_abstract()))
    {
        reveal(AbstractCrashAwareJournal::State::next_by);
        reveal(AbstractJournal::State::init_by);

        let persistent = post.persistent;
        let first = persistent.first;
        assert(persistent.tj.disk_view.pointer_is_upstream(persistent.tj.freshest_rec, first));
        assert(persistent.tj.decodable());
        persistent.tj.iwf();
        JournalRecord::i_lemma_forall();
        assert(post.i().persistent.wf());
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
        AbstractCrashAwareJournal::State::next_by(self.i(), post.i(), lbl.i(), AbstractCrashAwareJournal::Step::read_for_recovery())
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
        AbstractCrashAwareJournal::State::next_by(self.i(), post.i(), lbl.i(), AbstractCrashAwareJournal::Step::query_end_lsn())
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
        AbstractCrashAwareJournal::State::next_by(self.i(), post.i(), lbl.i(), 
            AbstractCrashAwareJournal::Step::put(new_journal.i_abstract()))
    {
        reveal(AbstractCrashAwareJournal::State::next_by);

        let aj = self.ephemeral->v;
        let alloc_lbl = AllocationJournal::Label::Put{messages: lbl.arrow_Put_records() };
        aj.next_refines_abstract(new_journal, alloc_lbl);
    }

    pub proof fn internal_refines(self, post: Self, lbl: AllocationCrashAwareJournal::Label, 
        new_journal: AllocationJournal::State)
    requires
        self.inv(),
        post.inv(),
        Self::internal(self, post, lbl, new_journal)
    ensures
        AbstractCrashAwareJournal::State::next_by(self.i(), post.i(), lbl.i(), 
            AbstractCrashAwareJournal::Step::internal(new_journal.i_abstract()))
    {
        reveal(AbstractCrashAwareJournal::State::next_by);

        let aj = self.ephemeral->v;
        let alloc_lbl = AllocationJournal::Label::InternalAllocations{
            allocs: lbl->allocs,
            deallocs: lbl.arrow_Internal_deallocs(),
        };
        aj.next_refines_abstract(new_journal, alloc_lbl);
    }

    pub proof fn commit_start_refines(self, post: Self, lbl: AllocationCrashAwareJournal::Label)
    requires
        self.inv(),
        post.inv(),
        Self::commit_start(self, post, lbl)
    ensures
        AbstractCrashAwareJournal::State::next_by(self.i(), post.i(), lbl.i(),
            AbstractCrashAwareJournal::Step::commit_start())
    {
        reveal(AbstractCrashAwareJournal::State::next_by);

        let frozen_journal = lbl->frozen_journal;
        let aj = self.ephemeral->v;
        let alloc_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal};
        frozen_journal.tj.iwf();
        JournalRecord::i_lemma_forall();
        assert(frozen_journal.tj.seq_start() == frozen_journal.i().seq_start);
        assert(frozen_journal.tj.seq_end() == frozen_journal.i().seq_end);
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
        let abstract_lbl = alloc_lbl.i_abstract();
        assert(abstract_lbl
            == AbstractJournal::Label::FreezeForCommitLabel{frozen_journal: frozen_journal.i()});
        assert(self.i().ephemeral->v == aj.i_abstract());
        reveal(AbstractJournal::State::next);
        reveal(AbstractJournal::State::next_by);
        let abstract_step = choose |step|
            AbstractJournal::State::next_by(aj.i_abstract(), aj.i_abstract(), abstract_lbl, step);
        assert(AbstractJournal::State::next_by(aj.i_abstract(), aj.i_abstract(), abstract_lbl, abstract_step));
        match abstract_step {
            AbstractJournal::Step::freeze_for_commit() => {
                reveal(AbstractJournal::State::next_by);
                reveal(AbstractJournal::State::freeze_for_commit);
            },
            _ => {
                reveal(AbstractJournal::State::next_by);
                assert(false);
            },
        }
        assert(aj.i_abstract().journal.includes_subseq(frozen_journal.i()));
        assert(self.i().ephemeral->v.journal == aj.i_abstract().journal);
        assert(self.i().ephemeral->v.journal.includes_subseq(frozen_journal.i()));

        assert(self.i().frozen is None);
        assert(frozen_journal.tj.seq_start() == frozen_journal.i().seq_start);
        assert(post.i().frozen == Some(frozen_journal.i()));
        assert(AbstractCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(),
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
        AbstractCrashAwareJournal::State::next_by(self.i(), post.i(), lbl.i(), 
            AbstractCrashAwareJournal::Step::commit_complete(new_journal.i_abstract()))
    {
        reveal(AbstractCrashAwareJournal::State::next_by);

        self.frozen.unwrap().tj.iwf();
        JournalRecord::i_lemma_forall();

        assert(self.frozen.unwrap().tj.seq_start() == self.i().frozen.unwrap().seq_start);

        let aj = self.ephemeral->v;
        let alloc_lbl = AllocationJournal::Label::DiscardOld{ 
            start_lsn: self.frozen.unwrap().tj.seq_start(),
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
        AbstractCrashAwareJournal::State::next(self.i(), post.i(), lbl.i())
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
                assert( AbstractCrashAwareJournal::State::next_by(self.i(), post.i(), lbl.i(), 
                    AbstractCrashAwareJournal::Step::query_lsn_persistence()) ); // witness
            },
            AllocationCrashAwareJournal::Step::commit_start() => {
                self.commit_start_refines(post, lbl);
            },
            AllocationCrashAwareJournal::Step::commit_complete(new_journal) => {
                self.commit_complete_refines(post, lbl, new_journal);
            },
            AllocationCrashAwareJournal::Step::crash() => {
                assert( AbstractCrashAwareJournal::State::next_by(self.i(), post.i(), lbl.i(), 
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
    }
}

} // verus
