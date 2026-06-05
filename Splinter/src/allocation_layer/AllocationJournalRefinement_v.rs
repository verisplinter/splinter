// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

//use vstd::prelude_macros::*;
use vstd::prelude::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::*;
use crate::journal::LinkedJournal_v::{LinkedJournal, DiskView, TruncatedJournal};
use crate::allocation_layer::LikesJournal_v;
use crate::allocation_layer::LikesJournal_v::{LikesJournal};
use crate::allocation_layer::AllocationJournal_v::*;

verus!{

impl AllocationJournal::Step {
    pub open spec fn i(self) -> LikesJournal::Step {
        match self {
            Self::read_for_recovery(start_lsn, addr) =>
                LikesJournal::Step::read_for_recovery(addr),
            Self::freeze_for_commit() =>
                LikesJournal::Step::freeze_for_commit(),
            Self::query_end_lsn() =>
                LikesJournal::Step::query_end_lsn(),
            Self::put() =>
                LikesJournal::Step::put(),
            Self::discard_old(new_journal) =>
                LikesJournal::Step::discard_old(new_journal),
            Self::internal_journal_marshal(cut, addr, new_journal) =>
                LikesJournal::Step::internal_journal_marshal(cut, addr, new_journal),
            Self::internal_mini_allocator_fill() =>
                LikesJournal::Step::internal_no_op(),
            Self::internal_mini_allocator_prune() =>
                LikesJournal::Step::internal_no_op(),
            Self::internal_no_op() =>
                LikesJournal::Step::internal_no_op(),
            _ => { arbitrary() },   // TODO(travis): wart on the state machine language
        }
    }
}

impl AllocationJournal::Label {
    pub open spec(checked) fn i(self) -> LikesJournal::Label
    {
        match self {
            Self::ReadForRecovery{messages} =>
                LikesJournal::Label::ReadForRecovery{messages},
            Self::FreezeForCommit{frozen_journal} =>
                LikesJournal::Label::FreezeForCommit{frozen_journal: frozen_journal.tj},
            Self::QueryEndLsn{end_lsn} =>
                LikesJournal::Label::QueryEndLsn{end_lsn},
            Self::Put{messages} =>
                LikesJournal::Label::Put{messages},
            Self::DiscardOld{start_lsn, require_end, deallocs} =>
                LikesJournal::Label::DiscardOld{start_lsn, require_end},
            Self::InternalAllocations{allocs, deallocs} =>
                LikesJournal::Label::Internal{},
        }
    }
}

// The thrilling climax, the actual proof goal we want to use in lower
// refinement layers.
impl AllocationJournal::State {
    pub open spec(checked) fn i(self) -> LikesJournal::State
        recommends self.tj().decodable()
    {
        LikesJournal::State{
            journal: self.journal,
            lsn_addr_index: self.tj().build_lsn_addr_index(),
        }
    }

    proof fn read_witness_implies_addr_index_contains_value(self, start_lsn: LSN, addr: Address)
        requires
            self.inv(),
            self.tj().disk_view.entries.contains_key(addr),
            start_lsn == self.tj().disk_view.entries[addr].message_seq.maybe_discard_old(
                self.tj().disk_view.boundary_lsn,
            ).seq_start,
            start_lsn < self.tj().disk_view.entries[addr].message_seq.seq_end,
            self.lsn_au_index.contains_key(start_lsn),
            self.lsn_au_index[start_lsn] == addr.au,
        ensures
            self.i().lsn_addr_index.contains_value(addr),
    {
        let lsn = start_lsn;
        let index = self.i().lsn_addr_index;
        let first = self.lsn_au_index[self.tj().seq_start()];
        self.tj().build_lsn_au_index_from_first_ensures(first);
        reveal(TruncatedJournal::au_domain_valid);
        assert(self.tj().seq_start() <= lsn < self.tj().seq_end());
        self.tj().build_lsn_addr_index_ensures();
        reveal(TruncatedJournal::index_domain_valid);
        assert(index.contains_key(lsn));

        assert(self.tj().disk_view.addr_supports_lsn(addr, lsn));
        self.tj().disk_view.instantiate_index_keys_map_to_valid_entries(index, lsn);
        assert(self.tj().disk_view.addr_supports_lsn(index[lsn], lsn));
        assert(self.tj().disk_view.has_unique_lsns());
        assert(index[lsn] == addr);
        assert(index.contains_value(addr));
    }

    pub proof fn freeze_for_commit_refines(self, post: Self, lbl: AllocationJournal::Label)
        requires self.inv(), post.inv(), Self::freeze_for_commit(self, post, lbl)
        ensures
            LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::freeze_for_commit()),
            lbl->frozen_journal.tj.decodable(),
    {
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);
        reveal(LikesJournal::State::next_by);

        let frozen_journal = lbl->frozen_journal;
        let frozen_root = frozen_journal.tj.freshest_rec;
        let new_bdy = frozen_journal.tj.seq_start();

        assert(Self::next_by(self, post, lbl, AllocationJournal::Step::freeze_for_commit()));
        Self::frozen_journal_is_valid_image(self, post, lbl);
        assert(frozen_journal.tj.decodable());

        if frozen_root is Some {
            let root = frozen_root.unwrap();
            let frozen_index = frozen_journal.tj.build_lsn_addr_index();
            let pre_index = self.tj().build_lsn_addr_index();
            let frozen_dv = frozen_journal.tj.disk_view;
            let pre_dv = self.tj().disk_view;

            frozen_journal.tj.build_lsn_addr_index_ensures();
            assert(frozen_index.contains_value(root));
            let lsn = choose |lsn: LSN| #![auto] frozen_index.contains_key(lsn) && frozen_index[lsn] == root;
            frozen_dv.instantiate_index_keys_map_to_valid_entries(frozen_index, lsn);

            assert(frozen_journal.tj.disk_view.entries.contains_key(root));
            assert(self.tj().disk_view.entries.contains_key(root));
            assert(frozen_journal.tj.disk_view.entries[root] == self.tj().disk_view.entries[root]);
            assert(frozen_dv.addr_supports_lsn(root, lsn));
            assert(frozen_dv.boundary_lsn <= lsn);
            assert(frozen_dv.entries[root].message_seq.contains(lsn));
            assert(self.tj().disk_view.boundary_lsn <= frozen_journal.tj.disk_view.boundary_lsn);
            assert(pre_dv.entries[root].message_seq.contains(lsn));
            assert(pre_dv.addr_supports_lsn(root, lsn));

            assert(self.lsn_au_index.values().contains(root.au));
            if !self.lsn_au_index.contains_key(lsn) {
                assert(lsn < pre_dv.boundary_lsn);
                assert(false);
            }

            self.tj().build_lsn_au_index_ensures(self.tj().seq_start());
            reveal(TruncatedJournal::au_domain_valid);
            assert(self.tj().seq_start() <= lsn < self.tj().seq_end());

            self.tj().build_lsn_addr_index_ensures();
            reveal(TruncatedJournal::index_domain_valid);
            assert(pre_index.contains_key(lsn));
            pre_dv.instantiate_index_keys_map_to_valid_entries(pre_index, lsn);
            assert(pre_dv.addr_supports_lsn(pre_index[lsn], lsn));
            assert(pre_index[lsn] == root);
            assert(self.i().lsn_addr_index.contains_value(root));
        }
    }

    pub proof fn read_for_recovery_refines(self, post: Self, lbl: AllocationJournal::Label, start_lsn: LSN, addr: Address)
        requires self.inv(), post.inv(), Self::read_for_recovery(self, post, lbl, start_lsn, addr)
        ensures LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::read_for_recovery(addr))
    {
        reveal(LikesJournal::State::next_by);
        self.read_witness_implies_addr_index_contains_value(start_lsn, addr);
    }

    pub proof fn discard_old_refines(self, post: Self, lbl: AllocationJournal::Label, new_journal: LinkedJournal::State)
        requires self.inv(), post.inv(), Self::discard_old(self, post, lbl, new_journal)
        ensures LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::discard_old(new_journal))
    {
        reveal(LikesJournal::State::next_by);
        assert(post.i().journal == new_journal);

        let start_lsn = lbl->start_lsn;
        let require_end = lbl->require_end;
        let keep_addrs = Set::new(|addr: Address| addr.wf() && post.lsn_au_index.values().contains(addr.au));

        let lsn_addr_index_post = LikesJournal_v::lsn_addr_index_discard_up_to(self.i().lsn_addr_index, start_lsn);
        let i_keep_addrs = lsn_addr_index_post.values();

        reveal(TruncatedJournal::index_domain_valid);

        if self.tj().freshest_rec is Some {
            self.tj().disk_view.build_lsn_addr_index_domain_valid(self.tj().freshest_rec);
        }

        post.tj().disk_view.sub_disk_with_newer_lsn_repr_index(self.tj().disk_view, post.tj().freshest_rec);
        assert(post.i().lsn_addr_index <= self.i().lsn_addr_index);

        LikesJournal_v::lsn_addr_index_discard_up_to_ensures(self.i().lsn_addr_index, start_lsn);
        assert(lsn_addr_index_post <= self.i().lsn_addr_index);

        if post.tj().freshest_rec is Some {
            post.tj().disk_view.build_lsn_addr_index_domain_valid(self.tj().freshest_rec);
        }

        assert(post.i().lsn_addr_index =~= lsn_addr_index_post);
        let first = self.lsn_au_index[self.tj().seq_start()];
        assert(self.lsn_au_index == self.tj().build_lsn_au_index_from_first(first));

        self.tj().disk_view.build_lsn_au_index_equiv_page_walk(self.tj().freshest_rec, first);
        self.tj().disk_view.build_lsn_au_index_page_walk_consistency(self.tj().freshest_rec);
        self.tj().disk_view.build_lsn_addr_index_reflects_disk_view(self.tj().freshest_rec);
        assert(i_keep_addrs <= keep_addrs);

        if start_lsn < self.tj().seq_end() {
            assert(self.tj().discard_old_cond(start_lsn, i_keep_addrs, new_journal.truncated_journal));
        } else {
            TruncatedJournal::empty_at_ensures(start_lsn);
            assert(new_journal.truncated_journal == TruncatedJournal::empty_at(start_lsn));
            assert(new_journal.truncated_journal.wf());
            assert(new_journal.truncated_journal.freshest_rec is None);
            assert(new_journal.truncated_journal.disk_view.is_sub_disk(self.tj().disk_view.discard_old(start_lsn)));
        }
    }

    pub proof fn internal_journal_marshal_refines(self, post: Self, lbl: AllocationJournal::Label, 
        cut: LSN, addr: Address, new_journal: LinkedJournal::State)
        requires self.inv(), post.inv(), Self::internal_journal_marshal(self, post, lbl, cut, addr, new_journal)
        ensures LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::internal_journal_marshal(cut, addr, new_journal))
    {
        reveal(LikesJournal::State::next_by);
        reveal(LinkedJournal::State::next_by);
        self.tj().disk_view.sub_disk_repr_index(post.tj().disk_view, self.tj().freshest_rec);
    }

    pub proof fn next_refines(self, post: Self, lbl: AllocationJournal::Label)
    requires
        self.inv(),
        post.inv(),
        AllocationJournal::State::next(self, post, lbl),
    ensures
        LikesJournal::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(LikesJournal::State::next_by);  // unfortunate defaults
        reveal(LikesJournal::State::next);
        reveal(AllocationJournal::State::next_by);
        reveal(AllocationJournal::State::next);

        let step = choose |step| AllocationJournal::State::next_by(self, post, lbl, step);
        match step {
            AllocationJournal::Step::read_for_recovery(start_lsn, addr) => {
                self.read_for_recovery_refines(post, lbl, start_lsn, addr);
            },
            AllocationJournal::Step::freeze_for_commit() => {
                self.freeze_for_commit_refines(post, lbl);
            },
            AllocationJournal::Step::discard_old(new_journal) => {
                self.discard_old_refines(post, lbl, new_journal);
            },
            AllocationJournal::Step::internal_journal_marshal(cut, addr, new_journal) => {
                self.internal_journal_marshal_refines(post, lbl, cut, addr, new_journal);
            },
            _ => {
                reveal(LinkedJournal::State::next);
                reveal(LinkedJournal::State::next_by);
                assert( LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), step.i()) );
            },
        }
    }

    pub proof fn init_refines(self, journal: LinkedJournal::State, image: JournalImage) 
    requires AllocationJournal::State::initialize(self, journal, image)
    ensures LikesJournal::State::initialize(self.i(), image.tj)
    {
    }
}


} // verus!
