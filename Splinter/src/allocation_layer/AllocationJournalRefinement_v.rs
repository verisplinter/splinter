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
            Self::discard_old() =>
                arbitrary(),
            Self::internal_journal_marshal(_, _) =>
                arbitrary(),
            Self::internal_mini_allocator_fill(_) =>
                LikesJournal::Step::internal_no_op(),
            Self::internal_mini_allocator_prune(_) =>
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
                arbitrary(),
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
    pub open spec(checked) fn refinement_inv(self) -> bool {
        &&& self.inv()
        &&& self.semantic_inv()
    }

    pub open spec(checked) fn label_i(self, lbl: AllocationJournal::Label) -> LikesJournal::Label
    {
        match lbl {
            AllocationJournal::Label::FreezeForCommit{frozen_journal} =>
                LikesJournal::Label::FreezeForCommit{
                    frozen_journal: self.frozen_image(frozen_journal).tight_tj(),
                },
            _ => lbl.i(),
        }
    }

    pub open spec(checked) fn i(self) -> LikesJournal::State
        recommends self.tj().decodable()
    {
        LikesJournal::State{
            journal: LinkedJournal::State{
                truncated_journal: self.tj(),
                unmarshalled_tail: self.unmarshalled_tail,
            },
            lsn_addr_index: self.tj().build_lsn_addr_index(),
        }
    }

    proof fn read_witness_implies_addr_index_contains_value(self, start_lsn: LSN, addr: Address)
        requires
            self.refinement_inv(),
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
        self.tj_inherits_semantic_structure();
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
        requires self.refinement_inv(), post.inv(), Self::freeze_for_commit(self, post, lbl)
        ensures
            LikesJournal::State::next_by(self.i(), post.i(), self.label_i(lbl), LikesJournal::Step::freeze_for_commit()),
            post.refinement_inv(),
            self.frozen_image(lbl->frozen_journal).tight_tj().decodable(),
    {
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);
        reveal(LikesJournal::State::next_by);

        let frozen_metadata = lbl->frozen_journal;
        let frozen_journal = self.frozen_image(frozen_metadata);
        let frozen_root = frozen_metadata.freshest_rec;
        let new_bdy = frozen_metadata.boundary_lsn;
        assert(post == self);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
        self.tj_inherits_semantic_structure();

        assert(Self::next_by(self, post, lbl, AllocationJournal::Step::freeze_for_commit()));
        Self::frozen_journal_is_valid_image(self, post, lbl);
        assert(self.frozen_metadata_valid(frozen_metadata));
        assert(frozen_journal.valid_image());
        frozen_journal.valid_image_implies_tight_valid_image();
        assert(frozen_journal.tight_tj().decodable());
        assert(frozen_journal.tight_tj().disk_view.is_sub_disk_with_newer_lsn(self.tj().disk_view));

        if frozen_root is Some {
            let root = frozen_root.unwrap();
            let first = if self.tj().freshest_rec is Some {
                self.lsn_au_index[self.tj().seq_start()]
            } else {
                0
            };

            assert(frozen_journal.valid_image());
            assert(frozen_journal.tight_tj().disk_view.is_nondangling_pointer(frozen_root));
            assert(frozen_journal.tight_tj().disk_view.entries.contains_key(root));
            assert(frozen_journal.tight_tj().disk_view.entries[root].message_seq.seq_end
                == frozen_metadata.seq_end);
            assert(frozen_journal.tight_tj().disk_view.is_sub_disk_with_newer_lsn(self.tj().disk_view));
            assert(self.tj().disk_view.entries.contains_key(root));
            assert(self.tj().disk_view.entries[root] == frozen_journal.tight_tj().disk_view.entries[root]);
            assert(self.tj().seq_start() <= frozen_metadata.boundary_lsn);
            assert(frozen_metadata.boundary_lsn < frozen_metadata.seq_end);
            assert(self.tj().disk_view.boundary_lsn < self.tj().disk_view.entries[root].message_seq.seq_end);
            assert(self.tj().valid_structure(self.lsn_au_index, first));
            assert(self.tj().disk_view.pointer_is_upstream(self.tj().freshest_rec, first));
            self.semantic_entry_not_after_freshest(root);
            self.tj().disk_view.boundary_crossing_entry_in_build_tight(
                self.tj().freshest_rec,
                first,
                self.lsn_au_index,
                root,
            );
            self.tj().disk_view.build_tight_domain_is_build_lsn_addr_index_range(self.tj().freshest_rec);
            assert(self.tj().disk_view.build_tight(self.tj().freshest_rec).entries.dom().contains(root));
            assert(self.tj().build_lsn_addr_index().values().contains(root));
            assert(self.tj().build_lsn_addr_index().contains_value(root));
            assert(self.i().lsn_addr_index == self.tj().build_lsn_addr_index());
            assert(self.i().lsn_addr_index.contains_value(root));
        }
    }

    pub proof fn read_for_recovery_refines(self, post: Self, lbl: AllocationJournal::Label, start_lsn: LSN, addr: Address)
        requires self.refinement_inv(), post.inv(), Self::read_for_recovery(self, post, lbl, start_lsn, addr)
        ensures
            LikesJournal::State::next_by(self.i(), post.i(), self.label_i(lbl), LikesJournal::Step::read_for_recovery(addr)),
            post.refinement_inv(),
    {
        reveal(LikesJournal::State::next_by);
        assert(post == self);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
        assert(self.tj().disk_view.entries.dom().contains(addr));
        assert(self.tj().disk_view.entries.contains_key(addr));
        assert(self.tj().disk_view.entries[addr] == self.disk_view.entries[addr]);
        self.read_witness_implies_addr_index_contains_value(start_lsn, addr);
    }

    pub proof fn discard_old_refines(self, post: Self, lbl: AllocationJournal::Label)
        requires self.refinement_inv(), post.inv(), Self::discard_old(self, post, lbl)
        ensures
            LikesJournal::State::next_by(self.i(), post.i(), self.label_i(lbl), LikesJournal::Step::discard_old(post.i().journal)),
            post.refinement_inv(),
    {
        reveal(LikesJournal::State::next_by);
        let new_journal = post.i().journal;
        self.tj_inherits_semantic_structure();
        AllocationJournal::State::discard_old_tj_is_newer_subdisk(self, post, lbl);
        post.tj_inherits_semantic_structure();
        assert(post.refinement_inv());
        assert(new_journal.truncated_journal == post.tj());

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
            post.tj().disk_view.build_lsn_addr_index_domain_valid(post.tj().freshest_rec);
        }

        assert(post.i().lsn_addr_index =~= lsn_addr_index_post);
        let first = self.lsn_au_index[self.tj().seq_start()];
        assert(self.lsn_au_index == self.tj().build_lsn_au_index_from_first(first));

        self.tj().disk_view.build_lsn_au_index_equiv_page_walk(self.tj().freshest_rec, first);
        self.tj().disk_view.build_lsn_au_index_page_walk_consistency(self.tj().freshest_rec);
        self.tj().disk_view.build_lsn_addr_index_reflects_disk_view(self.tj().freshest_rec);
        assert(i_keep_addrs <= keep_addrs);

        if start_lsn < self.tj().seq_end() {
            assert(i_keep_addrs <= post.tj().disk_view.entries.dom()) by {
                assert forall |addr: Address| #[trigger] i_keep_addrs.contains(addr)
                    implies post.tj().disk_view.entries.dom().contains(addr) by {
                    let lsn = choose |lsn: LSN| #[trigger] lsn_addr_index_post.contains_key(lsn)
                        && lsn_addr_index_post[lsn] == addr;
                    assert(post.i().lsn_addr_index.contains_key(lsn));
                    assert(post.i().lsn_addr_index[lsn] == addr);
                    post.tj().build_lsn_addr_index_ensures();
                    reveal(DiskView::index_keys_map_to_valid_entries);
                    assert(post.tj().disk_view.index_keys_map_to_valid_entries(post.i().lsn_addr_index));
                    post.tj().disk_view.instantiate_index_keys_map_to_valid_entries(post.i().lsn_addr_index, lsn);
                }
            }
            assert(self.tj().discard_old_cond(start_lsn, i_keep_addrs, new_journal.truncated_journal));
        } else {
            TruncatedJournal::empty_at_ensures(start_lsn);
            assert(new_journal.truncated_journal == TruncatedJournal::empty_at(start_lsn));
            assert(new_journal.truncated_journal.wf());
            assert(new_journal.truncated_journal.freshest_rec is None);
            assert(new_journal.truncated_journal.disk_view.is_sub_disk(self.tj().disk_view.discard_old(start_lsn)));
        }
    }

    pub proof fn query_end_lsn_refines(self, post: Self, lbl: AllocationJournal::Label)
        requires self.refinement_inv(), post.inv(), Self::query_end_lsn(self, post, lbl)
        ensures
            LikesJournal::State::next_by(self.i(), post.i(), self.label_i(lbl), LikesJournal::Step::query_end_lsn()),
            post.refinement_inv(),
    {
        reveal(LikesJournal::State::next_by);
        assert(post == self);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn put_refines(self, post: Self, lbl: AllocationJournal::Label)
        requires self.refinement_inv(), post.inv(), Self::put(self, post, lbl)
        ensures
            LikesJournal::State::next_by(self.i(), post.i(), self.label_i(lbl), LikesJournal::Step::put()),
            post.refinement_inv(),
    {
        reveal(LikesJournal::State::next_by);
        assert(post.disk_view == self.disk_view);
        assert(post.freshest_rec == self.freshest_rec);
        assert(post.lsn_au_index == self.lsn_au_index);
        assert(post.au_page_bounds == self.au_page_bounds);
        assert(post.mini_allocator == self.mini_allocator);
        assert(post.tj() == self.tj());
        assert(post.unmarshalled_tail.seq_start == self.unmarshalled_tail.seq_start);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn internal_journal_marshal_refines(self, post: Self, lbl: AllocationJournal::Label, 
        cut: LSN, addr: Address)
        requires self.refinement_inv(), post.inv(), Self::internal_journal_marshal(self, post, lbl, cut, addr)
        ensures
            LikesJournal::State::next_by(self.i(), post.i(), self.label_i(lbl), LikesJournal::Step::internal_journal_marshal(cut, addr, post.i().journal)),
            post.refinement_inv(),
    {
        reveal(LikesJournal::State::next_by);
        reveal(LinkedJournal::State::next_by);
        let new_journal = post.i().journal;
        self.tj_inherits_semantic_structure();
        AllocationJournal::State::internal_journal_marshal_view_preserves(self, post, lbl, cut, addr);
        AllocationJournal::State::internal_journal_marshal_index_preserves(self, post, lbl, cut, addr);
        AllocationJournal::State::internal_journal_marshal_allocator_preserves(self, post, lbl, cut, addr);
        let msgs = self.unmarshalled_tail.discard_recent(cut);
        let update = singleton_index(msgs.seq_start, msgs.seq_end, addr.au);
        lsn_au_index_append_record_ensures(self.lsn_au_index, msgs, addr.au);
        assert(post.au_page_bounds_match_index()) by {
            assert(post.au_page_bounds == self.au_page_bounds.insert(addr.au, addr.page));
            assert(post.lsn_au_index == lsn_au_index_append_record(self.lsn_au_index, msgs, addr.au));
            assert(post.lsn_au_index.values() == self.lsn_au_index.values() + set![addr.au]);
            assert(self.au_page_bounds_match_index());
            assert(post.au_page_bounds.dom() =~= self.au_page_bounds.dom() + set![addr.au]);
        }
        assert(post.tj().disk_view.is_sub_disk(post.disk_view)) by {
            assert(post.tj().disk_view.entries <= post.disk_view.entries);
        }
        post.disk_view.sub_disk_decodable_implies_path_decodable(post.tj().disk_view, post.freshest_rec);
        assert(post.disk_view.path_decodable(post.freshest_rec));
        AllocationJournal::State::internal_journal_marshal_semantic_inv(self, post, lbl, cut, addr);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
        post.tj_inherits_semantic_structure();
        assert(new_journal.truncated_journal == post.tj());
        assert(new_journal.unmarshalled_tail == post.unmarshalled_tail);
        assert(self.tj().disk_view.is_sub_disk(post.tj().disk_view)) by {
            assert(post.tj() == self.tj().append_record(addr, msgs));
            assert(!self.tj().disk_view.entries.contains_key(addr)) by {
                if self.tj().disk_view.entries.contains_key(addr) {
                    assert(AllocationJournal::State::disk_domain_not_free(self.tj().disk_view, self.mini_allocator));
                    assert(!self.mini_allocator.can_allocate(addr));
                    assert(false);
                }
            }
            assert forall |x: Address| #[trigger] self.tj().disk_view.entries.contains_key(x)
                implies post.tj().disk_view.entries.contains_key(x)
                    && post.tj().disk_view.entries[x] == self.tj().disk_view.entries[x] by {
                assert(x != addr);
            }
        }
        self.tj().disk_view.sub_disk_repr_index(post.tj().disk_view, self.tj().freshest_rec);
    }

    pub proof fn internal_mini_allocator_fill_refines(self, post: Self, lbl: AllocationJournal::Label, post_disk_view: DiskView)
        requires self.refinement_inv(), post.inv(), Self::internal_mini_allocator_fill(self, post, lbl, post_disk_view)
        ensures
            LikesJournal::State::next_by(self.i(), post.i(), self.label_i(lbl), LikesJournal::Step::internal_no_op()),
            post.refinement_inv(),
    {
        reveal(LikesJournal::State::next_by);
        reveal(AllocationJournal::State::next_by);
        assert(AllocationJournal::State::next_by(
            self,
            post,
            lbl,
            AllocationJournal::Step::internal_mini_allocator_fill(post_disk_view),
        ));
        AllocationJournal::State::internal_mini_allocator_fill_tj_unchanged(self, post, lbl, post_disk_view);
        assert(post.tj() == self.tj());
        assert(self.tj().disk_view.is_sub_disk(self.disk_view));
        assert(self.disk_view.is_sub_disk(post.disk_view));
        assert(post.tj().disk_view.is_sub_disk(post.disk_view)) by {
            DiskView::sub_disk_transitive_auto();
        }
        post.disk_view.sub_disk_decodable_implies_path_decodable(post.tj().disk_view, post.freshest_rec);
        assert(post.disk_view.path_decodable(post.freshest_rec));
        assert(post.au_page_bounds_match_index()) by {
            assert(post.au_page_bounds == self.au_page_bounds);
            assert(post.lsn_au_index == self.lsn_au_index);
            assert(self.au_page_bounds_match_index());
        }
        AllocationJournal::State::internal_mini_allocator_fill_semantic_inv(self, post, lbl, post_disk_view);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
        assert(post.i() == self.i());
    }

    pub proof fn internal_mini_allocator_prune_refines(
        self,
        post: Self,
        lbl: AllocationJournal::Label,
        prune_aus: Set<AU>,
    )
        requires self.refinement_inv(), post.inv(), Self::internal_mini_allocator_prune(self, post, lbl, prune_aus)
        ensures
            LikesJournal::State::next_by(self.i(), post.i(), self.label_i(lbl), LikesJournal::Step::internal_no_op()),
            post.refinement_inv(),
    {
        reveal(LikesJournal::State::next_by);
        reveal(AllocationJournal::State::next_by);
        assert(AllocationJournal::State::next_by(
            self,
            post,
            lbl,
            AllocationJournal::Step::internal_mini_allocator_prune(prune_aus),
        ));
        AllocationJournal::State::internal_mini_allocator_prune_tj_unchanged(self, post, lbl, prune_aus);
        assert(post.tj() == self.tj());
        assert(post.tj().disk_view.is_sub_disk(post.disk_view)) by {
            assert(self.tj().disk_view.is_sub_disk(post.disk_view));
        }
        post.disk_view.sub_disk_decodable_implies_path_decodable(post.tj().disk_view, post.freshest_rec);
        assert(post.disk_view.path_decodable(post.freshest_rec));
        assert(post.au_page_bounds_match_index()) by {
            assert(post.au_page_bounds == self.au_page_bounds);
            assert(post.lsn_au_index == self.lsn_au_index);
            assert(self.au_page_bounds_match_index());
        }
        AllocationJournal::State::internal_mini_allocator_prune_semantic_inv(self, post, lbl, prune_aus);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
        assert(post.i() == self.i());
    }

    pub proof fn internal_no_op_refines(self, post: Self, lbl: AllocationJournal::Label)
        requires self.refinement_inv(), post.inv(), Self::internal_no_op(self, post, lbl)
        ensures
            LikesJournal::State::next_by(self.i(), post.i(), self.label_i(lbl), LikesJournal::Step::internal_no_op()),
            post.refinement_inv(),
    {
        reveal(LikesJournal::State::next_by);
        assert(post.i() == self.i());
        assert(post == self);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn next_refines(self, post: Self, lbl: AllocationJournal::Label)
    requires
        self.refinement_inv(),
        AllocationJournal::State::next(self, post, lbl),
    ensures
        post.refinement_inv(),
        LikesJournal::State::next(self.i(), post.i(), self.label_i(lbl)),
    {
        reveal(LikesJournal::State::next_by);  // unfortunate defaults
        reveal(LikesJournal::State::next);
        reveal(AllocationJournal::State::next_by);
        reveal(AllocationJournal::State::next);

        AllocationJournal::State::inv_next(self, post, lbl);
        assert(post.inv());
        let step = choose |step| AllocationJournal::State::next_by(self, post, lbl, step);
        match step {
            AllocationJournal::Step::read_for_recovery(start_lsn, addr) => {
                self.read_for_recovery_refines(post, lbl, start_lsn, addr);
            },
            AllocationJournal::Step::freeze_for_commit() => {
                self.freeze_for_commit_refines(post, lbl);
            },
            AllocationJournal::Step::query_end_lsn() => {
                self.query_end_lsn_refines(post, lbl);
            },
            AllocationJournal::Step::put() => {
                self.put_refines(post, lbl);
            },
            AllocationJournal::Step::discard_old() => {
                self.discard_old_refines(post, lbl);
            },
            AllocationJournal::Step::internal_journal_marshal(cut, addr) => {
                self.internal_journal_marshal_refines(post, lbl, cut, addr);
            },
            AllocationJournal::Step::internal_mini_allocator_fill(post_disk_view) => {
                self.internal_mini_allocator_fill_refines(post, lbl, post_disk_view);
            },
            AllocationJournal::Step::internal_mini_allocator_prune(prune_aus) => {
                self.internal_mini_allocator_prune_refines(post, lbl, prune_aus);
            },
            AllocationJournal::Step::internal_no_op() => {
                self.internal_no_op_refines(post, lbl);
            },
            _ => {
                reveal(LinkedJournal::State::next_by);
                assert( LikesJournal::State::next_by(self.i(), post.i(), self.label_i(lbl), step.i()) );
                assert(false);
            },
        }
    }

    pub proof fn init_refines(self, image: JournalImage)
    requires AllocationJournal::State::initialize(self, image)
    ensures
        self.inv(),
        self.semantic_inv(),
        self.refinement_inv(),
        LikesJournal::State::initialize(self.i(), self.tj()),
    {
        reveal(AllocationJournal::State::initialize);
        reveal(LikesJournal::State::initialize);
        AllocationJournal::State::initialize_inductive(self, image);
        AllocationJournal::State::initialize_semantic_inv(self, image);
        image.valid_image_implies_tight_valid_image();
        AllocationJournal::State::initialize_tj_matches(self, image);
        assert(self.inv());
        assert(self.semantic_inv());
        assert(self.refinement_inv());
        assert(self.tj() == image.tight_tj());
        assert(self.tj().decodable());
        assert(self.i().journal == LinkedJournal::State{
            truncated_journal: self.tj(),
            unmarshalled_tail: crate::abstract_system::MsgHistory_v::MsgHistory::empty_history_at(self.tj().seq_end()),
        });
        assert(self.i().lsn_addr_index == self.tj().build_lsn_addr_index());
    }
}


} // verus!
