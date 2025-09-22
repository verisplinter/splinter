// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
use verus_builtin::*;
use verus_builtin_macros::*;

use vstd::prelude::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::Pointer;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::{LinkedJournal, TruncatedJournal};
use crate::allocation_layer::LikesJournal_v::*;

verus!{

// The thrilling climax, the actual proof goal we want to use in lower
// refinement layers.
impl LikesJournal::State {
    pub open spec fn tj(self) -> TruncatedJournal
    {
        self.journal.truncated_journal
    }

    pub open spec(checked) fn i(self) -> LinkedJournal::State
    recommends self.journal.truncated_journal.decodable()
    {
        self.journal
    }

    // TODO: fix
    pub proof fn next_index_refines(self, ptr: Pointer)
    requires 
        self.inv(), 
        ptr is Some,
        self.tj().disk_view.is_nondangling_pointer(ptr),
    ensures ({
        let result = next_index(self.lsn_addr_index, self.tj().disk_view.boundary_lsn, ptr);
        let index = self.lsn_addr_index;
        &&& result is Some ==> index.contains_value(result.unwrap())
        &&& result == self.tj().disk_view.next(ptr)
    })
    {
        assume(false);
/*
        let addr = ptr.unwrap();
        let bdy = self.journal.boundary_lsn;
        let index = self.journal.lsn_addr_index;

        let record = self.ephemeral_disk().entries[addr];
        let next = record.cropped_prior(bdy);
        let lsns = addr_to_lsns(index, addr, bdy);

        // TODO: not going to prove this right now, to prove it 
        // we can maintain inv that index is finite, and show lsns is a subset of index.dom()
        assume(lsns.finite());

        self.ephemeral_tj().build_lsn_addr_index_ensures();

        // a combination of addr_supports_lsn, index_keys_map_to_valid_entries
        // instantiate_index_keys_map_to_valid_entries(lsn addr index, lsn)
        // and index_range_valid, every_lsn_at_addr_indexed_to_addr
        let start = record.message_seq.seq_start;

        if next is Some {
            assert(bdy < start);
            assert(self.ephemeral_tj().index_range_valid(index));
            assert(DiskView::cropped_msg_seq_contains_lsn(bdy, record.message_seq, start));
            assert(index.contains_key(start));
            assert(lsns.contains(start));
            assert(!lsns.is_empty());

            assert(min_lsn(lsns) == start) by {
                min_lsn_ensures(lsns);

                let min = min_lsn(lsns);
                if min != start {
                    assert(min < start);
                    assert(index[min] == addr);
                    self.ephemeral_disk().instantiate_index_keys_map_to_valid_entries(index, min);
                    assert(record.contains_lsn(bdy, min));
                    assert(false);
                }
            }

            assert(self.ephemeral_disk().is_nondangling_pointer(next));
            let next_record = self.ephemeral_disk().entries[next.unwrap()];
            assert(next_record.message_seq.seq_end == record.message_seq.seq_start);

            let last_lsn = (next_record.message_seq.seq_end - 1) as nat;
            assert(next_record.message_seq.contains(last_lsn));
            assert(index.contains_value(next.unwrap()));

            assert(self.ephemeral_tj().every_lsn_at_addr_indexed_to_addr(index, next.unwrap()));
            assert(DiskView::cropped_msg_seq_contains_lsn(bdy, next_record.message_seq, last_lsn));
            assert(index.contains_key(last_lsn));
            assert(index[last_lsn] == next.unwrap());
        } else {
            assert(start <= bdy);
            if lsns.is_empty() {
                assert(self.journal.next_index(ptr) is None);
            } else {
                reveal(TruncatedJournal::index_domain_valid);
                assert(forall |lsn| lsns.contains(lsn) ==> bdy <= lsn);
            
                let min = min_lsn(lsns);
                if min < 1 {
                    assert(self.journal.next_index(ptr) is None);
                    return;
                }

                // goal here is to show that it's either none or c
                let prior_lsn = (min - 1) as nat;
                min_lsn_ensures(lsns);
                if bdy >= record.message_seq.seq_end {
                    assert(index.contains_key(min));
                    assert(index[min] == ptr.unwrap());
                    self.ephemeral_disk().instantiate_index_keys_map_to_valid_entries(index, min);
                    assert(false);
                }
                assert(bdy < record.message_seq.seq_end);
                assert(min == bdy) by {
                    assert(DiskView::cropped_msg_seq_contains_lsn(bdy, record.message_seq, bdy));
                    assert(index.contains_key(bdy));
                    assert(lsns.contains(bdy));
                }
            }
        }
            */
    }

    // NOTE: maybe this should have been how we define these operations in the likes layer 
    // in the first place...
    proof fn can_crop_ptr_after_index_refines(self, root: Pointer, depth: nat)
        requires 
            self.inv(),
            can_crop_index(self.lsn_addr_index, self.tj().disk_view.boundary_lsn, root, depth),
            root is Some ==> self.lsn_addr_index.contains_value(root.unwrap()),
        ensures 
            self.tj().disk_view.can_crop(root, depth),
            self.tj().disk_view.pointer_after_crop(root, depth)
            == pointer_after_crop_index(self.lsn_addr_index, self.tj().disk_view.boundary_lsn, root, depth),
        decreases depth
    {
        if 0 < depth {
            assert(root is Some);
            self.tj().disk_view.build_lsn_addr_all_decodable(root);

            assert(self.lsn_addr_index.contains_value(root.unwrap()));

            self.tj().disk_view.build_lsn_addr_index_domain_valid(root);
            self.tj().disk_view.build_lsn_addr_index_range_valid(root);

            self.next_index_refines(root);
            let next = next_index(self.lsn_addr_index, self.tj().disk_view.boundary_lsn, root);
            self.can_crop_ptr_after_index_refines(next, (depth-1) as nat);
        }
    }

    pub proof fn read_for_recovery_refines(self, post: Self, lbl: LikesJournal::Label, depth: nat)
    requires 
        self.inv(), 
        post.inv(),
        Self::read_for_recovery(self, post, lbl, depth)
    ensures 
        LinkedJournal::State::next_by(self.i(), post.i(), Self::lbl_i(lbl), 
            LinkedJournal::Step::read_for_recovery(depth))
    {
        reveal(LinkedJournal::State::next_by);

        let i_lbl = Self::lbl_i(lbl);
        let messages = i_lbl.arrow_ReadForRecovery_messages();
        let tj = self.tj();

        if tj.freshest_rec is Some {
            assume(self.lsn_addr_index.contains_value(tj.freshest_rec.unwrap()));
        }

        self.can_crop_ptr_after_index_refines(tj.freshest_rec, depth);
        tj.disk_view.pointer_after_crop_ensures(tj.freshest_rec, depth);
        let ptr = tj.disk_view.pointer_after_crop(tj.freshest_rec, depth);

        assert(ptr is Some && tj.disk_view.entries.contains_key(ptr.unwrap()));
        assert(messages == tj.disk_view.entries[ptr.unwrap()].message_seq.maybe_discard_old(tj.disk_view.boundary_lsn));
        assert(messages.wf());

        // read for recovery is the same
        assert(LinkedJournal::State::next_by(self.i(), post.i(), i_lbl, 
            LinkedJournal::Step::read_for_recovery(depth)));
        assume(false);
    }

    pub proof fn freeze_for_commit_refines(self, post: Self, lbl: LikesJournal::Label, depth: nat)
    requires 
        self.inv(), 
        post.inv(),
        Self::freeze_for_commit(self, post, lbl, depth)
    ensures 
        LinkedJournal::State::next_by(self.i(), post.i(), Self::lbl_i(lbl), 
            LinkedJournal::Step::freeze_for_commit(depth))
    {
        reveal(LinkedJournal::State::next_by);

        let fj = lbl->frozen_journal;
        let tj = self.journal.truncated_journal;
        let new_bdy = fj.seq_start();

        let cropped_tj = tj.crop(depth);
        tj.disk_view.pointer_after_crop_ensures(tj.freshest_rec, depth);

        let post_discard = cropped_tj.discard_old(new_bdy);
        let post_tight = post_discard.build_tight();
        
        cropped_tj.discard_old_decodable(new_bdy);
        assert(post_discard.disk_view.acyclic()); 

        post_discard.disk_view.build_tight_ensures(post_discard.freshest_rec);
        post_discard.disk_view.build_tight_domain_is_build_lsn_addr_index_range(post_discard.freshest_rec);

        let tj_sub_index = tj.disk_view.build_lsn_addr_index(post_discard.freshest_rec);
        let post_discard_repr = post_discard.disk_view.build_lsn_addr_index(post_discard.freshest_rec);

        if post_discard.freshest_rec is Some {
            tj.disk_view.pointer_after_crop_seq_end(tj.freshest_rec, depth);
            assert(post_discard.seq_end() <= tj.seq_end());

            let frozen_lsns = Set::new(|lsn: LSN| new_bdy <= lsn && lsn < post_discard.seq_end());
            let frozen_index = self.lsn_addr_index.restrict(frozen_lsns);

            tj.build_lsn_addr_index_ensures();
            post_discard.build_lsn_addr_index_ensures();

            assert(post_discard_repr.dom() =~= frozen_index.dom()) by {
                reveal(TruncatedJournal::index_domain_valid); 
            }

            tj.disk_view.cropped_ptr_build_sub_index(tj.freshest_rec, post_discard.freshest_rec, depth);
            assert(tj_sub_index <= self.lsn_addr_index);

            post_discard.disk_view.sub_disk_with_newer_lsn_repr_index(tj.disk_view, post_discard.freshest_rec);
            assert(post_discard_repr <= tj_sub_index);

            assert forall |lsn| #[trigger] post_discard_repr.contains_key(lsn)
            implies post_discard_repr[lsn] == self.lsn_addr_index[lsn]
            by {
                assert(tj_sub_index.contains_key(lsn));
            }
            assert(post_discard_repr <= self.lsn_addr_index);
            assert(frozen_index =~= post_discard_repr);
            assert(cropped_tj.valid_discard_old(new_bdy, fj));
        }
    }

    pub proof fn discard_old_refines(self, post: Self, lbl: LikesJournal::Label, new_journal: LinkedJournal_v::LinkedJournal::State)
    requires 
        self.inv(), 
        post.inv(),
        Self::discard_old(self, post, lbl, new_journal)
    ensures 
        LinkedJournal::State::next_by(self.i(), post.i(), Self::lbl_i(lbl), 
            LinkedJournal::Step::discard_old(new_journal.truncated_journal))
    {
        reveal(LinkedJournal::State::next_by);

        let tj_pre = self.journal.truncated_journal;
        let tj_post = post.journal.truncated_journal;

        let start_lsn = lbl->start_lsn;
        let require_end = lbl->require_end;

        let post_discard = tj_pre.discard_old(start_lsn);
        let post_tight = post_discard.build_tight();

        assert(tj_post.wf());
        assert(tj_post.freshest_rec == post_discard.freshest_rec);
        assert(tj_post.disk_view.is_sub_disk(post_discard.disk_view)); // new must be a subset of original

        tj_pre.discard_old_decodable(start_lsn);
        assert(post_discard.disk_view.acyclic()); 

        post_discard.disk_view.build_tight_ensures(post_discard.freshest_rec);
        post_discard.disk_view.tight_sub_disk(post_discard.freshest_rec, post_tight.disk_view);
        assert(post_tight.disk_view.acyclic()); 

        // post_tight has the same build_lsn_addr_index as post_discard and as tj_post
        post_tight.disk_view.sub_disk_repr_index(post_discard.disk_view, post_discard.freshest_rec);
        tj_post.disk_view.sub_disk_repr_index(post_discard.disk_view, post_discard.freshest_rec);
        assert(post_tight.disk_view.build_lsn_addr_index(post_discard.freshest_rec) == post.lsn_addr_index);
        assert(post.lsn_addr_index.values() <= tj_post.disk_view.entries.dom());

        post_discard.disk_view.build_tight_domain_is_build_lsn_addr_index_range(post_discard.freshest_rec);
        assert(post_tight.disk_view.entries.dom() <= tj_post.disk_view.entries.dom());
        assert(post_tight.disk_view.entries <= tj_post.disk_view.entries);
        assert(post_discard.freshest_rec == tj_post.freshest_rec);

        assert(post_tight.disk_view.is_sub_disk(tj_post.disk_view));   // tight must be fully contained by new
    }

    pub proof fn next_refines(self, post: Self, lbl: LikesJournal::Label)
    requires
        self.inv(),
        post.inv(),
        LikesJournal::State::next(self, post, lbl),
    ensures
        LinkedJournal::State::next(self.i(), post.i(), Self::lbl_i(lbl)),
    {
        // unfortunate defaults
        reveal(LinkedJournal::State::next);
        reveal(LinkedJournal::State::next_by);
        reveal(LikesJournal::State::next);
        reveal(LikesJournal::State::next_by);  

        let step = choose |step| LikesJournal::State::next_by(self, post, lbl, step);
        match step {
            LikesJournal::Step::read_for_recovery(depth) => {
                self.read_for_recovery_refines(post, lbl, depth);
            },
            LikesJournal::Step::freeze_for_commit(depth) => {
                self.freeze_for_commit_refines(post, lbl, depth);
            },
            LikesJournal::Step::query_end_lsn() => {},
            LikesJournal::Step::put(..) => {},
            LikesJournal::Step::discard_old(new_journal) => {
                self.discard_old_refines(post, lbl, new_journal);
            },
            LikesJournal::Step::internal_journal_marshal(cut, addr, new_journal) => {
                assert(LinkedJournal::State::next_by(self.i(), post.i(), Self::lbl_i(lbl), LinkedJournal::Step::internal_journal_marshal(cut, addr)));
            },
            _ => {
                assert( LinkedJournal::State::next_by(self.i(), post.i(), Self::lbl_i(lbl), LinkedJournal::Step::internal_no_op()) );
            },
        }
    }

    pub proof fn init_refines(self, truncated_journal: TruncatedJournal) 
    requires LikesJournal::State::initialize(self, truncated_journal)
    ensures LinkedJournal::State::initialize(self.i(), truncated_journal)
    {
    }
}

} // verus!
