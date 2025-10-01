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

broadcast use TruncatedJournal::build_lsn_addr_index_ensures;

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

    pub proof fn next_index_refines(self, ptr: Pointer)
    requires 
        self.inv(), 
        ptr is Some,
        self.lsn_addr_index.values().contains(ptr.unwrap()),
    ensures ({
        let result = next_index(self.lsn_addr_index, self.tj().disk_view.boundary_lsn, ptr);
        let index = self.lsn_addr_index;
        &&& result is Some ==> index.contains_value(result.unwrap())
        &&& result == self.tj().disk_view.next(ptr)
    }) {
        let addr = ptr.unwrap();
        let bdy = self.tj().disk_view.boundary_lsn;
        let index = self.lsn_addr_index;

        let result = next_index(index, bdy, ptr);        
        let record = self.tj().disk_view.entries[addr];
        let next = record.cropped_prior(bdy);

        reveal(LinkedJournal_v::TruncatedJournal::index_domain_valid);
        reveal(LinkedJournal_v::DiskView::index_keys_map_to_valid_entries);

        let tight_tj = self.tj().build_tight();
        self.tj().disk_view.build_tight_ensures(self.tj().freshest_rec);
        tight_tj.disk_view.sub_disk_repr_index(self.tj().disk_view, self.tj().freshest_rec);
        assert(tight_tj.build_lsn_addr_index() == index);
        self.tj().disk_view.build_tight_domain_is_build_lsn_addr_index_range(self.tj().freshest_rec);
        assert(index.values() == tight_tj.disk_view.entries.dom());

        let start = record.message_seq.seq_start;
        if next is Some {
            assert(bdy < start);
            assert(LinkedJournal_v::DiskView::cropped_msg_seq_contains_lsn(bdy, record.message_seq, start));
            assert(index.contains_key(start));
            assert(index[start] == addr);

            if !minmin(index, addr, start) {
                let min = choose |min| minmin(index, addr, min);
                assert(min < start);
                assert(index[min] == addr);
                self.tj().disk_view.instantiate_index_keys_map_to_valid_entries(index, min);
                assert(record.contains_lsn(bdy, min));
                assert(false);
            }
            assert(minmin(index, addr, start));

            let next_record = self.tj().disk_view.entries[next.unwrap()];
            assert(next_record.message_seq.seq_end == record.message_seq.seq_start);
            let last_lsn = (next_record.message_seq.seq_end - 1) as nat;
            assert(next_record.message_seq.contains(last_lsn));
            assert(index.contains_key(last_lsn));
            assert(LinkedJournal_v::DiskView::cropped_msg_seq_contains_lsn(bdy, next_record.message_seq, last_lsn)); // trigger
            assert(index.contains_value(next.unwrap()));
        } else {
            assert(LinkedJournal_v::DiskView::cropped_msg_seq_contains_lsn(bdy, record.message_seq, bdy)); // trigger
            assert(minmin(index, ptr.unwrap(), bdy));
            assert(result is None);
        }
    }

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

        self.can_crop_ptr_after_index_refines(tj.freshest_rec, depth);
        tj.disk_view.pointer_after_crop_ensures(tj.freshest_rec, depth);
        let ptr = tj.disk_view.pointer_after_crop(tj.freshest_rec, depth);

        assert(ptr is Some && tj.disk_view.entries.contains_key(ptr.unwrap()));
        assert(messages == tj.disk_view.entries[ptr.unwrap()].message_seq.maybe_discard_old(tj.disk_view.boundary_lsn));
        assert(messages.wf());

        assert(self.i().wf());
        assert(LinkedJournal::State::next_by(self.i(), post.i(), i_lbl, 
            LinkedJournal::Step::read_for_recovery(depth)));
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

        self.can_crop_ptr_after_index_refines(tj.freshest_rec, depth);
        assert(tj.disk_view.can_crop(tj.freshest_rec, depth));
        assert(tj.seq_start() <= fj.seq_start());

        let cropped_tj = tj.crop(depth);
        tj.crop_ensures(depth);
        assert(cropped_tj.can_discard_to(fj.seq_start())); 
        assert(tj.disk_view.can_crop(tj.freshest_rec, depth));

        tj.disk_view.pointer_after_crop_ensures(tj.freshest_rec, depth);
        let post_discard = cropped_tj.discard_old(fj.seq_start());
        let post_tight = post_discard.build_tight();
        
        cropped_tj.discard_old_decodable(fj.seq_start());
        assert(post_discard.disk_view.acyclic()); 
        post_discard.disk_view.build_tight_ensures(post_discard.freshest_rec);
        post_discard.disk_view.build_tight_domain_is_build_lsn_addr_index_range(post_discard.freshest_rec);

        let tj_sub_index = tj.disk_view.build_lsn_addr_index(post_discard.freshest_rec);
        let post_discard_repr = post_discard.disk_view.build_lsn_addr_index(post_discard.freshest_rec);

        assert(post_discard_repr.values() == post_tight.disk_view.entries.dom()); 

        let fj_index = fj.build_lsn_addr_index();
        assert(fj.disk_view.is_sub_disk(post_discard.disk_view));
        assert(fj.freshest_rec == post_discard.freshest_rec);        

        fj.disk_view.sub_disk_repr_index(post_discard.disk_view, fj.freshest_rec);
        assert(fj_index == post_discard_repr);

        if post_discard.freshest_rec is Some {
            tj.disk_view.pointer_after_crop_seq_end(tj.freshest_rec, depth);
            reveal(TruncatedJournal::index_domain_valid);

            tj.disk_view.cropped_ptr_build_sub_index(tj.freshest_rec, post_discard.freshest_rec, depth);
            assert(tj_sub_index <= self.lsn_addr_index);
            post_discard.disk_view.sub_disk_with_newer_lsn_repr_index(tj.disk_view, post_discard.freshest_rec);
            assert(post_discard_repr <= tj_sub_index);

            assert forall |lsn| #[trigger] post_discard_repr.contains_key(lsn)
            implies post_discard_repr[lsn] == self.lsn_addr_index[lsn]
            by {
                assert(tj_sub_index.contains_key(lsn));
            }

            assert(post_discard_repr.values() <= fj.disk_view.entries.dom()) by {
                reveal(LinkedJournal_v::DiskView::index_keys_map_to_valid_entries);
            }
            assert(post_tight.disk_view.entries.dom() <= fj.disk_view.entries.dom());
            assert(cropped_tj.valid_discard_old(fj.seq_start(), fj));
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
            LikesJournal::Step::query_end_lsn() => {
                assert(LinkedJournal::State::next_by(self.i(), post.i(), Self::lbl_i(lbl), LinkedJournal::Step::query_end_lsn()));
            },
            LikesJournal::Step::put() => {
                assert(LinkedJournal::State::next_by(self.i(), post.i(), Self::lbl_i(lbl), LinkedJournal::Step::put()));
            },
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
