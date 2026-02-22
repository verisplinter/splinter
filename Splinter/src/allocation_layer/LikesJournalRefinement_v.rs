// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
use vstd::prelude::*;
//use vstd::prelude_macros::*;

use vstd::prelude::*;
use crate::disk::GenericDisk_v::Pointer;
use crate::abstract_system::StampedMap_v::LSN;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::{LinkedJournal, TruncatedJournal};
use crate::allocation_layer::LikesJournal_v::{
    LikesJournal, can_crop_index, minmin, next_index, pointer_after_crop_index,
    largest_lsn_plus_one, maxmax, discard_old_ptr_by_index,
};

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

    proof fn cropped_ptr_in_index_values(self, root: Pointer, depth: nat)
        requires
            self.inv(),
            can_crop_index(self.lsn_addr_index, self.tj().disk_view.boundary_lsn, root, depth),
            root is Some ==> self.lsn_addr_index.values().contains(root.unwrap()),
        ensures
            pointer_after_crop_index(self.lsn_addr_index, self.tj().disk_view.boundary_lsn, root, depth) is Some
                ==> self.lsn_addr_index.values().contains(
                    pointer_after_crop_index(self.lsn_addr_index, self.tj().disk_view.boundary_lsn, root, depth).unwrap()),
        decreases depth
    {
        if depth == 0 {
            if pointer_after_crop_index(self.lsn_addr_index, self.tj().disk_view.boundary_lsn, root, depth) is Some {
                assert(root is Some);
                assert(self.lsn_addr_index.values().contains(root.unwrap()));
            }
        } else {
            assert(root is Some);
            self.next_index_refines(root);
            let next = next_index(self.lsn_addr_index, self.tj().disk_view.boundary_lsn, root);
            assert(next is Some ==> self.lsn_addr_index.values().contains(next.unwrap()));
            self.cropped_ptr_in_index_values(next, (depth - 1) as nat);
        }
    }

    proof fn largest_lsn_plus_one_matches_seq_end(self, ptr: Pointer)
        requires
            self.inv(),
            ptr is Some,
            self.lsn_addr_index.values().contains(ptr.unwrap()),
        ensures
            largest_lsn_plus_one(self.lsn_addr_index, ptr)
                == self.tj().disk_view.entries[ptr.unwrap()].message_seq.seq_end,
    {
        let tj = self.tj();
        let index = self.lsn_addr_index;
        let addr = ptr.unwrap();
        let bdy = tj.disk_view.boundary_lsn;
        let msgs = tj.disk_view.entries[addr].message_seq;

        tj.build_lsn_addr_index_ensures();
        reveal(TruncatedJournal::index_domain_valid);

        assert(tj.disk_view.index_keys_map_to_valid_entries(index));
        assert(tj.index_range_valid(index));
        assert(tj.every_lsn_at_addr_indexed_to_addr(index, addr));

        let witness_lsn = choose |lsn: LSN| #![auto] index.contains_key(lsn) && index[lsn] == addr;
        assert(index.contains_key(witness_lsn) && index[witness_lsn] == addr);
        tj.disk_view.instantiate_index_keys_map_to_valid_entries(index, witness_lsn);
        assert(LinkedJournal_v::DiskView::cropped_msg_seq_contains_lsn(bdy, msgs, witness_lsn));
        assert(bdy < msgs.seq_end) by {
            assert(bdy <= witness_lsn);
            assert(witness_lsn < msgs.seq_end);
        }

        let end_minus_one = (msgs.seq_end - 1) as nat;
        assert(LinkedJournal_v::DiskView::cropped_msg_seq_contains_lsn(bdy, msgs, end_minus_one)) by {
            assert(bdy <= end_minus_one) by {
                if !(bdy <= end_minus_one) {
                    assert(end_minus_one < bdy);
                    assert(msgs.seq_end <= bdy);
                    assert(false);
                }
            }
            assert(msgs.seq_start <= end_minus_one) by {
                assert(tj.disk_view.entries.contains_key(addr));
                assert(tj.disk_view.entries[addr].wf());
                if !(msgs.seq_start <= end_minus_one) {
                    assert(end_minus_one < msgs.seq_start);
                    assert(msgs.seq_end <= msgs.seq_start);
                    assert(false);
                }
            }
            assert(end_minus_one < msgs.seq_end);
        }
        assert(index.contains_key(end_minus_one));
        assert(index[end_minus_one] == addr);
        assert(index.contains_pair(end_minus_one, addr));

        assert forall |other_lsn| (#[trigger] index.contains_key(other_lsn) && index[other_lsn] == addr)
            implies other_lsn <= end_minus_one by {
            tj.disk_view.instantiate_index_keys_map_to_valid_entries(index, other_lsn);
            assert(other_lsn < msgs.seq_end);
            assert(other_lsn <= end_minus_one);
        }
        assert(maxmax(index, addr, end_minus_one));
        assert(exists |lsn: LSN| maxmax(index, addr, lsn));

        let max_lsn = choose |lsn: LSN| maxmax(index, addr, lsn);
        assert(maxmax(index, addr, max_lsn));
        assert(max_lsn <= end_minus_one) by {
            assert(index.contains_pair(max_lsn, addr));
        }
        assert(end_minus_one <= max_lsn) by {
            assert(index.contains_pair(end_minus_one, addr));
        }
        assert(max_lsn == end_minus_one);
        assert(largest_lsn_plus_one(index, ptr) == (max_lsn + 1) as nat);
        assert((max_lsn + 1) as nat == msgs.seq_end);
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
        let frozen_bdy = fj.seq_start();
        let cropped_ptr = pointer_after_crop_index(self.lsn_addr_index, tj.seq_start(), tj.freshest_rec, depth);

        self.can_crop_ptr_after_index_refines(tj.freshest_rec, depth);
        tj.build_lsn_addr_index_ensures();
        if tj.freshest_rec is Some {
            assert(self.lsn_addr_index.contains_value(tj.freshest_rec.unwrap()));
        }
        self.cropped_ptr_in_index_values(tj.freshest_rec, depth);
        assert(tj.seq_start() <= frozen_bdy);

        let cropped_tj = tj.crop(depth);
        tj.crop_ensures(depth);
        assert(cropped_tj.wf());
        assert(cropped_tj.freshest_rec == tj.disk_view.pointer_after_crop(tj.freshest_rec, depth));
        assert(cropped_tj.freshest_rec == cropped_ptr);
        assert(fj.freshest_rec == discard_old_ptr_by_index(self.lsn_addr_index, cropped_ptr, frozen_bdy));

        if fj.freshest_rec is Some {
            let addr = fj.freshest_rec.unwrap();
            assert(cropped_ptr is Some);
            assert(self.lsn_addr_index.contains_value(cropped_ptr.unwrap())) by {
                assert(cropped_ptr is Some ==> self.lsn_addr_index.values().contains(cropped_ptr.unwrap()));
                assert(cropped_ptr is Some);
            }
            if largest_lsn_plus_one(self.lsn_addr_index, cropped_ptr) == frozen_bdy {
                assert(discard_old_ptr_by_index(self.lsn_addr_index, cropped_ptr, frozen_bdy) is None);
                assert(false);
            }
            assert(discard_old_ptr_by_index(self.lsn_addr_index, cropped_ptr, frozen_bdy) == cropped_ptr);
            assert(fj.freshest_rec == cropped_ptr);
            assert(cropped_tj.freshest_rec == fj.freshest_rec);

            assert(fj.disk_view.block_in_bounds(fj.freshest_rec));
            assert(fj.disk_view.is_sub_disk_with_newer_lsn(tj.disk_view));
            assert(tj.disk_view.entries.contains_key(addr));
            assert(tj.disk_view.entries[addr] == fj.disk_view.entries[addr]);
            assert(frozen_bdy < fj.disk_view.entries[addr].message_seq.seq_end);
            assert(cropped_tj.seq_end() == tj.disk_view.entries[addr].message_seq.seq_end);
        } else {
            if cropped_ptr is Some {
                assert(discard_old_ptr_by_index(self.lsn_addr_index, cropped_ptr, frozen_bdy) is None);
                assert(self.lsn_addr_index.contains_value(cropped_ptr.unwrap())) by {
                    assert(cropped_ptr is Some ==> self.lsn_addr_index.values().contains(cropped_ptr.unwrap()));
                    assert(cropped_ptr is Some);
                }
                assert(largest_lsn_plus_one(self.lsn_addr_index, cropped_ptr) == frozen_bdy) by {
                    if largest_lsn_plus_one(self.lsn_addr_index, cropped_ptr) != frozen_bdy {
                        assert(discard_old_ptr_by_index(self.lsn_addr_index, cropped_ptr, frozen_bdy) == cropped_ptr);
                        assert(false);
                    }
                }
                self.largest_lsn_plus_one_matches_seq_end(cropped_ptr);
                assert(cropped_tj.freshest_rec == cropped_ptr);
                let addr = cropped_ptr.unwrap();
                assert(cropped_tj.seq_end() == tj.disk_view.entries[addr].message_seq.seq_end);
                assert(largest_lsn_plus_one(self.lsn_addr_index, cropped_ptr) == cropped_tj.seq_end());
                assert(frozen_bdy == cropped_tj.seq_end());
            } else {
                assert(cropped_ptr is None);
                assert(frozen_bdy == tj.seq_start());
                assert(cropped_tj.freshest_rec is None);
                assert(cropped_tj.seq_end() == tj.seq_start());
                assert(frozen_bdy == cropped_tj.seq_end());
            }
            assert(frozen_bdy <= cropped_tj.seq_end());
        }
        assert(cropped_tj.can_discard_to(frozen_bdy));

        let post_discard = cropped_tj.discard_old(frozen_bdy);
        cropped_tj.discard_old_decodable(frozen_bdy);
        let post_tight = post_discard.build_tight();

        if fj.freshest_rec is Some {
            assert(post_discard.freshest_rec == cropped_tj.freshest_rec);
        } else {
            if cropped_tj.freshest_rec is Some {
                assert(frozen_bdy == cropped_tj.seq_end());
            } else {
                assert(cropped_tj.seq_end() == tj.seq_start());
                assert(frozen_bdy == tj.seq_start());
            }
            assert(post_discard.freshest_rec is None);
        }
        assert(fj.freshest_rec == post_discard.freshest_rec);

        assert(post_discard.disk_view.acyclic()); 
        post_discard.disk_view.build_tight_ensures(post_discard.freshest_rec);
        post_discard.disk_view.build_tight_domain_is_build_lsn_addr_index_range(post_discard.freshest_rec);

        let tj_sub_index = tj.disk_view.build_lsn_addr_index(post_discard.freshest_rec);
        let post_discard_repr = post_discard.disk_view.build_lsn_addr_index(post_discard.freshest_rec);

        assert(post_discard_repr.values() == post_tight.disk_view.entries.dom()); 

        let fj_index = fj.build_lsn_addr_index();
        assert(fj.disk_view.is_sub_disk(post_discard.disk_view));

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
                assert(post_discard_repr.contains_key(lsn));
                assert(post_discard_repr <= tj_sub_index);
                assert(tj_sub_index.contains_key(lsn));
                assert(tj_sub_index <= self.lsn_addr_index);
                assert(post_discard_repr[lsn] == tj_sub_index[lsn]);
                assert(tj_sub_index.contains_pair(lsn, tj_sub_index[lsn]));
                assert(self.lsn_addr_index.contains_pair(lsn, tj_sub_index[lsn]));
                assert(self.lsn_addr_index.contains_key(lsn));
                assert(tj_sub_index[lsn] == self.lsn_addr_index[lsn]);
            }

            assert(post_discard_repr.values() <= fj.disk_view.entries.dom()) by {
                reveal(LinkedJournal_v::DiskView::index_keys_map_to_valid_entries);
            }
            assert(post_tight.disk_view.entries.dom() <= fj.disk_view.entries.dom());
            assert(cropped_tj.valid_discard_old(frozen_bdy, fj));
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
