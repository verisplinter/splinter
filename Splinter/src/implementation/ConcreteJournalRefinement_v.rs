// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::prelude::*;
use vstd::{map::*,set::*,set_lib::*};
use vstd::math;

//use vstd::prelude_macros::*;
use verus_state_machines_macros::state_machine;

use crate::spec::AsyncDisk_t::*;
use crate::spec::MapSpec_t::{ID};
use crate::disk::GenericDisk_v::Pointer;
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
use crate::journal::LinkedJournal_v::*;
use crate::implementation::CachedJournal_v::*;
use crate::implementation::CachedJournal_v::{addr_to_lsns, min_lsn, min_lsn_ensures};
use crate::implementation::Cache_v::*;
use crate::allocation_layer::LikesJournal_v::{
    LikesJournal, LsnAddrIndex, pointer_after_crop_index, next_index,
    largest_lsn_plus_one, maxmax, discard_old_ptr_by_index,
    singleton_index,
};
use crate::allocation_layer::AllocationJournal_v::{
    AllocationJournal, JournalImage, lsn_au_index_append_record, lsn_au_index_discard_up_to,
};
use crate::implementation::ConcreteJournal_v::*;
use crate::implementation::AtomicState_v::{raw_page_to_record, to_journal_records};
use crate::betree::Utils_v::lemma_subset_finite;

verus!{

proof fn nat_lsn_range_finite(start_lsn: LSN, end_lsn: LSN)
    requires
        start_lsn <= end_lsn,
    ensures
        Set::<LSN>::new(|lsn: LSN| start_lsn <= lsn < end_lsn).finite(),
{
    let int_range = vstd::set_lib::set_int_range(start_lsn as int, end_lsn as int);
    let nat_range = Set::<LSN>::new(|lsn: LSN| start_lsn <= lsn < end_lsn);
    let mapped = int_range.map(|i: int| i as nat);

    vstd::set_lib::lemma_int_range(start_lsn as int, end_lsn as int);
    int_range.lemma_map_finite(|i: int| i as nat);

    assert(nat_range =~= mapped) by {
        assert forall |lsn: LSN| #[trigger] nat_range.contains(lsn)
            implies mapped.contains(lsn) by {
            let i = lsn as int;
            assert(int_range.contains(i));
        };

        assert forall |lsn: LSN| #[trigger] mapped.contains(lsn)
            implies nat_range.contains(lsn) by {
            let i = choose |i: int| int_range.contains(i) && (i as nat) == lsn;
            assert(lsn as int == i);
        };
    };
}

impl ConcreteJournal::State {
    pub open spec fn refinement_wf(self) -> bool
    {
        &&& self.inv()
        &&& self.i().inv()
    }

    pub proof fn journal_tj_ensures(self)
        requires
            self.inv(),
        ensures ({
            let tj = self.journal_tj();
            let index = cj_lsn_addr_index(self.journal);
            &&& tj.decodable()
            &&& tj.seq_end() == cj_unmarshalled_tail(self.journal).seq_start
            &&& index == tj.build_lsn_addr_index()
            &&& tj.index_domain_valid(index)
            &&& tj.disk_view.index_keys_map_to_valid_entries(index)
            &&& tj.index_range_valid(index)
            &&& tj.freshest_rec is Some ==> index.contains_value(tj.freshest_rec.unwrap())
        })
    {
        reveal(ConcreteJournal::State::valid_journal_structure);
        let tj = self.journal_tj();
        assert(tj.decodable());
        assert(cj_lsn_addr_index(self.journal) == tj.build_lsn_addr_index());
        tj.build_lsn_addr_index_ensures();
    }

    // TODO(JL): this almost feels like something we should have adopted in likesjournal
    pub proof fn next_index_refines(self, ptr: Pointer)
        requires
            self.inv(),
            ptr is Some,
            cj_lsn_addr_index(self.journal).contains_value(ptr.unwrap()),
        ensures ({
            let result = self.journal.next_index(ptr);
            let index = cj_lsn_addr_index(self.journal);
            &&& result is Some ==> index.contains_value(result.unwrap())
            &&& result == self.journal_disk_view().next(ptr)
        })
    {
        let result = self.journal.next_index(ptr);
        let index = cj_lsn_addr_index(self.journal);
        let tj = self.journal_tj();
        let disk = self.journal_disk_view();
        let bdy = disk.boundary_lsn;
        let addr = ptr.unwrap();
        let record = disk.entries[addr];
        let next = disk.next(ptr);
        let lsns = addr_to_lsns(index, addr, bdy);
        let range = Set::<LSN>::new(|lsn: LSN| bdy <= lsn < record.message_seq.seq_end);

        reveal(ConcreteJournal::State::valid_journal_structure);
        self.journal_tj_ensures();
        assert(tj.decodable());
        assert(index == tj.build_lsn_addr_index());
        tj.build_lsn_addr_index_ensures();
        reveal(TruncatedJournal::index_domain_valid);
        reveal(DiskView::index_keys_map_to_valid_entries);
        assert(index.values().contains(addr));
        assert(tj.index_range_valid(index));
        assert(disk.index_keys_map_to_valid_entries(index));
        let witness_lsn: LSN = choose |lsn: LSN| index.contains_key(lsn) && index[lsn] == addr;
        disk.instantiate_index_keys_map_to_valid_entries(index, witness_lsn);
        assert(disk.entries.contains_key(addr));

        assert forall |lsn: LSN| #[trigger] lsns.contains(lsn)
            implies range.contains(lsn) by {
            assert(index.contains_key(lsn));
            assert(index[lsn] == addr);
            assert(disk.addr_supports_lsn(addr, lsn));
        }
        nat_lsn_range_finite(bdy, record.message_seq.seq_end);
        lemma_subset_finite(range, lsns);

        if next is Some {
            let start = record.message_seq.seq_start;
            assert(bdy < start);
            assert(DiskView::cropped_msg_seq_contains_lsn(bdy, record.message_seq, start));
            assert(index.contains_key(start));
            assert(index[start] == addr);
            assert(lsns.contains(start));
            min_lsn_ensures(lsns);
            assert(start <= min_lsn(lsns)) by {
                assert(lsns.contains(min_lsn(lsns)));
                assert(index.contains_key(min_lsn(lsns)));
                assert(index[min_lsn(lsns)] == addr);
                assert(disk.addr_supports_lsn(addr, min_lsn(lsns)));
            }
            assert(min_lsn(lsns) <= start);
            assert(min_lsn(lsns) == start);

            let next_addr = next.unwrap();
            let next_record = disk.entries[next_addr];
            assert(disk.is_nondangling_pointer(next));
            assert(disk.entries.contains_key(next_addr));
            assert(next_record.message_seq.seq_end == record.message_seq.seq_start);
            disk.build_lsn_addr_index_immediate_prior(cj_freshest_rec(self.journal), addr);
            assert(index.values().contains(next_addr));
            let last_lsn = (next_record.message_seq.seq_end - 1) as nat;
            assert(last_lsn < start);
            assert(DiskView::cropped_msg_seq_contains_lsn(bdy, next_record.message_seq, last_lsn));
            assert(index.contains_key(last_lsn));
            assert(index[last_lsn] == next_addr);
            assert(result == Some(index[last_lsn]));
            assert(result == next);
            assert(index.values().contains(next_addr));
            assert(result is Some ==> index.contains_value(result.unwrap()));
        } else {
            assert(DiskView::cropped_msg_seq_contains_lsn(bdy, record.message_seq, bdy));
            assert(index.contains_key(bdy));
            assert(index[bdy] == addr);
            assert(lsns.contains(bdy));
            min_lsn_ensures(lsns);
            assert(bdy <= min_lsn(lsns)) by {
                assert(lsns.contains(min_lsn(lsns)));
            }
            assert(min_lsn(lsns) <= bdy);
            assert(min_lsn(lsns) == bdy);
            assert(result == None::<Address>);
        }
    }

    // NOTE: maybe this should have been how we define these operations in the likes layer
    // in the first place...
    proof fn can_crop_ptr_after_index_refines(self, root: Pointer, depth: nat)
        requires
            self.inv(),
            self.journal.can_crop_index(root, depth),
            root is Some ==> cj_lsn_addr_index(self.journal).contains_value(root.unwrap()),
        ensures
            self.journal_disk_view().can_crop(root, depth),
            self.journal_disk_view().pointer_after_crop(root, depth)
            == self.journal.pointer_after_crop_index(root, depth),
        decreases depth
    {
        if 0 < depth {
            assert(root is Some);
            assert(cj_lsn_addr_index(self.journal).contains_value(root.unwrap()));
            assert(self.journal_disk_view().is_nondangling_pointer(root)) by {
                self.journal_tj_ensures();
                let index = cj_lsn_addr_index(self.journal);
                let addr = root.unwrap();
                let witness_lsn: LSN = choose |lsn: LSN| index.contains_key(lsn) && index[lsn] == addr;
                self.journal_disk_view().instantiate_index_keys_map_to_valid_entries(index, witness_lsn);
            }
            self.next_index_refines(root);
            let next = self.journal.next_index(root);
            assert(next == self.journal_disk_view().next(root));
            self.can_crop_ptr_after_index_refines(next, (depth-1) as nat);
            assert(self.journal_disk_view().can_crop(next, (depth-1) as nat));
            assert(self.journal_disk_view().can_crop(self.journal_disk_view().next(root), (depth-1) as nat));
            assert(self.journal_disk_view().can_crop(root, depth));
            assert(self.journal_disk_view().pointer_after_crop(root, depth)
                == self.journal_disk_view().pointer_after_crop(self.journal_disk_view().next(root), (depth-1) as nat));
            assert(self.journal.pointer_after_crop_index(root, depth)
                == self.journal.pointer_after_crop_index(next, (depth-1) as nat));
        }
    }

    proof fn cropped_ptr_in_index_values(self, root: Pointer, depth: nat)
        requires
            self.inv(),
            self.journal.can_crop_index(root, depth),
            root is Some ==> cj_lsn_addr_index(self.journal).contains_value(root.unwrap()),
        ensures
            self.journal.pointer_after_crop_index(root, depth) is Some ==>
                cj_lsn_addr_index(self.journal).contains_value(
                    self.journal.pointer_after_crop_index(root, depth).unwrap()),
        decreases depth
    {
        if depth == 0 {
        } else {
            reveal(ConcreteJournal::State::valid_journal_structure);
            self.journal_tj_ensures();
            assert(self.journal_disk_view().is_nondangling_pointer(root)) by {
                let index = cj_lsn_addr_index(self.journal);
                let addr = root.unwrap();
                let witness_lsn: LSN = choose |lsn: LSN| index.contains_key(lsn) && index[lsn] == addr;
                self.journal_disk_view().instantiate_index_keys_map_to_valid_entries(index, witness_lsn);
            }
            self.next_index_refines(root);
            let next = self.journal.next_index(root);
            self.cropped_ptr_in_index_values(next, (depth - 1) as nat);
        }
    }

    proof fn largest_lsn_plus_one_matches_seq_end(self, ptr: Pointer)
        requires
            self.inv(),
            ptr is Some,
            cj_lsn_addr_index(self.journal).contains_value(ptr.unwrap()),
        ensures
            largest_lsn_plus_one(cj_lsn_addr_index(self.journal), ptr)
                == self.journal_tj().disk_view.entries[ptr.unwrap()].message_seq.seq_end,
    {
        let tj = self.journal_tj();
        let index = cj_lsn_addr_index(self.journal);
        let addr = ptr.unwrap();
        let bdy = tj.disk_view.boundary_lsn;
        let msgs = tj.disk_view.entries[addr].message_seq;

        reveal(ConcreteJournal::State::valid_journal_structure);
        self.journal_tj_ensures();
        assert(tj == self.journal_tj());
        assert(index == tj.build_lsn_addr_index());
        tj.build_lsn_addr_index_ensures();
        reveal(TruncatedJournal::index_domain_valid);

        let witness_lsn = choose |lsn: LSN|
            #![auto] index.contains_key(lsn) && index[lsn] == addr;
        tj.disk_view.instantiate_index_keys_map_to_valid_entries(index, witness_lsn);
        assert(bdy < msgs.seq_end);

        let end_minus_one = (msgs.seq_end - 1) as nat;
        assert(DiskView::cropped_msg_seq_contains_lsn(bdy, msgs, end_minus_one)) by {
            assert(bdy <= end_minus_one);
            assert(msgs.seq_start <= end_minus_one);
        }
        assert(index.values().contains(addr));
        assert(tj.index_range_valid(index));
        assert(tj.every_lsn_at_addr_indexed_to_addr(index, addr));
        assert(index.contains_key(end_minus_one));
        assert(index[end_minus_one] == addr);

        assert forall |other_lsn| (#[trigger] index.contains_key(other_lsn) && index[other_lsn] == addr)
            implies other_lsn <= end_minus_one by {
            tj.disk_view.instantiate_index_keys_map_to_valid_entries(index, other_lsn);
        }
        assert(maxmax(index, addr, end_minus_one));

        let max_lsn = choose |lsn: LSN| maxmax(index, addr, lsn);
        assert(max_lsn <= end_minus_one);
        assert(end_minus_one <= max_lsn);
    }

    proof fn indexed_addr_refines_to_allocation_addr(self, addr: Address)
        requires
            self.refinement_wf(),
            cj_lsn_addr_index(self.journal).contains_value(addr),
        ensures
            ({
                let record = self.i().tj().disk_view.entries[addr];
                let start_lsn = record.message_seq.maybe_discard_old(
                    self.i().tj().disk_view.boundary_lsn,
                ).seq_start;
                &&& self.i().tj().disk_view.entries.contains_key(addr)
                &&& start_lsn < record.message_seq.seq_end
                &&& self.i().lsn_au_index.contains_key(start_lsn)
                &&& self.i().lsn_au_index[start_lsn] == addr.au
            }),
    {
        assume({
            let record = self.i().tj().disk_view.entries[addr];
            let start_lsn = record.message_seq.maybe_discard_old(
                self.i().tj().disk_view.boundary_lsn,
            ).seq_start;
            &&& self.i().tj().disk_view.entries.contains_key(addr)
            &&& start_lsn < record.message_seq.seq_end
            &&& self.i().lsn_au_index.contains_key(start_lsn)
            &&& self.i().lsn_au_index[start_lsn] == addr.au
        });
    }

    proof fn journal_cache_reads_ensures(self, post: Self, reads: Map<Address, RawPage>)
        requires
            self.inv(), post.inv(),
            Cache::State::next(self.cache, post.cache, Cache::Label::Access{reads: reads, writes: Map::empty()})
        ensures
            forall |addr| #[trigger] reads.contains_key(addr) && self.journal_disk_view().entries.contains_key(addr)
            ==> to_journal_records(reads)[addr] == self.journal_disk_view().entries[addr]
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);

        let journal_reads = to_journal_records(reads);
        assert(journal_reads.dom() =~= reads.dom());

        let cache_lbl = Cache::Label::Access{reads: reads, writes: Map::empty()};
        self.cache.build_lookup_map_ensures();
        self.journal_tj_ensures();

        assert forall |addr| #[trigger] reads.contains_key(addr)
            && self.journal_disk_view().entries.contains_key(addr)
        implies journal_reads[addr] == self.journal_disk_view().entries[addr]
        by {
            assert(journal_reads.contains_key(addr));
            assert(raw_page_to_record(reads[addr]) == journal_reads[addr]);

            // reads match with content in the cache
            assert(cache_lbl->reads.contains_key(addr)); // trigger
            assert(self.cache.lookup_map.contains_key(addr));

            // connect this slot to content on ephemeral disk
            let slot = self.cache.lookup_map[addr];
            assert(self.cache.non_empty_slot(slot));
            assert(self.journal_disk_view().is_sub_disk(self.journal_disk_view()));
            assert(self.journal_disk_view().entries.contains_key(addr));
            assert(self.journal_disk_view().entries[addr] == self.journal_disk_view().entries[addr]);

            assert(journal_reads[addr] == raw_page_to_record(self.cache.entries[slot]->data));
            if self.cache.status_map[slot] is Clean {
                assert(self.cache.valid_clean_slot(slot)); // trigger
                assert(self.cache.entries[slot].get_addr() == addr);
                assert(self.clean_journal_cache_matches_disk());
                assert(self.disk.content.contains_key(addr));
                assert(self.journal_disk_view().entries[addr] == raw_page_to_record(self.disk.content[addr]));
                assert(reads[addr] == self.disk.content[addr]);
            } else {
                assert(self.cache.status_map[slot] is Dirty || self.cache.status_map[slot] is Writeback);
                assert(self.dirty_cache_journal_entries().contains_key(addr));
                assert(self.dirty_cache_journal_entries()[addr] == raw_page_to_record(self.cache.entries[slot]->data));
                assert(self.journal_disk_view().entries[addr] == self.dirty_cache_journal_entries()[addr]);
            }
            assert(journal_reads[addr] == self.journal_disk_view().entries[addr]);
        }
    }

    proof fn read_for_recovery_refines(self, post: Self, lbl: ConcreteJournal::Label, reads: Map<Address, RawPage>)
        requires self.refinement_wf(), post.inv(), Self::read_for_recovery(self, post, lbl, reads)
        ensures AllocationJournal::State::next(self.i(), post.i(), lbl.i(self))
    {
        let i_lbl = lbl.i(self);
        let messages = i_lbl.arrow_ReadForRecovery_messages();

        reveal(ConcreteJournal::State::read_for_recovery);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);

        let journal_lbl = CachedJournal::Label::ReadForRecovery{messages, reads: to_journal_records(reads)};
        let journal_step = choose |journal_step| CachedJournal::State::next_by(self.journal, post.journal, journal_lbl, journal_step);
        let start_lsn = journal_step.arrow_read_for_recovery_0();
        let addr = journal_step.arrow_read_for_recovery_1();

        let tj = self.journal_tj();
        self.journal_tj_ensures();
        reveal(ConcreteJournal::State::valid_journal_structure);
        assert(tj.decodable());
        assert(tj.disk_view.wf());
        assert(tj.disk_view.is_nondangling_pointer(tj.freshest_rec));
        assert(tj.disk_view.block_in_bounds(tj.freshest_rec));
        assert(tj.disk_view.decodable(tj.freshest_rec));
        if tj.freshest_rec is Some {
            assert(cj_lsn_addr_index(self.journal).contains_value(tj.freshest_rec.unwrap()));
        }

        self.journal_cache_reads_ensures(post, reads);

        reveal(ConcreteJournal::State::i);
        assert(post == self);
        reveal(AllocationJournal::State::next_by);
        assume(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::read_for_recovery(start_lsn, addr),
        ));
        reveal(AllocationJournal::State::next);
    }

    proof fn query_end_lsn_refines(self, post: Self, lbl: ConcreteJournal::Label)
        requires self.refinement_wf(), post.inv(), Self::query_end_lsn(self, post, lbl)
        ensures AllocationJournal::State::next(self.i(), post.i(), lbl.i(self))
    {
        reveal(ConcreteJournal::State::query_end_lsn);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);

        let linked_lbl = AllocationJournal::State::linked_lbl(lbl.i(self));
        reveal(ConcreteJournal::State::i);
        reveal(ConcreteJournal::State::valid_journal_structure);
        self.journal_tj_ensures();
        assert(post == self);
        assert(self.i().journal == self.linked_journal_i());
        assert(self.i().journal.wf());
        assert(self.i().journal.seq_end() == self.journal.seq_end());
        assert(LinkedJournal::State::next_by(
            self.i().journal,
            self.i().journal,
            linked_lbl,
            LinkedJournal::Step::query_end_lsn(),
        )) by {
            reveal(LinkedJournal::State::next_by);
        }
        reveal(LinkedJournal::State::next);
        assert(LinkedJournal::State::next(self.i().journal, self.i().journal, linked_lbl));
        reveal(AllocationJournal::State::next_by);
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::query_end_lsn(),
        ));
        reveal(AllocationJournal::State::next);
    }

    proof fn put_refines(self, post: Self, lbl: ConcreteJournal::Label, new_journal: CachedJournal::State)
        requires self.refinement_wf(), post.inv(), Self::put(self, post, lbl, new_journal)
        ensures AllocationJournal::State::next(self.i(), post.i(), lbl.i(self))
    {
        reveal(ConcreteJournal::State::put);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);

        let messages = lbl.arrow_Put_messages();
        let linked_lbl = AllocationJournal::State::linked_lbl(lbl.i(self));
        reveal(ConcreteJournal::State::i);
        reveal(ConcreteJournal::State::valid_journal_structure);
        self.journal_tj_ensures();
        post.journal_tj_ensures();
        assert(post.journal == new_journal);
        assert(post.cache == self.cache);
        assert(post.disk == self.disk);
        assert(post.mini_allocator == self.mini_allocator);
        assert(self.i().journal.wf());
        assert(self.i().journal.seq_end() == self.journal.seq_end());
        assert(post.i().journal.truncated_journal == self.i().journal.truncated_journal);
        assert(post.i().journal.unmarshalled_tail
            == self.i().journal.unmarshalled_tail.concat(messages));
        assert(LinkedJournal::State::next_by(
            self.i().journal,
            post.i().journal,
            linked_lbl,
            LinkedJournal::Step::put(),
        )) by {
            reveal(LinkedJournal::State::next_by);
        }
        reveal(LinkedJournal::State::next);
        assert(LinkedJournal::State::next(self.i().journal, post.i().journal, linked_lbl));
        reveal(AllocationJournal::State::next_by);
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::put(),
        ));
        reveal(AllocationJournal::State::next);
    }

    proof fn freeze_for_commit_refines(self, post: Self, lbl: ConcreteJournal::Label, frozen_domain: Set<Address>, reads: Map<Address, RawPage>)
        requires self.refinement_wf(), post.inv(), Self::freeze_for_commit(self, post, lbl, frozen_domain, reads)
        ensures AllocationJournal::State::next(self.i(), post.i(), lbl.i(self))
    {
        reveal(ConcreteJournal::State::freeze_for_commit);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);

        let frozen_reads = to_journal_records(reads);
        let frozen_ptr = lbl->frozen.freshest_rec;
        let frozen_seq_end = if frozen_ptr is Some { frozen_reads[frozen_ptr.unwrap()].message_seq.seq_end } else { lbl->frozen.boundary_lsn };
        let journal_lbl = CachedJournal::Label::FreezeForCommit{frozen: lbl->frozen, frozen_seq_end};
        let journal_step = choose |journal_step| CachedJournal::State::next_by(self.journal, post.journal, journal_lbl, journal_step);
        assert(journal_step is freeze_for_commit);
        assume(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::freeze_for_commit(),
        ));
        reveal(AllocationJournal::State::next);
    }

    proof fn init_refines(self, disk: AsyncDisk::State, cache: Cache::State, journal: CachedJournal::State)
        requires self.inv(), ConcreteJournal::State::initialize(self, disk, cache, journal),
        ensures AllocationJournal::State::initialize(self.i(), self.i().journal, JournalImage{tj: self.loaded_journal_tj()})
    {
        reveal(ConcreteJournal::State::initialize);
        reveal(ConcreteJournal::State::i);
        reveal(LinkedJournal::State::initialize);
        reveal(AllocationJournal::State::initialize);

        let image = JournalImage{tj: self.loaded_journal_tj()};
        assert(image.valid_image());
        assert(self.i().journal == self.linked_journal_i());
        assert(self.i().journal.truncated_journal == self.loaded_journal_tj());
        assert(self.i().journal.unmarshalled_tail
            == MsgHistory::empty_history_at(self.loaded_journal_tj().seq_end()));
        assert(LinkedJournal::State::initialize(self.i().journal, image.tj));

        let tj = self.loaded_journal_tj();
        let addr_index = cj_lsn_addr_index(self.journal);
        let au_index = cached_lsn_au_index(self.journal);
        reveal(ConcreteJournal::State::valid_journal_structure);
        assume(self.i().lsn_au_index == image.tj.build_lsn_au_index(image.tj.seq_start()));
        assume(AllocationJournal::State::initialize(
            self.i(),
            self.i().journal,
            image,
        ));
    }

    proof fn internal_no_op_refines(self, post: Self, lbl: ConcreteJournal::Label)
        requires
            self.refinement_wf(),
            post.inv(),
            lbl is Internal,
            lbl->allocs == Set::<AU>::empty(),
            lbl->deallocs == Set::<AU>::empty(),
            post.i() =~= self.i(),
        ensures AllocationJournal::State::next(self.i(), post.i(), lbl.i(self))
    {
        assert(post.i() == self.i());
        reveal(AllocationJournal::State::next_by);
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::internal_no_op(),
        ));
        reveal(AllocationJournal::State::next);
    }

    proof fn internal_mini_allocator_fill_refines(self, post: Self, lbl: ConcreteJournal::Label)
        requires self.refinement_wf(), post.inv(), Self::internal_mini_allocator_fill(self, post, lbl)
        ensures AllocationJournal::State::next(self.i(), post.i(), lbl.i(self))
    {
        reveal(ConcreteJournal::State::internal_mini_allocator_fill);
        reveal(AllocationJournal::State::next_by);
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::internal_mini_allocator_fill(post.i().journal),
        ));
        reveal(AllocationJournal::State::next);
    }

    proof fn internal_mini_allocator_prune_refines(self, post: Self, lbl: ConcreteJournal::Label)
        requires self.refinement_wf(), post.inv(), Self::internal_mini_allocator_prune(self, post, lbl)
        ensures AllocationJournal::State::next(self.i(), post.i(), lbl.i(self))
    {
        reveal(ConcreteJournal::State::internal_mini_allocator_prune);
        reveal(ConcreteJournal::State::i);
        let concrete_deallocs = lbl.arrow_Internal_deallocs();
        assert forall |au| #[trigger] lbl.i(self).arrow_InternalAllocations_deallocs().contains(au)
            implies self.i().mini_allocator.can_remove(au) by {
            match lbl {
                ConcreteJournal::Label::Internal{allocs, deallocs} => {
                    assert(lbl.i(self).arrow_InternalAllocations_deallocs() == deallocs);
                    assert(deallocs.contains(au));
                    assert(self.mini_allocator.can_remove(au));
                    assert(self.i().mini_allocator == self.mini_allocator);
                }
                _ => {
                    assert(false);
                }
            }
        }
        reveal(AllocationJournal::State::next_by);
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::internal_mini_allocator_prune(),
        ));
        reveal(AllocationJournal::State::next);
    }

    proof fn discard_old_refines(
        self,
        post: Self,
        lbl: ConcreteJournal::Label,
        new_journal: CachedJournal::State,
        discard_addrs: Set<Address>,
    )
        requires self.refinement_wf(), post.inv(), Self::discard_old(self, post, lbl, new_journal, discard_addrs)
        ensures AllocationJournal::State::next(self.i(), post.i(), lbl.i(self))
    {
        reveal(ConcreteJournal::State::discard_old);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        reveal(ConcreteJournal::State::i);
        reveal(ConcreteJournal::State::valid_journal_structure);

        let start_lsn = lbl->start_lsn;
        let post_addr_index = cj_lsn_addr_index(post.journal);
        let new_au_index = lsn_au_index_discard_up_to(self.i().lsn_au_index, start_lsn);
        let keep_addrs = Set::new(|addr: Address|
            self.i().tj().disk_view.entries.contains_key(addr)
                && new_au_index.values().contains(addr.au));
        ConcreteJournal::State::discard_old_full_disk_effect(
            self,
            post,
            lbl,
            new_journal,
            discard_addrs,
        );
        assume(self.i().journal.seq_end() == self.journal.seq_end());
        assume(self.i().tj().seq_end() == self.journal.marshalled_seq_end());
        assert(post.i().journal.unmarshalled_tail
            == self.i().journal.unmarshalled_tail.bounded_discard(start_lsn));
        assert(post.i().lsn_au_index =~= new_au_index);
        assert(lbl.i(self).arrow_DiscardOld_deallocs()
            == self.i().lsn_au_index.values().difference(new_au_index.values()));
        assume(keep_addrs =~= post_addr_index.values());
        if start_lsn < self.i().tj().seq_end() {
            assume(self.i().tj().discard_old_cond(start_lsn, keep_addrs, post.i().journal.truncated_journal));
            assume(keep_addrs =~= post.i().journal.truncated_journal.disk_view.entries.dom());
        } else {
            assume(post.i().journal.truncated_journal == TruncatedJournal::empty_at(start_lsn));
        }
        assert(post.i().mini_allocator
            == self.i().mini_allocator.prune(lbl.i(self).arrow_DiscardOld_deallocs()));
        reveal(AllocationJournal::State::next_by);
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::discard_old(post.i().journal),
        ));
        reveal(AllocationJournal::State::next);
    }

    proof fn journal_marshal_refines(
        self,
        post: Self,
        lbl: ConcreteJournal::Label,
        new_journal: CachedJournal::State,
        new_cache: Cache::State,
        addr: Address,
        writes: Map<Address, RawPage>,
    )
        requires self.refinement_wf(), post.inv(), Self::journal_marshal(self, post, lbl, new_journal, new_cache, addr, writes)
        ensures AllocationJournal::State::next(self.i(), post.i(), lbl.i(self))
    {
        reveal(ConcreteJournal::State::journal_marshal);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);

        let journal_lbl = CachedJournal::Label::JournalMarshal{writes: to_journal_records(writes)};
        let journal_step = choose |step| CachedJournal::State::next_by(self.journal, new_journal, journal_lbl, step);
        match journal_step {
            CachedJournal::Step::internal_journal_marshal(cut, marshalled_addr) => {
                assert(marshalled_addr == addr);
                ConcreteJournal::State::journal_marshal_full_disk_effect(
                    self,
                    post,
                    lbl,
                    new_journal,
                    new_cache,
                    addr,
                    writes,
                    cut,
                );
                reveal(ConcreteJournal::State::i);
                reveal(ConcreteJournal::State::valid_journal_structure);
                let marshalled_msgs = self.i().journal.unmarshalled_tail.discard_recent(cut);
                assume(post.i().journal.truncated_journal == self.i().tj().append_record(addr, marshalled_msgs));
                assert(post.i().journal.unmarshalled_tail
                    == self.i().journal.unmarshalled_tail.discard_old(cut));
                assert(post.i().lsn_au_index
                    =~= lsn_au_index_append_record(self.i().lsn_au_index, marshalled_msgs, addr.au));
                reveal(AllocationJournal::State::next_by);
                assert(AllocationJournal::State::next_by(
                    self.i(),
                    post.i(),
                    lbl.i(self),
                    AllocationJournal::Step::internal_journal_marshal(cut, addr, post.i().journal),
                ));
                reveal(AllocationJournal::State::next);
            }
            _ => {
                assert(false);
            }
        }
    }

    proof fn cache_disk_ops_refines(
        self,
        post: Self,
        lbl: ConcreteJournal::Label,
        new_cache: Cache::State,
        new_disk: AsyncDisk::State,
        cache_requests: Set<DiskRequest>,
        cache_responses: Map<Address, DiskResponse>,
        disk_requests: Map<ID, DiskRequest>,
        disk_responses: Map<ID, DiskResponse>,
    )
        requires
            self.refinement_wf(),
            post.inv(),
            Self::cache_disk_ops(self, post, lbl, new_cache, new_disk, cache_requests, cache_responses, disk_requests, disk_responses),
        ensures AllocationJournal::State::next(self.i(), post.i(), lbl.i(self))
    {
        reveal(ConcreteJournal::State::cache_disk_ops);
        cache_disk_ops_preserves_i(
            self,
            post,
            new_cache,
            new_disk,
            cache_requests,
            cache_responses,
            disk_requests,
            disk_responses,
        );
        self.internal_no_op_refines(post, lbl);
    }

    proof fn cache_internal_refines(self, post: Self, lbl: ConcreteJournal::Label, new_cache: Cache::State)
        requires self.refinement_wf(), post.inv(), Self::cache_internal(self, post, lbl, new_cache)
        ensures AllocationJournal::State::next(self.i(), post.i(), lbl.i(self))
    {
        reveal(ConcreteJournal::State::cache_internal);
        cache_internal_preserves_i(self, post, new_cache);
        self.internal_no_op_refines(post, lbl);
    }

    proof fn disk_internal_refines(self, post: Self, lbl: ConcreteJournal::Label, new_disk: AsyncDisk::State)
        requires self.refinement_wf(), post.inv(), Self::disk_internal(self, post, lbl, new_disk)
        ensures AllocationJournal::State::next(self.i(), post.i(), lbl.i(self))
    {
        reveal(ConcreteJournal::State::disk_internal);
        disk_internal_preserves_i(self, post, new_disk);
        self.internal_no_op_refines(post, lbl);
    }

    pub proof fn next_refines(self, post: Self, lbl: ConcreteJournal::Label)
        requires self.refinement_wf(), post.inv(), ConcreteJournal::State::next(self, post, lbl)
        ensures AllocationJournal::State::next(self.i(), post.i(), lbl.i(self))
    {
        reveal(ConcreteJournal::State::next);
        reveal(ConcreteJournal::State::next_by);

        let step = choose |step| ConcreteJournal::State::next_by(self, post, lbl, step);
        match step {
            ConcreteJournal::Step::read_for_recovery(reads) =>
                self.read_for_recovery_refines(post, lbl, reads),
            ConcreteJournal::Step::freeze_for_commit(frozen_domain, reads) =>
                self.freeze_for_commit_refines(post, lbl, frozen_domain, reads),
            ConcreteJournal::Step::query_end_lsn() =>
                self.query_end_lsn_refines(post, lbl),
            ConcreteJournal::Step::put(new_journal) =>
                self.put_refines(post, lbl, new_journal),
            ConcreteJournal::Step::discard_old(new_journal, discard_addrs) =>
                self.discard_old_refines(post, lbl, new_journal, discard_addrs),
            ConcreteJournal::Step::journal_marshal(new_journal, new_cache, addr, writes) =>
                self.journal_marshal_refines(post, lbl, new_journal, new_cache, addr, writes),
            ConcreteJournal::Step::internal_mini_allocator_fill() =>
                self.internal_mini_allocator_fill_refines(post, lbl),
            ConcreteJournal::Step::internal_mini_allocator_prune() =>
                self.internal_mini_allocator_prune_refines(post, lbl),
            ConcreteJournal::Step::cache_disk_ops(new_cache, new_disk, cache_requests, cache_responses, disk_requests, disk_responses) =>
                self.cache_disk_ops_refines(post, lbl, new_cache, new_disk, cache_requests, cache_responses, disk_requests, disk_responses),
            ConcreteJournal::Step::cache_internal(new_cache) =>
                self.cache_internal_refines(post, lbl, new_cache),
            ConcreteJournal::Step::disk_internal(new_disk) =>
                self.disk_internal_refines(post, lbl, new_disk),
            _ => { }
        }
    }
}
}
