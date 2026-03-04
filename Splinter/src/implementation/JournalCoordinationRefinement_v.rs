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
use crate::allocation_layer::LikesJournal_v::{LikesJournal, LsnAddrIndex};
use crate::implementation::JournalCoordinationSystem_v::*;
use crate::implementation::AtomicState_v::{raw_page_to_record, to_journal_records};

verus!{

impl JournalCoordinationSystem::State {
    // TODO(JL): this almost feels like something we should have adopted in likesjournal
    pub proof fn next_index_refines(self, ptr: Pointer)
        requires 
            self.inv(),
            ptr is Some,
            self.ephemeral_disk().is_nondangling_pointer(ptr),
        ensures ({
            let result = self.journal.next_index(ptr);
            let index = cj_lsn_addr_index(self.journal);
            &&& result is Some ==> index.contains_value(result.unwrap())
            &&& result == self.ephemeral_disk().next(ptr)
        })
    {
        assume({
            let result = self.journal.next_index(ptr);
            let index = cj_lsn_addr_index(self.journal);
            &&& result is Some ==> index.contains_value(result.unwrap())
            &&& result == self.ephemeral_disk().next(ptr)
        });
    }

    // NOTE: maybe this should have been how we define these operations in the likes layer 
    // in the first place...
    proof fn can_crop_ptr_after_index_refines(self, root: Pointer, depth: nat)
        requires 
            self.inv(), 
            self.journal.can_crop_index(root, depth),
            root is Some ==> cj_lsn_addr_index(self.journal).contains_value(root.unwrap()),
        ensures 
            self.ephemeral_disk().can_crop(root, depth),
            self.ephemeral_disk().pointer_after_crop(root, depth)
            == self.journal.pointer_after_crop_index(root, depth),
        decreases depth
    {
        assume(self.ephemeral_disk().can_crop(root, depth));
        assume(self.ephemeral_disk().pointer_after_crop(root, depth)
            == self.journal.pointer_after_crop_index(root, depth));
    }

    proof fn journal_cache_reads_ensures(self, post: Self, reads: Map<Address, RawPage>)
        requires
            self.inv(), post.inv(), 
            Cache::State::next(self.cache, post.cache, Cache::Label::Access{reads: reads, writes: Map::empty()})
        ensures 
            forall |addr| #[trigger] reads.contains_key(addr) && self.ephemeral_disk().entries.contains_key(addr)
            ==> to_journal_records(reads)[addr] == self.ephemeral_disk().entries[addr]
    {
        assume(false); // TODO: proof gap
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);

        let journal_reads = to_journal_records(reads);
        assert(journal_reads.dom() =~= reads.dom());

        let cache_lbl = Cache::Label::Access{reads: reads, writes: Map::empty()};
        self.cache.build_lookup_map_ensures();

        assert forall |addr| #[trigger] reads.contains_key(addr) 
            && self.ephemeral_disk().entries.contains_key(addr)
        implies journal_reads[addr] == self.ephemeral_disk().entries[addr]
        by {
            assert(journal_reads.contains_key(addr));
            journal_unmarshall_marshall(journal_reads[addr]);
            assert(raw_page_to_record(reads[addr]) == journal_reads[addr]);

            // reads match with content in the cache
            assert(cache_lbl->reads.contains_key(addr)); // trigger
            assert(self.cache.lookup_map.contains_key(addr));
    
            // connect this slot to content on ephemeral disk
            let slot = self.cache.lookup_map[addr];
            assert(self.cache.non_empty_slot(slot));
    
            assert(journal_reads[addr] == raw_page_to_record(self.cache.entries[slot]->data));
            assert(journal_reads[addr] == self.ephemeral_disk().entries[addr]) by {
                if self.cache.status_map[slot] is Clean {
                    assert(self.cache.valid_clean_slot(slot)); // trigger
                    assert(self.cache.entries[slot].get_addr() == addr);
                }
            }
        }
    }

    proof fn read_for_recovery_refines(self, post: Self, lbl: JournalCoordinationSystem::Label, reads: Map<Address, RawPage>)
        requires self.inv(), post.inv(), Self::read_for_recovery(self, post, lbl, reads)
        ensures LikesJournal::State::next(self.i(), post.i(), lbl.i(self))
    {
        assume(false); // TODO: proof gap
        let i_lbl = lbl.i(self);
        let messages = i_lbl.arrow_ReadForRecovery_messages();

        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);

        let journal_lbl = CachedJournal::Label::ReadForRecovery{messages, reads: to_journal_records(reads)};
        let journal_step = choose |journal_step| CachedJournal::State::next_by(self.journal, post.journal, journal_lbl, journal_step);
        let depth = journal_step.arrow_read_for_recovery_0();

        let tj = self.ephemeral_tj();

        self.can_crop_ptr_after_index_refines(tj.freshest_rec, depth);
        tj.disk_view.pointer_after_crop_ensures(tj.freshest_rec, depth);
        let ptr = tj.disk_view.pointer_after_crop(tj.freshest_rec, depth);

        self.journal_cache_reads_ensures(post, reads);

        // read for recovery is the same
        let linked_lbl = LikesJournal::State::lbl_i(lbl.i(self));
        assert(LinkedJournal::State::next_by(self.i().journal, self.i().journal, linked_lbl, 
            LinkedJournal::Step::read_for_recovery(depth))) by {
            reveal(LinkedJournal::State::next_by);
        }
        // reveal(LinkedJournal::State::next);
        reveal(LikesJournal::State::next_by);
        reveal(LikesJournal::State::next);
    }

    proof fn freeze_for_commit_refines(self, post: Self, lbl: JournalCoordinationSystem::Label, frozen_domain: Set<Address>, reads: Map<Address, RawPage>)
        requires self.inv(), post.inv(), Self::freeze_for_commit(self, post, lbl, frozen_domain, reads)
        ensures LikesJournal::State::next(self.i(), post.i(), lbl.i(self))
    {
        assume(false); // TODO: proof gap
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);

        let frozen_reads = to_journal_records(reads);
        let frozen_ptr = lbl->frozen.freshest_rec;
        let frozen_seq_end = if frozen_ptr is Some { frozen_reads[frozen_ptr.unwrap()].message_seq.seq_end } else { lbl->frozen.boundary_lsn };
        let journal_lbl = CachedJournal::Label::FreezeForCommit{frozen: lbl->frozen, frozen_seq_end};
        let journal_step = choose |journal_step| CachedJournal::State::next_by(self.journal, post.journal, journal_lbl, journal_step);
        let depth = journal_step.arrow_freeze_for_commit_0();

        let i_lbl = lbl.i(self);
        let i_frozen = i_lbl->frozen_journal;
        let new_bdy = i_frozen.seq_start();

        self.can_crop_ptr_after_index_refines(cj_freshest_rec(self.journal), depth);

        let cropped_tj = self.ephemeral_tj().crop(depth);
        let ptr = self.journal.pointer_after_crop_index(cj_freshest_rec(self.journal), depth);
        self.ephemeral_tj().crop_ensures(depth);

        assert(i_frozen.decodable()) by {
            if ptr is Some {
                self.journal_cache_reads_ensures(post, reads);
            }
        }

        let post_discard = cropped_tj.discard_old(new_bdy);
        let frozen_lsns = Set::new(|lsn: LSN| new_bdy <= lsn && lsn < post_discard.seq_end());
        let frozen_index = cj_lsn_addr_index(self.journal).restrict(frozen_lsns);


        reveal(LikesJournal::State::next);
        reveal(LikesJournal::State::next_by);
        assert(LikesJournal::State::next_by(self.i(), post.i(), lbl.i(self), 
            LikesJournal::Step::freeze_for_commit(depth)));
    }

    proof fn init_refines(self, disk: AsyncDisk::State, cache: Cache::State, journal: CachedJournal::State)
        requires self.inv(), JournalCoordinationSystem::State::initialize(self, disk, cache, journal),
        ensures LikesJournal::State::initialize(self.i(), self.ephemeral_tj())
    {
        assume(false); // TODO: proof gap
    }

    // Skipping the rest for this exercise
}
}
