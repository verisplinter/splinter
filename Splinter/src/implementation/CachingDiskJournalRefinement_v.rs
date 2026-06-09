// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Loaded-state refinement from CachingDiskJournal to AllocationJournal.

#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::map::*;
use vstd::assert_maps_equal;

use crate::abstract_system::MsgHistory_v::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::AllocationJournal_v::{
    AllocationJournal, JournalImage, lsn_au_index_append_record, lsn_au_index_discard_up_to,
};
use crate::allocation_layer::LikesJournal_v::{LsnAddrIndex, largest_lsn_plus_one, maxmax};
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::disk::GenericDisk_v::{Address, AU, Pointer, to_aus};
use crate::spec::AsyncDisk_t::RawPage;
use crate::implementation::CachedJournal_v::*;
use crate::implementation::CachingDisk_v::*;
use crate::implementation::CachingDiskJournal_v::*;
use crate::implementation::JournalTypes_v::{raw_page_to_record, to_journal_records};
use crate::journal::LinkedJournal_v::*;

verus!{

impl CachingDiskJournal::State {
    pub open spec fn journal_lsn_addr_index(self) -> LsnAddrIndex {
        self.journal_tj().build_lsn_addr_index()
    }

    pub open spec fn tj_at(self, snapshot: JournalSnapshot) -> TruncatedJournal {
        TruncatedJournal{
            freshest_rec: snapshot.freshest_rec(),
            disk_view: DiskView{
                boundary_lsn: snapshot.boundary_lsn,
                entries: self.journal_disk_view().entries,
            },
        }
    }

    pub open spec fn frozen_seq_end_i(self, snapshot: JournalSnapshot) -> LSN {
        if snapshot.freshest_rec() is Some {
            self.journal_disk_view().entries[snapshot.freshest_rec().unwrap()].message_seq.seq_end
        } else {
            snapshot.boundary_lsn
        }
    }

    pub open spec fn frozen_lsns_i(self, snapshot: JournalSnapshot) -> Set<LSN> {
        Set::new(|lsn: LSN| snapshot.boundary_lsn <= lsn < self.frozen_seq_end_i(snapshot))
    }

    pub open spec fn frozen_tj_i(self, snapshot: JournalSnapshot) -> TruncatedJournal {
        let frozen_index = self.i().lsn_au_index.restrict(self.frozen_lsns_i(snapshot));
        let frozen_domain = self.i().tj().disk_view.tight_domain(
            frozen_index,
            snapshot.freshest_rec(),
        );
        let frozen_tj = TruncatedJournal{
            freshest_rec: snapshot.freshest_rec(),
            disk_view: DiskView{
                boundary_lsn: snapshot.boundary_lsn,
                entries: self.i().tj().disk_view.entries.restrict(frozen_domain),
            },
        };
        frozen_tj.build_tight()
    }

    pub proof fn frozen_tj_i_matches_native_tight(self, snapshot: JournalSnapshot)
        requires
            self.inv(),
        ensures
            self.frozen_tj_i(snapshot) == self.frozen_tj(snapshot).build_tight(),
    {
        assert(self.i().journal.truncated_journal == self.journal_tj());
        assert(self.i().tj() == self.journal_tj());
        assert(self.i().lsn_au_index == self.lsn_au_index_or_empty()) by {
            self.lsn_au_index_or_empty_matches_full();
        }
        assert(self.frozen_seq_end_i(snapshot) == self.frozen_seq_end(snapshot));
        assert(self.frozen_lsns_i(snapshot) =~= self.frozen_lsns(snapshot));
        let i_index = self.i().lsn_au_index.restrict(self.frozen_lsns_i(snapshot));
        let native_index = self.lsn_au_index_or_empty().restrict(self.frozen_lsns(snapshot));
        assert(i_index == native_index);
        assert(self.i().tj().disk_view == self.journal_tj().disk_view);
        assert(self.frozen_tj_i(snapshot) == self.frozen_tj(snapshot).build_tight());
    }

    pub proof fn journal_tj_ensures(self)
        requires
            self.inv(),
            self.journal.status is Some,
        ensures
            self.journal_tj().decodable(),
            self.journal_tj().seq_end() == cj_unmarshalled_tail(self.journal).seq_start,
            self.journal_tj().disk_view.pointer_is_upstream(
                self.journal_tj().freshest_rec,
                self.journal.snapshot.first(),
            ),
            cj_lsn_au_index(self.journal) == self.journal_tj().build_lsn_au_index_from_first(
                self.journal.snapshot.first(),
            ),
            self.journal_tj().index_domain_valid(self.journal_lsn_addr_index()),
            self.journal_tj().disk_view.index_keys_map_to_valid_entries(self.journal_lsn_addr_index()),
            self.journal_tj().index_range_valid(self.journal_lsn_addr_index()),
            self.journal_tj().freshest_rec is Some
                ==> self.journal_lsn_addr_index().contains_value(self.journal_tj().freshest_rec.unwrap()),
    {
        let tj = self.journal_tj();
        assert(tj.decodable());
        tj.build_lsn_addr_index_ensures();
        tj.build_lsn_au_index_from_first_ensures(self.journal.snapshot.first());
    }

    pub proof fn interpreted_inv(self)
        requires
            self.inv(),
        ensures
            self.i().inv(),
    {
        let first = self.journal.snapshot.first();
        let tj = self.journal_tj();
        assert(self.i().journal.truncated_journal == tj);
        assert(self.i().journal.unmarshalled_tail == if self.journal.status is Some {
            cj_unmarshalled_tail(self.journal)
        } else {
            MsgHistory::empty_history_at(tj.seq_end())
        });
        assert(self.i().journal.wf());
        assert(self.i().journal.inv());
        assert(self.i().lsn_au_index == tj.build_lsn_au_index_from_first(first));
        tj.build_lsn_au_index_from_first_ensures(first);
        if tj.freshest_rec is Some {
            assert(self.i().lsn_au_index.contains_key(tj.seq_start()));
            assert(self.i().lsn_au_index[tj.seq_start()] == first);
        }
        assert(AllocationJournal::State::disk_domain_not_free(self.i().tj().disk_view, self.i().mini_allocator));
        assert(AllocationJournal::State::mini_allocator_follows_freshest_rec(
            self.i().tj().freshest_rec,
            self.i().mini_allocator,
        ));
        assert(self.i().inv());
    }

    pub proof fn disk_reads_ensures(self, reads: Map<Address, RawPage>)
        requires
            self.disk.inv(),
            CachingDisk::State::next(
                self.disk,
                self.disk,
                CachingDisk::Label::Access{reads, writes: Map::empty()},
            ),
        ensures
            reads <= self.disk.cache,
            forall |addr: Address| #[trigger] reads.contains_key(addr)
                ==> to_journal_records(reads)[addr] == self.visible_records()[addr],
    {
        CachingDisk::State::access_effect(self.disk, self.disk, reads, Map::empty());
        assert forall |addr: Address| #[trigger] reads.contains_key(addr)
            implies to_journal_records(reads)[addr] == self.visible_records()[addr] by {
            assert(reads <= self.disk.cache);
            assert(self.disk.visible().contains_key(addr));
            assert(self.disk.visible()[addr] == self.disk.cache[addr]);
            assert(reads[addr] == self.disk.visible()[addr]);
        }
    }

    pub proof fn largest_lsn_plus_one_matches_seq_end(self, addr: Address)
        requires
            self.inv(),
            self.journal.status is Some,
            self.journal_lsn_addr_index().contains_value(addr),
        ensures
            self.i().tj().disk_view.entries.contains_key(addr),
            ({
                let record = self.i().tj().disk_view.entries[addr];
                let end_minus_one = (record.message_seq.seq_end - 1) as nat;
                &&& maxmax(self.journal_lsn_addr_index(), addr, end_minus_one)
                &&& largest_lsn_plus_one(self.journal_lsn_addr_index(), Some(addr))
                    == record.message_seq.seq_end
                &&& record.message_seq.seq_end <= self.i().tj().seq_end()
            }),
    {
        self.journal_tj_ensures();
        let tj = self.i().tj();
        let dv = tj.disk_view;
        let index = self.journal_lsn_addr_index();
        let bdy = dv.boundary_lsn;
        let witness_lsn = choose |lsn: LSN| #![auto]
            index.contains_key(lsn) && index[lsn] == addr;

        assert(index == tj.build_lsn_addr_index());
        dv.instantiate_index_keys_map_to_valid_entries(index, witness_lsn);
        assert(dv.addr_supports_lsn(addr, witness_lsn));
        assert(dv.entries.contains_key(addr));
        let msgs = dv.entries[addr].message_seq;
        assert(bdy < msgs.seq_end);

        let end_minus_one = (msgs.seq_end - 1) as nat;
        assert(DiskView::cropped_msg_seq_contains_lsn(bdy, msgs, end_minus_one)) by {
            assert(bdy <= end_minus_one);
            assert(msgs.seq_start <= end_minus_one);
        }
        assert(tj.index_range_valid(index));
        assert(tj.every_lsn_at_addr_indexed_to_addr(index, addr));
        assert(index.contains_key(end_minus_one));
        assert(index[end_minus_one] == addr);
        assert(end_minus_one < tj.seq_end()) by {
            reveal(TruncatedJournal::index_domain_valid);
        }

        assert forall |other_lsn: LSN|
            (#[trigger] index.contains_key(other_lsn) && index[other_lsn] == addr)
            implies other_lsn <= end_minus_one by {
            dv.instantiate_index_keys_map_to_valid_entries(index, other_lsn);
        }
        assert(maxmax(index, addr, end_minus_one));

        let max_lsn = choose |lsn: LSN| maxmax(index, addr, lsn);
        assert(max_lsn <= end_minus_one);
        assert(end_minus_one <= max_lsn);
    }

    pub proof fn indexed_addr_refines_to_allocation_addr(self, addr: Address)
        requires
            self.inv(),
            self.journal.status is Some,
            self.journal_lsn_addr_index().contains_value(addr),
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
        self.journal_tj_ensures();
        let tj = self.i().tj();
        let dv = tj.disk_view;
        let index = self.journal_lsn_addr_index();
        let au_index = self.i().lsn_au_index;
        let lsn = choose |lsn: LSN| #![auto] index.contains_key(lsn) && index[lsn] == addr;
        assert(index == tj.build_lsn_addr_index());
        tj.build_lsn_addr_index_ensures();
        reveal(TruncatedJournal::index_domain_valid);
        reveal(DiskView::index_keys_map_to_valid_entries);
        dv.instantiate_index_keys_map_to_valid_entries(index, lsn);
        assert(dv.addr_supports_lsn(addr, lsn));
        assert(dv.entries.contains_key(addr));

        let record = dv.entries[addr];
        let cropped = record.message_seq.maybe_discard_old(dv.boundary_lsn);
        let start_lsn = cropped.seq_start;
        assert(record.wf());
        if record.message_seq.seq_start <= dv.boundary_lsn {
            assert(start_lsn == dv.boundary_lsn);
        } else {
            assert(start_lsn == record.message_seq.seq_start);
        }
        assert(dv.addr_supports_lsn(addr, start_lsn));
        assert(start_lsn < record.message_seq.seq_end);

        self.interpreted_inv();
        assert(au_index == tj.build_lsn_au_index_from_first(self.journal.snapshot.first()));
        tj.build_lsn_au_index_from_first_ensures(self.journal.snapshot.first());
        reveal(TruncatedJournal::au_domain_valid);
        assert(au_index.contains_key(start_lsn));
        dv.addr_supports_lsn_consistent_with_index(au_index, start_lsn, addr);
    }

}

impl CachingDiskJournal::Label {
    pub open spec fn i(self, state: CachingDiskJournal::State) -> AllocationJournal::Label {
        match self {
            Self::ReadForRecovery{messages} => {
                AllocationJournal::Label::ReadForRecovery{messages}
            },
            Self::FreezeForCommit{frozen, seq_end} => {
                AllocationJournal::Label::FreezeForCommit{
                    frozen_journal: JournalImage{tj: state.frozen_tj_i(frozen), first: frozen.first()},
                }
            },
            Self::QueryEndLsn{end_lsn} => {
                AllocationJournal::Label::QueryEndLsn{end_lsn}
            },
            Self::Put{messages} => {
                AllocationJournal::Label::Put{messages}
            },
            Self::DiscardOld{start_lsn, require_end} => {
                let new_lsn_au_index = lsn_au_index_discard_up_to(cj_lsn_au_index(state.journal), start_lsn);
                AllocationJournal::Label::DiscardOld{
                    start_lsn,
                    require_end,
                    deallocs: cj_lsn_au_index(state.journal).values().difference(new_lsn_au_index.values()),
                }
            },
            Self::ObserveCleanAUs{aus} => {
                AllocationJournal::Label::InternalAllocations{
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                }
            },
            Self::CommitPrepared{frozen, seq_end} => {
                AllocationJournal::Label::InternalAllocations{
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                }
            },
            Self::LoadIndex{discovered_aus} => {
                AllocationJournal::Label::InternalAllocations{
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                }
            },
            Self::Internal => {
                AllocationJournal::Label::InternalAllocations{
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                }
            },
            Self::InternalAlloc{allocs, deallocs, prune_aus} => {
                AllocationJournal::Label::InternalAllocations{allocs, deallocs: prune_aus}
            },
        }
    }
}

impl CachingDiskJournal::State {
    pub proof fn init_refines(
        self,
        snapshot: JournalSnapshot,
        disk: CachingDisk::State,
    )
        requires
            CachingDiskJournal::State::initialize(self, snapshot, disk),
        ensures
            AllocationJournal::State::initialize(
                self.i(),
                self.i().journal,
                JournalImage{tj: self.journal_tj(), first: snapshot.first()},
            ),
    {
        reveal(CachingDiskJournal::State::initialize);
        reveal(AllocationJournal::State::initialize);
        reveal(LinkedJournal::State::initialize);

        CachingDiskJournal::State::initialize_inductive(self, snapshot, disk);
        let image = JournalImage{tj: self.journal_tj(), first: snapshot.first()};
        assert(self.inv());
        assert(self.visible_journal_structure());
        assert(self.journal == CachedJournal::State{snapshot, status: Option::None});
        assert(self.i().journal == self.linked_journal_i());
        assert(self.i().journal.truncated_journal == self.journal_tj());
        assert(self.i().journal.unmarshalled_tail
            == MsgHistory::empty_history_at(self.journal_tj().seq_end()));
        assert(LinkedJournal::State::initialize(self.i().journal, image.tj));
        assert(image.valid_image());
    }

    pub proof fn query_end_lsn_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
    )
        requires
            self.inv(),
            post.inv(),
            CachingDiskJournal::State::query_end_lsn(self, post, lbl),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::query_end_lsn);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let end_lsn = lbl.arrow_QueryEndLsn_end_lsn();
        let journal_lbl = CachedJournal::Label::QueryEndLsn{end_lsn};
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(self.journal, self.journal, journal_lbl, step);
        match cj_step {
            CachedJournal::Step::query_end_lsn() => {
                reveal(CachedJournal::State::query_end_lsn);
            },
            _ => {
                assert(false);
            },
        }
        let i_lbl = lbl.i(self);
        let linked_lbl = AllocationJournal::State::linked_lbl(i_lbl);
        self.journal_tj_ensures();
        assert(post == self);
        assert(self.i().journal.wf());
        assert(self.i().journal.seq_end() == self.journal.seq_end());
        assert(LinkedJournal::State::next_by(
            self.i().journal,
            post.i().journal,
            linked_lbl,
            LinkedJournal::Step::query_end_lsn(),
        )) by {
            reveal(LinkedJournal::State::next_by);
        }
        reveal(LinkedJournal::State::next);
        assert(LinkedJournal::State::next(self.i().journal, post.i().journal, linked_lbl));
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            i_lbl,
            AllocationJournal::Step::query_end_lsn(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn put_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        new_journal: CachedJournal::State,
    )
        requires
            self.inv(),
            post.inv(),
            CachingDiskJournal::State::put(self, post, lbl, new_journal),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::put);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let messages = lbl.arrow_Put_messages();
        let journal_lbl = CachedJournal::Label::Put{messages};
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(self.journal, new_journal, journal_lbl, step);
        match cj_step {
            CachedJournal::Step::put() => {
                reveal(CachedJournal::State::put);
            },
            _ => {
                assert(false);
            },
        }
        let i_lbl = lbl.i(self);
        let linked_lbl = AllocationJournal::State::linked_lbl(i_lbl);
        self.journal_tj_ensures();
        assert(post.journal == new_journal);
        assert(post.disk == self.disk);
        assert(post.mini_allocator == self.mini_allocator);
        assert(post.journal.snapshot == self.journal.snapshot);
        assert(post.journal_tj() == self.journal_tj());
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
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            i_lbl,
            AllocationJournal::Step::put(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn read_for_recovery_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        reads: Map<Address, RawPage>,
    )
        requires
            self.inv(),
            post.inv(),
            CachingDiskJournal::State::read_for_recovery(self, post, lbl, reads),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::read_for_recovery);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        self.disk_reads_ensures(reads);
        self.journal_tj_ensures();

        let messages = lbl.arrow_ReadForRecovery_messages();
        let journal_lbl = CachedJournal::Label::ReadForRecovery{
            messages,
            reads: to_journal_records(reads),
        };
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(self.journal, self.journal, journal_lbl, step);
        match cj_step {
            CachedJournal::Step::read_for_recovery(start_lsn, addr) => {
                reveal(CachedJournal::State::read_for_recovery);
                assert(reads.contains_key(addr));
                assert(messages == to_journal_records(reads)[addr].message_seq.maybe_discard_old(
                    self.journal.snapshot.boundary_lsn,
                ));
                assert(self.i().tj().disk_view.entries.contains_key(addr));
                assert(to_journal_records(reads)[addr] == self.visible_records()[addr]);
                assert(self.visible_records()[addr] == self.i().tj().disk_view.entries[addr]);
                let record = self.i().tj().disk_view.entries[addr];
                let actual_start_lsn = record.message_seq.maybe_discard_old(
                    self.i().tj().disk_view.boundary_lsn,
                ).seq_start;
                assert(start_lsn == actual_start_lsn);
                assert(start_lsn < record.message_seq.seq_end);
                assert(self.i().lsn_au_index.contains_key(start_lsn));
                assert(self.i().lsn_au_index[start_lsn] == addr.au);
                assert(messages == record.message_seq.maybe_discard_old(
                    self.i().tj().disk_view.boundary_lsn,
                ));
                assert(post == self);
                assert(AllocationJournal::State::next_by(
                    self.i(),
                    post.i(),
                    lbl.i(self),
                    AllocationJournal::Step::read_for_recovery(start_lsn, addr),
                )) by {
                    reveal(AllocationJournal::State::next_by);
                }
            },
            _ => {
                assert(false);
            },
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn freeze_for_commit_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        reads: Map<Address, RawPage>,
    )
        requires
            self.inv(),
            post.inv(),
            CachingDiskJournal::State::freeze_for_commit(self, post, lbl, reads),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::freeze_for_commit);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        self.disk_reads_ensures(reads);
        self.journal_tj_ensures();

        let frozen = lbl.arrow_FreezeForCommit_frozen();
        let seq_end = lbl.arrow_FreezeForCommit_seq_end();
        let frozen_tj = self.frozen_tj_i(frozen);
        let frozen_journal = JournalImage{tj: frozen_tj, first: frozen.first()};
        assert(seq_end == self.frozen_seq_end(frozen));
        let journal_lbl = CachedJournal::Label::FreezeForCommit{
            frozen,
            reads: to_journal_records(reads),
        };
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(self.journal, self.journal, journal_lbl, step);
        match cj_step {
            CachedJournal::Step::freeze_for_commit() => {
                reveal(CachedJournal::State::freeze_for_commit);
            },
            _ => {
                assert(false);
            },
        }
        assert(post == self);
        let index = self.journal_lsn_addr_index();
        if self.journal.snapshot.freshest_rec() is Some {
            assert(self.journal_tj().freshest_rec == self.journal.snapshot.freshest_rec());
            assert(index.contains_value(self.journal.snapshot.freshest_rec().unwrap()));
        }
        if frozen.freshest_rec() is Some {
            let root = frozen.freshest_rec().unwrap();
            let frozen_seq_end = to_journal_records(reads)[root].message_seq.seq_end;
            assert(reads.contains_key(root));
            assert(to_journal_records(reads).contains_key(root));
            assert(self.disk.visible().contains_key(root));
            assert(self.visible_records().contains_key(root));
            assert(to_journal_records(reads)[root] == self.visible_records()[root]);
            assert(self.i().tj().disk_view.entries.contains_key(root));
            assert(frozen_seq_end == self.frozen_seq_end_i(frozen));
            assert(frozen.boundary_lsn < to_journal_records(reads)[root].message_seq.seq_end);
        }

        self.frozen_tj_i_matches_native_tight(frozen);
        let native_frozen_tj = self.frozen_tj(frozen);
        let native_frozen_journal = JournalImage{tj: native_frozen_tj, first: frozen.first()};
        assert(CachingDiskJournal::State::freeze_for_commit(self, self, lbl, reads));
        assert(lbl == CachingDiskJournal::Label::FreezeForCommit{frozen, seq_end});
        assert(CachingDiskJournal::State::next_by(
            self,
            self,
            lbl,
            CachingDiskJournal::Step::freeze_for_commit(reads),
        )) by {
            reveal(CachingDiskJournal::State::next_by);
        };
        reveal(CachingDiskJournal::State::next);
        assert(CachingDiskJournal::State::next(self, self, lbl));
        self.freeze_for_commit_image_valid(frozen, seq_end);
        assert(native_frozen_journal.valid_image());
        native_frozen_journal.valid_image_implies_tight_valid_image();
        assert(frozen_journal == JournalImage{
            tj: native_frozen_tj.build_tight(),
            first: frozen.first(),
        });
        assert(frozen_journal.valid_image());
        native_frozen_tj.disk_view.build_tight_ensures(native_frozen_tj.freshest_rec);
        assert(native_frozen_tj.build_tight().disk_view.is_sub_disk(native_frozen_tj.disk_view));
        assert(native_frozen_tj.disk_view.is_sub_disk_with_newer_lsn(self.journal_tj().disk_view));
        assert(frozen_tj.disk_view.is_sub_disk_with_newer_lsn(self.i().tj().disk_view)) by {
            assert(frozen_tj == native_frozen_tj.build_tight());
            assert(self.i().tj().disk_view == self.journal_tj().disk_view);
            assert(frozen_tj.disk_view.boundary_lsn == native_frozen_tj.disk_view.boundary_lsn);
            assert(self.i().tj().disk_view.boundary_lsn <= native_frozen_tj.disk_view.boundary_lsn);
            assert(frozen_tj.disk_view.entries <= native_frozen_tj.disk_view.entries);
            assert(native_frozen_tj.disk_view.entries <= self.journal_tj().disk_view.entries);
        };
        if frozen.freshest_rec() is None {
            assert(frozen_tj.seq_start() == frozen_tj.seq_end());
            assert(frozen_tj.seq_start() <= self.i().journal.seq_end()) by {
                assert(self.journal.wf());
                assert(frozen.freshest_rec() is None);
                assert(frozen.boundary_lsn <= self.journal.seq_end());
                assert(self.i().journal.wf());
            }
        }
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::freeze_for_commit(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn internal_noop_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
    )
        requires
            self.inv(),
            post.inv(),
            CachingDiskJournal::State::internal_noop(self, post, lbl),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::internal_noop);
        assert(post == self);
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::internal_no_op(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn caching_disk_internal_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        new_disk: CachingDisk::State,
    )
        requires
            self.inv(),
            post.inv(),
            CachingDiskJournal::State::caching_disk_internal(
                self,
                post,
                lbl,
                new_disk,
            ),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::caching_disk_internal);
        CachingDisk::State::internal_visible_unchanged(self.disk, post.disk);
        assert(post.journal == self.journal);
        assert(post.mini_allocator == self.mini_allocator);
        assert(post.disk.visible() == self.disk.visible());
        assert(post.visible_records() == self.visible_records());
        assert(post.journal_disk_view() == self.journal_disk_view());
        assert(post.journal_tj() == self.journal_tj());
        assert(post.linked_journal_i() == self.linked_journal_i());
        assert(post.i() == self.i());
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::internal_no_op(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn load_index_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        new_journal: CachedJournal::State,
        reads: Map<Address, RawPage>,
    )
        requires
            self.inv(),
            post.inv(),
            CachingDiskJournal::State::load_index(
                self,
                post,
                lbl,
                new_journal,
                reads,
            ),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::load_index);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        assert(lbl is LoadIndex);
        let discovered_aus = lbl.arrow_LoadIndex_discovered_aus();
        let journal_lbl = CachedJournal::Label::LoadIndex{
            reads: to_journal_records(reads),
            discovered_aus,
        };
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(self.journal, new_journal, journal_lbl, step);
        match cj_step {
            CachedJournal::Step::load_index(au_depth, page_depth) => {
                reveal(CachedJournal::State::load_index);
            },
            _ => {
                assert(false);
            },
        }
        assert(self.journal.status is None);
        assert(post.journal == new_journal);
        assert(post.disk == self.disk);
        assert(post.mini_allocator == self.mini_allocator);
        assert(post.journal.status is Some);
        assert(post.journal.snapshot == self.journal.snapshot);
        assert(post.journal_tj() == self.journal_tj());

        assert(post.i().journal.truncated_journal == self.i().journal.truncated_journal);
        assert(post.i().journal.unmarshalled_tail == self.i().journal.unmarshalled_tail) by {
            assert(post.loaded_journal_structure());
            assert(post.journal_tj().seq_end() == cj_unmarshalled_tail(post.journal).seq_start);
            assert(post.journal_tj().seq_end() == self.journal_tj().seq_end());
            assert(cj_unmarshalled_tail(post.journal)
                == MsgHistory::empty_history_at(post.journal_tj().seq_end()));
        }
        assert(post.i().journal == self.i().journal);
        assert(post.i().mini_allocator == self.i().mini_allocator);
        assert(post.i().lsn_au_index == self.i().tj().build_lsn_au_index_from_first(self.journal.snapshot.first())) by {
            post.interpreted_inv();
            assert(post.i().tj() == self.i().tj());
        }
        assert(post.i().lsn_au_index == self.i().lsn_au_index);
        assert(lbl.i(self).arrow_InternalAllocations_allocs() == Set::<AU>::empty());
        assert(lbl.i(self).arrow_InternalAllocations_deallocs() == Set::<AU>::empty());
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::internal_no_op(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn observe_clean_aus_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        new_journal: CachedJournal::State,
    )
        requires
            self.inv(),
            post.inv(),
            CachingDiskJournal::State::observe_clean_aus(
                self,
                post,
                lbl,
                new_journal,
            ),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::observe_clean_aus);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let aus = lbl.arrow_ObserveCleanAUs_aus();
        let journal_lbl = CachedJournal::Label::ObserveCleanAUs{aus};
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(self.journal, post.journal, journal_lbl, step);
        match cj_step {
            CachedJournal::Step::advance_watermark(target_lsn) => {
                reveal(CachedJournal::State::advance_watermark);
            },
            _ => {
                assert(false);
            },
        }
        assert(post.disk == self.disk);
        assert(post.disk.visible() == self.disk.visible());
        assert(post.journal.snapshot == self.journal.snapshot);
        assert(post.journal.status is Some);
        assert(self.journal.status is Some);
        assert(post.journal.status.unwrap().lsn_au_index
            == self.journal.status.unwrap().lsn_au_index);
        assert(post.journal.status.unwrap().unmarshalled_tail
            == self.journal.status.unwrap().unmarshalled_tail);
        assert(post.mini_allocator == self.mini_allocator);
        assert(post.visible_records() == self.visible_records());
        assert(post.journal_disk_view() == self.journal_disk_view());
        assert(post.journal_tj() == self.journal_tj());
        assert(post.linked_journal_i() == self.linked_journal_i());
        assert(post.i() == self.i());
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::internal_no_op(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn journal_marshal_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        new_journal: CachedJournal::State,
        new_disk: CachingDisk::State,
        addr: Address,
        writes: Map<Address, RawPage>,
    )
        requires
            self.inv(),
            post.inv(),
            CachingDiskJournal::State::journal_marshal(
                self,
                post,
                lbl,
                new_journal,
                new_disk,
                addr,
                writes,
            ),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::journal_marshal);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        CachingDisk::State::access_visible_effect(self.disk, post.disk, Map::empty(), writes);

        let journal_lbl = CachedJournal::Label::JournalMarshal{writes: to_journal_records(writes)};
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(self.journal, new_journal, journal_lbl, step);
        let (cut, hidden_addr) = match cj_step {
            CachedJournal::Step::internal_journal_marshal(cut, hidden_addr) => {
                reveal(CachedJournal::State::internal_journal_marshal);
                (cut, hidden_addr)
            },
            _ => {
                assert(false);
                arbitrary()
            },
        };
        let marshalled_msgs = self.journal.status.unwrap().unmarshalled_tail.discard_recent(cut);
        let expected_record = JournalRecord{
            message_seq: marshalled_msgs,
            prior_rec: self.journal.snapshot.freshest_rec(),
        };
        assert(to_journal_records(writes) == Map::empty().insert(hidden_addr, expected_record));
        assert(to_journal_records(writes).contains_key(hidden_addr));
        assert(to_journal_records(writes).contains_key(hidden_addr) == writes.contains_key(hidden_addr));
        assert(writes.contains_key(hidden_addr));
        assert(writes.dom().contains(hidden_addr));
        assert(writes.dom() =~= Set::new(|a: Address| a == addr));
        assert(Set::new(|a: Address| a == addr).contains(hidden_addr));
        assert(hidden_addr == addr);
        assert(to_journal_records(writes) == Map::empty().insert(addr, expected_record));
        assert(post.journal == new_journal);
        assert(post.journal.snapshot == JournalSnapshot{
            root: Some(JournalRoot{
                freshest_rec: addr,
                first: if self.journal.snapshot.root is None { addr.au } else { self.journal.snapshot.first() },
            }),
            ..self.journal.snapshot
        });
        assert(post.journal.status is Some);
        assert(self.journal.status is Some);
        assert(post.journal.status.unwrap().unmarshalled_tail
            == self.journal.status.unwrap().unmarshalled_tail.discard_old(cut));
        assert(post.journal.status.unwrap().lsn_au_index
            == lsn_au_index_append_record(
                self.journal.status.unwrap().lsn_au_index,
                marshalled_msgs,
                addr.au,
            ));
        assert(post.mini_allocator == self.mini_allocator.allocate(addr).observe(addr));
        assert(post.disk.visible() == self.disk.visible().union_prefer_right(writes));
        assert_maps_equal!(
            post.visible_records(),
            self.visible_records().union_prefer_right(to_journal_records(writes)),
            a => {
                if writes.contains_key(a) {
                } else {
                }
            }
        );
        assert_maps_equal!(
            post.journal_tj().disk_view.entries,
            self.journal_tj().append_record(addr, marshalled_msgs).disk_view.entries,
            a => {
                if a == addr {
                    assert(to_journal_records(writes).contains_key(addr));
                    assert(to_journal_records(writes)[addr] == expected_record);
                } else {
                }
            }
        );
        assert(post.journal_tj().freshest_rec == Some(addr));
        assert(post.journal_tj().disk_view.boundary_lsn == self.journal_tj().disk_view.boundary_lsn);
        assert(post.i().journal.truncated_journal
            == self.i().journal.truncated_journal.append_record(addr, marshalled_msgs));
        assert(post.i().journal.unmarshalled_tail
            == self.i().journal.unmarshalled_tail.discard_old(cut));
        assert_maps_equal!(
            post.i().lsn_au_index,
            lsn_au_index_append_record(self.i().lsn_au_index, marshalled_msgs, addr.au),
            lsn => {
            }
        );
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::internal_journal_marshal(cut, addr, post.i().journal),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn commit_prepared_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
    )
        requires
            self.inv(),
            post.inv(),
            CachingDiskJournal::State::commit_prepared(self, post, lbl),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::commit_prepared);
        assert(post == self);
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::internal_no_op(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn discard_old_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        new_journal: CachedJournal::State,
        new_disk: CachingDisk::State,
    )
        requires
            self.inv(),
            post.inv(),
            CachingDiskJournal::State::discard_old(
                self,
            post,
            lbl,
            new_journal,
            new_disk,
        ),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::discard_old);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let start_lsn = lbl.arrow_DiscardOld_start_lsn();
        let require_end = lbl.arrow_DiscardOld_require_end();
        let old_au_index = cj_lsn_au_index(self.journal);
        let expected_new_au_index = lsn_au_index_discard_up_to(old_au_index, start_lsn);
        let deallocs = old_au_index.values().difference(expected_new_au_index.values());
        CachingDisk::State::forget_effect(self.disk, post.disk, deallocs);

        let journal_lbl = CachedJournal::Label::DiscardOld{start_lsn, require_end, deallocs};
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(self.journal, post.journal, journal_lbl, step);
        match cj_step {
            CachedJournal::Step::discard_old() => {
                reveal(CachedJournal::State::discard_old);
            },
            _ => {
                assert(false);
            },
        }
        let new_au_index = cj_lsn_au_index(post.journal);
        let deallocs = old_au_index.values().difference(new_au_index.values());
        let discard_addrs = addresses_in_aus(deallocs);
        let keep_addrs = Set::new(|addr: Address|
            self.i().tj().disk_view.entries.contains_key(addr)
                && expected_new_au_index.values().contains(addr.au));
        post.journal_tj_ensures();
        assert(post.journal == new_journal);
        assert(post.mini_allocator == self.mini_allocator.prune(deallocs));
        assert(self.i().lsn_au_index == old_au_index);
        assert(new_au_index =~= expected_new_au_index);
        assert(post.i().lsn_au_index =~= expected_new_au_index);
        assert(lbl.i(self).arrow_DiscardOld_deallocs()
            == self.i().lsn_au_index.values().difference(expected_new_au_index.values()));
        assert(post.i().mini_allocator
            == self.i().mini_allocator.prune(lbl.i(self).arrow_DiscardOld_deallocs()));
        assert(post.i().journal.unmarshalled_tail
            == self.i().journal.unmarshalled_tail.bounded_discard(start_lsn));

        assert_maps_equal!(post.disk.visible(), self.disk.visible().remove_keys(discard_addrs), addr => {
            if discard_addrs.contains(addr) {
            } else {
            }
        });
        assert_maps_equal!(
            post.i().tj().disk_view.entries,
            self.i().tj().disk_view.entries.restrict(keep_addrs),
            addr => {
                if post.i().tj().disk_view.entries.contains_key(addr) {
                    assert(post.disk.visible().contains_key(addr));
                    assert(self.disk.visible().contains_key(addr));
                    assert(self.i().tj().disk_view.entries.contains_key(addr));
                    assert(!discard_addrs.contains(addr));
                    assert(self.i().lsn_au_index.values().contains(addr.au)) by {
                        self.interpreted_inv();
                        assert(self.i().tj().disk_view.domain_tight_wrt_index(
                            self.i().lsn_au_index,
                            self.i().tj().freshest_rec,
                        ));
                    }
                    assert(!deallocs.contains(addr.au));
                    if !expected_new_au_index.values().contains(addr.au) {
                        assert(deallocs.contains(addr.au));
                        assert(false);
                    }
                    assert(expected_new_au_index.values().contains(addr.au));
                    assert(keep_addrs.contains(addr));
                }
                if self.i().tj().disk_view.entries.restrict(keep_addrs).contains_key(addr) {
                    assert(keep_addrs.contains(addr));
                    assert(self.disk.visible().contains_key(addr));
                    assert(!deallocs.contains(addr.au));
                    assert(!discard_addrs.contains(addr));
                    assert(post.disk.visible().contains_key(addr));
                }
            }
        );

        if start_lsn < self.i().tj().seq_end() {
            assert(post.i().journal.truncated_journal.wf());
            assert(post.i().journal.truncated_journal.disk_view.boundary_lsn == start_lsn);
            assert(post.i().journal.truncated_journal.disk_view.entries
                <= self.i().tj().disk_view.entries);
            assert(keep_addrs <= post.i().journal.truncated_journal.disk_view.entries.dom());
            assert(post.i().journal.truncated_journal.freshest_rec == self.i().tj().freshest_rec);
            assert(self.i().tj().discard_old_cond(
                start_lsn,
                keep_addrs,
                post.i().journal.truncated_journal,
            ));
            assert(keep_addrs =~= post.i().journal.truncated_journal.disk_view.entries.dom()) by {
                assert_maps_equal!(
                    post.i().journal.truncated_journal.disk_view.entries,
                    self.i().tj().disk_view.entries.restrict(keep_addrs),
                );
            }
        } else {
            assert(post.i().journal.truncated_journal.wf());
            assert(post.i().journal.truncated_journal.freshest_rec is None);
            assert(post.i().journal.truncated_journal.disk_view.boundary_lsn == start_lsn);
            assert(post.i().journal.truncated_journal.disk_view.entries.dom()
                =~= Set::<Address>::empty()) by {
                assert forall |addr: Address|
                    #[trigger] post.i().journal.truncated_journal.disk_view.entries.dom().contains(addr)
                    implies false by {
                    assert(post.i().journal.truncated_journal.disk_view.entries.contains_key(addr));
                    assert(post.i().lsn_au_index.values().contains(addr.au)) by {
                        post.interpreted_inv();
                        assert(post.i().tj().disk_view.domain_tight_wrt_index(
                            post.i().lsn_au_index,
                            post.i().tj().freshest_rec,
                        ));
                    }
                    assert(post.i().lsn_au_index.contains_value(addr.au));
                    let lsn = choose |lsn: LSN| #![auto]
                        post.i().lsn_au_index.contains_key(lsn)
                            && post.i().lsn_au_index[lsn] == addr.au;
                    assert(expected_new_au_index.contains_key(lsn));
                    assert(self.i().lsn_au_index.contains_key(lsn));
                    assert(start_lsn <= lsn);
                    assert(self.i().tj().seq_start() <= lsn < self.i().tj().seq_end()) by {
                        self.i().tj().build_lsn_au_index_ensures(self.i().tj().seq_start());
                        reveal(TruncatedJournal::au_domain_valid);
                    }
                    assert(false);
                }
            }
            assert(post.i().journal.truncated_journal == TruncatedJournal::empty_at(start_lsn));
        }

        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::discard_old(post.i().journal),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn mini_allocator_fill_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
    )
        requires
            self.inv(),
            post.inv(),
            CachingDiskJournal::State::mini_allocator_fill(self, post, lbl),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::mini_allocator_fill);
        let allocs = lbl.arrow_InternalAlloc_allocs();
        assert(lbl.arrow_InternalAlloc_deallocs() == Set::<AU>::empty());
        assert(lbl.arrow_InternalAlloc_prune_aus() == Set::<AU>::empty());
        assert(post.journal == self.journal);
        assert(post.disk == self.disk);
        assert(post.mini_allocator == self.mini_allocator.add_aus(allocs));
        assert(allocs.disjoint(self.mini_allocator.allocs.dom()));
        assert(allocs.disjoint(to_aus(self.journal_disk_view().entries.dom())));
        assert(post.linked_journal_i() == self.linked_journal_i());
        assert(post.i().journal == self.i().journal);
        assert(post.i().lsn_au_index == self.i().lsn_au_index);
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::internal_mini_allocator_fill(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn mini_allocator_prune_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
    )
        requires
            self.inv(),
            post.inv(),
            CachingDiskJournal::State::mini_allocator_prune(self, post, lbl),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::mini_allocator_prune);
        let deallocs = lbl.arrow_InternalAlloc_deallocs();
        let prune_aus = lbl.arrow_InternalAlloc_prune_aus();
        assert(lbl.arrow_InternalAlloc_allocs() == Set::<AU>::empty());
        assert(post.journal == self.journal);
        assert(post.disk == self.disk);
        assert(post.mini_allocator == self.mini_allocator.prune(prune_aus));
        assert(self.i().mini_allocator == self.mini_allocator);
        assert(post.linked_journal_i() == self.linked_journal_i());
        assert(post.i().journal == self.i().journal);
        assert(post.i().lsn_au_index == self.i().lsn_au_index);
        assert(lbl.i(self).arrow_InternalAllocations_deallocs() == prune_aus);
        assert forall |au: AU| #[trigger] lbl.i(self).arrow_InternalAllocations_deallocs().contains(au)
            implies self.i().mini_allocator.can_remove(au) by {
            match lbl {
                CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus} => {
                    assert(lbl.i(self).arrow_InternalAllocations_deallocs() == prune_aus);
                    assert(prune_aus.contains(au));
                    assert(self.mini_allocator.can_remove(au));
                    assert(self.i().mini_allocator == self.mini_allocator);
                },
                _ => {
                    assert(false);
                },
            }
        }
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::internal_mini_allocator_prune(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn next_refines(self, post: Self, lbl: CachingDiskJournal::Label)
        requires
            self.inv(),
            CachingDiskJournal::State::next(self, post, lbl),
        ensures
            post.inv(),
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        CachingDiskJournal::State::inv_next(self, post, lbl);
        self.interpreted_inv();
        post.interpreted_inv();
        reveal(CachingDiskJournal::State::next);
        let step = choose |step: CachingDiskJournal::Step| #![auto]
            CachingDiskJournal::State::next_by(self, post, lbl, step);
        reveal(CachingDiskJournal::State::next_by);
        match step {
            CachingDiskJournal::Step::caching_disk_internal(new_disk) => {
                self.caching_disk_internal_refines(post, lbl, new_disk);
            },
            CachingDiskJournal::Step::load_index(new_journal, reads) => {
                self.load_index_refines(post, lbl, new_journal, reads);
            },
            CachingDiskJournal::Step::read_for_recovery(reads) => {
                self.read_for_recovery_refines(post, lbl, reads);
            },
            CachingDiskJournal::Step::freeze_for_commit(reads) => {
                self.freeze_for_commit_refines(post, lbl, reads);
            },
            CachingDiskJournal::Step::query_end_lsn() => {
                self.query_end_lsn_refines(post, lbl);
            },
            CachingDiskJournal::Step::put(new_journal) => {
                self.put_refines(post, lbl, new_journal);
            },
            CachingDiskJournal::Step::journal_marshal(new_journal, new_disk, addr, writes) => {
                self.journal_marshal_refines(post, lbl, new_journal, new_disk, addr, writes);
            },
            CachingDiskJournal::Step::observe_clean_aus(new_journal) => {
                self.observe_clean_aus_refines(post, lbl, new_journal);
            },
            CachingDiskJournal::Step::commit_prepared() => {
                self.commit_prepared_refines(post, lbl);
            },
            CachingDiskJournal::Step::discard_old(new_journal, new_disk) => {
                self.discard_old_refines(post, lbl, new_journal, new_disk);
            },
            CachingDiskJournal::Step::mini_allocator_fill() => {
                self.mini_allocator_fill_refines(post, lbl);
            },
            CachingDiskJournal::Step::mini_allocator_prune() => {
                self.mini_allocator_prune_refines(post, lbl);
            },
            CachingDiskJournal::Step::internal_noop() => {
                self.internal_noop_refines(post, lbl);
            },
            CachingDiskJournal::Step::dummy_to_use_type_params(_) => {
                assert(false);
            },
        }
    }
}

} // verus!
