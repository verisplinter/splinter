// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Journal variant using CachingDisk instead of Cache + AsyncDisk.

#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::map::*;
use vstd::assert_maps_equal;

use verus_state_machines_macros::state_machine;

use crate::abstract_system::MsgHistory_v::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::AllocationJournal_v::{
    AllocationJournal, JournalImage, LsnAUIndex, au_addrs_past_pointer, lsn_au_index_append_record,
    lsn_au_index_discard_up_to,
    lsn_au_index_discard_up_to_ensures, singleton_index,
};
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::disk::GenericDisk_v::{Address, AU, Pointer, to_aus};
use crate::spec::AsyncDisk_t::RawPage;
use crate::implementation::AllocationBranchStack_v::{
    mini_allocator_add_aus_preserves_all_aus, mini_allocator_allocate_preserves_all_aus,
};
use crate::implementation::CachedJournal_v::*;
use crate::implementation::CachingDisk_v::*;
use crate::implementation::JournalTypes_v::{raw_page_to_record, to_journal_records};
use crate::journal::LinkedJournal_v::*;

verus!{

impl DiskView {
    pub proof fn build_tight_entry_active_bounded(self, root: Pointer, addr: Address)
        requires
            self.decodable(root),
            self.acyclic(),
            root is Some ==> self.upstream(root.unwrap()),
            self.build_tight(root).entries.contains_key(addr),
        ensures
            self.boundary_lsn < self.build_tight(root).entries[addr].message_seq.seq_end,
            self.build_tight(root).entries[addr].message_seq.seq_end <= self.seq_end(root),
        decreases self.the_rank_of(root),
    {
        if root is Some {
            let root_addr = root.unwrap();
            if addr == root_addr {
                assert(self.upstream(root_addr));
            } else {
                self.build_tight_shape(root);
                assert(self.build_tight(self.next(root)).entries.contains_key(addr));
                if self.next(root) is Some {
                    assert(self.this_block_can_concat(root_addr));
                    assert(self.entries[self.next(root).unwrap()].message_seq.can_concat(
                        self.entries[root_addr].message_seq,
                    ));
                    assert(self.entries[self.next(root).unwrap()].message_seq.seq_end
                        == self.entries[root_addr].message_seq.seq_start);
                    assert(self.boundary_lsn < self.entries[root_addr].message_seq.seq_start);
                    assert(self.upstream(self.next(root).unwrap()));
                }
                self.build_tight_entry_active_bounded(self.next(root), addr);
                assert(self.this_block_can_concat(root_addr));
                if self.next(root) is Some {
                    assert(self.entries[self.next(root).unwrap()].message_seq.can_concat(
                        self.entries[root_addr].message_seq,
                    ));
                    assert(self.seq_end(self.next(root))
                        == self.entries[self.next(root).unwrap()].message_seq.seq_end);
                    assert(self.entries[root_addr].message_seq.seq_start
                        == self.entries[self.next(root).unwrap()].message_seq.seq_end);
                }
            }
        }
    }
}

pub open spec fn cj_boundary_lsn(journal: CachedJournal::State) -> LSN
{
    journal.snapshot.boundary_lsn
}

pub open spec fn cj_freshest_rec(journal: CachedJournal::State) -> Pointer
{
    journal.snapshot.freshest_rec()
}

pub open spec fn cj_lsn_au_index(journal: CachedJournal::State) -> LsnAUIndex
    recommends journal.status is Some
{
    journal.status.unwrap().lsn_au_index
}

pub open spec fn cj_unmarshalled_tail(journal: CachedJournal::State) -> MsgHistory
    recommends journal.status is Some
{
    journal.status.unwrap().unmarshalled_tail
}

state_machine!{ CachingDiskJournal {
    fields {
        pub journal: CachedJournal::State,
        pub disk: CachingDisk::State,
        pub mini_allocator: MiniAllocator,
    }

    pub enum Label {
        ReadForRecovery{messages: MsgHistory},
        FreezeForCommit{frozen: JournalSnapshot, seq_end: LSN},
        QueryEndLsn{end_lsn: LSN},
        Put{messages: MsgHistory},
        DiscardOld{start_lsn: LSN, require_end: LSN},
        ObserveCleanAUs{aus: Set<AU>},
        CommitPrepared{frozen: JournalSnapshot, seq_end: LSN, persistent: Map<Address, RawPage>},
        LoadIndex{discovered_aus: Set<AU>},
        Internal,
        InternalAlloc{allocs: Set<AU>, deallocs: Set<AU>, prune_aus: Set<AU>},
    }

    init!{ initialize(snapshot: JournalSnapshot, disk: CachingDisk::State) {
        require disk.inv();
        let init_journal = CachedJournal::State{
            snapshot,
            status: Option::None,
        };
        let init_mini_allocator = MiniAllocator::empty();
        let init_state = CachingDiskJournal::State{
            journal: init_journal,
            disk,
            mini_allocator: init_mini_allocator,
        };
        require init_state.visible_journal_structure();
        require init_state.clean_watermark_durable();

        init journal = init_journal;
        init disk = disk;
        init mini_allocator = init_mini_allocator;
    }}

    transition!{ caching_disk_internal(lbl: Label, new_disk: CachingDisk::State) {
        require lbl is Internal;
        require CachingDisk::State::next(
            pre.disk,
            new_disk,
            CachingDisk::Label::Internal{},
        );

        update disk = new_disk;
    }}

    transition!{ load_index(lbl: Label, new_journal: CachedJournal::State, reads: Map<Address, RawPage>) {
        require let Label::LoadIndex{discovered_aus} = lbl;
        require CachingDisk::State::next(
            pre.disk,
            pre.disk,
            CachingDisk::Label::Access{reads, writes: Map::empty()},
        );
        require CachedJournal::State::next(
            pre.journal,
            new_journal,
            CachedJournal::Label::LoadIndex{
                reads: to_journal_records(reads),
                discovered_aus,
            },
        );
        update journal = new_journal;
    }}

    transition!{ read_for_recovery(lbl: Label, reads: Map<Address, RawPage>) {
        require let Label::ReadForRecovery{messages} = lbl;
        require CachingDisk::State::next(
            pre.disk,
            pre.disk,
            CachingDisk::Label::Access{reads, writes: Map::empty()},
        );
        require CachedJournal::State::next(
            pre.journal,
            pre.journal,
            CachedJournal::Label::ReadForRecovery{
                messages,
                reads: to_journal_records(reads),
            },
        );
    }}

    transition!{ freeze_for_commit(lbl: Label, reads: Map<Address, RawPage>) {
        require let Label::FreezeForCommit{frozen, seq_end} = lbl;
        require CachingDisk::State::next(
            pre.disk,
            pre.disk,
            CachingDisk::Label::Access{reads, writes: Map::empty()},
        );
        require seq_end == pre.frozen_seq_end(frozen);
        require CachedJournal::State::next(
            pre.journal,
            pre.journal,
            CachedJournal::Label::FreezeForCommit{
                frozen,
                reads: to_journal_records(reads),
            },
        );
    }}

    transition!{ query_end_lsn(lbl: Label) {
        require let Label::QueryEndLsn{end_lsn} = lbl;
        require CachedJournal::State::next(
            pre.journal,
            pre.journal,
            CachedJournal::Label::QueryEndLsn{end_lsn},
        );
    }}

    transition!{ put(lbl: Label, new_journal: CachedJournal::State) {
        require let Label::Put{messages} = lbl;
        require CachedJournal::State::next(
            pre.journal,
            new_journal,
            CachedJournal::Label::Put{messages},
        );

        update journal = new_journal;
    }}

    transition!{ journal_marshal(
        lbl: Label,
        new_journal: CachedJournal::State,
        new_disk: CachingDisk::State,
        addr: Address,
        writes: Map<Address, RawPage>,
    ) {
        require lbl is Internal;
        require pre.mini_allocator.tight_next_addr(pre.journal.snapshot.freshest_rec(), addr);
        require writes.dom() =~= Set::new(|a: Address| a == addr);

        require CachedJournal::State::next(
            pre.journal,
            new_journal,
            CachedJournal::Label::JournalMarshal{writes: to_journal_records(writes)},
        );
        require CachingDisk::State::next(
            pre.disk,
            new_disk,
            CachingDisk::Label::Access{reads: Map::empty(), writes},
        );

        update journal = new_journal;
        update disk = new_disk;
        update mini_allocator = pre.mini_allocator.allocate(addr);
    }}

    transition!{ observe_clean_aus(
        lbl: Label,
        new_journal: CachedJournal::State,
    ) {
        require let Label::ObserveCleanAUs{aus} = lbl;
        require CachingDisk::State::next(
            pre.disk,
            pre.disk,
            CachingDisk::Label::ObserveCleanAUs{aus},
        );
        let journal_lbl = CachedJournal::Label::ObserveCleanAUs{aus};
        require CachedJournal::State::next(
            pre.journal,
            new_journal,
            journal_lbl,
        );

        update journal = new_journal;
    }}

    transition!{ commit_prepared(lbl: Label) {
        require let Label::CommitPrepared{frozen, seq_end, persistent} = lbl;
        require pre.journal.status is Some;
        require persistent == pre.disk.persistent;
        require frozen.freshest_rec() is Some ==> seq_end <= pre.journal.clean_watermark();
    }}

    transition!{ discard_old(
        lbl: Label,
        new_journal: CachedJournal::State,
        new_disk: CachingDisk::State,
    ) {
        require lbl is DiscardOld;
        let old_au_index = cj_lsn_au_index(pre.journal);
        let new_au_index = lsn_au_index_discard_up_to(old_au_index, lbl->start_lsn);
        let deallocs = old_au_index.values().difference(new_au_index.values());
        let journal_lbl = CachedJournal::Label::DiscardOld{
            start_lsn: lbl->start_lsn,
            require_end: lbl->require_end,
            deallocs,
        };
        require CachedJournal::State::next(
            pre.journal,
            new_journal,
            journal_lbl,
        );
        require CachingDisk::State::next(
            pre.disk,
            new_disk,
            CachingDisk::Label::Forget{aus: deallocs},
        );

        update journal = new_journal;
        update disk = new_disk;
        update mini_allocator = pre.mini_allocator.prune(deallocs);
    }}

    transition!{ mini_allocator_fill(lbl: Label) {
        require lbl is InternalAlloc;
        require lbl->deallocs == Set::<AU>::empty();
        require lbl->prune_aus == Set::<AU>::empty();
        require pre.journal.status is Some;
        require lbl->allocs.disjoint(pre.mini_allocator.all_aus());
        require lbl->allocs.disjoint(cj_lsn_au_index(pre.journal).values());

        update mini_allocator = pre.mini_allocator.add_aus(lbl->allocs);
    }}

    transition!{ mini_allocator_prune(lbl: Label) {
        require lbl is InternalAlloc;
        require lbl->allocs == Set::<AU>::empty();
        require lbl->deallocs <= lbl->prune_aus;
        require forall |au: AU| #[trigger] lbl->prune_aus.contains(au)
            ==> pre.mini_allocator.can_remove(au);

        update mini_allocator = pre.mini_allocator.prune(lbl->prune_aus);
    }}

    transition!{ internal_noop(lbl: Label) {
        require lbl is Internal;
    }}

    pub open spec fn visible_journal_structure(self) -> bool {
        let index = self.journal_tj().build_lsn_au_index_from_first(self.journal.snapshot.first());
        &&& self.journal_tj().decodable()
        &&& self.journal_tj().disk_view.wf_addrs()
        &&& self.journal_tj().disk_view.pointer_is_upstream(
            self.journal_tj().freshest_rec,
            self.journal.snapshot.first(),
        )
        &&& self.journal_tj().disk_view.domain_tight_wrt_index(
            index,
            self.journal_tj().freshest_rec,
        )
        &&& self.journal_tj().disk_view.bounded_inactive_lsns(
            index,
            self.journal_tj().freshest_rec,
        )
        &&& AllocationJournal::State::disk_domain_not_free(
            self.journal_tj().disk_view,
            self.mini_allocator,
        )
        &&& AllocationJournal::State::mini_allocator_follows_freshest_rec(
            self.journal_tj().freshest_rec,
            self.mini_allocator,
        )
    }

    pub open spec fn loaded_journal_structure(self) -> bool
        recommends self.journal.status is Some
    {
        &&& self.journal_tj().seq_end() == cj_unmarshalled_tail(self.journal).seq_start
        &&& cj_lsn_au_index(self.journal) == self.journal_tj().build_lsn_au_index_from_first(
            self.journal.snapshot.first(),
        )
    }

    #[invariant]
    pub open spec fn inv(self) -> bool {
        &&& self.journal.wf()
        &&& self.disk.inv()
        &&& self.mini_allocator.wf()
        &&& self.visible_journal_structure()
        &&& self.journal.status is Some ==> self.loaded_journal_structure()
        &&& self.clean_watermark_durable()
    }

    #[inductive(initialize)]
    pub fn initialize_inductive(post: Self, snapshot: JournalSnapshot, disk: CachingDisk::State) {}

    #[inductive(caching_disk_internal)]
    fn caching_disk_internal_inductive(pre: Self, post: Self, lbl: Label, new_disk: CachingDisk::State) {
        CachingDisk::State::inv_next(pre.disk, post.disk, CachingDisk::Label::Internal{});
        CachingDisk::State::internal_visible_unchanged(pre.disk, post.disk);
        assert(post.journal == pre.journal);
        assert(post.mini_allocator == pre.mini_allocator);
        assert_maps_equal!(post.visible_records(), pre.visible_records(), addr => {});
        assert(post.journal_disk_view() == pre.journal_disk_view());
        assert(post.journal_tj() == pre.journal_tj());
        assert(post.visible_journal_structure());
        if post.journal.status is Some {
            assert(post.loaded_journal_structure());
        }
        assert(post.clean_watermark_pages() =~= pre.clean_watermark_pages());
        CachingDisk::State::internal_preserves_addrs_clean_or_evictable(
            pre.disk,
            post.disk,
            pre.clean_watermark_pages(),
        );
        assert(post.clean_watermark_durable());
    }

    #[inductive(load_index)]
    fn load_index_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CachedJournal::State,
        reads: Map<Address, RawPage>,
    ) {
        let journal_lbl = CachedJournal::Label::LoadIndex{
            reads: to_journal_records(reads),
            discovered_aus: lbl.arrow_LoadIndex_discovered_aus(),
        };
        assert(CachedJournal::State::next(pre.journal, post.journal, journal_lbl));
        CachedJournal::State::load_index_effect(
            pre.journal,
            post.journal,
            to_journal_records(reads),
            lbl.arrow_LoadIndex_discovered_aus(),
        );
        CachedJournal::State::inv_next(pre.journal, post.journal, journal_lbl);
        assert(post.disk == pre.disk);
        assert(post.mini_allocator == pre.mini_allocator);
        assert(post.journal.snapshot == pre.journal.snapshot);
        assert(post.journal_disk_view() == pre.journal_disk_view());
        assert(post.journal_tj() == pre.journal_tj());
        assert(post.visible_journal_structure());
        CachingDisk::State::access_effect(pre.disk, pre.disk, reads, Map::empty());
        assert(to_journal_records(reads) <= pre.visible_records()) by {
            assert forall |addr: Address| #[trigger] to_journal_records(reads).contains_key(addr)
                implies pre.visible_records().contains_key(addr)
                    && to_journal_records(reads)[addr] == pre.visible_records()[addr] by {
                assert(reads.contains_key(addr));
                assert(reads <= pre.disk.cache);
                assert(pre.disk.cache.contains_key(addr));
                assert(pre.disk.visible().contains_key(addr));
                assert(pre.disk.visible()[addr] == pre.disk.cache[addr]);
            }
        };
        CachedJournal::State::load_index_matches_full(
            pre.journal,
            post.journal,
            to_journal_records(reads),
            lbl.arrow_LoadIndex_discovered_aus(),
            pre.visible_records(),
        );
        assert(post.loaded_journal_structure());
    }

    #[inductive(read_for_recovery)]
    fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label, reads: Map<Address, RawPage>) {}

    #[inductive(freeze_for_commit)]
    fn freeze_for_commit_inductive(pre: Self, post: Self, lbl: Label, reads: Map<Address, RawPage>) {}

    #[inductive(query_end_lsn)]
    fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label, new_journal: CachedJournal::State) {
        let journal_lbl = CachedJournal::Label::Put{messages: lbl.arrow_Put_messages()};
        assert(CachedJournal::State::next(pre.journal, post.journal, journal_lbl));
        CachedJournal::State::put_effect(pre.journal, post.journal, lbl.arrow_Put_messages());
        CachedJournal::State::inv_next(pre.journal, post.journal, journal_lbl);
        assert(post.disk == pre.disk);
        assert(post.mini_allocator == pre.mini_allocator);
        assert(post.journal.snapshot == pre.journal.snapshot);
        assert(post.journal_disk_view() == pre.journal_disk_view());
        assert(post.journal_tj() == pre.journal_tj());
        assert(post.visible_journal_structure());
        assert(post.journal.status.unwrap().clean_watermark_lsn
            == pre.journal.status.unwrap().clean_watermark_lsn);
        assert(post.clean_watermark_pages() =~= pre.clean_watermark_pages());
        assert(post.clean_watermark_durable());
        assert(post.loaded_journal_structure());
    }

    #[inductive(journal_marshal)]
    fn journal_marshal_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CachedJournal::State,
        new_disk: CachingDisk::State,
        addr: Address,
        writes: Map<Address, RawPage>,
    ) {
        let journal_lbl = CachedJournal::Label::JournalMarshal{writes: to_journal_records(writes)};
        assert(CachedJournal::State::next(pre.journal, post.journal, journal_lbl));
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        CachingDisk::State::access_visible_effect(pre.disk, post.disk, Map::empty(), writes);
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
        let (cut, hidden_addr) = match cj_step {
            CachedJournal::Step::internal_journal_marshal(cut, hidden_addr) => {
                (cut, hidden_addr)
            },
            _ => {
                assert(false);
                arbitrary()
            },
        };
        let marshalled_msgs = pre.journal.status.unwrap().unmarshalled_tail.discard_recent(cut);
        let expected_record = JournalRecord{
            message_seq: marshalled_msgs,
            prior_rec: pre.journal.snapshot.freshest_rec(),
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
                first: if pre.journal.snapshot.root is None { addr.au } else { pre.journal.snapshot.first() },
            }),
            ..pre.journal.snapshot
        });
        assert(post.journal.status is Some);
        assert(pre.journal.status is Some);
        assert(post.journal.status.unwrap().unmarshalled_tail
            == pre.journal.status.unwrap().unmarshalled_tail.discard_old(cut));
        assert(post.journal.status.unwrap().lsn_au_index
            == lsn_au_index_append_record(
                pre.journal.status.unwrap().lsn_au_index,
                marshalled_msgs,
                addr.au,
            ));
        assert(post.disk.visible() == pre.disk.visible().union_prefer_right(writes));
        assert_maps_equal!(
            post.visible_records(),
            pre.visible_records().union_prefer_right(to_journal_records(writes)),
            a => {
                if writes.contains_key(a) {
                } else {
                }
            }
        );
        assert_maps_equal!(
            post.journal_tj().disk_view.entries,
            pre.journal_tj().append_record(addr, marshalled_msgs).disk_view.entries,
            a => {
                if a == addr {
                    assert(to_journal_records(writes).contains_key(addr));
                    assert(to_journal_records(writes)[addr] == expected_record);
                } else {
                }
            }
        );
        assert(post.journal_tj().freshest_rec == Some(addr));
        assert(post.journal_tj().disk_view.boundary_lsn == pre.journal_tj().disk_view.boundary_lsn);
        assert(post.i().journal.truncated_journal
            == pre.i().journal.truncated_journal.append_record(addr, marshalled_msgs));
        assert(post.i().journal.unmarshalled_tail
            == pre.i().journal.unmarshalled_tail.discard_old(cut));
        assert_maps_equal!(
            post.i().lsn_au_index,
            lsn_au_index_append_record(pre.i().lsn_au_index, marshalled_msgs, addr.au),
            lsn => {
            }
        );
        let pre_first = pre.journal.snapshot.first();
        pre.journal_tj().build_lsn_au_index_from_first_ensures(pre_first);
        if pre.journal_tj().freshest_rec is Some {
            assert(pre.i().lsn_au_index.contains_key(pre.i().tj().seq_start()));
            assert(pre.i().lsn_au_index[pre.i().tj().seq_start()] == pre_first);
        }
        assert(pre.i().inv());
        let allocation_post = AllocationJournal::State{
            journal: post.i().journal,
            lsn_au_index: post.i().lsn_au_index,
            mini_allocator: pre.mini_allocator.allocate(addr).observe(addr),
        };
        let alloc_lbl = AllocationJournal::Label::InternalAllocations{
            allocs: Set::<AU>::empty(),
            deallocs: Set::<AU>::empty(),
        };
        assert(AllocationJournal::State::next_by(
            pre.i(),
            allocation_post,
            alloc_lbl,
            AllocationJournal::Step::internal_journal_marshal(cut, addr, post.i().journal),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
        assert(AllocationJournal::State::next(pre.i(), allocation_post, alloc_lbl));
        AllocationJournal::State::inv_next(pre.i(), allocation_post, alloc_lbl);
        assert(allocation_post.inv());
        CachedJournal::State::inv_next(pre.journal, post.journal, journal_lbl);
        CachingDisk::State::inv_next(pre.disk, post.disk, CachingDisk::Label::Access{reads: Map::empty(), writes});
        assert(writes.dom().disjoint(pre.clean_watermark_pages())) by {
            assert forall |a: Address| #[trigger] writes.dom().contains(a)
                implies !pre.clean_watermark_pages().contains(a) by {
                assert(a == addr);
                if pre.clean_watermark_pages().contains(a) {
                    assert(pre.journal_disk_view().entries.contains_key(a));
                    assert(AllocationJournal::State::disk_domain_not_free(
                        pre.journal_tj().disk_view,
                        pre.mini_allocator,
                    ));
                    assert(pre.mini_allocator.can_allocate(a));
                    assert(false);
                }
            }
        };
        CachingDisk::State::access_preserves_addrs_clean_or_evictable(
            pre.disk,
            post.disk,
            Map::empty(),
            writes,
            pre.clean_watermark_pages(),
        );
        assert(post.clean_watermark_pages() <= pre.clean_watermark_pages()) by {
            assert forall |a: Address| #[trigger] post.clean_watermark_pages().contains(a)
                implies pre.clean_watermark_pages().contains(a) by {
                assert(post.journal.status.unwrap().clean_watermark_lsn
                    == pre.journal.status.unwrap().clean_watermark_lsn);
                assert(post.journal_disk_view().entries.contains_key(a));
                if a == addr {
                    assert(post.journal_disk_view().entries[a] == expected_record);
                    assert(expected_record.message_seq.seq_start == pre.journal.marshalled_seq_end());
                    assert(pre.journal.clean_watermark() <= pre.journal.marshalled_seq_end());
                    assert(false);
                } else {
                    assert(post.journal_disk_view().entries[a] == pre.journal_disk_view().entries[a]);
                }
            }
        };
        Self::addrs_clean_or_evictable_subset(
            post.disk,
            post.clean_watermark_pages(),
            pre.clean_watermark_pages(),
        );
        assert(pre.mini_allocator.can_allocate(addr));
        assert(pre.mini_allocator.allocate(addr).wf());
        assert(pre.mini_allocator.allocate(addr).allocs.contains_key(addr.au));
        assert(pre.mini_allocator.allocate(addr).allocs[addr.au].reserved.contains(addr));
        assert(post.mini_allocator.wf());
        assert(AllocationJournal::State::disk_domain_not_free(
            post.journal_tj().disk_view,
            post.mini_allocator,
        )) by {
            assert forall |a: Address| #[trigger] post.journal_tj().disk_view.entries.dom().contains(a)
                implies !post.mini_allocator.can_allocate(a) by {
                assert(allocation_post.inv());
                assert(!allocation_post.mini_allocator.can_allocate(a));
                if post.mini_allocator.can_allocate(a) {
                    assert(post.mini_allocator == pre.mini_allocator.allocate(addr));
                    if a == addr {
                        assert(post.mini_allocator.allocs[a.au].reserved.contains(a));
                        assert(!post.mini_allocator.allocs[a.au].is_free_addr(a));
                    } else {
                        if a.au == addr.au {
                            assert(allocation_post.mini_allocator.allocs[a.au].observed.contains(a)
                                == post.mini_allocator.allocs[a.au].observed.contains(a));
                            assert(allocation_post.mini_allocator.allocs[a.au].reserved.contains(a)
                                == post.mini_allocator.allocs[a.au].reserved.contains(a));
                        } else {
                            assert(allocation_post.mini_allocator.allocs[a.au]
                                == post.mini_allocator.allocs[a.au]);
                        }
                        assert(allocation_post.mini_allocator.can_allocate(a));
                    }
                    assert(false);
                }
            }
        }
        assert(AllocationJournal::State::mini_allocator_follows_freshest_rec(
            post.journal_tj().freshest_rec,
            post.mini_allocator,
        ));
        assert(allocation_post.tj() == post.journal_tj());
        assert(allocation_post.lsn_au_index == post.lsn_au_index_or_empty());
        assert(post.journal_tj().decodable()) by {
            assert(allocation_post.inv());
        }
        assert(post.journal_tj().disk_view.wf_addrs()) by {
            assert(allocation_post.inv());
        }
        assert(post.journal_tj().disk_view.pointer_is_upstream(
            post.journal_tj().freshest_rec,
            post.journal.snapshot.first(),
        )) by {
            assert(allocation_post.inv());
        }
        assert(post.journal_tj().disk_view.domain_tight_wrt_index(
            post.journal_tj().build_lsn_au_index_from_first(post.journal.snapshot.first()),
            post.journal_tj().freshest_rec,
        )) by {
            assert(allocation_post.inv());
        }
        assert(post.journal_tj().disk_view.bounded_inactive_lsns(
            post.journal_tj().build_lsn_au_index_from_first(post.journal.snapshot.first()),
            post.journal_tj().freshest_rec,
        )) by {
            assert(allocation_post.inv());
        }
        assert(post.visible_journal_structure());
        assert(post.journal_tj().seq_end() == cj_unmarshalled_tail(post.journal).seq_start);
        assert(cj_lsn_au_index(post.journal) == post.journal_tj().build_lsn_au_index_from_first(
            post.journal.snapshot.first(),
        )) by {
            assert(allocation_post.inv());
        }
        assert(post.clean_watermark_durable());
        assert(post.loaded_journal_structure());
    }

    #[inductive(observe_clean_aus)]
    fn observe_clean_aus_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CachedJournal::State,
    ) {
        let journal_lbl = CachedJournal::Label::ObserveCleanAUs{aus: lbl.arrow_ObserveCleanAUs_aus()};
        assert(CachedJournal::State::next(pre.journal, post.journal, journal_lbl));
        CachedJournal::State::observe_clean_aus_effect(
            pre.journal,
            post.journal,
            lbl.arrow_ObserveCleanAUs_aus(),
        );
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let target_lsn = choose |target_lsn: LSN|
            CachedJournal::State::next_by(
                pre.journal,
                post.journal,
                journal_lbl,
                CachedJournal::Step::advance_watermark(target_lsn),
            );
        let old_clean_pages = pre.clean_watermark_pages();
        let observed_pages = addresses_in_aus(lbl.arrow_ObserveCleanAUs_aus());
        CachedJournal::State::inv_next(pre.journal, post.journal, journal_lbl);
        assert(post.disk == pre.disk);
        assert(post.mini_allocator == pre.mini_allocator);
        assert(post.journal.snapshot == pre.journal.snapshot);
        assert(post.journal_disk_view() == pre.journal_disk_view());
        assert(post.journal_tj() == pre.journal_tj());
        assert(post.visible_journal_structure());
        assert(pre.disk.aus_clean_or_evictable(lbl.arrow_ObserveCleanAUs_aus())) by {
            assert(CachingDisk::State::next(
                pre.disk,
                pre.disk,
                CachingDisk::Label::ObserveCleanAUs{aus: lbl.arrow_ObserveCleanAUs_aus()},
            ));
            reveal(CachingDisk::State::next);
            reveal(CachingDisk::State::next_by);
            let disk_step = choose |step: CachingDisk::Step|
                CachingDisk::State::next_by(
                    pre.disk,
                    pre.disk,
                    CachingDisk::Label::ObserveCleanAUs{aus: lbl.arrow_ObserveCleanAUs_aus()},
                    step,
                );
            match disk_step {
                CachingDisk::Step::observe_clean_aus() => {},
                _ => { assert(false); },
            }
        };
        Self::aus_clean_or_evictable_implies_addrs_clean(
            post.disk,
            lbl.arrow_ObserveCleanAUs_aus(),
            observed_pages,
        );
        Self::addrs_clean_or_evictable_union(post.disk, old_clean_pages, observed_pages);
        assert(post.clean_watermark_pages() <= old_clean_pages + observed_pages) by {
            assert forall |addr: Address| #[trigger] post.clean_watermark_pages().contains(addr)
                implies (old_clean_pages + observed_pages).contains(addr) by {
                let record = post.journal_disk_view().entries[addr];
                if old_clean_pages.contains(addr) {
                } else {
                    assert(post.journal.clean_watermark() == target_lsn);
                    assert(pre.journal.clean_watermark() < target_lsn);
                    assert(post.journal_disk_view().entries == pre.journal_disk_view().entries);
                    assert(pre.journal_disk_view().entries.contains_key(addr));
                    assert(pre.journal_disk_view().entries[addr] == record);
                    assert(record.message_seq.seq_end <= target_lsn);
                    assert(pre.journal.clean_watermark() < record.message_seq.seq_end) by {
                        if record.message_seq.seq_end <= pre.journal.clean_watermark() {
                            assert(old_clean_pages.contains(addr));
                            assert(false);
                        }
                    }
                    let last_lsn = (record.message_seq.seq_end - 1) as nat;
                    assert(record.message_seq.contains(last_lsn));
                    assert(pre.journal.clean_watermark() <= last_lsn);
                    assert(last_lsn < target_lsn);
                    assert(pre.journal_tj().disk_view.addr_supports_lsn(addr, last_lsn));
                    pre.journal_tj().build_lsn_au_index_from_first_ensures(pre.journal.snapshot.first());
                    assert(cj_lsn_au_index(pre.journal) == pre.journal_tj().build_lsn_au_index_from_first(
                        pre.journal.snapshot.first(),
                    ));
                    pre.journal_tj().disk_view.addr_supports_lsn_consistent_with_index(
                        cj_lsn_au_index(pre.journal),
                        last_lsn,
                        addr,
                    );
                    let flushed_lsns = Set::new(|lsn: LSN| pre.journal.clean_watermark() <= lsn < target_lsn);
                    assert(flushed_lsns.contains(last_lsn));
                    assert(lbl.arrow_ObserveCleanAUs_aus()
                        == cj_lsn_au_index(pre.journal).restrict(flushed_lsns).values());
                    assert(cj_lsn_au_index(pre.journal).restrict(flushed_lsns).contains_key(last_lsn));
                    assert(cj_lsn_au_index(pre.journal).restrict(flushed_lsns)[last_lsn] == addr.au);
                    assert(lbl.arrow_ObserveCleanAUs_aus().contains(addr.au));
                    assert(observed_pages.contains(addr));
                }
            }
        };
        Self::addrs_clean_or_evictable_subset(
            post.disk,
            post.clean_watermark_pages(),
            old_clean_pages + observed_pages,
        );
        assert(post.clean_watermark_durable());
        assert(post.loaded_journal_structure());
    }

    #[inductive(discard_old)]
    fn discard_old_inductive(pre: Self, post: Self, lbl: Label, new_journal: CachedJournal::State, new_disk: CachingDisk::State) {
        let start_lsn = lbl.arrow_DiscardOld_start_lsn();
        let require_end = lbl.arrow_DiscardOld_require_end();
        let old_au_index = cj_lsn_au_index(pre.journal);
        let new_au_index = lsn_au_index_discard_up_to(old_au_index, start_lsn);
        let deallocs = old_au_index.values().difference(new_au_index.values());
        let journal_lbl = CachedJournal::Label::DiscardOld{
            start_lsn,
            require_end,
            deallocs,
        };
        assert(CachedJournal::State::next(pre.journal, post.journal, journal_lbl));
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(pre.journal, post.journal, journal_lbl, step);
        match cj_step {
            CachedJournal::Step::discard_old() => {
            },
            _ => {
                assert(false);
            },
        }
        CachingDisk::State::forget_effect(pre.disk, post.disk, deallocs);

        let discard_addrs = addresses_in_aus(deallocs);
        let keep_addrs = Set::new(|addr: Address|
            pre.i().tj().disk_view.entries.contains_key(addr)
                && new_au_index.values().contains(addr.au));
        let new_root = if pre.journal.marshalled_seq_end() <= start_lsn {
            None
        } else {
            Some(JournalRoot{
                freshest_rec: pre.journal.snapshot.freshest_rec().unwrap(),
                first: new_au_index[start_lsn],
            })
        };
        assert(post.journal == new_journal);
        assert(post.journal.snapshot == JournalSnapshot{boundary_lsn: start_lsn, root: new_root});
        assert(post.journal.status is Some);
        assert(post.journal.status.unwrap().lsn_au_index =~= new_au_index);
        assert(post.i().lsn_au_index =~= new_au_index);
        assert(post.mini_allocator == pre.mini_allocator.prune(deallocs));
        assert(post.i().mini_allocator == pre.i().mini_allocator.prune(deallocs));
        assert(post.i().journal.unmarshalled_tail == pre.i().journal.unmarshalled_tail.bounded_discard(start_lsn));

        assert_maps_equal!(post.disk.visible(), pre.disk.visible().remove_keys(discard_addrs), addr => {
            if discard_addrs.contains(addr) {
            } else {
            }
        });
        assert_maps_equal!(
            post.i().tj().disk_view.entries,
            pre.i().tj().disk_view.entries.restrict(keep_addrs),
            addr => {
                if post.i().tj().disk_view.entries.contains_key(addr) {
                    assert(post.disk.visible().contains_key(addr));
                    assert(pre.disk.visible().contains_key(addr));
                    assert(pre.i().tj().disk_view.entries.contains_key(addr));
                    assert(!discard_addrs.contains(addr));
                    assert(old_au_index.values().contains(addr.au)) by {
                        assert(pre.visible_journal_structure());
                        assert(pre.journal_tj().disk_view.domain_tight_wrt_index(
                            old_au_index,
                            pre.journal_tj().freshest_rec,
                        ));
                    }
                    assert(!deallocs.contains(addr.au));
                    if !new_au_index.values().contains(addr.au) {
                        assert(deallocs.contains(addr.au));
                        assert(false);
                    }
                    assert(new_au_index.values().contains(addr.au));
                    assert(keep_addrs.contains(addr));
                }
                if pre.i().tj().disk_view.entries.restrict(keep_addrs).contains_key(addr) {
                    assert(keep_addrs.contains(addr));
                    assert(pre.disk.visible().contains_key(addr));
                    assert(!deallocs.contains(addr.au));
                    assert(!discard_addrs.contains(addr));
                    assert(post.disk.visible().contains_key(addr));
                }
            }
        );

        let pre_first = pre.journal.snapshot.first();
        pre.journal_tj().build_lsn_au_index_from_first_ensures(pre_first);
        if pre.journal_tj().freshest_rec is Some {
            assert(pre.i().lsn_au_index.contains_key(pre.i().tj().seq_start()));
            assert(pre.i().lsn_au_index[pre.i().tj().seq_start()] == pre_first);
        }
        assert(pre.i().inv());

        if start_lsn < pre.i().tj().seq_end() {
            let sub_first = new_au_index[start_lsn];
            let sub_lsns = Set::new(|lsn: LSN| start_lsn <= lsn < pre.i().tj().seq_end());
            assert(new_au_index =~= old_au_index.restrict(sub_lsns)) by {
                assert forall |lsn: LSN| #[trigger] new_au_index.contains_key(lsn)
                    <==> old_au_index.restrict(sub_lsns).contains_key(lsn) by {
                    if new_au_index.contains_key(lsn) {
                        assert(old_au_index.contains_key(lsn));
                        assert(start_lsn <= lsn);
                        assert(pre.i().tj().seq_start() <= lsn < pre.i().tj().seq_end()) by {
                            pre.i().tj().build_lsn_au_index_from_first_ensures(pre_first);
                            reveal(TruncatedJournal::au_domain_valid);
                        }
                        assert(sub_lsns.contains(lsn));
                    }
                    if old_au_index.restrict(sub_lsns).contains_key(lsn) {
                        assert(old_au_index.contains_key(lsn));
                        assert(start_lsn <= lsn);
                        lsn_au_index_discard_up_to_ensures(old_au_index, start_lsn);
                    }
                }
                assert forall |lsn: LSN| #[trigger] new_au_index.contains_key(lsn)
                    implies new_au_index[lsn] == old_au_index.restrict(sub_lsns)[lsn] by {
                    assert(old_au_index.restrict(sub_lsns).contains_key(lsn));
                }
            }
            assert(old_au_index.contains_key(start_lsn)) by {
                pre.i().tj().build_lsn_au_index_from_first_ensures(pre_first);
                reveal(TruncatedJournal::au_domain_valid);
            }
            assert(new_au_index.contains_key(start_lsn));
            assert(old_au_index[start_lsn] == new_au_index[start_lsn]);
            let sub_dv = pre.i().tj().sub_disk_preserves_pointer_is_upstream(
                old_au_index,
                pre_first,
                start_lsn,
                pre.i().tj().freshest_rec,
                sub_first,
            );
            assert(sub_dv.entries =~= pre.i().tj().disk_view.entries.restrict(keep_addrs)) by {
                let tight = pre.i().tj().disk_view.tight_domain(new_au_index, pre.i().tj().freshest_rec);
                assert(tight =~= keep_addrs) by {
                    assert forall |addr: Address| #[trigger] tight.contains(addr)
                        <==> keep_addrs.contains(addr) by {
                        if tight.contains(addr) {
                            assert(pre.i().tj().disk_view.entries.contains_key(addr));
                            assert(new_au_index.values().contains(addr.au));
                            if au_addrs_past_pointer(pre.i().tj().freshest_rec).contains(addr) {
                                assert(false);
                            }
                            assert(keep_addrs.contains(addr));
                        }
                        if keep_addrs.contains(addr) {
                            assert(pre.i().tj().disk_view.entries.contains_key(addr));
                            assert(new_au_index.values().contains(addr.au));
                            assert(!au_addrs_past_pointer(pre.i().tj().freshest_rec).contains(addr)) by {
                                assert(pre.visible_journal_structure());
                                assert(pre.journal_tj().disk_view.domain_tight_wrt_index(
                                    old_au_index,
                                    pre.journal_tj().freshest_rec,
                                ));
                            }
                            assert(tight.contains(addr));
                        }
                    }
                }
                assert(new_au_index =~= old_au_index.restrict(sub_lsns));
            }
            assert(post.i().journal.truncated_journal.disk_view == sub_dv);
            assert(post.i().journal.truncated_journal.wf());
            assert(post.i().journal.truncated_journal.disk_view.boundary_lsn == start_lsn);
            assert(post.i().journal.truncated_journal.disk_view.entries
                <= pre.i().tj().disk_view.entries);
            assert(keep_addrs <= post.i().journal.truncated_journal.disk_view.entries.dom());
            assert(post.i().journal.truncated_journal.freshest_rec == pre.i().tj().freshest_rec);
            assert(pre.i().tj().discard_old_cond(
                start_lsn,
                keep_addrs,
                post.i().journal.truncated_journal,
            ));
            assert(keep_addrs =~= post.i().journal.truncated_journal.disk_view.entries.dom()) by {
                assert_maps_equal!(
                    post.i().journal.truncated_journal.disk_view.entries,
                    pre.i().tj().disk_view.entries.restrict(keep_addrs),
                );
            }
        } else {
            TruncatedJournal::empty_at_ensures(start_lsn);
            lsn_au_index_discard_up_to_ensures(old_au_index, start_lsn);
            assert(new_au_index =~= Map::<LSN, AU>::empty()) by {
                assert forall |lsn: LSN| #[trigger] new_au_index.contains_key(lsn)
                    implies false by {
                    assert(old_au_index.contains_key(lsn));
                    assert(start_lsn <= lsn);
                    assert(pre.i().tj().seq_start() <= lsn < pre.i().tj().seq_end()) by {
                        pre.i().tj().build_lsn_au_index_from_first_ensures(pre.journal.snapshot.first());
                        reveal(TruncatedJournal::au_domain_valid);
                    }
                    assert(false);
                }
            }
            assert(post.i().journal.truncated_journal.disk_view.entries.dom()
                =~= Set::<Address>::empty()) by {
                assert forall |addr: Address|
                    #[trigger] post.i().journal.truncated_journal.disk_view.entries.dom().contains(addr)
                    implies false by {
                    assert(post.i().journal.truncated_journal.disk_view.entries.contains_key(addr));
                    assert(pre.i().tj().disk_view.entries.contains_key(addr));
                    assert(old_au_index.values().contains(addr.au)) by {
                        assert(pre.visible_journal_structure());
                        assert(pre.journal_tj().disk_view.domain_tight_wrt_index(
                            old_au_index,
                            pre.journal_tj().freshest_rec,
                        ));
                    }
                    assert(new_au_index =~= Map::<LSN, AU>::empty());
                    assert(!new_au_index.values().contains(addr.au));
                    assert(deallocs.contains(addr.au));
                    assert(discard_addrs.contains(addr));
                    assert(!post.disk.visible().contains_key(addr));
                    assert(false);
                }
            }
            assert(post.i().journal.truncated_journal == TruncatedJournal::empty_at(start_lsn));
        }

        let alloc_lbl = AllocationJournal::Label::DiscardOld{
            start_lsn,
            require_end,
            deallocs,
        };
        assert(AllocationJournal::State::next_by(
            pre.i(),
            post.i(),
            alloc_lbl,
            AllocationJournal::Step::discard_old(post.i().journal),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
        assert(AllocationJournal::State::next(pre.i(), post.i(), alloc_lbl));
        AllocationJournal::State::inv_next(pre.i(), post.i(), alloc_lbl);
        CachedJournal::State::inv_next(pre.journal, post.journal, journal_lbl);
        CachingDisk::State::inv_next(pre.disk, post.disk, CachingDisk::Label::Forget{aus: deallocs});
        CachingDisk::State::forget_preserves_addrs_clean_or_evictable(
            pre.disk,
            post.disk,
            deallocs,
            pre.clean_watermark_pages(),
        );
        assert(post.clean_watermark_pages() <= pre.clean_watermark_pages()) by {
            assert forall |addr: Address| #[trigger] post.clean_watermark_pages().contains(addr)
                implies pre.clean_watermark_pages().contains(addr) by {
                assert(post.journal_disk_view().entries.contains_key(addr));
                assert(pre.journal_disk_view().entries.contains_key(addr)) by {
                    assert(post.disk.visible().contains_key(addr));
                    assert(pre.disk.visible().contains_key(addr));
                }
                assert(post.journal_disk_view().entries[addr] == pre.journal_disk_view().entries[addr]);
                if start_lsn <= pre.journal.clean_watermark() {
                    assert(post.journal.clean_watermark() == pre.journal.clean_watermark());
                } else {
                    assert(post.journal.clean_watermark() == start_lsn);
                    assert(post.journal_tj().disk_view.boundary_lsn == start_lsn);
                    assert(!post.clean_watermark_pages().contains(addr));
                    assert(false);
                }
            }
        };
        Self::addrs_clean_or_evictable_subset(
            post.disk,
            post.clean_watermark_pages(),
            pre.clean_watermark_pages(),
        );
        pre.mini_allocator.prune_preserves_wf(deallocs);
        assert(post.mini_allocator.wf());
        assert(post.i().inv());
        assert(post.visible_journal_structure());
        assert(post.clean_watermark_durable());
        assert(post.loaded_journal_structure());
    }

    #[inductive(mini_allocator_fill)]
    fn mini_allocator_fill_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.mini_allocator.wf());
        assert(post.journal == pre.journal);
        assert(post.disk == pre.disk);
        assert(post.journal_tj() == pre.journal_tj());
        assert(AllocationJournal::State::disk_domain_not_free(
            post.journal_tj().disk_view,
            post.mini_allocator,
        )) by {
            assert forall |addr| #[trigger] post.journal_tj().disk_view.entries.dom().contains(addr)
                implies !post.mini_allocator.can_allocate(addr) by {
                assert(pre.journal_tj().disk_view.entries.dom().contains(addr));
                assert(!pre.mini_allocator.can_allocate(addr));
                if lbl.arrow_InternalAlloc_allocs().contains(addr.au) {
                    assert(to_aus(pre.disk.visible().dom()).contains(addr.au)) by {
                        assert(pre.disk.visible().dom().contains(addr));
                        let m = Map::new(
                            |addr| pre.disk.visible().dom().contains(addr),
                            |addr: Address| addr.au,
                        );
                        assert(m.contains_key(addr));
                        assert(m[addr] == addr.au);
                        assert(m.values().contains(addr.au));
                    }
                    assert(false);
                }
            }
        }
        assert(post.visible_journal_structure());
        if post.journal.status is Some {
            assert(post.loaded_journal_structure());
        }
    }

    #[inductive(mini_allocator_prune)]
    fn mini_allocator_prune_inductive(pre: Self, post: Self, lbl: Label) {
        pre.mini_allocator.prune_preserves_wf(lbl.arrow_InternalAlloc_deallocs());
        assert(post.mini_allocator.wf());
    }

    #[inductive(internal_noop)]
    fn internal_noop_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(commit_prepared)]
    fn commit_prepared_inductive(pre: Self, post: Self, lbl: Label) {}

    pub proof fn inv_next(pre: Self, post: Self, lbl: Label)
        requires
            pre.inv(),
            CachingDiskJournal::State::next(pre, post, lbl),
        ensures
            post.inv(),
    {
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);

        let step = choose |step| CachingDiskJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskJournal::Step::caching_disk_internal(new_disk) => {
                CachingDiskJournal::State::caching_disk_internal_inductive(pre, post, lbl, new_disk);
            },
            CachingDiskJournal::Step::load_index(new_journal, reads) => {
                CachingDiskJournal::State::load_index_inductive(pre, post, lbl, new_journal, reads);
            },
            CachingDiskJournal::Step::read_for_recovery(reads) => {
                CachingDiskJournal::State::read_for_recovery_inductive(pre, post, lbl, reads);
            },
            CachingDiskJournal::Step::freeze_for_commit(reads) => {
                CachingDiskJournal::State::freeze_for_commit_inductive(pre, post, lbl, reads);
            },
            CachingDiskJournal::Step::query_end_lsn() => {
                CachingDiskJournal::State::query_end_lsn_inductive(pre, post, lbl);
            },
            CachingDiskJournal::Step::put(new_journal) => {
                CachingDiskJournal::State::put_inductive(pre, post, lbl, new_journal);
            },
            CachingDiskJournal::Step::journal_marshal(new_journal, new_disk, addr, writes) => {
                CachingDiskJournal::State::journal_marshal_inductive(
                    pre, post, lbl, new_journal, new_disk, addr, writes,
                );
            },
            CachingDiskJournal::Step::observe_clean_aus(new_journal) => {
                CachingDiskJournal::State::observe_clean_aus_inductive(pre, post, lbl, new_journal);
            },
            CachingDiskJournal::Step::commit_prepared() => {
                CachingDiskJournal::State::commit_prepared_inductive(pre, post, lbl);
            },
            CachingDiskJournal::Step::discard_old(new_journal, new_disk) => {
                CachingDiskJournal::State::discard_old_inductive(pre, post, lbl, new_journal, new_disk);
            },
            CachingDiskJournal::Step::mini_allocator_fill() => {
                CachingDiskJournal::State::mini_allocator_fill_inductive(pre, post, lbl);
            },
            CachingDiskJournal::Step::mini_allocator_prune() => {
                CachingDiskJournal::State::mini_allocator_prune_inductive(pre, post, lbl);
            },
            CachingDiskJournal::Step::internal_noop() => {
                CachingDiskJournal::State::internal_noop_inductive(pre, post, lbl);
            },
            _ => {
                assert(post.inv());
            },
        }
    }

}}

impl CachingDiskJournal::State {
    pub open spec fn disk_from_persistent(persistent: Map<Address, RawPage>) -> CachingDisk::State {
        CachingDisk::State{
            cache: Map::empty(),
            persistent,
            status: Map::empty(),
        }
    }

    pub open spec fn load_from_persistent(
        snapshot: JournalSnapshot,
        persistent: Map<Address, RawPage>,
    ) -> Self {
        Self{
            journal: CachedJournal::State{
                snapshot,
                status: Option::None,
            },
            disk: Self::disk_from_persistent(persistent),
            mini_allocator: MiniAllocator::empty(),
        }
    }

    pub proof fn load_from_persistent_accessible_aus(
        snapshot: JournalSnapshot,
        persistent: Map<Address, RawPage>,
    )
        requires
            Self::load_from_persistent(snapshot, persistent).inv(),
        ensures
            Self::load_from_persistent(snapshot, persistent).accessible_aus()
                <= to_aus(persistent.dom()),
    {
        let loaded = Self::load_from_persistent(snapshot, persistent);
        loaded.journal_disk_aus_match_index_values();
        assert(loaded.mini_allocator.all_aus() =~= Set::<AU>::empty());
        assert(loaded.disk.visible().dom() == persistent.dom());
        assert forall |au: AU| #[trigger] Self::load_from_persistent(
            snapshot,
            persistent,
        ).accessible_aus().contains(au)
            implies to_aus(persistent.dom()).contains(au) by {
            if loaded.mini_allocator.all_aus().contains(au) {
                assert(false);
            } else {
                assert(to_aus(loaded.journal_disk_view().entries.dom()).contains(au));
                assert(loaded.journal_disk_view().entries.dom() == persistent.dom());
            }
        }
    }

    pub open spec fn visible_records(self) -> Map<Address, JournalRecord> {
        to_journal_records(self.disk.visible())
    }

    pub open spec fn journal_disk_view(self) -> DiskView {
        DiskView{
            boundary_lsn: cj_boundary_lsn(self.journal),
            entries: self.visible_records(),
        }
    }

    pub open spec fn journal_tj(self) -> TruncatedJournal {
        TruncatedJournal{
            freshest_rec: cj_freshest_rec(self.journal),
            disk_view: self.journal_disk_view(),
        }
    }

    pub open spec fn accessible_aus(self) -> Set<AU> {
        self.lsn_au_index_or_empty().values() + self.mini_allocator.all_aus()
    }

    pub open spec fn clean_watermark_aus(self) -> Set<AU> {
        if self.journal.status is Some {
            let clean_lsns = Set::new(|lsn: LSN|
                self.journal.snapshot.boundary_lsn <= lsn && lsn < self.journal.clean_watermark());
            cj_lsn_au_index(self.journal).restrict(clean_lsns).values()
        } else {
            to_aus(self.journal_disk_view().entries.dom())
        }
    }

    pub open spec fn clean_watermark_pages(self) -> Set<Address> {
        if self.journal.status is Some {
            Set::new(|addr: Address| {
                &&& self.journal_disk_view().entries.contains_key(addr)
                &&& self.journal_disk_view().boundary_lsn
                    < self.journal_disk_view().entries[addr].message_seq.seq_end
                &&& self.journal_disk_view().entries[addr].message_seq.seq_end
                    <= self.journal.clean_watermark()
            })
        } else {
            self.journal_disk_view().entries.dom()
        }
    }

    pub open spec fn clean_watermark_disk_view(self) -> DiskView {
        DiskView{
            boundary_lsn: self.journal_disk_view().boundary_lsn,
            entries: self.journal_disk_view().entries.restrict(self.clean_watermark_pages()),
        }
    }

    pub open spec fn frozen_domain(self, snapshot: JournalSnapshot) -> Set<Address> {
        let frozen_index = self.lsn_au_index_or_empty().restrict(self.frozen_lsns(snapshot));
        self.journal_tj().disk_view.tight_domain(
            frozen_index,
            snapshot.freshest_rec(),
        )
    }

    pub open spec fn frozen_domain_old(self, snapshot: JournalSnapshot) -> Set<Address> {
        let frozen_index = self.lsn_au_index_or_empty().restrict(self.frozen_lsns(snapshot));
        self.journal_tj().disk_view.tight_domain(
            frozen_index,
            snapshot.freshest_rec(),
        )
    }

    pub open spec fn clean_watermark_durable(self) -> bool {
        self.disk.addrs_clean_or_evictable(self.clean_watermark_pages())
    }

    pub proof fn addrs_clean_or_evictable_subset(disk: CachingDisk::State, small: Set<Address>, big: Set<Address>)
        requires
            disk.addrs_clean_or_evictable(big),
            small <= big,
        ensures
            disk.addrs_clean_or_evictable(small),
    {
        assert forall |addr: Address| #[trigger] disk.cache.contains_key(addr) && small.contains(addr)
            implies {
                &&& disk.status.contains_key(addr)
                &&& disk.status[addr] == PageStatus::Clean
            }
        by {
            assert(big.contains(addr));
            assert(disk.addrs_clean_or_evictable(big));
        };
    }

    pub proof fn addrs_clean_or_evictable_union(disk: CachingDisk::State, a: Set<Address>, b: Set<Address>)
        requires
            disk.addrs_clean_or_evictable(a),
            disk.addrs_clean_or_evictable(b),
        ensures
            disk.addrs_clean_or_evictable(a + b),
    {
        assert forall |addr: Address| #[trigger] disk.cache.contains_key(addr) && (a + b).contains(addr)
            implies {
                &&& disk.status.contains_key(addr)
                &&& disk.status[addr] == PageStatus::Clean
            }
        by {
            if a.contains(addr) {
                assert(disk.addrs_clean_or_evictable(a));
            } else {
                assert(b.contains(addr));
                assert(disk.addrs_clean_or_evictable(b));
            }
        };
    }

    pub proof fn clean_watermark_disk_view_is_sub_disk(self)
        requires
            self.inv(),
        ensures
            self.clean_watermark_disk_view().is_sub_disk(self.journal_disk_view()),
    {
        let clean = self.clean_watermark_disk_view();
        let full = self.journal_disk_view();
        assert(clean.entries <= full.entries) by {
            assert forall |addr: Address| #[trigger] clean.entries.contains_key(addr)
                implies full.entries.contains_key(addr) && clean.entries[addr] == full.entries[addr] by {
                assert(self.clean_watermark_pages().contains(addr));
            }
        }
    }

    pub proof fn clean_watermark_disk_view_wf(self)
        requires
            self.inv(),
        ensures
            self.clean_watermark_disk_view().wf(),
            self.clean_watermark_disk_view().acyclic(),
            self.clean_watermark_disk_view().is_sub_disk(self.journal_disk_view()),
    {
        let full = self.journal_disk_view();
        let clean = self.clean_watermark_disk_view();
        self.clean_watermark_disk_view_is_sub_disk();
        assert(clean.entries <= full.entries);
        assert(full.wf());
        assert(full.acyclic());

        assert(clean.entries_wf()) by {
            assert forall |addr: Address| #[trigger] clean.entries.contains_key(addr)
                implies clean.entries[addr].wf() by {
                assert(full.entries.contains_key(addr));
                assert(clean.entries[addr] == full.entries[addr]);
                assert(full.entries_wf());
            }
        }

        assert(clean.nondangling_pointers()) by {
            assert forall |addr: Address| #[trigger] clean.entries.contains_key(addr)
                implies clean.is_nondangling_pointer(
                    clean.entries[addr].cropped_prior(clean.boundary_lsn),
                ) by {
                let prior = clean.entries[addr].cropped_prior(clean.boundary_lsn);
                if prior is Some {
                    let prior_addr = prior.unwrap();
                    assert(full.entries.contains_key(addr));
                    assert(clean.entries[addr] == full.entries[addr]);
                    assert(full.nondangling_pointers());
                    assert(full.entries.contains_key(prior_addr));
                    assert(full.this_block_can_concat(addr));
                    assert(full.entries[prior_addr].message_seq.can_concat(
                        full.entries[addr].message_seq,
                    ));
                    assert(full.entries[addr].message_seq.can_follow(
                        full.entries[prior_addr].message_seq.seq_end,
                    ));
                    assert(full.entries[addr].message_seq.seq_start
                        == full.entries[prior_addr].message_seq.seq_end);
                    assert(clean.boundary_lsn < clean.entries[addr].message_seq.seq_start);
                    assert(full.boundary_lsn < full.entries[prior_addr].message_seq.seq_end);
                    assert(full.entries[prior_addr].message_seq.seq_end
                        <= full.entries[addr].message_seq.seq_end);
                    if self.journal.status is Some {
                        assert(self.clean_watermark_pages().contains(addr));
                        assert(full.entries[addr].message_seq.seq_end
                            <= self.journal.clean_watermark());
                        assert(full.entries[prior_addr].message_seq.seq_end
                            <= self.journal.clean_watermark());
                    }
                    assert(self.clean_watermark_pages().contains(prior_addr));
                    assert(clean.entries.contains_key(prior_addr));
                }
            }
        }

        assert(clean.blocks_can_concat()) by {
            assert forall |addr: Address| #[trigger] clean.entries.contains_key(addr)
                implies clean.this_block_can_concat(addr) by {
                let prior = clean.entries[addr].cropped_prior(clean.boundary_lsn);
                if prior is Some {
                    let prior_addr = prior.unwrap();
                    assert(full.entries.contains_key(addr));
                    assert(clean.entries[addr] == full.entries[addr]);
                    assert(clean.entries.contains_key(prior_addr));
                    assert(clean.entries[prior_addr] == full.entries[prior_addr]);
                    assert(full.this_block_can_concat(addr));
                }
            }
        }

        assert(clean.blocks_each_have_link()) by {
            assert forall |addr: Address| #[trigger] clean.entries.contains_key(addr)
                implies clean.entries[addr].has_link(clean.boundary_lsn) by {
                assert(full.entries.contains_key(addr));
                assert(clean.entries[addr] == full.entries[addr]);
                assert(full.blocks_each_have_link());
            }
        }

        assert(clean.wf());
        assert(clean.valid_ranking(full.the_ranking())) by {
            assert(clean.entries.dom().subset_of(full.the_ranking().dom()));
            assert forall |addr: Address| #[trigger] clean.entries.contains_key(addr)
                && clean.entries[addr].cropped_prior(clean.boundary_lsn) is Some
                implies full.the_ranking()[
                    clean.entries[addr].cropped_prior(clean.boundary_lsn).unwrap()
                ] < full.the_ranking()[addr] by {
                let prior = clean.entries[addr].cropped_prior(clean.boundary_lsn);
                assert(full.entries.contains_key(addr));
                assert(clean.entries[addr] == full.entries[addr]);
                assert(full.valid_ranking(full.the_ranking()));
            }
        }
        assert(clean.acyclic());
    }

    pub proof fn clean_watermark_persistent_records_eq(self)
        requires
            self.inv(),
        ensures
            (DiskView{
                boundary_lsn: self.journal_disk_view().boundary_lsn,
                entries: to_journal_records(self.disk.persistent.restrict(self.clean_watermark_pages())),
            }).entries
                == self.clean_watermark_disk_view().entries,
    {
        let addrs = self.clean_watermark_pages();
        self.clean_watermark_persistent_visible_eq(addrs);
        assert_maps_equal!(
            to_journal_records(self.disk.persistent.restrict(addrs)),
            self.clean_watermark_disk_view().entries,
            addr => {
                if to_journal_records(self.disk.persistent.restrict(addrs)).contains_key(addr) {
                    assert(self.disk.persistent.restrict(addrs).contains_key(addr));
                    assert(addrs.contains(addr));
                    assert(self.disk.visible().restrict(addrs).contains_key(addr));
                    assert(self.disk.persistent.restrict(addrs)[addr]
                        == self.disk.visible().restrict(addrs)[addr]);
                    assert(self.journal_disk_view().entries.contains_key(addr));
                    assert(self.clean_watermark_disk_view().entries.contains_key(addr));
                    assert(to_journal_records(self.disk.persistent.restrict(addrs))[addr]
                        == self.journal_disk_view().entries[addr]);
                }
                if self.clean_watermark_disk_view().entries.contains_key(addr) {
                    assert(addrs.contains(addr));
                    assert(self.journal_disk_view().entries.contains_key(addr));
                    assert(self.disk.visible().contains_key(addr));
                    assert(self.disk.visible().restrict(addrs).contains_key(addr));
                    assert(self.disk.persistent.restrict(addrs).contains_key(addr));
                    assert(self.disk.persistent.restrict(addrs)[addr]
                        == self.disk.visible().restrict(addrs)[addr]);
                    assert(to_journal_records(self.disk.persistent.restrict(addrs)).contains_key(addr));
                    assert(to_journal_records(self.disk.persistent.restrict(addrs))[addr]
                        == self.clean_watermark_disk_view().entries[addr]);
                }
            }
        );
    }

    pub proof fn clean_watermark_persistent_visible_eq(self, addrs: Set<Address>)
        requires
            self.inv(),
            addrs <= self.clean_watermark_pages(),
        ensures
            self.disk.persistent.restrict(addrs) == self.disk.visible().restrict(addrs),
    {
        assert_maps_equal!(
            self.disk.persistent.restrict(addrs),
            self.disk.visible().restrict(addrs),
            addr => {
                if addrs.contains(addr) {
                    assert(self.clean_watermark_pages().contains(addr));
                    if self.disk.cache.contains_key(addr) {
                        assert(self.disk.addrs_clean_or_evictable(self.clean_watermark_pages()));
                        assert(self.disk.status.contains_key(addr));
                        assert(self.disk.status[addr] == PageStatus::Clean);
                        assert(self.disk.persistent.contains_key(addr));
                        assert(self.disk.persistent[addr] == self.disk.cache[addr]);
                    }
                }
            }
        );
    }

    pub proof fn clean_watermark_record_eq(self, addr: Address)
        requires
            self.inv(),
            self.clean_watermark_pages().contains(addr),
        ensures
            self.disk.persistent.contains_key(addr),
            to_journal_records(self.disk.persistent).contains_key(addr),
            to_journal_records(self.disk.persistent)[addr] == self.journal_disk_view().entries[addr],
    {
        let addrs = Set::new(|a: Address| a == addr);
        assert(addrs <= self.clean_watermark_pages()) by {
            assert forall |a: Address| #[trigger] addrs.contains(a)
                implies self.clean_watermark_pages().contains(a) by {
                assert(a == addr);
            }
        }
        self.clean_watermark_persistent_visible_eq(addrs);
        assert(self.disk.persistent.restrict(addrs) == self.disk.visible().restrict(addrs));
        assert(self.disk.persistent.restrict(addrs).contains_key(addr));
        assert(self.disk.visible().restrict(addrs).contains_key(addr));
        assert(self.disk.persistent.contains_key(addr));
        assert(self.disk.visible().contains_key(addr));
        assert(self.disk.persistent[addr] == self.disk.visible()[addr]);
        assert(to_journal_records(self.disk.persistent).contains_key(addr));
        assert(to_journal_records(self.disk.persistent)[addr] == raw_page_to_record(self.disk.persistent[addr]));
        assert(self.journal_disk_view().entries.contains_key(addr));
        assert(self.journal_disk_view().entries[addr] == raw_page_to_record(self.disk.visible()[addr]));
    }

    pub proof fn frozen_tight_domain_clean_watermark(
        self,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.inv(),
            self.frozen_snapshot_valid(frozen, seq_end),
            frozen.freshest_rec() is Some ==> seq_end <= self.journal.clean_watermark(),
        ensures
            self.frozen_tj(frozen).build_tight().disk_view.entries.dom()
                <= self.clean_watermark_pages(),
    {
        let frozen_tj = self.frozen_tj(frozen);
        let tight_tj = frozen_tj.build_tight();
        if frozen.freshest_rec() is Some {
            let root = frozen.freshest_rec().unwrap();
            assert(seq_end == self.frozen_seq_end(frozen));
            self.frozen_snapshot_valid_image(frozen, seq_end);
            assert(frozen_tj.decodable());
            assert(frozen_tj.disk_view.acyclic());
            assert(frozen_tj.disk_view.upstream(root));
            assert(tight_tj.disk_view.entries <= frozen_tj.disk_view.entries) by {
                frozen_tj.disk_view.build_tight_ensures(frozen_tj.freshest_rec);
            }
            assert forall |addr: Address| #[trigger] tight_tj.disk_view.entries.dom().contains(addr)
                implies self.clean_watermark_pages().contains(addr) by {
                assert(tight_tj.disk_view.entries.contains_key(addr));
                assert(frozen_tj.disk_view.build_tight(frozen_tj.freshest_rec).entries.contains_key(addr));
                frozen_tj.disk_view.build_tight_entry_active_bounded(frozen_tj.freshest_rec, addr);
                assert(frozen_tj.disk_view.boundary_lsn
                    < tight_tj.disk_view.entries[addr].message_seq.seq_end);
                assert(tight_tj.disk_view.entries[addr].message_seq.seq_end
                    <= frozen_tj.seq_end());
                assert(frozen_tj.seq_end() == seq_end);
                assert(seq_end <= self.journal.clean_watermark());
                assert(frozen_tj.disk_view.entries.contains_key(addr));
                assert(self.journal_disk_view().entries.contains_key(addr));
                assert(frozen_tj.disk_view.entries[addr]
                    == self.journal_disk_view().entries[addr]);
            }
        } else {
            assert(tight_tj.disk_view.entries.dom() =~= Set::<Address>::empty()) by {
                assert forall |addr: Address| #[trigger] tight_tj.disk_view.entries.dom().contains(addr)
                    implies false by {
                    assert(tight_tj.disk_view.entries.contains_key(addr));
                }
            }
        }
    }

    pub proof fn frozen_tight_subdisk_clean_watermark(
        self,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.inv(),
            self.frozen_snapshot_valid(frozen, seq_end),
            frozen.freshest_rec() is Some ==> seq_end <= self.journal.clean_watermark(),
        ensures
            self.frozen_tj(frozen).build_tight().disk_view.is_sub_disk_with_newer_lsn(
                self.clean_watermark_disk_view(),
            ),
    {
        let frozen_tj = self.frozen_tj(frozen);
        let tight_tj = frozen_tj.build_tight();
        self.frozen_snapshot_valid_image(frozen, seq_end);
        self.frozen_tight_domain_clean_watermark(frozen, seq_end);
        frozen_tj.disk_view.build_tight_ensures(frozen_tj.freshest_rec);
        assert(tight_tj.disk_view.entries <= frozen_tj.disk_view.entries);
        assert(tight_tj.disk_view.entries <= self.journal_disk_view().entries) by {
            assert forall |addr: Address| #[trigger] tight_tj.disk_view.entries.contains_key(addr)
                implies self.journal_disk_view().entries.contains_key(addr)
                    && tight_tj.disk_view.entries[addr] == self.journal_disk_view().entries[addr] by {
                assert(frozen_tj.disk_view.entries.contains_key(addr));
                assert(frozen_tj.disk_view.entries[addr] == tight_tj.disk_view.entries[addr]);
                assert(frozen_tj.disk_view.entries <= self.journal_disk_view().entries);
            }
        }
        assert(tight_tj.disk_view.entries <= self.clean_watermark_disk_view().entries) by {
            assert forall |addr: Address| #[trigger] tight_tj.disk_view.entries.contains_key(addr)
                implies self.clean_watermark_disk_view().entries.contains_key(addr)
                    && tight_tj.disk_view.entries[addr]
                        == self.clean_watermark_disk_view().entries[addr] by {
                assert(self.clean_watermark_pages().contains(addr));
                assert(self.journal_disk_view().entries.contains_key(addr));
                assert(tight_tj.disk_view.entries[addr] == self.journal_disk_view().entries[addr]);
            }
        }
    }

    pub proof fn aus_clean_or_evictable_implies_addrs_clean(
        disk: CachingDisk::State,
        aus: Set<AU>,
        addrs: Set<Address>,
    )
        requires
            disk.aus_clean_or_evictable(aus),
            addrs <= addresses_in_aus(aus),
        ensures
            disk.addrs_clean_or_evictable(addrs),
    {
        assert forall |addr: Address| #[trigger] disk.cache.contains_key(addr) && addrs.contains(addr)
            implies {
                &&& disk.status.contains_key(addr)
                &&& disk.status[addr] == PageStatus::Clean
            }
        by {
            assert(addresses_in_aus(aus).contains(addr));
            assert(aus.contains(addr.au));
            assert(disk.aus_clean_or_evictable(aus));
        };
    }

    pub proof fn lsn_au_index_restrict_values_subset(index: LsnAUIndex, keys: Set<LSN>)
        ensures
            index.restrict(keys).values() <= index.values(),
    {
        assert forall |au: AU| #[trigger] index.restrict(keys).values().contains(au)
            implies index.values().contains(au) by {
            let lsn = choose |lsn: LSN|
                index.restrict(keys).contains_key(lsn) && index.restrict(keys)[lsn] == au;
            assert(index.contains_key(lsn));
            assert(index[lsn] == au);
        };
    }

    pub proof fn lsn_au_index_append_record_values_subset(
        index: LsnAUIndex,
        msgs: MsgHistory,
        au: AU,
    )
        requires
            msgs.wf(),
            msgs.seq_start < msgs.seq_end,
        ensures
            lsn_au_index_append_record(index, msgs, au).values()
                <= index.values().insert(au),
    {
        let out = lsn_au_index_append_record(index, msgs, au);
        let update = singleton_index(msgs.seq_start, msgs.seq_end, au);
        assert forall |v: AU| #[trigger] out.values().contains(v)
            implies index.values().insert(au).contains(v) by {
            let lsn = choose |lsn: LSN| out.contains_key(lsn) && out[lsn] == v;
            if update.contains_key(lsn) {
                assert(update[lsn] == au);
                assert(out[lsn] == au);
            } else {
                assert(index.contains_key(lsn));
                assert(out[lsn] == index[lsn]);
                assert(index.values().contains(v));
            }
        }
    }

    pub proof fn internal_preserves_accessible_aus(pre: Self, post: Self)
        requires
            pre.inv(),
            CachingDiskJournal::State::next(pre, post, CachingDiskJournal::Label::Internal),
        ensures
            post.accessible_aus() <= pre.accessible_aus(),
    {
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let lbl = CachingDiskJournal::Label::Internal;
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskJournal::Step::caching_disk_internal(new_disk) => {
                assert(CachingDiskJournal::State::caching_disk_internal(pre, post, lbl, new_disk)) by {
                    reveal(CachingDiskJournal::State::caching_disk_internal);
                }
                CachingDisk::State::internal_visible_unchanged(pre.disk, post.disk);
                assert(post.journal == pre.journal);
                assert(post.mini_allocator == pre.mini_allocator);
                assert(post.journal_disk_view().entries.dom() == pre.journal_disk_view().entries.dom());
            },
            CachingDiskJournal::Step::journal_marshal(new_journal, new_disk, addr, writes) => {
                assert(CachingDiskJournal::State::journal_marshal(pre, post, lbl, new_journal, new_disk, addr, writes)) by {
                    reveal(CachingDiskJournal::State::journal_marshal);
                }
                CachingDisk::State::access_visible_effect(pre.disk, post.disk, Map::empty(), writes);
                assert(pre.mini_allocator.can_allocate(addr));
                mini_allocator_allocate_preserves_all_aus(pre.mini_allocator, addr);
                assert(post.mini_allocator.all_aus() == pre.mini_allocator.all_aus()) by {
                    assert(pre.mini_allocator.allocate(addr).all_aus() == pre.mini_allocator.all_aus());
                    assert forall |au: AU| #[trigger] post.mini_allocator.all_aus().contains(au)
                        <==> pre.mini_allocator.all_aus().contains(au) by { }
                }
                assert forall |au: AU| #[trigger] post.accessible_aus().contains(au)
                    implies pre.accessible_aus().contains(au) by {
                    if post.mini_allocator.all_aus().contains(au) {
                        assert(pre.mini_allocator.all_aus().contains(au));
                    } else {
                        reveal(CachedJournal::State::next);
                        reveal(CachedJournal::State::next_by);
                        let journal_lbl = CachedJournal::Label::JournalMarshal{
                            writes: to_journal_records(writes),
                        };
                        let journal_step = choose |step: CachedJournal::Step|
                            CachedJournal::State::next_by(pre.journal, post.journal, journal_lbl, step);
                        match journal_step {
                            CachedJournal::Step::internal_journal_marshal(cut, marshalled_addr) => {
                                reveal(CachedJournal::State::internal_journal_marshal);
                                let marshalled_msgs =
                                    pre.journal.status.unwrap().unmarshalled_tail.discard_recent(cut);
                                Self::lsn_au_index_append_record_values_subset(
                                    cj_lsn_au_index(pre.journal),
                                    marshalled_msgs,
                                    marshalled_addr.au,
                                );
                                assert(to_journal_records(writes).dom() == writes.dom()) by {
                                    assert_maps_equal!(to_journal_records(writes), to_journal_records(writes));
                                    assert forall |a: Address| #[trigger] to_journal_records(writes).contains_key(a)
                                        <==> writes.contains_key(a) by { }
                                }
                                assert(to_journal_records(writes).contains_key(marshalled_addr));
                                assert(writes.dom().contains(marshalled_addr));
                                assert(writes.dom().contains(addr));
                                assert(post.lsn_au_index_or_empty().values()
                                    <= cj_lsn_au_index(pre.journal).values().insert(marshalled_addr.au));
                                assert(marshalled_addr == addr);
                                assert(au == addr.au || cj_lsn_au_index(pre.journal).values().contains(au));
                            },
                            _ => { assert(false); },
                        }
                        if au == addr.au {
                            assert(pre.mini_allocator.can_allocate(addr));
                            assert(pre.mini_allocator.all_aus().contains(au));
                        } else {
                            assert(cj_lsn_au_index(pre.journal).values().contains(au));
                            assert(pre.accessible_aus().contains(au));
                        }
                    }
                }
            },
            CachingDiskJournal::Step::internal_noop() => {
                assert(CachingDiskJournal::State::internal_noop(pre, post, lbl)) by {
                    reveal(CachingDiskJournal::State::internal_noop);
                }
                assert(post == pre);
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn loaded_index_values_accessible(self)
        requires
            self.inv(),
            self.journal.status is Some,
        ensures
            cj_lsn_au_index(self.journal).values() <= self.accessible_aus(),
    {
        let index = cj_lsn_au_index(self.journal);
        assert forall |au: AU| #[trigger] index.values().contains(au)
            implies self.accessible_aus().contains(au) by {
            assert(self.lsn_au_index_or_empty() == index);
        }
    }

    pub proof fn lsn_au_index_or_empty_matches_full(self)
        requires
            self.inv(),
        ensures
            self.lsn_au_index_or_empty()
                == self.journal_tj().build_lsn_au_index_from_first(self.journal.snapshot.first()),
    {
        if self.journal.status is Some {
            assert(self.loaded_journal_structure());
        }
    }

    pub proof fn journal_disk_aus_match_index_values(self)
        requires
            self.inv(),
        ensures
            to_aus(self.journal_disk_view().entries.dom()) =~= self.lsn_au_index_or_empty().values(),
            to_aus(self.journal_disk_view().entries.dom()) <= self.accessible_aus(),
            self.lsn_au_index_or_empty().values() <= to_aus(self.journal_disk_view().entries.dom()),
    {
        let tj = self.journal_tj();
        let index = self.lsn_au_index_or_empty();
        self.lsn_au_index_or_empty_matches_full();
        tj.build_lsn_au_index_from_first_ensures(self.journal.snapshot.first());
        assert(tj.disk_view.index_keys_exist_valid_entries(index));
        assert(tj.disk_view.domain_tight_wrt_index(index, tj.freshest_rec));

        assert(to_aus(self.journal_disk_view().entries.dom()) <= index.values()) by {
            assert forall |au: AU| #[trigger] to_aus(self.journal_disk_view().entries.dom()).contains(au)
                implies index.values().contains(au) by {
                let addr = choose |addr: Address|
                    self.journal_disk_view().entries.dom().contains(addr) && addr.au == au;
                assert(tj.disk_view.entries.dom().contains(addr));
                assert(index.values().contains(addr.au));
            }
        };
        assert(index.values() <= to_aus(self.journal_disk_view().entries.dom())) by {
            assert forall |au: AU| #[trigger] index.values().contains(au)
                implies to_aus(self.journal_disk_view().entries.dom()).contains(au) by {
                let lsn = choose |lsn: LSN| index.contains_key(lsn) && index[lsn] == au;
                let addr = tj.disk_view.instantiate_index_keys_exist_valid_entries(index, lsn);
                assert(tj.disk_view.addr_supports_lsn(addr, lsn));
                assert(tj.disk_view.entries.dom().contains(addr));
                crate::disk::GenericDisk_v::to_aus_domain(tj.disk_view.entries.dom());
            }
        };
        assert(to_aus(self.journal_disk_view().entries.dom()) <= self.accessible_aus()) by {
            assert(index.values() <= self.accessible_aus());
        }
    }

    pub proof fn discard_old_accessible_aus(
        pre: Self,
        post: Self,
        start_lsn: LSN,
        require_end: LSN,
    )
        requires
            pre.inv(),
            CachingDiskJournal::State::next(
                pre,
                post,
                CachingDiskJournal::Label::DiscardOld{start_lsn, require_end},
            ),
        ensures
            ({
                let old_au_index = cj_lsn_au_index(pre.journal);
                let new_au_index = lsn_au_index_discard_up_to(old_au_index, start_lsn);
                let deallocs = old_au_index.values().difference(new_au_index.values());
                &&& deallocs <= pre.accessible_aus()
                &&& post.accessible_aus() <= pre.accessible_aus()
                &&& deallocs.disjoint(post.accessible_aus())
            }),
    {
        let lbl = CachingDiskJournal::Label::DiscardOld{start_lsn, require_end};
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskJournal::Step::discard_old(new_journal, new_disk) => {
                assert(CachingDiskJournal::State::discard_old(pre, post, lbl, new_journal, new_disk)) by {
                    reveal(CachingDiskJournal::State::discard_old);
                }
                let old_au_index = cj_lsn_au_index(pre.journal);
                let new_au_index = lsn_au_index_discard_up_to(old_au_index, start_lsn);
                let deallocs = old_au_index.values().difference(new_au_index.values());
                let journal_lbl = CachedJournal::Label::DiscardOld{start_lsn, require_end, deallocs};
                assert(pre.journal.status is Some) by {
                    reveal(CachedJournal::State::next);
                    reveal(CachedJournal::State::next_by);
                    let journal_step = choose |step: CachedJournal::Step|
                        CachedJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
                    match journal_step {
                        CachedJournal::Step::discard_old() => {},
                        _ => { assert(false); },
                    }
                }
                reveal(CachedJournal::State::next);
                reveal(CachedJournal::State::next_by);
                let journal_step = choose |step: CachedJournal::Step|
                    CachedJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
                match journal_step {
                    CachedJournal::Step::discard_old() => {
                        reveal(CachedJournal::State::discard_old);
                    },
                    _ => { assert(false); },
                }
                assert(post.lsn_au_index_or_empty() == new_au_index);
                pre.loaded_index_values_accessible();
                assert(deallocs <= pre.accessible_aus());
                CachingDisk::State::forget_effect(pre.disk, post.disk, deallocs);
                pre.mini_allocator.prune_preserves_wf(deallocs);
                assert(post.mini_allocator.all_aus()
                    == pre.mini_allocator.all_aus().difference(deallocs));
                assert forall |au: AU| #[trigger] post.accessible_aus().contains(au)
                    implies pre.accessible_aus().contains(au) by {
                    if post.mini_allocator.all_aus().contains(au) {
                        assert(pre.mini_allocator.all_aus().contains(au));
                    } else {
                        lsn_au_index_discard_up_to_ensures(old_au_index, start_lsn);
                        assert(post.lsn_au_index_or_empty().values().contains(au));
                        assert(new_au_index.values().contains(au));
                        assert(old_au_index.values().contains(au));
                        assert(pre.accessible_aus().contains(au));
                    }
                }
                assert(deallocs.disjoint(post.accessible_aus())) by {
                    assert forall |au: AU| #[trigger] deallocs.contains(au)
                        implies !post.accessible_aus().contains(au) by {
                        if post.accessible_aus().contains(au) {
                            if post.mini_allocator.all_aus().contains(au) {
                                assert(!post.mini_allocator.all_aus().contains(au));
                            } else {
                                assert(post.lsn_au_index_or_empty().values().contains(au));
                                assert(new_au_index.values().contains(au));
                                assert(!new_au_index.values().contains(au));
                                assert(false);
                            }
                        }
                    }
                };
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn internal_alloc_accessible_aus(
        pre: Self,
        post: Self,
        allocs: Set<AU>,
        deallocs: Set<AU>,
        prune_aus: Set<AU>,
    )
        requires
            pre.inv(),
            CachingDiskJournal::State::next(
                pre,
                post,
                CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus},
            ),
        ensures
            post.accessible_aus() <= pre.accessible_aus() + allocs,
            deallocs <= pre.accessible_aus(),
    {
        let lbl = CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus};
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskJournal::Step::mini_allocator_fill() => {
                assert(CachingDiskJournal::State::mini_allocator_fill(pre, post, lbl)) by {
                    reveal(CachingDiskJournal::State::mini_allocator_fill);
                }
                assert(deallocs == Set::<AU>::empty());
                mini_allocator_add_aus_preserves_all_aus(pre.mini_allocator, allocs);
                assert(post.mini_allocator.all_aus() == pre.mini_allocator.all_aus() + allocs);
                assert(post.journal == pre.journal);
                assert(post.disk == pre.disk);
                assert(post.journal_disk_view() == pre.journal_disk_view());
                assert forall |au: AU| #[trigger] post.accessible_aus().contains(au)
                    implies (pre.accessible_aus() + allocs).contains(au) by {
                    if post.mini_allocator.all_aus().contains(au) {
                        assert((pre.mini_allocator.all_aus() + allocs).contains(au));
                    } else {
                        assert(post.lsn_au_index_or_empty() == pre.lsn_au_index_or_empty());
                        assert(pre.accessible_aus().contains(au));
                    }
                }
            },
            CachingDiskJournal::Step::mini_allocator_prune() => {
                assert(CachingDiskJournal::State::mini_allocator_prune(pre, post, lbl)) by {
                    reveal(CachingDiskJournal::State::mini_allocator_prune);
                }
                assert(allocs == Set::<AU>::empty());
                pre.mini_allocator.prune_preserves_wf(prune_aus);
                assert(post.mini_allocator.all_aus()
                    == pre.mini_allocator.all_aus().difference(prune_aus));
                assert(deallocs <= pre.accessible_aus()) by {
                    assert forall |au: AU| #[trigger] deallocs.contains(au)
                        implies pre.accessible_aus().contains(au) by {
                        assert(prune_aus.contains(au));
                        assert(pre.mini_allocator.can_remove(au));
                        assert(pre.mini_allocator.all_aus().contains(au));
                    }
                };
                assert(post.journal == pre.journal);
                assert(post.disk == pre.disk);
                assert(post.journal_disk_view() == pre.journal_disk_view());
                assert(post.accessible_aus() <= pre.accessible_aus()) by {
                    assert forall |au: AU| #[trigger] post.accessible_aus().contains(au)
                        implies pre.accessible_aus().contains(au) by {
                        if post.mini_allocator.all_aus().contains(au) {
                            assert(pre.mini_allocator.all_aus().contains(au));
                        } else {
                            assert(post.lsn_au_index_or_empty() == pre.lsn_au_index_or_empty());
                            assert(pre.accessible_aus().contains(au));
                        }
                    }
                };
            },
            _ => {
                assert(false);
            },
        }
    }

    pub open spec fn lsn_au_index_or_empty(self) -> LsnAUIndex {
        if self.journal.status is Some {
            cj_lsn_au_index(self.journal)
        } else {
            self.journal_tj().build_lsn_au_index_from_first(self.journal.snapshot.first())
        }
    }

    pub open spec fn frozen_seq_end(self, snapshot: JournalSnapshot) -> LSN {
        if snapshot.freshest_rec() is Some {
            self.journal_disk_view().entries[snapshot.freshest_rec().unwrap()].message_seq.seq_end
        } else {
            snapshot.boundary_lsn
        }
    }

    pub open spec fn frozen_lsns(self, snapshot: JournalSnapshot) -> Set<LSN> {
        Set::new(|lsn: LSN| snapshot.boundary_lsn <= lsn < self.frozen_seq_end(snapshot))
    }

    pub open spec fn frozen_tj(self, snapshot: JournalSnapshot) -> TruncatedJournal {
        TruncatedJournal{
            freshest_rec: snapshot.freshest_rec(),
            disk_view: DiskView{
                boundary_lsn: snapshot.boundary_lsn,
                entries: self.journal_tj().disk_view.entries.restrict(self.frozen_domain(snapshot)),
            },
        }
    }

    pub open spec fn frozen_snapshot_valid(self, snapshot: JournalSnapshot, seq_end: LSN) -> bool
    {
        let index = self.lsn_au_index_or_empty();
        &&& self.journal.status is Some
        &&& seq_end == self.frozen_seq_end(snapshot)
        &&& self.journal_tj().seq_start() <= snapshot.boundary_lsn
        &&& snapshot.freshest_rec() is Some ==> {
            let root = snapshot.freshest_rec().unwrap();
            &&& self.journal_tj().disk_view.entries.contains_key(root)
            &&& snapshot.boundary_lsn < seq_end
            &&& seq_end <= self.journal_tj().seq_end()
            &&& index.contains_key(snapshot.boundary_lsn)
            &&& index[snapshot.boundary_lsn] == snapshot.first()
        }
    }

    pub open spec fn linked_journal_i(self) -> LinkedJournal::State {
        LinkedJournal::State{
            truncated_journal: self.journal_tj(),
            unmarshalled_tail: if self.journal.status is Some {
                cj_unmarshalled_tail(self.journal)
            } else {
                MsgHistory::empty_history_at(self.journal_tj().seq_end())
            },
        }
    }

    pub open spec fn i(self) -> AllocationJournal::State {
        AllocationJournal::State{
            journal: self.linked_journal_i(),
            lsn_au_index: if self.journal.status is Some {
                cj_lsn_au_index(self.journal)
            } else {
                self.journal_tj().build_lsn_au_index_from_first(self.journal.snapshot.first())
            },
            mini_allocator: self.mini_allocator,
        }
    }

    pub proof fn freeze_for_commit_image_valid(
        self,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.inv(),
            CachingDiskJournal::State::next(
                self,
                self,
                CachingDiskJournal::Label::FreezeForCommit{frozen, seq_end},
            ),
        ensures
            self.frozen_snapshot_valid(frozen, seq_end),
            seq_end == self.frozen_seq_end(frozen),
            (JournalImage{tj: self.frozen_tj(frozen), first: frozen.first()}).valid_image(),
            self.frozen_tj(frozen).disk_view.is_sub_disk_with_newer_lsn(
                self.journal_tj().disk_view,
            ),
            self.frozen_tj(frozen).freshest_rec is Some ==>
                self.frozen_tj(frozen).seq_end() <= self.journal_tj().seq_end(),
    {
        let lbl = CachingDiskJournal::Label::FreezeForCommit{frozen, seq_end};
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(self, self, lbl, step);
        let reads = match step {
            CachingDiskJournal::Step::freeze_for_commit(reads) => {
                reveal(CachingDiskJournal::State::freeze_for_commit);
                reads
            },
            _ => {
                assert(false);
                arbitrary()
            },
        };

        let disk_lbl = CachingDisk::Label::Access{reads, writes: Map::empty()};
        reveal(CachingDisk::State::next);
        reveal(CachingDisk::State::next_by);
        let disk_step = choose |step: CachingDisk::Step|
            CachingDisk::State::next_by(self.disk, self.disk, disk_lbl, step);
        match disk_step {
            CachingDisk::Step::access() => {
                reveal(CachingDisk::State::access);
            },
            _ => {
                assert(false);
            },
        }
        assert(reads <= self.disk.cache);

        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
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

        let full_tj = self.journal_tj();
        let full_index = cj_lsn_au_index(self.journal);
        let first = self.journal.snapshot.first();
        let frozen_tj = self.frozen_tj(frozen);
        let frozen_journal = JournalImage{tj: frozen_tj, first: frozen.first()};
        let sub_first = if frozen.freshest_rec() is Some {
            full_index[frozen.boundary_lsn]
        } else {
            0
        };

        assert(self.journal.status is Some);
        assert(full_index == full_tj.build_lsn_au_index_from_first(first));
        full_tj.build_lsn_au_index_from_first_ensures(first);
        reveal(TruncatedJournal::au_domain_valid);
        assert(full_tj.valid_structure(full_index, first));

        if frozen.freshest_rec() is Some {
            let root = frozen.freshest_rec().unwrap();
            let frozen_seq_end = to_journal_records(reads)[root].message_seq.seq_end;
            assert(reads.contains_key(root));
            assert(to_journal_records(reads).contains_key(root));
            assert(self.disk.visible().contains_key(root));
            assert(self.visible_records().contains_key(root));
            assert(to_journal_records(reads)[root] == self.visible_records()[root]) by {
                assert(reads <= self.disk.cache);
                assert(self.disk.visible()[root] == self.disk.cache[root]);
            }
            assert(full_tj.disk_view.entries.contains_key(root));
            assert(frozen_seq_end == self.frozen_seq_end(frozen));
            assert(frozen.boundary_lsn < frozen_seq_end);
            assert(full_tj.seq_start() == self.journal.snapshot.boundary_lsn);
            assert(full_tj.seq_end() == self.journal.marshalled_seq_end());
            assert(full_tj.seq_start() <= frozen.boundary_lsn);
            assert(full_index.contains_key(frozen.boundary_lsn));

            let last_lsn = (self.frozen_seq_end(frozen) - 1) as nat;
            assert(full_tj.disk_view.entries[root].message_seq.contains(last_lsn));
            assert(full_tj.disk_view.addr_supports_lsn(root, last_lsn));
            assert(full_tj.seq_start() <= last_lsn);
            assert(last_lsn < full_tj.seq_end());
            assert(frozen.boundary_lsn < full_tj.seq_end());
            assert(full_index.contains_key(last_lsn));
            full_tj.disk_view.addr_supports_lsn_consistent_with_index(
                full_index,
                last_lsn,
                root,
            );
            assert(full_index[frozen.boundary_lsn] == frozen.first());
        }

        assert(self.frozen_snapshot_valid(frozen, seq_end));
        self.frozen_snapshot_valid_image(frozen, seq_end);
    }

    pub proof fn frozen_snapshot_valid_image(
        self,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.inv(),
            self.frozen_snapshot_valid(frozen, seq_end),
        ensures
            (JournalImage{tj: self.frozen_tj(frozen), first: frozen.first()}).valid_image(),
            self.frozen_tj(frozen).disk_view.is_sub_disk_with_newer_lsn(
                self.journal_tj().disk_view,
            ),
            self.frozen_tj(frozen).freshest_rec is Some ==>
                self.frozen_tj(frozen).seq_end() <= self.journal_tj().seq_end(),
    {
        let full_tj = self.journal_tj();
        let full_index = cj_lsn_au_index(self.journal);
        let first = self.journal.snapshot.first();
        let frozen_tj = self.frozen_tj(frozen);
        let frozen_journal = JournalImage{tj: frozen_tj, first: frozen.first()};
        let sub_first = if frozen.freshest_rec() is Some {
            full_index[frozen.boundary_lsn]
        } else {
            0
        };

        assert(self.journal.status is Some);
        assert(full_index == full_tj.build_lsn_au_index_from_first(first));
        full_tj.build_lsn_au_index_from_first_ensures(first);
        reveal(TruncatedJournal::au_domain_valid);
        assert(full_tj.valid_structure(full_index, first));

        if frozen.freshest_rec() is Some {
            let root = frozen.freshest_rec().unwrap();
            assert(full_tj.disk_view.entries.contains_key(root));
            assert(seq_end == self.frozen_seq_end(frozen));
            assert(frozen.boundary_lsn < seq_end);
            assert(seq_end <= full_tj.seq_end());
            assert(full_tj.seq_start() <= frozen.boundary_lsn);
            assert(full_index.contains_key(frozen.boundary_lsn));
            assert(full_index[frozen.boundary_lsn] == frozen.first());

            let last_lsn = (self.frozen_seq_end(frozen) - 1) as nat;
            assert(full_tj.disk_view.entries[root].message_seq.contains(last_lsn));
            assert(full_tj.disk_view.addr_supports_lsn(root, last_lsn));
            assert(full_tj.seq_start() <= last_lsn);
            assert(last_lsn < full_tj.seq_end());
            assert(full_index.contains_key(last_lsn));
            full_tj.disk_view.addr_supports_lsn_consistent_with_index(
                full_index,
                last_lsn,
                root,
            );
        }

        assert(full_tj.valid_subrange(
            full_index,
            first,
            frozen.boundary_lsn,
            frozen.freshest_rec(),
            sub_first,
        ));
        let sub_dv = full_tj.sub_disk_preserves_pointer_is_upstream(
            full_index,
            first,
            frozen.boundary_lsn,
            frozen.freshest_rec(),
            sub_first,
        );
        assert(sub_dv.is_sub_disk(frozen_tj.disk_view)) by {
            assert(sub_dv.boundary_lsn == frozen_tj.disk_view.boundary_lsn);
            assert(sub_dv.entries <= frozen_tj.disk_view.entries) by {
                assert forall |addr: Address| #[trigger] sub_dv.entries.contains_key(addr)
                    implies frozen_tj.disk_view.entries.contains_key(addr) by {
                    assert(sub_dv.entries.contains_key(addr));
                    assert(full_tj.disk_view.entries.contains_key(addr));
                    assert(full_index.restrict(self.frozen_lsns(frozen)).values().contains(addr.au));
                    assert(self.frozen_domain(frozen).contains(addr));
                }
            }
        }
        assert(frozen_tj.disk_view.is_sub_disk_with_newer_lsn(full_tj.disk_view)) by {
            assert(full_tj.disk_view.boundary_lsn <= frozen_tj.disk_view.boundary_lsn);
            assert(frozen_tj.disk_view.entries <= full_tj.disk_view.entries);
        }
        assert(frozen_tj.freshest_rec is Some ==> frozen_tj.seq_end() <= full_tj.seq_end()) by {
            if frozen.freshest_rec() is Some {
                assert(full_tj.valid_subrange(
                    full_index,
                    first,
                    frozen.boundary_lsn,
                    frozen.freshest_rec(),
                    sub_first,
                ));
            }
        }
        let full_dv = full_tj.disk_view;
        let frozen_dv = frozen_tj.disk_view;
        let frozen_index = full_index.restrict(self.frozen_lsns(frozen));
        assert(frozen_dv.entries <= full_dv.entries);
        assert forall |addr: Address| #[trigger] frozen_dv.entries.contains_key(addr)
            implies full_dv.entries.contains_key(addr) && frozen_dv.entries[addr] == full_dv.entries[addr] by {
            assert(frozen_dv.entries <= full_dv.entries);
        }
        assert(frozen_dv.entries_wf()) by {
            assert forall |addr: Address| #[trigger] frozen_dv.entries.contains_key(addr)
                implies frozen_dv.entries[addr].wf() by {
                assert(full_dv.entries.contains_key(addr));
                assert(frozen_dv.entries[addr] == full_dv.entries[addr]);
                assert(full_dv.entries[addr].wf());
            }
        }
        assert(frozen_dv.nondangling_pointers()) by {
            assert forall |addr: Address| #[trigger] frozen_dv.entries.contains_key(addr)
                implies frozen_dv.is_nondangling_pointer(
                    frozen_dv.entries[addr].cropped_prior(frozen_dv.boundary_lsn),
                ) by {
                let prior = frozen_dv.entries[addr].cropped_prior(frozen_dv.boundary_lsn);
                if prior is Some {
                    let prior_addr = prior.unwrap();
                    assert(full_dv.entries.contains_key(addr));
                    assert(frozen_dv.entries[addr] == full_dv.entries[addr]);
                    assert(full_dv.boundary_lsn <= frozen_dv.boundary_lsn);
                    assert(frozen_dv.boundary_lsn < frozen_dv.entries[addr].message_seq.seq_start);
                    assert(full_dv.entries[addr].cropped_prior(full_dv.boundary_lsn) == prior);
                    assert(full_dv.entries.contains_key(prior_addr));
                    if frozen_index.values().contains(prior_addr.au) {
                        assert(self.frozen_domain(frozen).contains(prior_addr));
                    } else {
                        assert(frozen.freshest_rec() is Some);
                        assert(!sub_dv.entries.contains_key(addr));
                        assert(frozen.freshest_rec().unwrap().after_page(addr));
                        assert(addr.page != 0);
                        assert(full_dv.nonzero_pages_point_backward());
                        assert(full_dv.entries[addr].prior_rec == Some(addr.previous()));
                        assert(prior_addr == addr.previous());
                        assert(prior_addr.au == addr.au);
                        assert(frozen_index.values().contains(addr.au));
                        assert(frozen_index.values().contains(prior_addr.au));
                        assert(false);
                    }
                    assert(frozen_dv.entries.contains_key(prior_addr));
                }
            }
        }
        assert(frozen_dv.blocks_can_concat()) by {
            assert forall |addr: Address| #[trigger] frozen_dv.entries.contains_key(addr)
                implies frozen_dv.this_block_can_concat(addr) by {
                let prior = frozen_dv.entries[addr].cropped_prior(frozen_dv.boundary_lsn);
                if prior is Some {
                    assert(full_dv.entries.contains_key(addr));
                    assert(frozen_dv.entries[addr] == full_dv.entries[addr]);
                    assert(frozen_dv.entries.contains_key(prior.unwrap()));
                    assert(full_dv.entries.contains_key(prior.unwrap()));
                    assert(full_dv.boundary_lsn <= frozen_dv.boundary_lsn);
                    assert(frozen_dv.boundary_lsn < frozen_dv.entries[addr].message_seq.seq_start);
                    assert(full_dv.entries[addr].cropped_prior(full_dv.boundary_lsn) == prior);
                    assert(full_dv.this_block_can_concat(addr));
                    assert(full_dv.entries[prior.unwrap()] == frozen_dv.entries[prior.unwrap()]);
                }
            }
        }
        assert(frozen_dv.blocks_each_have_link()) by {
            assert forall |addr: Address| #[trigger] frozen_dv.entries.contains_key(addr)
                implies frozen_dv.entries[addr].has_link(frozen_dv.boundary_lsn) by {
                assert(full_dv.entries.contains_key(addr));
                assert(frozen_dv.entries[addr] == full_dv.entries[addr]);
                assert(full_dv.entries[addr].has_link(full_dv.boundary_lsn));
            }
        }
        assert(frozen_dv.wf());
        assert(frozen_dv.valid_ranking(full_dv.the_ranking())) by {
            assert(frozen_dv.entries.dom().subset_of(full_dv.the_ranking().dom()));
            assert forall |addr: Address| #[trigger] frozen_dv.entries.contains_key(addr)
                && frozen_dv.entries[addr].cropped_prior(frozen_dv.boundary_lsn) is Some
                implies full_dv.the_ranking()[
                    frozen_dv.entries[addr].cropped_prior(frozen_dv.boundary_lsn).unwrap()
                ] < full_dv.the_ranking()[addr] by {
                let prior = frozen_dv.entries[addr].cropped_prior(frozen_dv.boundary_lsn);
                assert(full_dv.entries.contains_key(addr));
                assert(frozen_dv.entries[addr] == full_dv.entries[addr]);
                assert(full_dv.boundary_lsn <= frozen_dv.boundary_lsn);
                assert(frozen_dv.boundary_lsn < frozen_dv.entries[addr].message_seq.seq_start);
                assert(full_dv.entries[addr].cropped_prior(full_dv.boundary_lsn) == prior);
                assert(full_dv.valid_ranking(full_dv.the_ranking()));
            }
        }
        assert(frozen_dv.acyclic());
        assert(frozen_dv.nonzero_pages_point_backward()) by {
            assert forall |addr: Address| #![auto]
                ({
                    &&& addr.page != 0
                    &&& frozen_dv.entries.contains_key(addr)
                }) ==> frozen_dv.entries[addr].prior_rec == Some(addr.previous()) by {
                if addr.page != 0 && frozen_dv.entries.contains_key(addr) {
                    assert(frozen_dv.entries <= full_dv.entries);
                    assert(full_dv.entries.contains_key(addr));
                    assert(frozen_dv.entries[addr] == full_dv.entries[addr]);
                    assert(full_dv.nonzero_pages_point_backward());
                }
            }
        }
        reveal(DiskView::pages_allocated_in_lsn_order);
        assert(frozen_dv.pages_allocated_in_lsn_order()) by {
            assert forall |alo: Address, ahi: Address| #![auto]
                ({
                    &&& alo.au == ahi.au
                    &&& alo.page < ahi.page
                    &&& frozen_dv.entries.contains_key(alo)
                    &&& frozen_dv.entries.contains_key(ahi)
                }) ==> frozen_dv.entries[alo].message_seq.seq_end
                    <= frozen_dv.entries[ahi].message_seq.seq_start by {
                if alo.au == ahi.au && alo.page < ahi.page
                    && frozen_dv.entries.contains_key(alo)
                    && frozen_dv.entries.contains_key(ahi) {
                    assert(frozen_dv.entries <= full_dv.entries);
                    assert(full_dv.entries.contains_key(alo));
                    assert(full_dv.entries.contains_key(ahi));
                    assert(frozen_dv.entries[alo] == full_dv.entries[alo]);
                    assert(frozen_dv.entries[ahi] == full_dv.entries[ahi]);
                    assert(full_dv.pages_allocated_in_lsn_order());
                }
            }
        }
        assert(frozen_dv.internal_au_pages_fully_linked());
        assert(frozen_dv.has_unique_lsns()) by {
            assert forall |lsn, addr1, addr2|
                frozen_dv.addr_supports_lsn(addr1, lsn)
                && frozen_dv.addr_supports_lsn(addr2, lsn)
                implies addr1 == addr2 by {
                assert(full_dv.addr_supports_lsn(addr1, lsn));
                assert(full_dv.addr_supports_lsn(addr2, lsn));
                assert(full_dv.has_unique_lsns());
            }
        }
        if frozen.freshest_rec() is Some {
            assert(sub_dv.valid_first_au(sub_first));
            let first_addr = choose |addr: Address| #![auto]
                addr.au == sub_first && sub_dv.addr_supports_lsn(addr, sub_dv.boundary_lsn);
            assert(sub_dv.entries.contains_key(first_addr));
            assert(frozen_dv.entries.contains_key(first_addr));
            assert(sub_dv.entries[first_addr] == frozen_dv.entries[first_addr]);
            assert(sub_dv.boundary_lsn == frozen_dv.boundary_lsn);
            assert(frozen_dv.addr_supports_lsn(first_addr, frozen_dv.boundary_lsn));
            assert(frozen_dv.valid_first_au(sub_first));
        }
        assert(sub_first == frozen.first()) by {
            if frozen.freshest_rec() is Some {
                assert(full_index[frozen.boundary_lsn] == frozen.first());
            }
        }
        assert(frozen_tj.disk_view.pointer_is_upstream(frozen_tj.freshest_rec, sub_first));
        assert(frozen_tj.disk_view.pointer_is_upstream(frozen_tj.freshest_rec, frozen.first()));
        let frozen_built_index = frozen_tj.build_lsn_au_index_from_first(frozen.first());
        let sub_tj = TruncatedJournal{disk_view: sub_dv, freshest_rec: frozen.freshest_rec()};
        assert(sub_tj.disk_view.pointer_is_upstream(sub_tj.freshest_rec, sub_first));
        sub_tj.build_lsn_au_index_from_first_ensures(sub_first);
        frozen_tj.build_lsn_au_index_from_first_ensures(frozen.first());
        sub_dv.build_lsn_au_index_equiv_page_walk(frozen.freshest_rec(), sub_first);
        frozen_dv.build_lsn_au_index_equiv_page_walk(frozen.freshest_rec(), frozen.first());
        sub_dv.build_lsn_au_index_page_walk_sub_disk(frozen_dv, frozen.freshest_rec());
        assert(sub_dv.is_sub_disk(frozen_dv));
        assert(sub_dv.build_lsn_au_index_page_walk(frozen.freshest_rec())
            == frozen_dv.build_lsn_au_index_page_walk(frozen.freshest_rec()));
        assert(frozen_built_index == frozen_index);
        assert(frozen_dv.domain_au_bounded_wrt_index(frozen_built_index)) by {
            assert forall |addr: Address| #[trigger] frozen_dv.entries.dom().contains(addr)
                implies frozen_built_index.values().contains(addr.au) by {
                assert(frozen_dv.entries.contains_key(addr));
                assert(self.frozen_domain(frozen).contains(addr));
                assert(frozen_index.values().contains(addr.au));
            }
        }
        if frozen.freshest_rec() is Some {
            frozen_tj.boundary_au_matches_first(sub_first);
            full_tj.sub_disk_preserves_bounded_inactive_lsns(
                full_index,
                first,
                frozen_tj,
                sub_first,
            );
        }
        assert(frozen_journal.valid_image());
    }

    pub proof fn internal_extends_journal_view(pre: Self, post: Self)
        requires
            pre.inv(),
            CachingDiskJournal::State::next(pre, post, CachingDiskJournal::Label::Internal),
        ensures
            post.journal_tj().disk_view.boundary_lsn == pre.journal_tj().disk_view.boundary_lsn,
            pre.journal_tj().disk_view.entries <= post.journal_tj().disk_view.entries,
            pre.journal_tj().seq_end() <= post.journal_tj().seq_end(),
    {
        let lbl = CachingDiskJournal::Label::Internal;
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskJournal::Step::caching_disk_internal(new_disk) => {
                reveal(CachingDiskJournal::State::caching_disk_internal);
                CachingDisk::State::internal_visible_unchanged(pre.disk, post.disk);
                assert(post.journal == pre.journal);
                assert(post.visible_records() == pre.visible_records());
                assert(post.journal_tj() == pre.journal_tj());
            },
            CachingDiskJournal::Step::journal_marshal(new_journal, new_disk, addr, writes) => {
                reveal(CachingDiskJournal::State::journal_marshal);
                reveal(CachedJournal::State::next);
                reveal(CachedJournal::State::next_by);
                let journal_lbl = CachedJournal::Label::JournalMarshal{
                    writes: to_journal_records(writes),
                };
                let cj_step = choose |step: CachedJournal::Step|
                    CachedJournal::State::next_by(pre.journal, post.journal, journal_lbl, step);
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
                CachingDisk::State::access_visible_effect(pre.disk, post.disk, Map::empty(), writes);
                let marshalled_msgs = pre.journal.status.unwrap().unmarshalled_tail.discard_recent(cut);
                let expected_record = JournalRecord{
                    message_seq: marshalled_msgs,
                    prior_rec: pre.journal.snapshot.freshest_rec(),
                };
                assert(to_journal_records(writes) == Map::empty().insert(hidden_addr, expected_record));
                assert(writes.dom() =~= Set::new(|a: Address| a == addr));
                assert(hidden_addr == addr) by {
                    assert(to_journal_records(writes).contains_key(hidden_addr));
                    assert(writes.contains_key(hidden_addr));
                    assert(writes.dom().contains(hidden_addr));
                    assert(Set::new(|a: Address| a == addr).contains(hidden_addr));
                }
                assert(post.journal.snapshot == JournalSnapshot{
                    root: Some(JournalRoot{
                        freshest_rec: addr,
                        first: if pre.journal.snapshot.root is None { addr.au } else { pre.journal.snapshot.first() },
                    }),
                    ..pre.journal.snapshot
                });
                assert(post.journal_tj().disk_view.boundary_lsn == pre.journal_tj().disk_view.boundary_lsn);
                assert(pre.journal_tj().disk_view.entries <= post.journal_tj().disk_view.entries) by {
                    assert forall |old_addr: Address| #[trigger] pre.journal_tj().disk_view.entries.dom().contains(old_addr)
                        implies post.journal_tj().disk_view.entries.dom().contains(old_addr)
                            && pre.journal_tj().disk_view.entries[old_addr]
                                == post.journal_tj().disk_view.entries[old_addr] by {
                        assert(pre.visible_records().contains_key(old_addr));
                        assert(pre.disk.visible().contains_key(old_addr));
                        assert(!writes.contains_key(old_addr)) by {
                            if writes.contains_key(old_addr) {
                                assert(writes.dom().contains(old_addr));
                                assert(writes.dom() =~= Set::new(|a: Address| a == addr));
                                assert(old_addr == addr);
                                assert(pre.mini_allocator.tight_next_addr(pre.journal.snapshot.freshest_rec(), addr));
                                assert(pre.mini_allocator.can_allocate(addr));
                                assert(AllocationJournal::State::disk_domain_not_free(
                                    pre.journal_tj().disk_view,
                                    pre.mini_allocator,
                                ));
                                assert(!pre.mini_allocator.can_allocate(old_addr));
                                assert(false);
                            }
                        }
                        assert(post.disk.visible().contains_key(old_addr));
                        assert(post.disk.visible()[old_addr] == pre.disk.visible()[old_addr]);
                        assert(post.visible_records().contains_key(old_addr));
                        assert(post.visible_records()[old_addr] == pre.visible_records()[old_addr]);
                    }
                }
                assert(pre.journal_tj().seq_end() <= post.journal_tj().seq_end()) by {
                    assert(pre.journal_tj().seq_end() == pre.journal.marshalled_seq_end());
                    assert_maps_equal!(
                        post.visible_records(),
                        pre.visible_records().union_prefer_right(to_journal_records(writes)),
                        a => {
                            if writes.contains_key(a) {
                            } else {
                            }
                        }
                    );
                    assert(to_journal_records(writes).contains_key(addr));
                    assert(writes.contains_key(addr));
                    assert(post.disk.visible().contains_key(addr));
                    assert(post.visible_records().contains_key(addr));
                    assert(pre.visible_records().union_prefer_right(to_journal_records(writes))[addr]
                        == to_journal_records(writes)[addr]);
                    assert(to_journal_records(writes)[addr] == expected_record);
                    assert(post.visible_records()[addr] == expected_record);
                    assert(post.journal_tj().freshest_rec == Some(addr));
                    assert(post.journal_tj().disk_view.entries[addr] == expected_record);
                    assert(expected_record.message_seq.seq_end == cut);
                    assert(post.journal_tj().seq_end() == cut);
                }
            },
            CachingDiskJournal::Step::internal_noop() => {
                reveal(CachingDiskJournal::State::internal_noop);
                assert(post == pre);
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn load_index_visible_unchanged(pre: Self, post: Self, discovered_aus: Set<AU>)
        requires
            CachingDiskJournal::State::next(
                pre,
                post,
                CachingDiskJournal::Label::LoadIndex{discovered_aus},
            ),
        ensures
            post.journal_disk_view() == pre.journal_disk_view(),
            post.journal_tj() == pre.journal_tj(),
    {
        let lbl = CachingDiskJournal::Label::LoadIndex{discovered_aus};
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskJournal::Step::load_index(new_journal, reads) => {
                reveal(CachingDiskJournal::State::load_index);
                CachedJournal::State::load_index_effect(
                    pre.journal,
                    post.journal,
                    to_journal_records(reads),
                    discovered_aus,
                );
                assert(post.disk == pre.disk);
                assert(post.journal.snapshot == pre.journal.snapshot);
                assert(post.journal_disk_view() == pre.journal_disk_view());
                assert(post.journal_tj() == pre.journal_tj());
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn observe_clean_aus_visible_unchanged(pre: Self, post: Self, aus: Set<AU>)
        requires
            CachingDiskJournal::State::next(
                pre,
                post,
                CachingDiskJournal::Label::ObserveCleanAUs{aus},
            ),
        ensures
            post.journal_disk_view() == pre.journal_disk_view(),
            post.journal_tj() == pre.journal_tj(),
    {
        let lbl = CachingDiskJournal::Label::ObserveCleanAUs{aus};
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskJournal::Step::observe_clean_aus(new_journal) => {
                reveal(CachingDiskJournal::State::observe_clean_aus);
                CachedJournal::State::observe_clean_aus_effect(pre.journal, post.journal, aus);
                assert(post.disk == pre.disk);
                assert(post.journal.snapshot == pre.journal.snapshot);
                assert(post.journal_disk_view() == pre.journal_disk_view());
                assert(post.journal_tj() == pre.journal_tj());
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn internal_alloc_visible_unchanged(
        pre: Self,
        post: Self,
        allocs: Set<AU>,
        deallocs: Set<AU>,
        prune_aus: Set<AU>,
    )
        requires
            CachingDiskJournal::State::next(
                pre,
                post,
                CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus},
            ),
        ensures
            post.journal_disk_view() == pre.journal_disk_view(),
            post.journal_tj() == pre.journal_tj(),
    {
        let lbl = CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus};
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskJournal::Step::mini_allocator_fill() => {
                reveal(CachingDiskJournal::State::mini_allocator_fill);
                assert(post.journal == pre.journal);
                assert(post.disk == pre.disk);
                assert(post.journal_disk_view() == pre.journal_disk_view());
                assert(post.journal_tj() == pre.journal_tj());
            },
            CachingDiskJournal::Step::mini_allocator_prune() => {
                reveal(CachingDiskJournal::State::mini_allocator_prune);
                assert(post.journal == pre.journal);
                assert(post.disk == pre.disk);
                assert(post.journal_disk_view() == pre.journal_disk_view());
                assert(post.journal_tj() == pre.journal_tj());
            },
            _ => {
                assert(false);
            },
        }
    }
}

}
