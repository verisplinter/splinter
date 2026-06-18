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
    AllocationJournal, JournalMetadata, JournalImage, LsnAUIndex, AUPageBounds, au_addrs_past_pointer, lsn_au_index_append_record,
    lsn_au_index_append_record_ensures, lsn_au_index_discard_up_to,
    lsn_au_index_discard_up_to_ensures, singleton_index,
};
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::disk::GenericDisk_v::{Address, AU, Pointer, Ranking, to_aus, to_aus_domain, to_aus_preserves_lte};
use crate::spec::AsyncDisk_t::RawPage;
use crate::implementation::CachedJournal_v::*;
use crate::implementation::CachingDisk_v::*;
use crate::implementation::JournalTypes_v::{raw_page_to_record, to_journal_records};
use crate::journal::LinkedJournal_v::*;

verus!{

pub proof fn mini_allocator_add_aus_preserves_all_aus(mini_allocator: MiniAllocator, aus: Set<AU>)
    requires
        mini_allocator.wf(),
    ensures
        mini_allocator.add_aus(aus).all_aus() == mini_allocator.all_aus() + aus,
{
    assert forall |au: AU| #[trigger] mini_allocator.add_aus(aus).all_aus().contains(au)
        <==> (mini_allocator.all_aus() + aus).contains(au) by { };
}

pub proof fn mini_allocator_allocate_preserves_all_aus(mini_allocator: MiniAllocator, addr: Address)
    requires
        mini_allocator.wf(),
        mini_allocator.can_allocate(addr),
    ensures
        mini_allocator.allocate(addr).all_aus() == mini_allocator.all_aus(),
{
    assert forall |au: AU| #[trigger] mini_allocator.allocate(addr).all_aus().contains(au)
        <==> mini_allocator.all_aus().contains(au) by {
        if au == addr.au {
            assert(mini_allocator.all_aus().contains(au));
        }
    };
}

impl DiskView {
    pub proof fn path_valid_ranking_insert_fresh(
        self,
        root: Pointer,
        ranking: Ranking,
        fresh_addr: Address,
        fresh_rank: nat,
    )
        requires
            self.path_valid_ranking(root, ranking),
            !self.entries.contains_key(fresh_addr),
        ensures
            self.path_valid_ranking(root, ranking.insert(fresh_addr, fresh_rank)),
        decreases if root is Some && ranking.contains_key(root.unwrap()) {
            ranking[root.unwrap()] + 1
        } else {
            0
        },
    {
        match root {
            None => {},
            Some(addr) => {
                assert(addr != fresh_addr);
                let record = self.entries[addr];
                let next = record.cropped_prior(self.boundary_lsn);
                if next is Some {
                    self.path_valid_ranking_insert_fresh(
                        next,
                        ranking,
                        fresh_addr,
                        fresh_rank,
                    );
                    assert(ranking.insert(fresh_addr, fresh_rank)[next.unwrap()]
                        == ranking[next.unwrap()]);
                    assert(ranking.insert(fresh_addr, fresh_rank)[next.unwrap()]
                        < ranking.insert(fresh_addr, fresh_rank)[addr]);
                }
                reveal_with_fuel(DiskView::path_valid_ranking, 2);
                assert(self.path_valid_ranking(root, ranking.insert(fresh_addr, fresh_rank)));
            },
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
        pub au_page_bounds: AUPageBounds,
    }

    pub enum Label {
        ReadForRecovery{messages: MsgHistory},
        FreezeForCommit{frozen: JournalSnapshot, seq_end: LSN},
        QueryEndLsn{end_lsn: LSN},
        Put{messages: MsgHistory},
        DiscardOld{start_lsn: LSN, require_end: LSN},
        ObserveCleanAUs{aus: Set<AU>},
        CommitPrepared{frozen: JournalSnapshot, seq_end: LSN},
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
        let init_base = CachingDiskJournal::State{
            journal: init_journal,
            disk,
            mini_allocator: init_mini_allocator,
            au_page_bounds: Map::empty(),
        };
        let init_image = init_base.backing_journal_image();
        require init_image.valid_image();
        let init_bounds = init_image.tj.disk_view.loose_build_au_page_bounds_au_walk(
            init_image.tj.freshest_rec,
            init_image.first,
        );
        let init_state = CachingDiskJournal::State{
            au_page_bounds: init_bounds,
            ..init_base
        };
        init journal = init_journal;
        init disk = disk;
        init mini_allocator = init_mini_allocator;
        init au_page_bounds = init_bounds;
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
        require to_journal_records(reads) <= pre.journal_disk_view().entries;
        require forall |addr: Address| #[trigger] reads.contains_key(addr) ==> {
            &&& pre.au_page_bounds.contains_key(addr.au)
            &&& addr.page <= pre.au_page_bounds[addr.au]
        };
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
        require frozen.freshest_rec() is Some ==> {
            let root = frozen.freshest_rec().unwrap();
            &&& to_journal_records(reads).contains_key(root)
            &&& pre.journal_disk_view().entries.contains_key(root)
            &&& to_journal_records(reads)[root] == pre.journal_disk_view().entries[root]
            &&& pre.au_page_bounds.contains_key(root.au)
            &&& root.page <= pre.au_page_bounds[root.au]
        };
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
        require cj_lsn_au_index(pre.journal).values() <= cj_lsn_au_index(new_journal).values();
        require CachingDisk::State::next(
            pre.disk,
            new_disk,
            CachingDisk::Label::Access{reads: Map::empty(), writes},
        );

        update journal = new_journal;
        update disk = new_disk;
        update mini_allocator = pre.mini_allocator.allocate(addr).observe(addr);
        update au_page_bounds = pre.au_page_bounds.insert(addr.au, addr.page);
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
        require let Label::CommitPrepared{frozen, seq_end} = lbl;
        require pre.journal.status is Some;
        require frozen.freshest_rec() is Some ==> seq_end <= pre.journal.clean_watermark();
        require pre.disk.addrs_clean_or_evictable(pre.frozen_prefix_domain(frozen));
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
        update au_page_bounds = AllocationJournal::State::au_page_bounds_restrict(
            pre.au_page_bounds,
            new_au_index.values(),
        );
    }}

    transition!{ mini_allocator_fill(lbl: Label, new_disk: CachingDisk::State) {
        require lbl is InternalAlloc;
        require lbl->deallocs == Set::<AU>::empty();
        require lbl->prune_aus == Set::<AU>::empty();
        require pre.journal.status is Some;
        require lbl->allocs.disjoint(pre.mini_allocator.all_aus());
        require lbl->allocs.disjoint(cj_lsn_au_index(pre.journal).values());
        require new_disk.inv();
        require pre.disk.cache <= new_disk.cache;
        require pre.disk.persistent <= new_disk.persistent;
        require pre.disk.status <= new_disk.status;
        require new_disk.cache.dom() <= addresses_in_aus(
            cj_lsn_au_index(pre.journal).values() + pre.mini_allocator.all_aus() + lbl->allocs,
        );
        require new_disk.persistent.dom() <= addresses_in_aus(
            cj_lsn_au_index(pre.journal).values() + pre.mini_allocator.all_aus() + lbl->allocs,
        );
        require new_disk.status.dom() <= addresses_in_aus(
            cj_lsn_au_index(pre.journal).values() + pre.mini_allocator.all_aus() + lbl->allocs,
        );
        require new_disk.cache.dom() - pre.disk.cache.dom() <= addresses_in_aus(lbl->allocs);
        require new_disk.persistent.dom() - pre.disk.persistent.dom() <= addresses_in_aus(lbl->allocs);
        require new_disk.status.dom() - pre.disk.status.dom() <= addresses_in_aus(lbl->allocs);
        require new_disk.cache.dom() <= Set::new(|addr: Address| addr.wf());
        require new_disk.persistent.dom() <= Set::new(|addr: Address| addr.wf());

        update disk = new_disk;
        update mini_allocator = pre.mini_allocator.add_aus(lbl->allocs);
    }}

    transition!{ mini_allocator_prune(lbl: Label, new_disk: CachingDisk::State) {
        require lbl is InternalAlloc;
        require pre.journal.status is Some;
        require lbl->allocs == Set::<AU>::empty();
        require lbl->deallocs <= lbl->prune_aus;
        require CachingDisk::State::next(
            pre.disk,
            new_disk,
            CachingDisk::Label::Forget{aus: lbl->deallocs},
        );
        require forall |au: AU| #[trigger] lbl->prune_aus.contains(au)
            ==> pre.mini_allocator.can_remove(au);
        require forall |au: AU| #[trigger] lbl->deallocs.contains(au)
            ==> pre.mini_allocator.allocs[au].all_pages_free();
        require forall |addr: Address| {
            &&& #[trigger] pre.disk.visible().contains_key(addr)
            &&& lbl->prune_aus.contains(addr.au)
            &&& !lbl->deallocs.contains(addr.au)
        } ==> cj_lsn_au_index(pre.journal).values().contains(addr.au);

        update disk = new_disk;
        update mini_allocator = pre.mini_allocator.prune(lbl->prune_aus);
    }}

    transition!{ internal_noop(lbl: Label) {
        require lbl is Internal;
    }}

    pub open spec fn visible_journal_structure(self) -> bool {
        let index = self.journal_tj().disk_view.build_lsn_au_index_au_walk(
            self.journal_tj().freshest_rec,
            self.journal.snapshot.first(),
        );
        &&& self.journal_tj().decodable()
        &&& self.journal_disk_view().wf_addrs()
        &&& self.journal_tj().disk_view.wf_addrs()
        &&& self.journal_tj().freshest_rec is Some
            ==> self.journal_tj().disk_view.valid_first_au(self.journal.snapshot.first())
        &&& self.journal_tj().disk_view.domain_tight_wrt_index(
            index,
            self.journal_tj().freshest_rec,
        )
        &&& index.values() <= to_aus(self.journal_tj().disk_view.entries.dom())
        &&& self.journal_tj().disk_view.bounded_inactive_lsns(
            index,
            self.journal_tj().freshest_rec,
        )
        &&& self.visible_lsn_au_index() == index
        &&& self.au_page_bounds.dom() =~= index.values()
        &&& self.journal_tj().freshest_rec is Some ==> {
            let root = self.journal_tj().freshest_rec.unwrap();
            &&& self.au_page_bounds.contains_key(root.au)
            &&& self.au_page_bounds[root.au] == root.page
        }
        &&& forall |addr: Address| #[trigger] self.journal_tj().disk_view.entries.contains_key(addr) ==> {
            &&& self.au_page_bounds.contains_key(addr.au)
            &&& addr.page <= self.au_page_bounds[addr.au]
        }
        &&& forall |addr: Address| {
            &&& #[trigger] self.journal_disk_view().entries.contains_key(addr)
            &&& self.au_page_bounds.contains_key(addr.au)
            &&& addr.page <= self.au_page_bounds[addr.au]
            &&& self.journal_disk_view().boundary_lsn
                < self.journal_disk_view().entries[addr].message_seq.seq_end
        } ==> self.journal_tj().disk_view.entries.contains_key(addr)
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
        &&& cj_lsn_au_index(self.journal) == self.journal_tj().disk_view.build_lsn_au_index_au_walk(
            self.journal_tj().freshest_rec,
            self.journal.snapshot.first(),
        )
    }

    pub open spec fn backing_journal_image(self) -> JournalImage {
        JournalImage{
            tj: self.journal_backing_tj(),
            first: self.journal.snapshot.first(),
        }
    }

    pub open spec fn unloaded_backing_image_valid(self) -> bool {
        self.journal.status is None ==> self.backing_journal_image().valid_image()
    }

    pub open spec fn indexed_aus_not_all_pages_free(self) -> bool {
        self.journal.status is Some ==> forall |au: AU| {
            &&& #[trigger] cj_lsn_au_index(self.journal).values().contains(au)
            &&& self.mini_allocator.allocs.contains_key(au)
        } ==> !self.mini_allocator.allocs[au].all_pages_free()
    }

    pub open spec fn unloaded_mini_allocator_empty(self) -> bool {
        self.journal.status is None ==> self.mini_allocator.allocs.dom() =~= Set::<AU>::empty()
    }

    #[invariant]
    pub open spec fn inv(self) -> bool {
        &&& self.journal.wf()
        &&& self.disk.inv()
        &&& self.mini_allocator.wf()
        &&& self.indexed_aus_not_all_pages_free()
        &&& self.unloaded_mini_allocator_empty()
    }

    #[inductive(initialize)]
    pub fn initialize_inductive(post: Self, snapshot: JournalSnapshot, disk: CachingDisk::State) {}

    #[inductive(caching_disk_internal)]
    fn caching_disk_internal_inductive(pre: Self, post: Self, lbl: Label, new_disk: CachingDisk::State) {
        CachingDisk::State::inv_next(pre.disk, post.disk, CachingDisk::Label::Internal{});
        CachingDisk::State::internal_visible_unchanged(pre.disk, post.disk);
        assert(post.journal == pre.journal);
        assert(post.mini_allocator == pre.mini_allocator);
        assert(post.journal_disk_view().entries == pre.journal_disk_view().entries);
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
        CachedJournal::State::inv_next(pre.journal, post.journal, journal_lbl);
        CachedJournal::State::load_index_effect(
            pre.journal,
            post.journal,
            to_journal_records(reads),
            lbl.arrow_LoadIndex_discovered_aus(),
        );
        CachingDisk::State::access_effect(
            pre.disk,
            pre.disk,
            reads,
            Map::empty(),
        );
        assert(post.disk == pre.disk);
        assert(post.mini_allocator == pre.mini_allocator);
        assert(post.indexed_aus_not_all_pages_free()) by {
            assert(pre.journal.status is None);
            assert(pre.mini_allocator.allocs.dom() =~= Set::<AU>::empty());
            assert forall |au: AU| {
                &&& #[trigger] cj_lsn_au_index(post.journal).values().contains(au)
                &&& post.mini_allocator.allocs.contains_key(au)
            } implies !post.mini_allocator.allocs[au].all_pages_free() by {
                assert(false);
            }
        }
    }

    #[inductive(read_for_recovery)]
    fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label, reads: Map<Address, RawPage>) {
        assert(post == pre);
    }

    #[inductive(freeze_for_commit)]
    fn freeze_for_commit_inductive(pre: Self, post: Self, lbl: Label, reads: Map<Address, RawPage>) {
        assert(post == pre);
    }

    #[inductive(query_end_lsn)]
    fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post == pre);
    }

    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label, new_journal: CachedJournal::State) {
        let journal_lbl = CachedJournal::Label::Put{messages: lbl.arrow_Put_messages()};
        CachedJournal::State::inv_next(pre.journal, post.journal, journal_lbl);
        CachedJournal::State::put_effect(pre.journal, post.journal, lbl.arrow_Put_messages());
        assert(post.disk == pre.disk);
        assert(post.mini_allocator == pre.mini_allocator);
        assert(post.indexed_aus_not_all_pages_free()) by {
            if post.journal.status is Some {
                assert(pre.journal.status is Some);
                assert(cj_lsn_au_index(post.journal) == cj_lsn_au_index(pre.journal));
            }
        }
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
        CachedJournal::State::inv_next(pre.journal, post.journal, journal_lbl);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(pre.journal, post.journal, journal_lbl, step);
        match cj_step {
            CachedJournal::Step::internal_journal_marshal(cut, hidden_addr) => {
                reveal(CachedJournal::State::internal_journal_marshal);
                assert(to_journal_records(writes).contains_key(hidden_addr));
                assert(writes.contains_key(hidden_addr));
                assert(writes.dom().contains(hidden_addr));
                assert(writes.dom() =~= Set::new(|a: Address| a == addr));
                assert(hidden_addr == addr);
                assert(post.indexed_aus_not_all_pages_free()) by {
                    assert(post.journal.status is Some);
                    let marshalled_msgs = to_journal_records(writes)[addr].message_seq;
                    let tail = pre.journal.status.unwrap().unmarshalled_tail;
                    assert(marshalled_msgs == tail.discard_recent(cut));
                    assert(tail.wf());
                    assert(tail.can_discard_to(cut));
                    assert(marshalled_msgs.seq_start == tail.seq_start);
                    assert(marshalled_msgs.seq_end == cut);
                    assert(marshalled_msgs.seq_start < marshalled_msgs.seq_end);
                    assert(marshalled_msgs.wf()) by {
                        assert forall |lsn: LSN| #[trigger] marshalled_msgs.msgs.dom().contains(lsn)
                            <==> marshalled_msgs.contains(lsn) by {
                            if marshalled_msgs.msgs.dom().contains(lsn) {
                                assert(tail.seq_start <= lsn < cut);
                            }
                            if marshalled_msgs.contains(lsn) {
                                assert(tail.seq_start <= lsn < cut);
                            }
                        }
                    }
                    let old_index = cj_lsn_au_index(pre.journal);
                    lsn_au_index_append_record_ensures(old_index, marshalled_msgs, addr.au);
                    Self::lsn_au_index_append_record_values_subset(old_index, marshalled_msgs, addr.au);
                    assert forall |au: AU| {
                        &&& #[trigger] cj_lsn_au_index(post.journal).values().contains(au)
                        &&& post.mini_allocator.allocs.contains_key(au)
                    } implies !post.mini_allocator.allocs[au].all_pages_free() by {
                        if au == addr.au {
                            assert(post.mini_allocator == pre.mini_allocator.allocate(addr).observe(addr));
                            let after_allocate = pre.mini_allocator.allocate(addr);
                            assert(after_allocate.allocs[addr.au].reserved.contains(addr));
                            assert(post.mini_allocator.allocs[addr.au].observed.contains(addr));
                            assert(!post.mini_allocator.allocs[addr.au].has_no_observed_pages());
                            assert(!post.mini_allocator.allocs[addr.au].all_pages_free());
                        } else {
                            assert(old_index.values().contains(au));
                            assert(pre.mini_allocator.allocs.contains_key(au));
                            assert(post.mini_allocator.allocs[au] == pre.mini_allocator.allocs[au]);
                            assert(!pre.mini_allocator.allocs[au].all_pages_free());
                        }
                    }
                }
            },
            _ => { assert(false); },
        }
        assert(pre.journal.status is Some);
        assert(post.journal.status is Some);
        CachingDisk::State::inv_next(pre.disk, post.disk, CachingDisk::Label::Access{reads: Map::empty(), writes});
        assert(pre.mini_allocator.can_allocate(addr));
        assert(pre.mini_allocator.allocate(addr).wf());
        assert(pre.mini_allocator.allocate(addr).allocs.contains_key(addr.au));
        assert(pre.mini_allocator.allocate(addr).allocs[addr.au].reserved.contains(addr));
        assert(post.mini_allocator.allocs[addr.au].observed.contains(addr));
        assert(!post.mini_allocator.allocs[addr.au].all_pages_free());
        assert(post.mini_allocator.wf());
        CachingDisk::State::access_effect(pre.disk, post.disk, Map::empty(), writes);
        mini_allocator_allocate_preserves_all_aus(pre.mini_allocator, addr);
        assert(post.mini_allocator.all_aus() == pre.mini_allocator.all_aus()) by {
            assert(pre.mini_allocator.allocate(addr).all_aus() == pre.mini_allocator.all_aus());
            assert forall |au: AU| #[trigger] post.mini_allocator.all_aus().contains(au)
                <==> pre.mini_allocator.all_aus().contains(au) by {
            }
        }
    }

    #[inductive(observe_clean_aus)]
    fn observe_clean_aus_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CachedJournal::State,
    ) {
        let journal_lbl = CachedJournal::Label::ObserveCleanAUs{aus: lbl.arrow_ObserveCleanAUs_aus()};
        CachedJournal::State::inv_next(pre.journal, post.journal, journal_lbl);
        CachedJournal::State::observe_clean_aus_effect(
            pre.journal,
            post.journal,
            lbl.arrow_ObserveCleanAUs_aus(),
        );
        assert(post.disk == pre.disk);
        assert(post.mini_allocator == pre.mini_allocator);
        assert(post.indexed_aus_not_all_pages_free()) by {
            if post.journal.status is Some {
                assert(pre.journal.status is Some);
                assert(cj_lsn_au_index(post.journal) == cj_lsn_au_index(pre.journal));
            }
        }
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
        CachedJournal::State::inv_next(pre.journal, post.journal, journal_lbl);
        CachingDisk::State::inv_next(pre.disk, post.disk, CachingDisk::Label::Forget{aus: deallocs});
        pre.mini_allocator.prune_preserves_wf(deallocs);
        assert(post.mini_allocator.wf());
        CachingDisk::State::forget_effect(pre.disk, post.disk, deallocs);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(pre.journal, post.journal, journal_lbl, step);
        match cj_step {
            CachedJournal::Step::discard_old() => {},
            _ => { assert(false); },
        }
        lsn_au_index_discard_up_to_ensures(old_au_index, start_lsn);
        assert(post.mini_allocator.all_aus()
            == pre.mini_allocator.all_aus().difference(deallocs));
        assert(post.indexed_aus_not_all_pages_free()) by {
            assert(post.journal.status is Some);
            assert(cj_lsn_au_index(post.journal) == new_au_index);
            assert forall |au: AU| {
                &&& #[trigger] cj_lsn_au_index(post.journal).values().contains(au)
                &&& post.mini_allocator.allocs.contains_key(au)
            } implies !post.mini_allocator.allocs[au].all_pages_free() by {
                assert(new_au_index.values().contains(au));
                assert(old_au_index.values().contains(au));
                assert(pre.mini_allocator.allocs.contains_key(au));
                assert(post.mini_allocator.allocs[au] == pre.mini_allocator.allocs[au]);
                assert(!pre.mini_allocator.allocs[au].all_pages_free());
            }
        }
    }

    #[inductive(mini_allocator_fill)]
    pub fn mini_allocator_fill_inductive(pre: Self, post: Self, lbl: Label, new_disk: CachingDisk::State) {
        assert(post.mini_allocator.wf());
        assert(post.journal == pre.journal);
        assert(post.disk == new_disk);
        mini_allocator_add_aus_preserves_all_aus(pre.mini_allocator, lbl.arrow_InternalAlloc_allocs());
        assert(post.mini_allocator.all_aus()
            == pre.mini_allocator.all_aus() + lbl.arrow_InternalAlloc_allocs());
        assert(post.indexed_aus_not_all_pages_free()) by {
            let allocs = lbl.arrow_InternalAlloc_allocs();
            assert(cj_lsn_au_index(post.journal) == cj_lsn_au_index(pre.journal));
            assert(allocs.disjoint(cj_lsn_au_index(pre.journal).values()));
            assert forall |au: AU| {
                &&& #[trigger] cj_lsn_au_index(post.journal).values().contains(au)
                &&& post.mini_allocator.allocs.contains_key(au)
            } implies !post.mini_allocator.allocs[au].all_pages_free() by {
                assert(!allocs.contains(au));
                assert(pre.mini_allocator.allocs.contains_key(au));
                assert(post.mini_allocator.allocs[au] == pre.mini_allocator.allocs[au]);
                assert(!pre.mini_allocator.allocs[au].all_pages_free());
            }
        }
    }

    #[inductive(mini_allocator_prune)]
    fn mini_allocator_prune_inductive(pre: Self, post: Self, lbl: Label, new_disk: CachingDisk::State) {
        CachingDisk::State::inv_next(pre.disk, post.disk, CachingDisk::Label::Forget{aus: lbl.arrow_InternalAlloc_deallocs()});
        CachingDisk::State::forget_effect(pre.disk, post.disk, lbl.arrow_InternalAlloc_deallocs());
        pre.mini_allocator.prune_preserves_wf(lbl.arrow_InternalAlloc_prune_aus());
        assert(post.mini_allocator.wf());
        let prune_aus = lbl.arrow_InternalAlloc_prune_aus();
        let deallocs = lbl.arrow_InternalAlloc_deallocs();
        assert(post.journal == pre.journal);
        assert(post.mini_allocator.all_aus() == pre.mini_allocator.all_aus().difference(prune_aus));
        assert(post.indexed_aus_not_all_pages_free()) by {
            assert(cj_lsn_au_index(post.journal) == cj_lsn_au_index(pre.journal));
            assert forall |au: AU| {
                &&& #[trigger] cj_lsn_au_index(post.journal).values().contains(au)
                &&& post.mini_allocator.allocs.contains_key(au)
            } implies !post.mini_allocator.allocs[au].all_pages_free() by {
                assert(!prune_aus.contains(au));
                assert(pre.mini_allocator.allocs.contains_key(au));
                assert(post.mini_allocator.allocs[au] == pre.mini_allocator.allocs[au]);
                assert(!pre.mini_allocator.allocs[au].all_pages_free());
            }
        }
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
            CachingDiskJournal::Step::mini_allocator_fill(new_disk) => {
                CachingDiskJournal::State::mini_allocator_fill_inductive(pre, post, lbl, new_disk);
            },
            CachingDiskJournal::Step::mini_allocator_prune(new_disk) => {
                CachingDiskJournal::State::mini_allocator_prune_inductive(pre, post, lbl, new_disk);
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
        let base = Self{
            journal: CachedJournal::State{
                snapshot,
                status: Option::None,
            },
            disk: Self::disk_from_persistent(persistent),
            mini_allocator: MiniAllocator::empty(),
            au_page_bounds: Map::empty(),
        };
        Self{
            au_page_bounds: base.journal_disk_view().loose_build_au_page_bounds_au_walk(
                base.journal.snapshot.freshest_rec(),
                snapshot.first(),
            ),
            ..base
        }
    }

    pub proof fn load_from_persistent_accessible_aus(
        snapshot: JournalSnapshot,
        persistent: Map<Address, RawPage>,
    )
        requires
            Self::load_from_persistent(snapshot, persistent).inv(),
            Self::load_from_persistent(snapshot, persistent).backing_journal_image().valid_image(),
        ensures
            Self::load_from_persistent(snapshot, persistent).accessible_aus()
                <= to_aus(persistent.dom()),
    {
        let loaded = Self::load_from_persistent(snapshot, persistent);
        assert(loaded.mini_allocator.all_aus() =~= Set::<AU>::empty());
        assert(loaded.disk.visible().dom() == persistent.dom());
    }

    pub open spec fn visible_lsn_au_index(self) -> LsnAUIndex {
        if self.journal.status is Some {
            cj_lsn_au_index(self.journal)
        } else {
            self.journal_disk_view().loose_build_lsn_au_index_au_walk(
                self.journal.snapshot.freshest_rec(),
                self.journal.snapshot.first(),
            )
        }
    }

    pub open spec fn journal_disk_view(self) -> DiskView {
        DiskView{
            boundary_lsn: cj_boundary_lsn(self.journal),
            entries: to_journal_records(self.disk.visible()),
        }
    }

    pub open spec fn journal_backing_tj(self) -> TruncatedJournal {
        TruncatedJournal{
            freshest_rec: cj_freshest_rec(self.journal),
            disk_view: self.journal_disk_view(),
        }
    }

    pub open spec fn journal_tj(self) -> TruncatedJournal {
        TruncatedJournal{
            freshest_rec: cj_freshest_rec(self.journal),
            disk_view: self.journal_disk_view().path_build_tight(cj_freshest_rec(self.journal)),
        }
    }

    pub open spec fn accessible_aus(self) -> Set<AU> {
        if self.journal.status is Some {
            self.visible_lsn_au_index().values() + self.mini_allocator.all_aus()
        } else {
            to_aus(self.disk.visible().dom()) + self.mini_allocator.all_aus()
        }
    }

    pub open spec fn clean_watermark_pages(self) -> Set<Address> {
        if self.journal.status is Some {
            Set::new(|addr: Address| {
                &&& self.journal_tj().disk_view.entries.contains_key(addr)
                &&& self.journal_tj().disk_view.boundary_lsn
                    < self.journal_tj().disk_view.entries[addr].message_seq.seq_end
                &&& self.journal_tj().disk_view.entries[addr].message_seq.seq_end
                    <= self.journal.clean_watermark()
            })
        } else {
            self.journal_tj().disk_view.entries.dom()
        }
    }

    pub open spec fn frozen_domain(self, snapshot: JournalSnapshot) -> Set<Address> {
        let frozen_index = self.lsn_au_index_or_empty().restrict(self.frozen_lsns(snapshot));
        self.journal_tj().disk_view.tight_domain(
            frozen_index,
            snapshot.freshest_rec(),
        )
    }

    pub open spec fn frozen_loose_domain(self, snapshot: JournalSnapshot) -> Set<Address> {
        let frozen_index = self.lsn_au_index_or_empty().restrict(self.frozen_lsns(snapshot));
        addresses_in_aus(frozen_index.values())
    }

    pub open spec fn frozen_prefix_domain(self, snapshot: JournalSnapshot) -> Set<Address> {
        let tight = (JournalImage{tj: self.frozen_tj(snapshot), first: snapshot.first()}).tight_tj();
        let tight_bounds = tight.disk_view.build_au_page_bounds_au_walk(
            tight.freshest_rec,
            snapshot.first(),
        );
        Set::new(|addr: Address| {
            &&& self.frozen_loose_domain(snapshot).contains(addr)
            &&& tight_bounds.contains_key(addr.au)
            &&& addr.page <= tight_bounds[addr.au]
        })
    }

    pub open spec fn clean_watermark_durable(self) -> bool {
        self.disk.addrs_clean_or_evictable(self.clean_watermark_pages())
    }

    pub proof fn persistent_visible_eq_on_clean_or_evictable(self, addrs: Set<Address>)
        requires
            self.inv(),
            self.disk.addrs_clean_or_evictable(addrs),
        ensures
            self.disk.persistent.restrict(addrs) == self.disk.visible().restrict(addrs),
    {
        assert_maps_equal!(
            self.disk.persistent.restrict(addrs),
            self.disk.visible().restrict(addrs),
            addr => {
                if addrs.contains(addr) {
                    if self.disk.cache.contains_key(addr) {
                        assert(self.disk.addrs_clean_or_evictable(addrs));
                        assert(self.disk.status.contains_key(addr));
                        assert(self.disk.status[addr] == PageStatus::Clean);
                        assert(self.disk.persistent.contains_key(addr));
                        assert(self.disk.persistent[addr] == self.disk.cache[addr]);
                    }
                }
            }
        );
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

    pub proof fn load_index_preserves_accessible_aus(
        pre: Self,
        post: Self,
        discovered_aus: Set<AU>,
    )
        requires
            pre.inv(),
            CachingDiskJournal::State::next(
                pre,
                post,
                CachingDiskJournal::Label::LoadIndex{discovered_aus},
            ),
        ensures
            post.accessible_aus() <= pre.accessible_aus(),
    {
        let lbl = CachingDiskJournal::Label::LoadIndex{discovered_aus};
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskJournal::Step::load_index(new_journal, reads) => {
                reveal(CachingDiskJournal::State::load_index);
                let disk_lbl = CachingDisk::Label::Access{reads, writes: Map::empty()};
                CachingDisk::State::access_effect(pre.disk, pre.disk, reads, Map::empty());
                CachedJournal::State::load_index_effect(
                    pre.journal,
                    post.journal,
                    to_journal_records(reads),
                    discovered_aus,
                );
                CachedJournal::State::load_index_discovered_aus_in_reads(
                    pre.journal,
                    post.journal,
                    to_journal_records(reads),
                    discovered_aus,
                );
                assert(pre.journal.status is None);
                assert(post.journal.status is Some);
                assert(post.disk == pre.disk);
                assert(post.mini_allocator == pre.mini_allocator);
                assert(to_journal_records(reads).dom() == reads.dom()) by {
                    assert_maps_equal!(to_journal_records(reads), to_journal_records(reads));
                    assert forall |addr: Address| #[trigger] to_journal_records(reads).contains_key(addr)
                        <==> reads.contains_key(addr) by { }
                }
                assert(reads.dom() <= pre.disk.cache.dom()) by {
                    assert(reads <= pre.disk.cache);
                    assert forall |addr: Address| #[trigger] reads.dom().contains(addr)
                        implies pre.disk.cache.dom().contains(addr) by {
                        assert(reads.contains_key(addr));
                    }
                };
                assert(pre.disk.cache.dom() <= pre.disk.visible().dom()) by {
                    assert forall |addr: Address| #[trigger] pre.disk.cache.dom().contains(addr)
                        implies pre.disk.visible().dom().contains(addr) by {
                        assert(pre.disk.cache.contains_key(addr));
                        assert(pre.disk.visible().contains_key(addr));
                    }
                };
                to_aus_preserves_lte(reads.dom(), pre.disk.cache.dom());
                to_aus_preserves_lte(pre.disk.cache.dom(), pre.disk.visible().dom());
                assert(discovered_aus <= to_aus(pre.disk.visible().dom()));
                assert forall |au: AU| #[trigger] post.accessible_aus().contains(au)
                    implies pre.accessible_aus().contains(au) by {
                    if post.mini_allocator.all_aus().contains(au) {
                        assert(pre.mini_allocator.all_aus().contains(au));
                    } else {
                        assert(post.visible_lsn_au_index().values().contains(au));
                        assert(cj_lsn_au_index(post.journal).values().contains(au));
                        assert(post.journal.status.unwrap().lsn_au_index.values().contains(au));
                        assert(discovered_aus.contains(au));
                        assert(to_aus(pre.disk.visible().dom()).contains(au));
                    }
                }
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

    pub proof fn frozen_loose_subdomain_accessible(
        self,
        snapshot: JournalSnapshot,
        addrs: Set<Address>,
    )
        requires
            self.inv(),
            addrs <= self.frozen_loose_domain(snapshot),
            addrs <= self.journal_disk_view().entries.dom(),
        ensures
            to_aus(addrs) <= self.accessible_aus(),
    {
        let frozen_index = self.lsn_au_index_or_empty().restrict(self.frozen_lsns(snapshot));
        assert(frozen_index.values() <= self.lsn_au_index_or_empty().values());
        assert forall |au: AU|
            #[trigger] to_aus(addrs).contains(au)
            implies self.accessible_aus().contains(au) by {
            let addr = choose |addr: Address|
                addrs.contains(addr) && addr.au == au;
            if self.journal.status is Some {
                assert(addrs.contains(addr));
                assert(self.frozen_loose_domain(snapshot).contains(addr));
                assert(addresses_in_aus(frozen_index.values()).contains(addr));
                assert(frozen_index.values().contains(addr.au));
                assert(self.lsn_au_index_or_empty().values().contains(addr.au));
                assert(self.accessible_aus().contains(addr.au));
            } else {
                assert(self.journal_disk_view().entries.contains_key(addr));
                assert(self.disk.visible().contains_key(addr)) by {
                    assert(to_journal_records(self.disk.visible()).contains_key(addr));
                }
                to_aus_domain(self.disk.visible().dom());
                assert(to_aus(self.disk.visible().dom()).contains(addr.au));
                assert(self.accessible_aus().contains(addr.au));
            }
        }
    }

    pub proof fn frozen_loose_domain_persistent_aus_accessible(self, snapshot: JournalSnapshot)
        requires
            self.inv(),
        ensures
            to_aus(self.disk.persistent.restrict(self.frozen_loose_domain(snapshot)).dom())
                <= self.accessible_aus(),
    {
        let addrs = self.disk.persistent.restrict(self.frozen_loose_domain(snapshot)).dom();
        assert(addrs <= self.frozen_loose_domain(snapshot)) by {
            assert forall |addr: Address| #[trigger] addrs.contains(addr)
                implies self.frozen_loose_domain(snapshot).contains(addr) by {
                assert(self.disk.persistent.restrict(self.frozen_loose_domain(snapshot)).contains_key(addr));
            }
        }
        assert(addrs <= self.journal_disk_view().entries.dom()) by {
            assert forall |addr: Address| #[trigger] addrs.contains(addr)
                implies self.journal_disk_view().entries.dom().contains(addr) by {
                assert(self.disk.persistent.restrict(self.frozen_loose_domain(snapshot)).contains_key(addr));
                assert(self.disk.persistent.contains_key(addr));
                assert(self.disk.visible().contains_key(addr));
                assert(to_journal_records(self.disk.visible()).contains_key(addr));
            }
        }
        self.frozen_loose_subdomain_accessible(snapshot, addrs);
    }

    pub proof fn frozen_tj_aus_accessible(self, snapshot: JournalSnapshot)
        requires
            self.inv(),
        ensures
            to_aus(self.frozen_tj(snapshot).disk_view.entries.dom()) <= self.accessible_aus(),
    {
        let addrs = self.frozen_tj(snapshot).disk_view.entries.dom();
        assert(addrs <= self.frozen_loose_domain(snapshot)) by {
            assert forall |addr: Address| #[trigger] addrs.contains(addr)
                implies self.frozen_loose_domain(snapshot).contains(addr) by {
                assert(self.frozen_tj(snapshot).disk_view.entries.contains_key(addr));
            }
        }
        assert(addrs <= self.journal_disk_view().entries.dom()) by {
            assert forall |addr: Address| #[trigger] addrs.contains(addr)
                implies self.journal_disk_view().entries.dom().contains(addr) by {
                assert(self.frozen_tj(snapshot).disk_view.entries.contains_key(addr));
            }
        }
        self.frozen_loose_subdomain_accessible(snapshot, addrs);
    }

    pub proof fn lsn_au_index_or_empty_matches_full(self)
        requires
            self.visible_journal_structure(),
        ensures
            self.lsn_au_index_or_empty()
                == self.journal_tj().disk_view.build_lsn_au_index_au_walk(
                    self.journal_tj().freshest_rec,
                    self.journal.snapshot.first(),
                ),
    {
        assert(self.visible_journal_structure());
        assert(self.lsn_au_index_or_empty() == self.visible_lsn_au_index());
    }

    pub proof fn interpreted_tj_matches(self)
        ensures
            self.i().tj().disk_view == self.journal_tj().disk_view,
            self.i().tj() == self.journal_tj(),
    {
        let aj = self.i();
        assert(aj.disk_view == self.journal_disk_view());
        assert(aj.freshest_rec == cj_freshest_rec(self.journal));
        assert(aj.tj() == self.journal_tj());
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
            deallocs.disjoint(post.accessible_aus()),
    {
        let lbl = CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus};
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskJournal::Step::mini_allocator_fill(new_disk) => {
                assert(CachingDiskJournal::State::mini_allocator_fill(pre, post, lbl, new_disk)) by {
                    reveal(CachingDiskJournal::State::mini_allocator_fill);
                }
                assert(deallocs == Set::<AU>::empty());
                mini_allocator_add_aus_preserves_all_aus(pre.mini_allocator, allocs);
                assert(post.mini_allocator.all_aus() == pre.mini_allocator.all_aus() + allocs);
                assert(post.journal == pre.journal);
                assert(post.disk == new_disk);
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
            CachingDiskJournal::Step::mini_allocator_prune(new_disk) => {
                assert(CachingDiskJournal::State::mini_allocator_prune(pre, post, lbl, new_disk)) by {
                    reveal(CachingDiskJournal::State::mini_allocator_prune);
                }
                CachingDisk::State::forget_effect(pre.disk, post.disk, deallocs);
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
                assert(deallocs.disjoint(post.accessible_aus())) by {
                    assert forall |au: AU| #[trigger] deallocs.contains(au)
                        implies !post.accessible_aus().contains(au) by {
                        if post.accessible_aus().contains(au) {
                            if post.mini_allocator.all_aus().contains(au) {
                                assert(post.mini_allocator.all_aus()
                                    == pre.mini_allocator.all_aus().difference(prune_aus));
                                assert(!post.mini_allocator.all_aus().contains(au));
                                assert(false);
                            } else {
                                assert(post.lsn_au_index_or_empty().values().contains(au));
                                assert(post.journal == pre.journal);
                                assert(post.lsn_au_index_or_empty()
                                    == pre.lsn_au_index_or_empty());
                                assert(pre.lsn_au_index_or_empty().values().contains(au));
                                assert(pre.mini_allocator.allocs.contains_key(au));
                                assert(pre.mini_allocator.allocs[au].all_pages_free());
                                assert(!pre.mini_allocator.allocs[au].all_pages_free()) by {
                                    assert(pre.indexed_aus_not_all_pages_free());
                                }
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

    pub open spec fn lsn_au_index_or_empty(self) -> LsnAUIndex {
        self.visible_lsn_au_index()
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

    pub open spec fn frozen_metadata(self, snapshot: JournalSnapshot) -> JournalMetadata {
        JournalMetadata{
            boundary_lsn: snapshot.boundary_lsn,
            seq_end: self.frozen_seq_end(snapshot),
            freshest_rec: snapshot.freshest_rec(),
            first: snapshot.first(),
        }
    }

    pub open spec fn frozen_tj(self, snapshot: JournalSnapshot) -> TruncatedJournal {
        TruncatedJournal{
            freshest_rec: snapshot.freshest_rec(),
            disk_view: DiskView{
                boundary_lsn: snapshot.boundary_lsn,
                entries: self.journal_disk_view().entries.restrict(self.frozen_loose_domain(snapshot)),
            },
        }
    }

    pub open spec fn frozen_snapshot_preserved_by(
        self,
        post: Self,
        snapshot: JournalSnapshot,
        seq_end: LSN,
    ) -> bool
    {
        &&& post.frozen_snapshot_valid(snapshot, seq_end)
        &&& post.frozen_tj(snapshot) == self.frozen_tj(snapshot)
    }

    pub open spec fn frozen_snapshot_valid(self, snapshot: JournalSnapshot, seq_end: LSN) -> bool
    {
        &&& self.journal.status is Some
        &&& seq_end == self.frozen_seq_end(snapshot)
        &&& self.journal.seq_start() <= snapshot.boundary_lsn
        &&& snapshot.boundary_lsn <= seq_end
        &&& snapshot.freshest_rec() is None ==> {
            &&& snapshot.first() == 0
            &&& snapshot.boundary_lsn == seq_end
            &&& snapshot.boundary_lsn <= self.journal.seq_end()
        }
        &&& snapshot.freshest_rec() is Some ==> {
            let root = snapshot.freshest_rec().unwrap();
            &&& snapshot.boundary_lsn < seq_end
            &&& self.lsn_au_index_or_empty().contains_key(snapshot.boundary_lsn)
            &&& self.lsn_au_index_or_empty()[snapshot.boundary_lsn] == snapshot.first()
            &&& self.journal_disk_view().entries.contains_key(root)
            &&& self.journal_disk_view().entries[root].message_seq.seq_end == seq_end
            &&& self.au_page_bounds.contains_key(root.au)
            &&& root.page <= self.au_page_bounds[root.au]
        }
    }

    pub open spec fn i(self) -> AllocationJournal::State {
        AllocationJournal::State{
            freshest_rec: cj_freshest_rec(self.journal),
            unmarshalled_tail: if self.journal.status is Some {
                cj_unmarshalled_tail(self.journal)
            } else {
                MsgHistory::empty_history_at(self.journal_tj().seq_end())
            },
            disk_view: self.journal_disk_view(),
            lsn_au_index: self.lsn_au_index_or_empty(),
            au_page_bounds: self.au_page_bounds,
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

        let full_index = cj_lsn_au_index(self.journal);

        assert(self.journal.status is Some);

        if frozen.freshest_rec() is Some {
            let root = frozen.freshest_rec().unwrap();
            let frozen_seq_end = to_journal_records(reads)[root].message_seq.seq_end;
            assert(reads.contains_key(root));
            assert(to_journal_records(reads).contains_key(root));
            assert(self.disk.visible().contains_key(root));
            assert(self.journal_disk_view().entries.contains_key(root));
            assert(to_journal_records(reads)[root] == self.journal_disk_view().entries[root]) by {
                assert(reads <= self.disk.cache);
                assert(self.disk.visible()[root] == self.disk.cache[root]);
            }
            assert(frozen_seq_end == self.frozen_seq_end(frozen));
            assert(frozen.boundary_lsn < frozen_seq_end);
            assert(full_index.contains_key(frozen.boundary_lsn));
            assert(full_index[frozen.boundary_lsn] == frozen.first());
        }

        assert(frozen.boundary_lsn <= self.journal.seq_end());
        assert(self.frozen_snapshot_valid(frozen, seq_end));
    }

    pub proof fn load_index_visible_unchanged(
        pre: Self,
        post: Self,
        discovered_aus: Set<AU>,
    )
        requires
            CachingDiskJournal::State::next(
                pre,
                post,
                CachingDiskJournal::Label::LoadIndex{discovered_aus},
            ),
        ensures
            post.journal_disk_view() == pre.journal_disk_view(),
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
                assert(post.journal_disk_view().entries == pre.journal_disk_view().entries);
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn observe_clean_aus_visible_unchanged(
        pre: Self,
        post: Self,
        aus: Set<AU>,
    )
        requires
            CachingDiskJournal::State::next(
                pre,
                post,
                CachingDiskJournal::Label::ObserveCleanAUs{aus},
            ),
        ensures
            post.journal_disk_view() == pre.journal_disk_view(),
    {
        let lbl = CachingDiskJournal::Label::ObserveCleanAUs{aus};
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskJournal::Step::observe_clean_aus(new_journal) => {
                reveal(CachingDiskJournal::State::observe_clean_aus);
                CachedJournal::State::observe_clean_aus_effect(
                    pre.journal,
                    post.journal,
                    aus,
                );
                assert(post.disk == pre.disk);
                assert(post.journal.snapshot == pre.journal.snapshot);
                assert(post.journal_disk_view().entries == pre.journal_disk_view().entries);
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn put_loaded_status_and_clean_watermark_unchanged(
        pre: Self,
        post: Self,
        messages: MsgHistory,
    )
        requires
            pre.journal.status is Some,
            CachingDiskJournal::State::next(
                pre,
                post,
                CachingDiskJournal::Label::Put{messages},
            ),
        ensures
            post.journal.status is Some,
            post.journal.clean_watermark() == pre.journal.clean_watermark(),
            post.disk == pre.disk,
            post.mini_allocator == pre.mini_allocator,
            post.journal.snapshot == pre.journal.snapshot,
            post.journal_disk_view() == pre.journal_disk_view(),
    {
        let lbl = CachingDiskJournal::Label::Put{messages};
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskJournal::Step::put(new_journal) => {
                reveal(CachingDiskJournal::State::put);
                CachedJournal::State::put_effect(pre.journal, post.journal, messages);
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn load_index_requires_unloaded(
        pre: Self,
        post: Self,
        discovered_aus: Set<AU>,
    )
        requires
            CachingDiskJournal::State::next(
                pre,
                post,
                CachingDiskJournal::Label::LoadIndex{discovered_aus},
            ),
        ensures
            pre.journal.status is None,
    {
        let lbl = CachingDiskJournal::Label::LoadIndex{discovered_aus};
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskJournal::Step::load_index(new_journal, reads) => {
                reveal(CachingDiskJournal::State::load_index);
                reveal(CachedJournal::State::next);
                reveal(CachedJournal::State::next_by);
                let journal_lbl = CachedJournal::Label::LoadIndex{
                    reads: to_journal_records(reads),
                    discovered_aus,
                };
                let journal_step = choose |step: CachedJournal::Step|
                    CachedJournal::State::next_by(pre.journal, post.journal, journal_lbl, step);
                match journal_step {
                    CachedJournal::Step::load_index(_, _) => {
                        reveal(CachedJournal::State::load_index);
                    },
                    _ => {
                        assert(false);
                    },
                }
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn observe_clean_aus_loaded_status_and_clean_watermark_monotonic(
        pre: Self,
        post: Self,
        aus: Set<AU>,
    )
        requires
            pre.journal.status is Some,
            CachingDiskJournal::State::next(
                pre,
                post,
                CachingDiskJournal::Label::ObserveCleanAUs{aus},
            ),
        ensures
            post.journal.status is Some,
            pre.journal.clean_watermark() <= post.journal.clean_watermark(),
            post.disk == pre.disk,
            post.mini_allocator == pre.mini_allocator,
            post.journal.snapshot == pre.journal.snapshot,
            post.journal_disk_view() == pre.journal_disk_view(),
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
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn commit_prepared_effect(
        state: Self,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            CachingDiskJournal::State::next(
                state,
                state,
                CachingDiskJournal::Label::CommitPrepared{frozen, seq_end},
            ),
        ensures
            state.journal.status is Some,
            frozen.freshest_rec() is Some ==> seq_end <= state.journal.clean_watermark(),
    {
        let lbl = CachingDiskJournal::Label::CommitPrepared{frozen, seq_end};
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(state, state, lbl, step);
        match step {
            CachingDiskJournal::Step::commit_prepared() => {
                reveal(CachingDiskJournal::State::commit_prepared);
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn internal_loaded_status_and_clean_watermark_monotonic(
        pre: Self,
        post: Self,
    )
        requires
            pre.inv(),
            pre.journal.status is Some,
            CachingDiskJournal::State::next(pre, post, CachingDiskJournal::Label::Internal),
        ensures
            post.journal.status is Some,
            pre.journal.clean_watermark() <= post.journal.clean_watermark(),
    {
        let lbl = CachingDiskJournal::Label::Internal;
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskJournal::Step::caching_disk_internal(new_disk) => {
                reveal(CachingDiskJournal::State::caching_disk_internal);
                assert(post.journal == pre.journal);
            },
            CachingDiskJournal::Step::journal_marshal(new_journal, new_disk, addr, writes) => {
                reveal(CachingDiskJournal::State::journal_marshal);
                reveal(CachedJournal::State::next);
                reveal(CachedJournal::State::next_by);
                let journal_lbl = CachedJournal::Label::JournalMarshal{
                    writes: to_journal_records(writes),
                };
                let journal_step = choose |step: CachedJournal::Step|
                    CachedJournal::State::next_by(pre.journal, post.journal, journal_lbl, step);
                match journal_step {
                    CachedJournal::Step::internal_journal_marshal(cut, hidden_addr) => {
                        reveal(CachedJournal::State::internal_journal_marshal);
                    },
                    _ => {
                        assert(false);
                    },
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

    pub proof fn internal_alloc_preserves_journal(
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
            post.journal == pre.journal,
    {
        let lbl = CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus};
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskJournal::Step::mini_allocator_fill(new_disk) => {
                reveal(CachingDiskJournal::State::mini_allocator_fill);
            },
            CachingDiskJournal::Step::mini_allocator_prune(new_disk) => {
                reveal(CachingDiskJournal::State::mini_allocator_prune);
            },
            _ => {
                assert(false);
            },
        }
    }


}

}
