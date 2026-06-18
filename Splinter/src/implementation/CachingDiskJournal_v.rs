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
use crate::disk::GenericDisk_v::{Address, AU, Pointer, Ranking, to_aus, to_aus_preserves_lte};
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

pub open spec fn snapshot_walk_ptr(
    records: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
) -> Pointer
    decreases depth
{
    if depth == 0 {
        root
    } else {
        let prev = snapshot_walk_ptr(records, boundary_lsn, root, (depth - 1) as nat);
        if prev is Some && records.contains_key(prev.unwrap()) {
            records[prev.unwrap()].cropped_prior(boundary_lsn)
        } else {
            None
        }
    }
}

pub open spec fn snapshot_walk_domain(
    records: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
) -> Set<Address> {
    Set::new(|addr: Address| exists |depth: nat|
        snapshot_walk_ptr(records, boundary_lsn, root, depth) == Some(addr))
}

pub proof fn snapshot_walk_restrict_domain_same(
    records: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
)
    ensures
        snapshot_walk_ptr(
            records.restrict(snapshot_walk_domain(records, boundary_lsn, root)),
            boundary_lsn,
            root,
            depth,
        ) == snapshot_walk_ptr(records, boundary_lsn, root, depth),
    decreases depth,
{
    let domain = snapshot_walk_domain(records, boundary_lsn, root);
    let restricted = records.restrict(domain);
    if depth == 0 {
    } else {
        snapshot_walk_restrict_domain_same(records, boundary_lsn, root, (depth - 1) as nat);
        let prev = snapshot_walk_ptr(records, boundary_lsn, root, (depth - 1) as nat);
        assert(snapshot_walk_ptr(restricted, boundary_lsn, root, (depth - 1) as nat) == prev);
        if prev is Some {
            let prev_addr = prev.unwrap();
            assert(domain.contains(prev_addr)) by {
                assert(snapshot_walk_ptr(records, boundary_lsn, root, (depth - 1) as nat)
                    == Some(prev_addr));
            }
            assert(restricted.contains_key(prev_addr) == records.contains_key(prev_addr));
            if records.contains_key(prev_addr) {
                assert(restricted[prev_addr] == records[prev_addr]);
            }
        }
    }
}

pub proof fn snapshot_walk_domain_restrict_domain_same(
    records: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
)
    ensures
        snapshot_walk_domain(
            records.restrict(snapshot_walk_domain(records, boundary_lsn, root)),
            boundary_lsn,
            root,
        ) =~= snapshot_walk_domain(records, boundary_lsn, root),
{
    let domain = snapshot_walk_domain(records, boundary_lsn, root);
    let restricted = records.restrict(domain);
    assert forall |addr: Address|
        #[trigger] snapshot_walk_domain(restricted, boundary_lsn, root).contains(addr)
            <==> domain.contains(addr)
    by {
        if snapshot_walk_domain(restricted, boundary_lsn, root).contains(addr) {
            let depth = choose |depth: nat|
                snapshot_walk_ptr(restricted, boundary_lsn, root, depth) == Some(addr);
            snapshot_walk_restrict_domain_same(records, boundary_lsn, root, depth);
            assert(snapshot_walk_ptr(records, boundary_lsn, root, depth) == Some(addr));
        }
        if domain.contains(addr) {
            let depth = choose |depth: nat|
                snapshot_walk_ptr(records, boundary_lsn, root, depth) == Some(addr);
            snapshot_walk_restrict_domain_same(records, boundary_lsn, root, depth);
            assert(snapshot_walk_ptr(restricted, boundary_lsn, root, depth) == Some(addr));
        }
    }
}

pub proof fn snapshot_walk_ptr_in_disk_view(
    dv: DiskView,
    root: Pointer,
    depth: nat,
)
    requires
        dv.wf(),
        dv.acyclic(),
        dv.is_nondangling_pointer(root),
    ensures
        snapshot_walk_ptr(dv.entries, dv.boundary_lsn, root, depth) is Some ==>
            dv.entries.contains_key(snapshot_walk_ptr(dv.entries, dv.boundary_lsn, root, depth).unwrap()),
    decreases depth,
{
    if depth == 0 {
        if root is Some {
            assert(dv.entries.contains_key(root.unwrap()));
        }
    } else {
        snapshot_walk_ptr_in_disk_view(dv, root, (depth - 1) as nat);
        let prev = snapshot_walk_ptr(dv.entries, dv.boundary_lsn, root, (depth - 1) as nat);
        if prev is Some {
            assert(dv.entries.contains_key(prev.unwrap()));
            let next = dv.entries[prev.unwrap()].cropped_prior(dv.boundary_lsn);
            if next is Some {
                assert(dv.nondangling_pointers());
                assert(dv.entries.contains_key(next.unwrap()));
            }
        }
    }
}

pub proof fn snapshot_walk_ptr_step(
    records: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
)
    ensures
        root is Some && records.contains_key(root.unwrap()) ==>
            snapshot_walk_ptr(records, boundary_lsn, root, depth + 1)
            == snapshot_walk_ptr(
                records,
                boundary_lsn,
                records[root.unwrap()].cropped_prior(boundary_lsn),
                depth,
            ),
    decreases depth,
{
    if depth > 0 && root is Some && records.contains_key(root.unwrap()) {
        let next = records[root.unwrap()].cropped_prior(boundary_lsn);
        snapshot_walk_ptr_step(
            records,
            boundary_lsn,
            root,
            (depth - 1) as nat,
        );
        assert(snapshot_walk_ptr(records, boundary_lsn, root, depth)
            == snapshot_walk_ptr(records, boundary_lsn, next, (depth - 1) as nat));
        let prev = snapshot_walk_ptr(records, boundary_lsn, root, depth);
        let next_prev = snapshot_walk_ptr(records, boundary_lsn, next, (depth - 1) as nat);
        assert(prev == next_prev);
    }
}

pub proof fn snapshot_walk_ptr_extends_same(
    base_dv: DiskView,
    records: Map<Address, JournalRecord>,
    root: Pointer,
    depth: nat,
)
    requires
        base_dv.wf(),
        base_dv.acyclic(),
        base_dv.is_nondangling_pointer(root),
        base_dv.entries <= records,
    ensures
        snapshot_walk_ptr(base_dv.entries, base_dv.boundary_lsn, root, depth)
            == snapshot_walk_ptr(records, base_dv.boundary_lsn, root, depth),
    decreases depth,
{
    if depth == 0 {
    } else {
        snapshot_walk_ptr_extends_same(base_dv, records, root, (depth - 1) as nat);
        snapshot_walk_ptr_in_disk_view(base_dv, root, (depth - 1) as nat);
        let prev = snapshot_walk_ptr(base_dv.entries, base_dv.boundary_lsn, root, (depth - 1) as nat);
        assert(prev == snapshot_walk_ptr(records, base_dv.boundary_lsn, root, (depth - 1) as nat));
        if prev is Some {
            let prev_addr = prev.unwrap();
            assert(base_dv.entries.contains_key(prev_addr));
            assert(records.contains_key(prev_addr));
            assert(records[prev_addr] == base_dv.entries[prev_addr]);
        }
    }
}

pub proof fn snapshot_walk_domain_next_subset(
    records: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
)
    requires
        root is Some,
        records.contains_key(root.unwrap()),
    ensures
        snapshot_walk_domain(
            records,
            boundary_lsn,
            records[root.unwrap()].cropped_prior(boundary_lsn),
        ) <= snapshot_walk_domain(records, boundary_lsn, root),
{
    let next = records[root.unwrap()].cropped_prior(boundary_lsn);
    assert forall |addr: Address| #[trigger] snapshot_walk_domain(records, boundary_lsn, next).contains(addr)
        implies snapshot_walk_domain(records, boundary_lsn, root).contains(addr) by {
        let depth = choose |depth: nat|
            snapshot_walk_ptr(records, boundary_lsn, next, depth) == Some(addr);
        snapshot_walk_ptr_step(records, boundary_lsn, root, depth);
        assert(snapshot_walk_ptr(records, boundary_lsn, root, depth + 1) == Some(addr));
    }
}

pub proof fn snapshot_restrict_preserves_path_valid_ranking(
    records: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    ranking: Ranking,
)
    requires
        (DiskView{boundary_lsn, entries: records}).path_valid_ranking(root, ranking),
    ensures
        (DiskView{
            boundary_lsn,
            entries: records.restrict(snapshot_walk_domain(records, boundary_lsn, root)),
        }).path_valid_ranking(root, ranking),
    decreases if root is Some && ranking.contains_key(root.unwrap()) {
        ranking[root.unwrap()] + 1
    } else {
        0
    },
{
    let domain = snapshot_walk_domain(records, boundary_lsn, root);
    let restricted = records.restrict(domain);
    let full_dv = DiskView{boundary_lsn, entries: records};
    let restricted_dv = DiskView{boundary_lsn, entries: restricted};
    match root {
        None => {},
        Some(addr) => {
            reveal_with_fuel(DiskView::path_valid_ranking, 2);
            assert(records.contains_key(addr));
            assert(snapshot_walk_ptr(records, boundary_lsn, root, 0) == Some(addr));
            assert(domain.contains(addr));
            assert(restricted.contains_key(addr));
            assert(restricted[addr] == records[addr]);
            let next = records[addr].cropped_prior(boundary_lsn);
            if next is Some {
                let next_domain = snapshot_walk_domain(records, boundary_lsn, next);
                let next_restricted = records.restrict(next_domain);
                let next_restricted_dv = DiskView{boundary_lsn, entries: next_restricted};
                snapshot_walk_domain_next_subset(records, boundary_lsn, root);
                snapshot_restrict_preserves_path_valid_ranking(records, boundary_lsn, next, ranking);
                assert(next_restricted_dv.path_valid_ranking(next, ranking));
                assert(next_restricted_dv.is_sub_disk(restricted_dv)) by {
                    assert(next_restricted_dv.boundary_lsn == restricted_dv.boundary_lsn);
                    assert(next_restricted_dv.entries <= restricted_dv.entries) by {
                        assert forall |a: Address| #[trigger] next_restricted_dv.entries.contains_key(a)
                            implies restricted_dv.entries.contains_key(a)
                                && next_restricted_dv.entries[a] == restricted_dv.entries[a] by {
                            assert(next_domain.contains(a));
                            assert(domain.contains(a));
                        }
                    }
                }
                restricted_dv.path_valid_ranking_lifts_from_sub_disk(
                    next_restricted_dv,
                    next,
                    ranking,
                );
                assert(restricted_dv.path_valid_ranking(next, ranking));
                assert(restricted.contains_key(next.unwrap()));
                assert(restricted[next.unwrap()] == records[next.unwrap()]);
            }
            reveal_with_fuel(DiskView::path_valid_ranking, 2);
            assert(restricted_dv.path_valid_ranking(root, ranking));
        },
    }
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

    #[invariant]
    pub open spec fn inv(self) -> bool {
        &&& self.journal.wf()
        &&& self.disk.inv()
        &&& self.mini_allocator.wf()
    }

    #[inductive(initialize)]
    pub fn initialize_inductive(post: Self, snapshot: JournalSnapshot, disk: CachingDisk::State) {}

    #[inductive(caching_disk_internal)]
    fn caching_disk_internal_inductive(pre: Self, post: Self, lbl: Label, new_disk: CachingDisk::State) {
        CachingDisk::State::inv_next(pre.disk, post.disk, CachingDisk::Label::Internal{});
        CachingDisk::State::internal_visible_unchanged(pre.disk, post.disk);
        assert(post.journal == pre.journal);
        assert(post.mini_allocator == pre.mini_allocator);
        assert(post.raw_visible_records() == pre.raw_visible_records());
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
            CachedJournal::Step::internal_journal_marshal(cut, hidden_addr) => {},
            _ => { assert(false); },
        }
        assert(pre.journal.status is Some);
        assert(post.journal.status is Some);
        CachingDisk::State::inv_next(pre.disk, post.disk, CachingDisk::Label::Access{reads: Map::empty(), writes});
        assert(pre.mini_allocator.can_allocate(addr));
        assert(pre.mini_allocator.allocate(addr).wf());
        assert(pre.mini_allocator.allocate(addr).allocs.contains_key(addr.au));
        assert(pre.mini_allocator.allocate(addr).allocs[addr.au].reserved.contains(addr));
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
    }

    #[inductive(mini_allocator_fill)]
    pub fn mini_allocator_fill_inductive(pre: Self, post: Self, lbl: Label, new_disk: CachingDisk::State) {
        assert(post.mini_allocator.wf());
        assert(post.journal == pre.journal);
        assert(post.disk == new_disk);
        mini_allocator_add_aus_preserves_all_aus(pre.mini_allocator, lbl.arrow_InternalAlloc_allocs());
        assert(post.mini_allocator.all_aus()
            == pre.mini_allocator.all_aus() + lbl.arrow_InternalAlloc_allocs());
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
            Self::load_from_persistent(snapshot, persistent).visible_journal_structure(),
        ensures
            Self::load_from_persistent(snapshot, persistent).accessible_aus()
                <= to_aus(persistent.dom()),
    {
        let loaded = Self::load_from_persistent(snapshot, persistent);
        loaded.journal_disk_aus_match_index_values();
        assert(loaded.mini_allocator.all_aus() =~= Set::<AU>::empty());
        assert(loaded.disk.visible().dom() == persistent.dom());
        assert(loaded.journal_tj().disk_view.entries <= to_journal_records(loaded.disk.visible())) by {
            assert forall |addr: Address| #[trigger] loaded.journal_tj().disk_view.entries.contains_key(addr)
                implies to_journal_records(loaded.disk.visible()).contains_key(addr)
                    && loaded.journal_tj().disk_view.entries[addr]
                        == to_journal_records(loaded.disk.visible())[addr] by {
                loaded.journal_disk_view().path_build_tight_is_sub_disk(
                    cj_freshest_rec(loaded.journal),
                );
            }
        };
        assert(loaded.journal_tj().disk_view.entries.dom() <= persistent.dom()) by {
            assert forall |addr: Address| #[trigger] loaded.journal_tj().disk_view.entries.dom().contains(addr)
                implies persistent.dom().contains(addr) by {
                assert(to_journal_records(loaded.disk.visible()).contains_key(addr));
                assert(loaded.disk.visible().contains_key(addr));
                assert(persistent.contains_key(addr));
            }
        };
        to_aus_preserves_lte(loaded.journal_tj().disk_view.entries.dom(), persistent.dom());
        assert forall |au: AU| #[trigger] Self::load_from_persistent(
            snapshot,
            persistent,
        ).accessible_aus().contains(au)
            implies to_aus(persistent.dom()).contains(au) by {
            if loaded.mini_allocator.all_aus().contains(au) {
                assert(false);
            } else {
                assert(to_aus(loaded.journal_tj().disk_view.entries.dom()).contains(au));
                assert(loaded.journal_tj().disk_view.entries.dom() <= persistent.dom());
            }
        }
    }

    pub open spec fn raw_visible_records(self) -> Map<Address, JournalRecord> {
        to_journal_records(self.disk.visible())
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

    pub open spec fn visible_records(self) -> Map<Address, JournalRecord> {
        self.journal_disk_view().entries
    }

    pub open spec fn journal_disk_view(self) -> DiskView {
        DiskView{
            boundary_lsn: cj_boundary_lsn(self.journal),
            entries: self.raw_visible_records(),
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
        self.visible_lsn_au_index().values() + self.mini_allocator.all_aus()
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

    pub open spec fn clean_watermark_disk_view(self) -> DiskView {
        DiskView{
            boundary_lsn: self.journal_tj().disk_view.boundary_lsn,
            entries: self.journal_tj().disk_view.entries.restrict(self.clean_watermark_pages()),
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
        Set::new(|addr: Address| {
            &&& self.frozen_loose_domain(snapshot).contains(addr)
            &&& self.au_page_bounds.contains_key(addr.au)
            &&& addr.page <= self.au_page_bounds[addr.au]
        })
    }

    pub open spec fn clean_watermark_durable(self) -> bool {
        self.disk.addrs_clean_or_evictable(self.clean_watermark_pages())
    }

    pub proof fn clean_watermark_persistent_visible_eq(self, addrs: Set<Address>)
        requires
            self.inv(),
            self.clean_watermark_durable(),
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

    pub proof fn clean_watermark_record_eq(self, addr: Address)
        requires
            self.inv(),
            self.unloaded_backing_image_valid(),
            self.clean_watermark_durable(),
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
        assert(addrs.contains(addr));
        assert(self.journal_tj().disk_view.entries.contains_key(addr));
        assert(self.journal_disk_view().path_decodable(cj_freshest_rec(self.journal))) by {
            let image = JournalImage{
                tj: self.journal_backing_tj(),
                first: self.journal.snapshot.first(),
            };
            if self.journal.status is None {
                assert(image.valid_image());
                assert(image.tj.disk_view.path_decodable(image.tj.freshest_rec));
            }
        }
        self.journal_disk_view().path_build_tight_is_sub_disk(cj_freshest_rec(self.journal));
        assert(self.journal_disk_view().entries.contains_key(addr));
        assert(self.disk.visible().contains_key(addr));
        assert(self.disk.visible().restrict(addrs).contains_key(addr));
        assert(self.disk.persistent.restrict(addrs).contains_key(addr));
        assert(self.disk.persistent.contains_key(addr));
        assert(self.disk.visible().contains_key(addr));
        assert(self.disk.persistent[addr] == self.disk.visible()[addr]);
        assert(to_journal_records(self.disk.persistent).contains_key(addr));
        assert(to_journal_records(self.disk.persistent)[addr] == raw_page_to_record(self.disk.persistent[addr]));
        assert(self.journal_disk_view().entries.contains_key(addr));
        assert(self.journal_disk_view().entries[addr] == raw_page_to_record(self.disk.visible()[addr]));
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

    pub proof fn journal_disk_aus_match_index_values(self)
        requires
            self.inv(),
            self.visible_journal_structure(),
        ensures
            to_aus(self.journal_tj().disk_view.entries.dom()) =~= self.lsn_au_index_or_empty().values(),
            to_aus(self.journal_tj().disk_view.entries.dom()) <= self.accessible_aus(),
            self.lsn_au_index_or_empty().values() <= to_aus(self.journal_tj().disk_view.entries.dom()),
    {
        let tj = self.journal_tj();
        let index = self.lsn_au_index_or_empty();
        self.lsn_au_index_or_empty_matches_full();
        assert(tj.disk_view.domain_tight_wrt_index(index, tj.freshest_rec));

        assert(to_aus(tj.disk_view.entries.dom()) <= index.values()) by {
            assert forall |au: AU| #[trigger] to_aus(tj.disk_view.entries.dom()).contains(au)
                implies index.values().contains(au) by {
                let addr = choose |addr: Address|
                    tj.disk_view.entries.dom().contains(addr) && addr.au == au;
                assert(tj.disk_view.entries.dom().contains(addr));
                assert(index.values().contains(addr.au));
            }
        };
        assert(index.values() <= to_aus(tj.disk_view.entries.dom())) by {
            assert forall |au: AU| #[trigger] index.values().contains(au)
                implies to_aus(tj.disk_view.entries.dom()).contains(au) by {
                assert(self.visible_journal_structure());
            }
        };
        assert(to_aus(tj.disk_view.entries.dom()) <= self.accessible_aus()) by {
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
            pre.visible_journal_structure(),
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
            pre.visible_journal_structure(),
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
                                pre.journal_disk_aus_match_index_values();
                                assert(to_aus(pre.journal_tj().disk_view.entries.dom()).contains(au));
                                let addr = choose |addr: Address|
                                    pre.journal_tj().disk_view.entries.dom().contains(addr)
                                        && addr.au == au;
                                assert(pre.journal_tj().disk_view.entries.dom().contains(addr));
                                assert(addr.wf()) by {
                                    assert(pre.visible_journal_structure());
                                    assert(pre.journal_tj().disk_view.wf_addrs());
                                }
                                assert(!pre.mini_allocator.can_allocate(addr)) by {
                                    assert(AllocationJournal::State::disk_domain_not_free(
                                        pre.journal_tj().disk_view,
                                        pre.mini_allocator,
                                    ));
                                }
                                assert(pre.mini_allocator.can_allocate(addr)) by {
                                    assert(pre.mini_allocator.allocs.contains_key(au));
                                    assert(pre.mini_allocator.allocs[au].all_pages_free());
                                    assert(pre.mini_allocator.allocs[au].has_no_observed_pages());
                                    assert(pre.mini_allocator.allocs[au].has_no_outstanding_refs());
                                    assert(!pre.mini_allocator.allocs[au].observed.contains(addr));
                                    assert(!pre.mini_allocator.allocs[au].reserved.contains(addr));
                                    assert(pre.mini_allocator.allocs[au].is_free_addr(addr));
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
        self.i().frozen_tj(self.frozen_metadata(snapshot))
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
            assert(self.visible_records().contains_key(root));
            assert(to_journal_records(reads)[root] == self.visible_records()[root]) by {
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
                assert(post.raw_visible_records() == pre.raw_visible_records());
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
                assert(post.raw_visible_records() == pre.raw_visible_records());
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn internal_extends_journal_view(pre: Self, post: Self)
        requires
            pre.inv(),
            pre.i().inv(),
            pre.i().semantic_inv(),
            pre.visible_journal_structure(),
            pre.journal.status is Some ==> pre.loaded_journal_structure(),
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
                let pre_tight_dv = pre.journal_tj().disk_view;
                let post_backing_dv = post.journal_disk_view();
                assert(pre.journal_tj().decodable());
                assert(pre_tight_dv.wf());
                assert(pre_tight_dv.acyclic());
                assert(pre_tight_dv.is_nondangling_pointer(pre.journal_tj().freshest_rec));
                pre.interpreted_tj_matches();
                let pre_aj = pre.i();
                pre_aj.tj_view_is_valid_acyclic_subdisk();
                assert(pre_aj.disk_view == pre.journal_disk_view());
                assert(pre_aj.tj().disk_view == pre_tight_dv);
                assert(pre_tight_dv.is_sub_disk(pre.journal_disk_view()));
                pre_tight_dv.decodable_implies_path_decodable(pre.journal_tj().freshest_rec);
                assert(pre_tight_dv.path_decodable(pre.journal_tj().freshest_rec));
                assert(pre_tight_dv.boundary_lsn == post_backing_dv.boundary_lsn);
                assert(pre_tight_dv.entries <= post_backing_dv.entries) by {
                    assert forall |old_addr: Address| #[trigger] pre_tight_dv.entries.dom().contains(old_addr)
                        implies post_backing_dv.entries.contains_key(old_addr)
                            && post_backing_dv.entries[old_addr] == pre_tight_dv.entries[old_addr] by {
                        assert(pre.journal_disk_view().entries.contains_key(old_addr));
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
                        assert(post_backing_dv.entries.contains_key(old_addr));
                        assert(post_backing_dv.entries[old_addr] == pre_tight_dv.entries[old_addr]);
                    }
                }
                assert(post_backing_dv.entries.contains_key(addr));
                assert(post.disk.visible()[addr] == writes[addr]);
                assert(post_backing_dv.entries[addr] == raw_page_to_record(post.disk.visible()[addr]));
                assert(to_journal_records(writes)[addr] == raw_page_to_record(writes[addr]));
                assert(to_journal_records(writes)[addr] == expected_record);
                assert(post_backing_dv.entries[addr] == expected_record);
                assert(expected_record.cropped_prior(pre_tight_dv.boundary_lsn)
                    == pre.journal_tj().freshest_rec);
                assert(!pre_tight_dv.entries.contains_key(addr)) by {
                    if pre_tight_dv.entries.contains_key(addr) {
                        assert(pre.mini_allocator.can_allocate(addr));
                        assert(AllocationJournal::State::disk_domain_not_free(
                            pre.journal_tj().disk_view,
                            pre.mini_allocator,
                        ));
                        assert(!pre.mini_allocator.can_allocate(addr));
                        assert(false);
                    }
                }
                assert(pre_tight_dv.path_build_tight(pre.journal_tj().freshest_rec)
                    == pre_tight_dv) by {
                    pre_tight_dv.path_build_tight_equals_build_tight(
                        pre.journal_tj().freshest_rec,
                    );
                    pre_aj.disk_view.path_build_tight_idempotent(pre.journal_tj().freshest_rec);
                    assert(pre_aj.disk_view.path_build_tight(pre.journal_tj().freshest_rec)
                        == pre_tight_dv);
                }
                let old_ranking = choose |ranking: Ranking|
                    pre_tight_dv.path_valid_ranking(pre.journal_tj().freshest_rec, ranking);
                let root_rank = if pre.journal_tj().freshest_rec is Some {
                    old_ranking[pre.journal_tj().freshest_rec.unwrap()] + 1
                } else {
                    0
                };
                let new_ranking = old_ranking.insert(addr, root_rank);
                pre_tight_dv.path_valid_ranking_insert_fresh(
                    pre.journal_tj().freshest_rec,
                    old_ranking,
                    addr,
                    root_rank,
                );
                post_backing_dv.path_valid_ranking_lifts_from_sub_disk(
                    pre_tight_dv,
                    pre.journal_tj().freshest_rec,
                    new_ranking,
                );
                assert(post_backing_dv.path_valid_ranking(pre.journal_tj().freshest_rec, new_ranking));
                assert(post_backing_dv.path_valid_ranking(Some(addr), new_ranking)) by {
                    reveal_with_fuel(DiskView::path_valid_ranking, 2);
                    if pre.journal_tj().freshest_rec is Some {
                        assert(new_ranking[pre.journal_tj().freshest_rec.unwrap()]
                            < new_ranking[addr]);
                    }
                }
                assert(post_backing_dv.path_decodable(Some(addr)));
                pre_tight_dv.path_build_tight_prepend_record(
                    post_backing_dv,
                    pre.journal_tj().freshest_rec,
                    addr,
                    expected_record,
                );
                assert(post.journal_tj().disk_view.entries
                    =~= pre_tight_dv.entries.insert(addr, expected_record));
                assert(pre.journal_tj().disk_view.entries <= post.journal_tj().disk_view.entries) by {
                    assert forall |old_addr: Address| #[trigger] pre.journal_tj().disk_view.entries.dom().contains(old_addr)
                        implies post.journal_tj().disk_view.entries.dom().contains(old_addr)
                            && pre.journal_tj().disk_view.entries[old_addr]
                                == post.journal_tj().disk_view.entries[old_addr] by {
                        assert(pre.journal_disk_view().entries.contains_key(old_addr));
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
                    assert(post.journal_tj().disk_view.entries
                        =~= pre_tight_dv.entries.insert(addr, expected_record));
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

}

}
