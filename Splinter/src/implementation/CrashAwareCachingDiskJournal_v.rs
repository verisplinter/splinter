// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Crash-aware wrapper for CachingDiskJournal.

#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::map::*;

use verus_state_machines_macros::state_machine;

use crate::abstract_system::MsgHistory_v::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::AllocationJournal_v::{
    AllocationJournal, JournalImage, LsnAUIndex, lsn_au_index_append_record,
    lsn_au_index_discard_up_to, lsn_au_index_discard_up_to_ensures, singleton_index,
};
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::disk::GenericDisk_v::{Address, AU, Pointer, to_aus};
use crate::implementation::CachedJournal_v::*;
use crate::implementation::CachingDisk_v::{addresses_in_aus, CachingDisk, CachingDiskRawPage as RawPage};
use crate::implementation::CachingDiskJournal_v::{
    CachingDiskJournal, cj_lsn_au_index,
};
use crate::implementation::JournalTypes_v::to_journal_records;
use crate::journal::LinkedJournalRefinement_v::*;
use crate::journal::LinkedJournal_v::*;

verus!{

#[verifier::ext_equal]
pub struct CachingDiskJournalImage {
    pub persistent: Map<Address, RawPage>,
    pub snapshot: JournalSnapshot,
    pub seq_end: LSN,
}

#[verifier::ext_equal]
pub struct CachingDiskJournalFrozenImage {
    pub snapshot: JournalSnapshot,
    pub seq_end: LSN,
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

pub open spec fn snapshot_tight_tj(
    records: Map<Address, JournalRecord>,
    snapshot: JournalSnapshot,
) -> TruncatedJournal {
    TruncatedJournal{
        freshest_rec: snapshot.freshest_rec(),
        disk_view: DiskView{
            boundary_lsn: snapshot.boundary_lsn,
            entries: records.restrict(snapshot_walk_domain(
                records,
                snapshot.boundary_lsn,
                snapshot.freshest_rec(),
            )),
        },
    }
}

pub open spec fn snapshot_tight_image(
    records: Map<Address, JournalRecord>,
    snapshot: JournalSnapshot,
) -> JournalImage {
    JournalImage{tj: snapshot_tight_tj(records, snapshot), first: snapshot.first()}
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

pub proof fn snapshot_tight_image_restrict_domain_same(
    records: Map<Address, JournalRecord>,
    snapshot: JournalSnapshot,
)
    ensures
        snapshot_tight_image(records, snapshot)
            == snapshot_tight_image(
                records.restrict(snapshot_walk_domain(
                    records,
                    snapshot.boundary_lsn,
                    snapshot.freshest_rec(),
                )),
                snapshot,
            ),
{
    let domain = snapshot_walk_domain(records, snapshot.boundary_lsn, snapshot.freshest_rec());
    let restricted = records.restrict(domain);
    assert_maps_equal!(
        snapshot_tight_tj(records, snapshot).disk_view.entries,
        snapshot_tight_tj(restricted, snapshot).disk_view.entries,
        addr => {
            if snapshot_tight_tj(records, snapshot).disk_view.entries.contains_key(addr) {
                let depth = choose |depth: nat|
                    snapshot_walk_ptr(records, snapshot.boundary_lsn, snapshot.freshest_rec(), depth)
                        == Some(addr);
                snapshot_walk_restrict_domain_same(
                    records,
                    snapshot.boundary_lsn,
                    snapshot.freshest_rec(),
                    depth,
                );
                assert(snapshot_walk_ptr(restricted, snapshot.boundary_lsn, snapshot.freshest_rec(), depth)
                    == Some(addr));
                assert(snapshot_tight_tj(restricted, snapshot).disk_view.entries.contains_key(addr));
                assert(restricted.contains_key(addr));
                assert(snapshot_tight_tj(records, snapshot).disk_view.entries[addr] == records[addr]);
                assert(snapshot_tight_tj(restricted, snapshot).disk_view.entries[addr] == restricted[addr]);
                assert(restricted[addr] == records[addr]);
            }
            if snapshot_tight_tj(restricted, snapshot).disk_view.entries.contains_key(addr) {
                let depth = choose |depth: nat|
                    snapshot_walk_ptr(restricted, snapshot.boundary_lsn, snapshot.freshest_rec(), depth)
                        == Some(addr);
                snapshot_walk_restrict_domain_same(
                    records,
                    snapshot.boundary_lsn,
                    snapshot.freshest_rec(),
                    depth,
                );
                assert(snapshot_walk_ptr(records, snapshot.boundary_lsn, snapshot.freshest_rec(), depth)
                    == Some(addr));
                assert(snapshot_tight_tj(records, snapshot).disk_view.entries.contains_key(addr));
                assert(restricted.contains_key(addr));
                assert(snapshot_tight_tj(records, snapshot).disk_view.entries[addr] == records[addr]);
                assert(snapshot_tight_tj(restricted, snapshot).disk_view.entries[addr] == restricted[addr]);
                assert(restricted[addr] == records[addr]);
            }
        }
    );
    assert(snapshot_tight_tj(records, snapshot) == snapshot_tight_tj(restricted, snapshot));
    assert(snapshot_tight_image(records, snapshot) == snapshot_tight_image(restricted, snapshot));
}

pub proof fn snapshot_tight_image_extends_same(
    records: Map<Address, JournalRecord>,
    bigger_records: Map<Address, JournalRecord>,
    snapshot: JournalSnapshot,
)
    requires
        snapshot_tight_image(records, snapshot).valid_image(),
        snapshot_tight_tj(records, snapshot).disk_view.entries <= bigger_records,
    ensures
        snapshot_tight_image(records, snapshot) == snapshot_tight_image(bigger_records, snapshot),
{
    let tight = snapshot_tight_tj(records, snapshot);
    let base_records = tight.disk_view.entries;
    let base_image = snapshot_tight_image(base_records, snapshot);
    snapshot_tight_image_restrict_domain_same(records, snapshot);
    assert(snapshot_tight_image(records, snapshot) == base_image);
    assert(tight.decodable());
    assert(tight.wf());
    assert(tight.disk_view.wf());
    assert(tight.disk_view.acyclic());
    assert(tight.disk_view.is_nondangling_pointer(tight.freshest_rec));
    assert_maps_equal!(
        snapshot_tight_tj(base_records, snapshot).disk_view.entries,
        snapshot_tight_tj(bigger_records, snapshot).disk_view.entries,
        addr => {
            if snapshot_tight_tj(base_records, snapshot).disk_view.entries.contains_key(addr) {
                let depth = choose |depth: nat|
                    snapshot_walk_ptr(base_records, snapshot.boundary_lsn, snapshot.freshest_rec(), depth)
                        == Some(addr);
                snapshot_walk_ptr_extends_same(tight.disk_view, bigger_records, snapshot.freshest_rec(), depth);
                assert(snapshot_walk_ptr(bigger_records, snapshot.boundary_lsn, snapshot.freshest_rec(), depth)
                    == Some(addr));
                assert(snapshot_tight_tj(bigger_records, snapshot).disk_view.entries.contains_key(addr));
                assert(base_records.contains_key(addr));
                assert(bigger_records.contains_key(addr));
                assert(bigger_records[addr] == base_records[addr]);
                assert(snapshot_tight_tj(base_records, snapshot).disk_view.entries[addr] == base_records[addr]);
                assert(snapshot_tight_tj(bigger_records, snapshot).disk_view.entries[addr] == bigger_records[addr]);
            }
            if snapshot_tight_tj(bigger_records, snapshot).disk_view.entries.contains_key(addr) {
                let depth = choose |depth: nat|
                    snapshot_walk_ptr(bigger_records, snapshot.boundary_lsn, snapshot.freshest_rec(), depth)
                        == Some(addr);
                snapshot_walk_ptr_extends_same(tight.disk_view, bigger_records, snapshot.freshest_rec(), depth);
                assert(snapshot_walk_ptr(base_records, snapshot.boundary_lsn, snapshot.freshest_rec(), depth)
                    == Some(addr));
                assert(snapshot_tight_tj(base_records, snapshot).disk_view.entries.contains_key(addr));
                assert(base_records.contains_key(addr));
                assert(bigger_records.contains_key(addr));
                assert(bigger_records[addr] == base_records[addr]);
                assert(snapshot_tight_tj(base_records, snapshot).disk_view.entries[addr] == base_records[addr]);
                assert(snapshot_tight_tj(bigger_records, snapshot).disk_view.entries[addr] == bigger_records[addr]);
            }
        }
    );
    assert(snapshot_tight_tj(base_records, snapshot) == snapshot_tight_tj(bigger_records, snapshot));
    assert(base_image == snapshot_tight_image(bigger_records, snapshot));
    assert(snapshot_tight_image(records, snapshot) == snapshot_tight_image(bigger_records, snapshot));
}

pub proof fn build_tight_entry_has_walk_depth(
    dv: DiskView,
    root: Pointer,
    addr: Address,
) -> (depth: nat)
    requires
        dv.decodable(root),
        dv.acyclic(),
        dv.build_tight(root).entries.contains_key(addr),
    ensures
        snapshot_walk_ptr(dv.entries, dv.boundary_lsn, root, depth) == Some(addr),
    decreases dv.the_rank_of(root),
{
    if root is Some {
        let root_addr = root.unwrap();
        if addr == root_addr {
            0
        } else {
            dv.build_tight_shape(root);
            assert(dv.build_tight(dv.next(root)).entries.contains_key(addr));
            let inner_depth = build_tight_entry_has_walk_depth(dv, dv.next(root), addr);
            assert(snapshot_walk_ptr(dv.entries, dv.boundary_lsn, dv.next(root), inner_depth)
                == Some(addr));
            snapshot_walk_ptr_step(dv.entries, dv.boundary_lsn, root, inner_depth);
            assert(snapshot_walk_ptr(dv.entries, dv.boundary_lsn, root, inner_depth + 1)
                == Some(addr));
            inner_depth + 1
        }
    } else {
        assert(false);
        0
    }
}

pub proof fn snapshot_walk_ptr_in_build_tight(
    dv: DiskView,
    root: Pointer,
    depth: nat,
)
    requires
        dv.decodable(root),
        dv.acyclic(),
    ensures
        snapshot_walk_ptr(dv.entries, dv.boundary_lsn, root, depth) is Some ==>
            dv.build_tight(root).entries.contains_key(
                snapshot_walk_ptr(dv.entries, dv.boundary_lsn, root, depth).unwrap(),
            ),
    decreases depth,
{
    dv.build_tight_is_awesome(root);
    let tight = dv.build_tight(root);
    if depth == 0 {
        if root is Some {
            assert(tight.entries.contains_key(root.unwrap()));
        }
    } else {
        snapshot_walk_ptr_in_build_tight(dv, root, (depth - 1) as nat);
        let prev = snapshot_walk_ptr(dv.entries, dv.boundary_lsn, root, (depth - 1) as nat);
        if prev is Some {
            assert(tight.entries.contains_key(prev.unwrap()));
            assert(tight.entries[prev.unwrap()] == dv.entries[prev.unwrap()]);
            let next = dv.entries[prev.unwrap()].cropped_prior(dv.boundary_lsn);
            if next is Some {
                assert(tight.wf());
                assert(tight.nondangling_pointers());
                assert(tight.entries[prev.unwrap()].cropped_prior(tight.boundary_lsn) == next);
                assert(tight.entries.contains_key(next.unwrap()));
            }
        }
    }
}

pub proof fn build_tight_entry_not_after_root(
    dv: DiskView,
    root: Pointer,
    first: AU,
    addr: Address,
)
    requires
        dv.pointer_is_upstream(root, first),
        root is Some,
        dv.build_tight(root).entries.contains_key(addr),
    ensures
        !root.unwrap().after_page(addr),
    decreases dv.the_rank_of(root),
{
    let root_addr = root.unwrap();
    if addr == root_addr {
        assert(!root_addr.after_page(addr));
    } else {
        dv.build_tight_shape(root);
        let next = dv.next(root);
        assert(dv.build_tight(next).entries.contains_key(addr));
        if next is Some {
            let next_addr = next.unwrap();
            dv.build_tight_ensures(next);
            dv.build_tight_is_awesome(next);
            assert(dv.build_tight(next).entries <= dv.entries);
            assert(dv.entries.contains_key(addr));
            if root_addr.after_page(addr) {
                assert(addr.au == root_addr.au);
                assert(root_addr.page < addr.page);
                assert(addr.wf());
                reveal(DiskView::pages_allocated_in_lsn_order);
                assert(dv.pages_allocated_in_lsn_order());
                assert(dv.entries[root_addr].message_seq.seq_end
                    <= dv.entries[addr].message_seq.seq_start);
                assert(dv.entries[root_addr].message_seq.wf());
                assert(dv.entries[addr].message_seq.wf());
                assert(dv.entries[addr].message_seq.seq_start
                    < dv.entries[addr].message_seq.seq_end);
                assert(dv.this_block_can_concat(root_addr));
                assert(dv.entries[next_addr].message_seq.can_concat(
                    dv.entries[root_addr].message_seq,
                ));
                assert(dv.entries[root_addr].message_seq.seq_start
                    == dv.entries[next_addr].message_seq.seq_end);
                assert(dv.boundary_lsn < dv.entries[root_addr].message_seq.seq_start) by {
                    assert(next == dv.entries[root_addr].cropped_prior(dv.boundary_lsn));
                }
                assert(dv.upstream(next_addr));
                assert(dv.decodable(next));
                assert(dv.acyclic());
                assert(dv.internal_au_pages_fully_linked());
                assert(dv.has_unique_lsns());
                assert(dv.valid_first_au(first));
                assert(dv.pointer_is_upstream(next, first));
                dv.build_tight_entry_active_bounded(next, addr);
                assert(dv.build_tight(next).entries[addr].message_seq.seq_end
                    <= dv.seq_end(next));
                assert(dv.build_tight(next).entries[addr] == dv.entries[addr]);
                assert(dv.seq_end(next) == dv.entries[next_addr].message_seq.seq_end);
                assert(dv.entries[addr].message_seq.seq_end
                    <= dv.entries[root_addr].message_seq.seq_start);
                assert(dv.entries[root_addr].message_seq.seq_start
                    < dv.entries[root_addr].message_seq.seq_end);
                assert(false);
            }
        } else {
            assert(false);
        }
    }
}

pub proof fn snapshot_walk_persistent_visible_frozen_agree(
    state: CachingDiskJournal::State,
    frozen: JournalSnapshot,
    seq_end: LSN,
    depth: nat,
)
    requires
        state.inv(),
        state.frozen_snapshot_valid(frozen, seq_end),
        frozen.freshest_rec() is Some ==> seq_end <= state.journal.clean_watermark(),
    ensures
        snapshot_walk_ptr(
            to_journal_records(state.disk.persistent),
            frozen.boundary_lsn,
            frozen.freshest_rec(),
            depth,
        ) == snapshot_walk_ptr(
            state.journal_disk_view().entries,
            frozen.boundary_lsn,
            frozen.freshest_rec(),
            depth,
        ),
        snapshot_walk_ptr(
            to_journal_records(state.disk.persistent),
            frozen.boundary_lsn,
            frozen.freshest_rec(),
            depth,
        ) == snapshot_walk_ptr(
            state.frozen_tj(frozen).disk_view.entries,
            frozen.boundary_lsn,
            frozen.freshest_rec(),
            depth,
        ),
        snapshot_walk_ptr(
            to_journal_records(state.disk.persistent),
            frozen.boundary_lsn,
            frozen.freshest_rec(),
            depth,
        ) is Some ==> state.clean_watermark_pages().contains(
            snapshot_walk_ptr(
                to_journal_records(state.disk.persistent),
                frozen.boundary_lsn,
                frozen.freshest_rec(),
                depth,
            ).unwrap(),
        ),
    decreases depth,
{
    let persistent_records = to_journal_records(state.disk.persistent);
    let visible_records = state.journal_disk_view().entries;
    let frozen_tj = state.frozen_tj(frozen);
    let frozen_records = frozen_tj.disk_view.entries;
    let root = frozen.freshest_rec();

    state.frozen_snapshot_valid_image(frozen, seq_end);
    state.frozen_tight_domain_clean_watermark(frozen, seq_end);

    if depth == 0 {
        if root is Some {
            let root_addr = root.unwrap();
            assert(state.frozen_snapshot_valid(frozen, seq_end));
            assert(visible_records.contains_key(root_addr));
            assert(frozen.boundary_lsn < seq_end);
            assert(seq_end == state.frozen_seq_end(frozen));
            assert(seq_end == visible_records[root_addr].message_seq.seq_end);
            assert(seq_end <= state.journal.clean_watermark());
            assert(state.clean_watermark_pages().contains(root_addr));
            state.clean_watermark_record_eq(root_addr);
            assert(persistent_records[root_addr] == visible_records[root_addr]);
            assert(frozen_records.contains_key(root_addr));
            assert(frozen_records[root_addr] == visible_records[root_addr]);
        }
    } else {
        snapshot_walk_persistent_visible_frozen_agree(state, frozen, seq_end, (depth - 1) as nat);
        let prev_persistent = snapshot_walk_ptr(
            persistent_records,
            frozen.boundary_lsn,
            root,
            (depth - 1) as nat,
        );
        let prev_visible = snapshot_walk_ptr(
            visible_records,
            frozen.boundary_lsn,
            root,
            (depth - 1) as nat,
        );
        let prev_frozen = snapshot_walk_ptr(
            frozen_records,
            frozen.boundary_lsn,
            root,
            (depth - 1) as nat,
        );
        assert(prev_persistent == prev_visible);
        assert(prev_persistent == prev_frozen);
        if prev_persistent is Some {
            let prev = prev_persistent.unwrap();
            state.clean_watermark_record_eq(prev);
            assert(persistent_records[prev] == visible_records[prev]);
            snapshot_walk_ptr_in_disk_view(frozen_tj.disk_view, root, (depth - 1) as nat);
            assert(frozen_records.contains_key(prev));
            assert(frozen_records[prev] == visible_records[prev]) by {
                assert(frozen_tj.disk_view.entries <= state.journal_tj().disk_view.entries);
                assert(state.journal_tj().disk_view.entries == visible_records);
            }
            assert(persistent_records[prev] == frozen_records[prev]);
            assert(snapshot_walk_ptr(
                persistent_records,
                frozen.boundary_lsn,
                root,
                depth,
            ) == persistent_records[prev].cropped_prior(frozen.boundary_lsn));
            assert(snapshot_walk_ptr(
                visible_records,
                frozen.boundary_lsn,
                root,
                depth,
            ) == visible_records[prev].cropped_prior(frozen.boundary_lsn));
            assert(snapshot_walk_ptr(
                frozen_records,
                frozen.boundary_lsn,
                root,
                depth,
            ) == frozen_records[prev].cropped_prior(frozen.boundary_lsn));
        }
        let current = snapshot_walk_ptr(
            persistent_records,
            frozen.boundary_lsn,
            root,
            depth,
        );
        if current is Some {
            snapshot_walk_ptr_in_build_tight(frozen_tj.disk_view, root, depth);
            assert(frozen_tj.disk_view.build_tight(root).entries.contains_key(current.unwrap()));
            assert(frozen_tj.build_tight().disk_view.entries.contains_key(current.unwrap()));
            assert(state.clean_watermark_pages().contains(current.unwrap()));
        }
    }
}

pub proof fn snapshot_walk_visible_frozen_agree(
    state: CachingDiskJournal::State,
    frozen: JournalSnapshot,
    seq_end: LSN,
    depth: nat,
)
    requires
        state.inv(),
        state.frozen_snapshot_valid(frozen, seq_end),
    ensures
        snapshot_walk_ptr(
            state.journal_disk_view().entries,
            frozen.boundary_lsn,
            frozen.freshest_rec(),
            depth,
        ) == snapshot_walk_ptr(
            state.frozen_tj(frozen).disk_view.entries,
            frozen.boundary_lsn,
            frozen.freshest_rec(),
            depth,
        ),
    decreases depth,
{
    let visible_records = state.journal_disk_view().entries;
    let frozen_tj = state.frozen_tj(frozen);
    let frozen_records = frozen_tj.disk_view.entries;
    let root = frozen.freshest_rec();

    state.frozen_snapshot_valid_image(frozen, seq_end);

    if depth == 0 {
        if root is Some {
            let root_addr = root.unwrap();
            assert(visible_records.contains_key(root_addr));
            assert(frozen_records.contains_key(root_addr));
            assert(frozen_records[root_addr] == visible_records[root_addr]) by {
                assert(frozen_tj.disk_view.entries <= state.journal_tj().disk_view.entries);
                assert(state.journal_tj().disk_view.entries == visible_records);
            }
        }
    } else {
        snapshot_walk_visible_frozen_agree(state, frozen, seq_end, (depth - 1) as nat);
        let prev_visible = snapshot_walk_ptr(
            visible_records,
            frozen.boundary_lsn,
            root,
            (depth - 1) as nat,
        );
        let prev_frozen = snapshot_walk_ptr(
            frozen_records,
            frozen.boundary_lsn,
            root,
            (depth - 1) as nat,
        );
        assert(prev_visible == prev_frozen);
        if prev_visible is Some {
            let prev = prev_visible.unwrap();
            snapshot_walk_ptr_in_disk_view(frozen_tj.disk_view, root, (depth - 1) as nat);
            assert(frozen_records.contains_key(prev));
            assert(frozen_records[prev] == visible_records[prev]) by {
                assert(frozen_tj.disk_view.entries <= state.journal_tj().disk_view.entries);
                assert(state.journal_tj().disk_view.entries == visible_records);
            }
        }
    }
}

impl CachingDiskJournalImage {
    pub open spec fn empty() -> Self {
        Self{
            persistent: Map::empty(),
            snapshot: JournalSnapshot{boundary_lsn: 0, root: None},
            seq_end: 0,
        }
    }

    pub open spec fn full_tj(self) -> TruncatedJournal {
        TruncatedJournal{
            freshest_rec: self.snapshot.freshest_rec(),
            disk_view: DiskView{
                boundary_lsn: self.snapshot.boundary_lsn,
                entries: to_journal_records(self.persistent),
            },
        }
    }

    pub open spec fn stable_persistent_domain(self) -> Set<Address> {
        let records = to_journal_records(self.persistent);
        snapshot_walk_domain(records, self.snapshot.boundary_lsn, self.snapshot.freshest_rec())
    }

    pub open spec fn stable_persistent(self) -> Map<Address, RawPage> {
        self.persistent.restrict(self.stable_persistent_domain())
    }

    pub open spec fn stable_tj(self) -> TruncatedJournal {
        snapshot_tight_tj(to_journal_records(self.persistent), self.snapshot)
    }

    pub open spec fn image_persistent_domain(self) -> Set<Address> {
        let full_tj = self.full_tj();
        let index = full_tj.build_lsn_au_index_from_first(self.snapshot.first());
        full_tj.disk_view.au_domain(index)
    }

    pub open spec fn relaxed_tj(self) -> TruncatedJournal {
        TruncatedJournal{
            freshest_rec: self.snapshot.freshest_rec(),
            disk_view: DiskView{
                boundary_lsn: self.snapshot.boundary_lsn,
                entries: to_journal_records(self.image_persistent()),
            },
        }
    }

    pub open spec fn live_persistent_domain(self) -> Set<Address> {
        self.stable_persistent_domain()
    }

    pub open spec fn image_persistent(self) -> Map<Address, RawPage> {
        self.persistent.restrict(self.image_persistent_domain())
    }

    pub open spec fn live_persistent(self) -> Map<Address, RawPage> {
        self.persistent.restrict(self.live_persistent_domain())
    }

    pub open spec fn tj(self) -> TruncatedJournal {
        self.live_tj()
    }

    pub open spec fn live_tj(self) -> TruncatedJournal {
        self.stable_tj()
    }

    pub open spec fn tight_tj(self) -> TruncatedJournal {
        self.tj().build_tight()
    }

    pub open spec fn i(self) -> JournalImage {
        snapshot_tight_image(to_journal_records(self.persistent), self.snapshot)
    }

    pub open spec fn seq_end(self) -> LSN {
        self.tj().seq_end()
    }

    pub open spec fn valid_image(self) -> bool {
        &&& self.tj().decodable()
        &&& self.tj().disk_view.wf_addrs()
        &&& self.tj().disk_view.pointer_is_upstream(self.tj().freshest_rec, self.snapshot.first())
        &&& self.tj().disk_view.domain_au_bounded_wrt_index(
            self.tj().build_lsn_au_index_from_first(self.snapshot.first()),
        )
        &&& self.tj().disk_view.bounded_inactive_lsns(
            self.tj().build_lsn_au_index_from_first(self.snapshot.first()),
            self.tj().freshest_rec,
        )
    }

    pub open spec fn wf(self) -> bool {
        self.valid_image()
    }

    pub proof fn valid_image_implies_live_valid_image(self)
        requires
            self.valid_image(),
        ensures
            (JournalImage{tj: self.live_tj(), first: self.snapshot.first()}).live_valid_image(),
    {
        let image_tj = self.tj();
        let live_tj = self.live_tj();
        let first = self.snapshot.first();
        let index = image_tj.build_lsn_au_index_from_first(first);
        let live_index = live_tj.build_lsn_au_index_from_first(first);
        assert(live_tj == image_tj);
        assert(image_tj.valid_structure(index, first));
        image_tj.build_lsn_au_index_from_first_ensures(first);
        assert(live_index == index);
        assert(live_tj.disk_view.domain_tight_wrt_index(
            live_index,
            live_tj.freshest_rec,
        )) by {
            assert forall |addr: Address| #[trigger] live_tj.disk_view.entries.dom().contains(addr)
                implies {
                    &&& live_index.values().contains(addr.au)
                    &&& live_tj.freshest_rec is Some ==> !live_tj.freshest_rec.unwrap().after_page(addr)
                } by {
                assert(live_tj.disk_view.domain_au_bounded_wrt_index(live_index));
                assert(live_index.values().contains(addr.au));
                if live_tj.freshest_rec is Some {
                    let records = to_journal_records(self.persistent);
                    let depth = choose |depth: nat|
                        snapshot_walk_ptr(
                            records,
                            self.snapshot.boundary_lsn,
                            self.snapshot.freshest_rec(),
                            depth,
                        ) == Some(addr);
                    snapshot_walk_restrict_domain_same(
                        records,
                        self.snapshot.boundary_lsn,
                        self.snapshot.freshest_rec(),
                        depth,
                    );
                    assert(snapshot_walk_ptr(
                        live_tj.disk_view.entries,
                        live_tj.disk_view.boundary_lsn,
                        live_tj.freshest_rec,
                        depth,
                    ) == Some(addr));
                    assert(live_tj.disk_view.decodable(live_tj.freshest_rec));
                    assert(live_tj.disk_view.acyclic());
                    snapshot_walk_ptr_in_build_tight(live_tj.disk_view, live_tj.freshest_rec, depth);
                    assert(snapshot_walk_ptr(
                        live_tj.disk_view.entries,
                        live_tj.disk_view.boundary_lsn,
                        live_tj.freshest_rec,
                        depth,
                    ) is Some);
                    assert(snapshot_walk_ptr(
                        live_tj.disk_view.entries,
                        live_tj.disk_view.boundary_lsn,
                        live_tj.freshest_rec,
                        depth,
                    ).unwrap() == addr);
                    assert(live_tj.disk_view.build_tight(live_tj.freshest_rec).entries.contains_key(addr));
                    build_tight_entry_not_after_root(
                        live_tj.disk_view,
                        live_tj.freshest_rec,
                        first,
                        addr,
                    );
                }
            }
        }
        assert((JournalImage{tj: live_tj, first}).live_valid_image());
    }

    pub proof fn valid_image_implies_tight_structure(self)
        requires
            self.valid_image(),
        ensures
            (JournalImage{tj: self.tight_tj(), first: self.snapshot.first()}).valid_image(),
            self.tight_tj().decodable(),
            self.tight_tj().disk_view.wf_addrs(),
            self.tight_tj().disk_view.internal_au_pages_fully_linked(),
            self.tight_tj().disk_view.has_unique_lsns(),
            self.tight_tj().freshest_rec is Some ==>
                self.tight_tj().disk_view.upstream(self.tight_tj().freshest_rec.unwrap()),
    {
        let image_tj = self.tj();
        let tight_tj = self.tight_tj();
        let first = self.snapshot.first();
        let index = image_tj.build_lsn_au_index_from_first(first);

        assert(image_tj.valid_structure(index, first));
        image_tj.build_lsn_au_index_from_first_ensures(first);
        image_tj.disk_view.build_tight_is_awesome(image_tj.freshest_rec);
        let image_dv = image_tj.disk_view;
        let tight_dv = tight_tj.disk_view;
        assert(tight_dv.is_sub_disk(image_dv));
        assert forall |addr: Address| #[trigger] tight_dv.entries.dom().contains(addr)
            implies image_dv.entries.dom().contains(addr) && tight_dv.entries[addr] == image_dv.entries[addr] by {
            assert(tight_dv.entries <= image_dv.entries);
        }
        assert(tight_tj.wf());
        assert(tight_tj.decodable());
        assert(tight_dv.wf_addrs()) by {
            assert forall |addr: Address| #[trigger] tight_dv.entries.dom().contains(addr)
                implies addr.wf() by {
                assert(image_dv.entries.dom().contains(addr));
                assert(image_dv.wf_addrs());
            }
        }
        assert(tight_dv.nonzero_pages_point_backward()) by {
            assert forall |addr: Address| #![auto]
                ({
                    &&& addr.page != 0
                    &&& tight_dv.entries.dom().contains(addr)
                }) ==> tight_dv.entries[addr].prior_rec == Some(addr.previous()) by {
                if addr.page != 0 && tight_dv.entries.dom().contains(addr) {
                    assert(image_dv.entries.dom().contains(addr));
                    assert(tight_dv.entries[addr] == image_dv.entries[addr]);
                    assert(image_dv.internal_au_pages_fully_linked());
                    assert(image_dv.nonzero_pages_point_backward());
                }
            }
        }
        reveal(DiskView::pages_allocated_in_lsn_order);
        assert(tight_dv.pages_allocated_in_lsn_order()) by {
            assert forall |alo: Address, ahi: Address| #![auto]
                ({
                    &&& alo.au == ahi.au
                    &&& alo.page < ahi.page
                    &&& tight_dv.entries.dom().contains(alo)
                    &&& tight_dv.entries.dom().contains(ahi)
                }) ==> tight_dv.entries[alo].message_seq.seq_end
                    <= tight_dv.entries[ahi].message_seq.seq_start by {
                if alo.au == ahi.au && alo.page < ahi.page
                    && tight_dv.entries.dom().contains(alo)
                    && tight_dv.entries.dom().contains(ahi) {
                    assert(image_dv.entries.dom().contains(alo));
                    assert(image_dv.entries.dom().contains(ahi));
                    assert(tight_dv.entries[alo] == image_dv.entries[alo]);
                    assert(tight_dv.entries[ahi] == image_dv.entries[ahi]);
                    assert(image_dv.internal_au_pages_fully_linked());
                    assert(image_dv.pages_allocated_in_lsn_order());
                }
            }
        }
        assert(tight_dv.internal_au_pages_fully_linked());
        assert(tight_dv.has_unique_lsns()) by {
            assert forall |lsn: LSN, addr1: Address, addr2: Address|
                tight_dv.addr_supports_lsn(addr1, lsn)
                && tight_dv.addr_supports_lsn(addr2, lsn)
                implies addr1 == addr2 by {
                assert(image_dv.addr_supports_lsn(addr1, lsn));
                assert(image_dv.addr_supports_lsn(addr2, lsn));
                assert(image_dv.has_unique_lsns());
            }
        }
        if tight_tj.freshest_rec is Some {
            let root = tight_tj.freshest_rec.unwrap();
            assert(tight_dv.entries.contains_key(root));
            assert(tight_dv.upstream(root));

            tight_dv.decodable_implies_lsns_have_entries(tight_tj.freshest_rec);
            assert(tight_dv.lsns_have_entries(tight_tj.freshest_rec));
            assert(tight_dv.lsn_has_entry(tight_dv.boundary_lsn));
            let tight_first_addr = choose |addr: Address|
                tight_dv.lsn_has_entry_at(tight_dv.boundary_lsn, addr);
            assert(tight_dv.addr_supports_lsn(tight_first_addr, tight_dv.boundary_lsn));

            assert(image_dv.addr_supports_lsn(tight_first_addr, image_dv.boundary_lsn));
            assert(image_dv.valid_first_au(first));
            let image_first_addr = choose |addr: Address| #![auto]
                addr.au == first && image_dv.addr_supports_lsn(addr, image_dv.boundary_lsn);
            assert(image_dv.addr_supports_lsn(image_first_addr, image_dv.boundary_lsn));
            assert(image_dv.has_unique_lsns());
            assert(tight_first_addr == image_first_addr);
            assert(tight_dv.valid_first_au(first));
        }
        assert(tight_dv.pointer_is_upstream(tight_tj.freshest_rec, first));
        let tight_index = tight_tj.build_lsn_au_index_from_first(first);
        tight_tj.build_lsn_au_index_from_first_ensures(first);
        tight_dv.build_lsn_au_index_equiv_page_walk(tight_tj.freshest_rec, first);
        image_dv.build_lsn_au_index_equiv_page_walk(image_tj.freshest_rec, first);
        tight_dv.build_lsn_au_index_page_walk_sub_disk(image_dv, tight_tj.freshest_rec);
        assert(tight_dv.build_lsn_au_index_page_walk(tight_tj.freshest_rec)
            == image_dv.build_lsn_au_index_page_walk(image_tj.freshest_rec));
        assert(tight_index == index);
        assert(tight_dv.domain_au_bounded_wrt_index(tight_index)) by {
            assert forall |addr: Address| #[trigger] tight_dv.entries.dom().contains(addr)
                implies tight_index.values().contains(addr.au) by {
                assert(image_dv.entries.dom().contains(addr));
                assert(image_dv.domain_au_bounded_wrt_index(index));
                assert(index.values().contains(addr.au));
            }
        }
        assert(tight_dv.bounded_inactive_lsns(tight_index, tight_tj.freshest_rec)) by {
            assert forall |addr: Address, lsn: LSN|
                ({
                    &&& tight_dv.entries.dom().contains(addr)
                    &&& tight_dv.entries[addr].message_seq.contains(lsn)
                    &&& tight_index.values().contains(addr.au)
                    &&& !tight_index.contains_key(lsn)
                    &&& tight_tj.freshest_rec is Some ==> !tight_tj.freshest_rec.unwrap().after_page(addr)
                }) implies lsn < tight_dv.boundary_lsn by {
                assert(image_dv.entries.dom().contains(addr));
                assert(tight_dv.entries[addr] == image_dv.entries[addr]);
                assert(index.values().contains(addr.au));
                assert(!index.contains_key(lsn));
                assert(image_dv.bounded_inactive_lsns(index, image_tj.freshest_rec));
            }
        }
        assert((JournalImage{tj: tight_tj, first}).valid_image());
    }

    pub open spec fn accessible_aus(self) -> Set<AU> {
        to_aus(self.persistent.dom())
    }

    pub proof fn live_persistent_aus_match_i(self)
        ensures
            to_aus(self.live_persistent().dom()) <= self.i().accessible_aus(),
    {
        assert forall |au: AU| #[trigger] to_aus(self.live_persistent().dom()).contains(au)
            implies self.i().accessible_aus().contains(au) by {
            crate::disk::GenericDisk_v::to_aus_domain(self.live_persistent().dom());
            let addr = choose |addr: Address| self.live_persistent().dom().contains(addr) && addr.au == au;
            assert(self.live_persistent().contains_key(addr));
            assert(self.persistent.contains_key(addr));
            assert(self.stable_persistent_domain().contains(addr));
            assert(to_journal_records(self.persistent).contains_key(addr));
            assert(self.live_tj().disk_view.entries.contains_key(addr));
            assert(self.i().tj.disk_view.entries.contains_key(addr));
            crate::disk::GenericDisk_v::to_aus_domain(self.i().tj.disk_view.entries.dom());
        }
    }

    pub proof fn valid_image_snapshot_walk_ptr_present(self, depth: nat)
        requires
            self.valid_image(),
            snapshot_walk_ptr(
                to_journal_records(self.persistent),
                self.snapshot.boundary_lsn,
                self.snapshot.freshest_rec(),
                depth,
            ) is Some,
        ensures
            to_journal_records(self.persistent).contains_key(snapshot_walk_ptr(
                to_journal_records(self.persistent),
                self.snapshot.boundary_lsn,
                self.snapshot.freshest_rec(),
                depth,
            ).unwrap()),
        decreases depth,
    {
        let records = to_journal_records(self.persistent);
        let root = self.snapshot.freshest_rec();
        let ptr = snapshot_walk_ptr(records, self.snapshot.boundary_lsn, root, depth);
        if depth == 0 {
            assert(ptr == root);
            assert(self.tj().disk_view.is_nondangling_pointer(self.tj().freshest_rec));
            assert(self.tj().freshest_rec == root);
            assert(self.tj().disk_view.entries.contains_key(ptr.unwrap()));
            assert(records.contains_key(ptr.unwrap()));
        } else {
            let prev = snapshot_walk_ptr(records, self.snapshot.boundary_lsn, root, (depth - 1) as nat);
            assert(ptr == if prev is Some && records.contains_key(prev.unwrap()) {
                records[prev.unwrap()].cropped_prior(self.snapshot.boundary_lsn)
            } else {
                None
            });
            assert(prev is Some);
            self.valid_image_snapshot_walk_ptr_present((depth - 1) as nat);
            let prev_addr = prev.unwrap();
            assert(records.contains_key(prev_addr));
            assert(snapshot_walk_domain(records, self.snapshot.boundary_lsn, root).contains(prev_addr));
            assert(self.tj().disk_view.entries.contains_key(prev_addr));
            assert(self.tj().disk_view.entries[prev_addr] == records[prev_addr]);
            assert(self.tj().disk_view.nondangling_pointers());
            assert(self.tj().disk_view.is_nondangling_pointer(
                self.tj().disk_view.entries[prev_addr].cropped_prior(self.snapshot.boundary_lsn),
            ));
            assert(ptr == self.tj().disk_view.entries[prev_addr].cropped_prior(self.snapshot.boundary_lsn));
            assert(self.tj().disk_view.entries.contains_key(ptr.unwrap()));
            assert(records.contains_key(ptr.unwrap()));
        }
    }

    pub proof fn valid_image_stable_domain_materialized(self)
        requires
            self.valid_image(),
        ensures
            self.stable_persistent_domain() <= self.persistent.dom(),
    {
        assert forall |addr: Address| #[trigger] self.stable_persistent_domain().contains(addr)
            implies self.persistent.dom().contains(addr) by {
            let records = to_journal_records(self.persistent);
            let depth = choose |depth: nat|
                snapshot_walk_ptr(records, self.snapshot.boundary_lsn, self.snapshot.freshest_rec(), depth)
                    == Some(addr);
            self.valid_image_snapshot_walk_ptr_present(depth);
            assert(records.contains_key(addr));
            assert(self.persistent.contains_key(addr));
        }
    }
}

pub open spec fn concrete_frozen_seq_end(
    state: CachingDiskJournal::State,
    snapshot: JournalSnapshot,
) -> LSN {
    state.frozen_seq_end(snapshot)
}

pub open spec fn concrete_frozen_lsns(
    state: CachingDiskJournal::State,
    snapshot: JournalSnapshot,
) -> Set<LSN> {
    state.frozen_lsns(snapshot)
}

pub open spec fn caching_disk_journal_lsn_au_index(state: CachingDiskJournal::State) -> LsnAUIndex {
    if state.journal.status is Some {
        cj_lsn_au_index(state.journal)
    } else {
        state.journal_tj().build_lsn_au_index_from_first(state.journal.snapshot.first())
    }
}

pub open spec fn caching_disk_journal_accessible_aus(state: CachingDiskJournal::State) -> Set<AU> {
    state.accessible_aus()
}

pub open spec fn concrete_frozen_tj(
    state: CachingDiskJournal::State,
    snapshot: JournalSnapshot,
) -> TruncatedJournal {
    state.frozen_tj(snapshot).build_tight()
}

pub open spec fn concrete_frozen_image(
    state: CachingDiskJournal::State,
    snapshot: JournalSnapshot,
) -> JournalImage {
    JournalImage{tj: concrete_frozen_tj(state, snapshot), first: snapshot.first()}
}

pub proof fn visible_snapshot_image_matches_concrete_frozen(
    state: CachingDiskJournal::State,
    frozen: JournalSnapshot,
    seq_end: LSN,
)
    requires
        state.inv(),
        state.frozen_snapshot_valid(frozen, seq_end),
    ensures
        snapshot_tight_image(state.journal_disk_view().entries, frozen)
            == concrete_frozen_image(state, frozen),
{
    let visible_records = state.journal_disk_view().entries;
    let visible_image = snapshot_tight_image(visible_records, frozen);
    let frozen_tj = state.frozen_tj(frozen);
    let concrete_image = concrete_frozen_image(state, frozen);
    let root = frozen.freshest_rec();

    state.frozen_snapshot_valid_image(frozen, seq_end);
    frozen_tj.disk_view.build_tight_ensures(root);

    assert_maps_equal!(
        visible_image.tj.disk_view.entries,
        concrete_image.tj.disk_view.entries,
        addr => {
            if visible_image.tj.disk_view.entries.contains_key(addr) {
                assert(snapshot_walk_domain(visible_records, frozen.boundary_lsn, root).contains(addr));
                let depth = choose |depth: nat|
                    snapshot_walk_ptr(visible_records, frozen.boundary_lsn, root, depth) == Some(addr);
                snapshot_walk_visible_frozen_agree(state, frozen, seq_end, depth);
                assert(snapshot_walk_ptr(
                    frozen_tj.disk_view.entries,
                    frozen.boundary_lsn,
                    root,
                    depth,
                ) == Some(addr));
                snapshot_walk_ptr_in_build_tight(frozen_tj.disk_view, root, depth);
                assert(concrete_image.tj.disk_view.entries.contains_key(addr));
                assert(frozen_tj.disk_view.entries.contains_key(addr));
                assert(frozen_tj.disk_view.entries[addr] == visible_records[addr]) by {
                    assert(frozen_tj.disk_view.entries <= state.journal_tj().disk_view.entries);
                    assert(state.journal_tj().disk_view.entries == visible_records);
                }
                assert(concrete_image.tj.disk_view.entries[addr] == frozen_tj.disk_view.entries[addr]);
                assert(visible_image.tj.disk_view.entries[addr] == visible_records[addr]);
            }
            if concrete_image.tj.disk_view.entries.contains_key(addr) {
                let depth = build_tight_entry_has_walk_depth(frozen_tj.disk_view, root, addr);
                snapshot_walk_visible_frozen_agree(state, frozen, seq_end, depth);
                assert(snapshot_walk_ptr(
                    frozen_tj.disk_view.entries,
                    frozen.boundary_lsn,
                    root,
                    depth,
                ) == Some(addr));
                assert(snapshot_walk_ptr(visible_records, frozen.boundary_lsn, root, depth) == Some(addr));
                assert(snapshot_walk_domain(visible_records, frozen.boundary_lsn, root).contains(addr));
                assert(visible_image.tj.disk_view.entries.contains_key(addr));
                assert(frozen_tj.disk_view.entries.contains_key(addr));
                assert(frozen_tj.disk_view.entries[addr] == visible_records[addr]) by {
                    assert(frozen_tj.disk_view.entries <= state.journal_tj().disk_view.entries);
                    assert(state.journal_tj().disk_view.entries == visible_records);
                }
                assert(concrete_image.tj.disk_view.entries[addr] == frozen_tj.disk_view.entries[addr]);
                assert(visible_image.tj.disk_view.entries[addr] == visible_records[addr]);
            }
        }
    );
    assert(visible_image.tj == concrete_image.tj);
    assert(visible_image == concrete_image);
}

pub proof fn prepared_snapshot_image_matches_visible(
    state: CachingDiskJournal::State,
    prepared_image: CachingDiskJournalImage,
    seq_end: LSN,
)
    requires
        state.inv(),
        state.frozen_snapshot_valid(prepared_image.snapshot, seq_end),
        prepared_image.seq_end == seq_end,
        prepared_image.persistent == state.disk.persistent,
        prepared_image.snapshot.freshest_rec() is Some ==>
            seq_end <= state.journal.clean_watermark(),
    ensures
        prepared_image.i()
            == snapshot_tight_image(state.journal_disk_view().entries, prepared_image.snapshot),
{
    let frozen = prepared_image.snapshot;
    let persistent_records = to_journal_records(prepared_image.persistent);
    let state_persistent_records = to_journal_records(state.disk.persistent);
    let visible_records = state.journal_disk_view().entries;
    let persistent_image = prepared_image.i();
    let visible_image = snapshot_tight_image(visible_records, frozen);
    let root = frozen.freshest_rec();

    assert(persistent_records == state_persistent_records);
    assert_maps_equal!(
        persistent_image.tj.disk_view.entries,
        visible_image.tj.disk_view.entries,
        addr => {
            if persistent_image.tj.disk_view.entries.contains_key(addr) {
                assert(snapshot_walk_domain(persistent_records, frozen.boundary_lsn, root).contains(addr));
                let depth = choose |depth: nat|
                    snapshot_walk_ptr(persistent_records, frozen.boundary_lsn, root, depth) == Some(addr);
                snapshot_walk_persistent_visible_frozen_agree(state, frozen, seq_end, depth);
                assert(snapshot_walk_ptr(visible_records, frozen.boundary_lsn, root, depth) == Some(addr));
                assert(snapshot_walk_domain(visible_records, frozen.boundary_lsn, root).contains(addr));
                assert(visible_image.tj.disk_view.entries.contains_key(addr));
                assert(state.clean_watermark_pages().contains(addr));
                state.clean_watermark_record_eq(addr);
                assert(persistent_records[addr] == visible_records[addr]);
                assert(persistent_image.tj.disk_view.entries[addr] == persistent_records[addr]);
                assert(visible_image.tj.disk_view.entries[addr] == visible_records[addr]);
            }
            if visible_image.tj.disk_view.entries.contains_key(addr) {
                assert(snapshot_walk_domain(visible_records, frozen.boundary_lsn, root).contains(addr));
                let depth = choose |depth: nat|
                    snapshot_walk_ptr(visible_records, frozen.boundary_lsn, root, depth) == Some(addr);
                snapshot_walk_persistent_visible_frozen_agree(state, frozen, seq_end, depth);
                assert(snapshot_walk_ptr(persistent_records, frozen.boundary_lsn, root, depth) == Some(addr));
                assert(snapshot_walk_domain(persistent_records, frozen.boundary_lsn, root).contains(addr));
                assert(persistent_image.tj.disk_view.entries.contains_key(addr));
                assert(state.clean_watermark_pages().contains(addr));
                state.clean_watermark_record_eq(addr);
                assert(persistent_records[addr] == visible_records[addr]);
                assert(persistent_image.tj.disk_view.entries[addr] == persistent_records[addr]);
                assert(visible_image.tj.disk_view.entries[addr] == visible_records[addr]);
            }
        }
    );
    assert(persistent_image.tj == visible_image.tj);
    assert(persistent_image == visible_image);
}

pub proof fn caching_disk_journal_freeze_image_facts(
    state: CachingDiskJournal::State,
    frozen: CachingDiskJournalFrozenImage,
)
    requires
        CachingDiskJournal::State::next(
            state,
            state,
            CachingDiskJournal::Label::FreezeForCommit{
                frozen: frozen.snapshot,
                seq_end: frozen.seq_end,
            },
        ),
    ensures
        frozen.seq_end == state.frozen_seq_end(frozen.snapshot),
{
    let lbl = CachingDiskJournal::Label::FreezeForCommit{
        frozen: frozen.snapshot,
        seq_end: frozen.seq_end,
    };
    reveal(CachingDiskJournal::State::next);
    reveal(CachingDiskJournal::State::next_by);
    let step = choose |step: CachingDiskJournal::Step|
        CachingDiskJournal::State::next_by(state, state, lbl, step);
    match step {
        CachingDiskJournal::Step::freeze_for_commit(reads) => {
            reveal(CachingDiskJournal::State::freeze_for_commit);
        },
        _ => {
            assert(false);
        },
    }
}

pub enum EphemeralCachingDiskJournal {
    Unknown,
    Known{v: CachingDiskJournal::State},
}

state_machine!{ CrashAwareCachingDiskJournal {
    fields {
        pub persistent: CachingDiskJournalImage,
        pub ephemeral: EphemeralCachingDiskJournal,
        pub frozen: Option<CachingDiskJournalFrozenImage>,
        pub prepared: Option<CachingDiskJournalImage>,
    }

    pub enum Label {
        LoadEphemeral,
        ReadForRecovery{records: MsgHistory},
        QueryEndLsn{end_lsn: LSN},
        Put{records: MsgHistory},
        LoadIndex{discovered_aus: Set<AU>},
        ObserveCleanAUs{aus: Set<AU>},
        CommitPrepared,
        Internal,
        InternalAlloc{allocs: Set<AU>, deallocs: Set<AU>, prune_aus: Set<AU>},
        QueryLsnPersistence{sync_lsn: LSN},
        CommitStart{new_boundary_lsn: LSN, snapshot: JournalSnapshot, seq_end: LSN},
        CommitComplete{require_end: LSN, discarded: Set<AU>},
        Crash{keep_in_flight: bool},
    }

    init!{ initialize() {
        init persistent = CachingDiskJournalImage::empty();
        init ephemeral = EphemeralCachingDiskJournal::Unknown;
        init frozen = Option::None;
        init prepared = Option::None;
    }}

    transition!{ load_ephemeral(lbl: Label) {
        require lbl is LoadEphemeral;
        require pre.ephemeral is Unknown;

        update ephemeral = EphemeralCachingDiskJournal::Known{
            v: CachingDiskJournal::State::load_from_persistent(
                pre.persistent.snapshot,
                pre.persistent.live_persistent(),
            ),
        };
    }}

    transition!{ read_for_recovery(lbl: Label) {
        require let Label::ReadForRecovery{records} = lbl;
        require pre.ephemeral is Known;
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            pre.ephemeral->v,
            CachingDiskJournal::Label::ReadForRecovery{messages: records},
        );
    }}

    transition!{ query_end_lsn(lbl: Label) {
        require let Label::QueryEndLsn{end_lsn} = lbl;
        require pre.ephemeral is Known;
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            pre.ephemeral->v,
            CachingDiskJournal::Label::QueryEndLsn{end_lsn},
        );
    }}

    transition!{ put(lbl: Label, new_ephemeral: CachingDiskJournal::State) {
        require let Label::Put{records} = lbl;
        require pre.ephemeral is Known;
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            new_ephemeral,
            CachingDiskJournal::Label::Put{messages: records},
        );

        update ephemeral = EphemeralCachingDiskJournal::Known{v: new_ephemeral};
    }}

    transition!{ load_index(
        lbl: Label,
        new_ephemeral: CachingDiskJournal::State,
    ) {
        require let Label::LoadIndex{discovered_aus} = lbl;
        require pre.ephemeral is Known;
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            new_ephemeral,
            CachingDiskJournal::Label::LoadIndex{discovered_aus},
        );

        update ephemeral = EphemeralCachingDiskJournal::Known{v: new_ephemeral};
    }}

    transition!{ observe_clean_aus(
        lbl: Label,
        new_ephemeral: CachingDiskJournal::State,
    ) {
        require let Label::ObserveCleanAUs{aus} = lbl;
        require pre.ephemeral is Known;
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            new_ephemeral,
            CachingDiskJournal::Label::ObserveCleanAUs{aus},
        );

        update ephemeral = EphemeralCachingDiskJournal::Known{v: new_ephemeral};
    }}

    transition!{ internal(
        lbl: Label,
        new_ephemeral: CachingDiskJournal::State,
    ) {
        require lbl is Internal;
        require pre.ephemeral is Known;
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            new_ephemeral,
            CachingDiskJournal::Label::Internal,
        );

        update ephemeral = EphemeralCachingDiskJournal::Known{v: new_ephemeral};
    }}

    transition!{ internal_alloc(
        lbl: Label,
        new_ephemeral: CachingDiskJournal::State,
    ) {
        require let Label::InternalAlloc{allocs, deallocs, prune_aus} = lbl;
        require pre.ephemeral is Known;
        require allocs.disjoint(caching_disk_journal_accessible_aus(pre.ephemeral->v));
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            new_ephemeral,
            CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus},
        );

        update ephemeral = EphemeralCachingDiskJournal::Known{v: new_ephemeral};
    }}

    transition!{ query_lsn_persistence(lbl: Label) {
        require let Label::QueryLsnPersistence{sync_lsn} = lbl;
        require sync_lsn <= pre.persistent.seq_end();
    }}

    transition!{ commit_prepared(lbl: Label, prepared_image: CachingDiskJournalImage) {
        require lbl is CommitPrepared;
        require pre.ephemeral is Known;
        require pre.frozen is Some;
        require pre.prepared is None;
        let frozen = pre.frozen.unwrap();
        require prepared_image.snapshot == frozen.snapshot;
        require prepared_image.seq_end == frozen.seq_end;
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            pre.ephemeral->v,
            CachingDiskJournal::Label::CommitPrepared{
                frozen: frozen.snapshot,
                seq_end: frozen.seq_end,
                persistent: prepared_image.persistent,
            },
        );

        update prepared = Option::Some(prepared_image);
    }}

    transition!{ commit_start(lbl: Label) {
        require let Label::CommitStart{new_boundary_lsn, snapshot, seq_end} = lbl;
        require pre.ephemeral is Known;
        require pre.frozen is None;
        require pre.prepared is None;
        require snapshot.boundary_lsn == new_boundary_lsn;
        require pre.persistent.seq_end() <= new_boundary_lsn;
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            pre.ephemeral->v,
            CachingDiskJournal::Label::FreezeForCommit{
                frozen: snapshot,
                seq_end,
            },
        );

        update frozen = Option::Some(CachingDiskJournalFrozenImage{snapshot, seq_end});
    }}

    transition!{ commit_complete(
        lbl: Label,
        new_ephemeral: CachingDiskJournal::State,
    ) {
        require let Label::CommitComplete{require_end, discarded} = lbl;
        require pre.ephemeral is Known;
        require pre.frozen is Some;
        require pre.prepared is Some;

        let frozen_image = pre.prepared.unwrap();
        let old_au_index = cj_lsn_au_index(pre.ephemeral->v.journal);
        let new_au_index = lsn_au_index_discard_up_to(
            old_au_index,
            frozen_image.snapshot.boundary_lsn,
        );
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            new_ephemeral,
            CachingDiskJournal::Label::DiscardOld{
                start_lsn: frozen_image.snapshot.boundary_lsn,
                require_end,
            },
        );
        require discarded == old_au_index.values().difference(new_au_index.values());

        update persistent = frozen_image;
        update ephemeral = EphemeralCachingDiskJournal::Known{v: new_ephemeral};
        update frozen = Option::None;
        update prepared = Option::None;
    }}

    transition!{ crash(lbl: Label) {
        require let Label::Crash{keep_in_flight} = lbl;
        require keep_in_flight ==> pre.frozen is Some;
        require keep_in_flight ==> pre.prepared is Some;

        update persistent = if keep_in_flight {
            pre.prepared.unwrap()
        } else {
            pre.persistent
        };
        update ephemeral = EphemeralCachingDiskJournal::Unknown;
        update frozen = Option::None;
        update prepared = Option::None;
    }}

    #[invariant]
    pub open spec fn inv(self) -> bool {
        &&& self.ephemeral is Unknown ==> self.frozen is None && self.prepared is None
        &&& self.persistent.wf()
        &&& self.ephemeral is Known ==> self.ephemeral->v.inv()
        &&& self.ephemeral is Known ==> self.persistent.live_tj().disk_view.entries.dom()
            <= self.ephemeral->v.journal_disk_view().entries.dom()
        &&& self.frozen is Some && self.ephemeral is Known ==> self.ephemeral->v.journal.status is Some
        &&& self.frozen is Some && self.ephemeral is Known && self.prepared is None ==>
            self.ephemeral->v.frozen_snapshot_valid(
                self.frozen.unwrap().snapshot,
                self.frozen.unwrap().seq_end,
            )
        &&& self.prepared is Some ==> {
            &&& self.frozen is Some
            &&& self.prepared.unwrap().i().valid_image()
            &&& self.prepared.unwrap().snapshot == self.frozen.unwrap().snapshot
            &&& self.prepared.unwrap().seq_end == self.frozen.unwrap().seq_end
        }
        &&& self.prepared is Some && self.ephemeral is Known ==> self.prepared.unwrap().i().tj.disk_view.entries.dom()
            <= self.ephemeral->v.journal_disk_view().entries.dom()
        &&& self.prepared is Some && self.ephemeral is Known ==> self.prepared.unwrap().i().tj.disk_view
            .is_sub_disk_with_newer_lsn(self.ephemeral->v.journal_tj().disk_view)
        &&& self.prepared is Some && self.ephemeral is Known ==>
            self.prepared.unwrap().i().tj.freshest_rec is Some ==>
                self.prepared.unwrap().i().tj.seq_end() <= self.ephemeral->v.journal_tj().seq_end()
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) {
        JournalImage::empty_is_valid_image();
        TruncatedJournal::mkfs_ensures();
        assert(post.persistent.i() == JournalImage::empty());
        assert(post.persistent.tj() == TruncatedJournal::mkfs());
        assert(post.persistent.wf());
    }

    #[inductive(load_ephemeral)]
    fn load_ephemeral_inductive(pre: Self, post: Self, lbl: Label) {
        let loaded = CachingDiskJournal::State::load_from_persistent(
            pre.persistent.snapshot,
            pre.persistent.live_persistent(),
        );
        assert(post.ephemeral is Known);
        assert(post.ephemeral->v == loaded);
        assert(loaded.disk.visible() =~= pre.persistent.live_persistent()) by {
            assert forall |addr: Address| #[trigger] loaded.disk.visible().contains_key(addr)
                implies pre.persistent.live_persistent().contains_key(addr) by {
                assert(loaded.disk.cache == Map::<Address, RawPage>::empty());
            }
            assert forall |addr: Address| #[trigger] pre.persistent.live_persistent().contains_key(addr)
                implies loaded.disk.visible().contains_key(addr) by {
                assert(loaded.disk.persistent.contains_key(addr));
            }
        }
        assert(loaded.visible_records().dom() =~= pre.persistent.live_persistent().dom()) by {
            assert forall |addr: Address| #[trigger] loaded.visible_records().dom().contains(addr)
                implies pre.persistent.live_persistent().dom().contains(addr) by {
                assert(loaded.visible_records().contains_key(addr));
                assert(loaded.disk.visible().contains_key(addr));
            }
            assert forall |addr: Address| #[trigger] pre.persistent.live_persistent().dom().contains(addr)
                implies loaded.visible_records().dom().contains(addr) by {
                assert(pre.persistent.live_persistent().contains_key(addr));
                assert(loaded.disk.visible().contains_key(addr));
                assert(loaded.visible_records().contains_key(addr));
            }
        }
        assert(loaded.journal_tj() == pre.persistent.live_tj());
        pre.persistent.valid_image_implies_live_valid_image();
        assert(loaded.visible_journal_structure()) by {
            assert(loaded.journal_tj().decodable());
            assert(loaded.journal_tj().disk_view.wf_addrs());
            assert(loaded.journal_tj().disk_view.pointer_is_upstream(
                loaded.journal_tj().freshest_rec,
                loaded.journal.snapshot.first(),
            ));
            assert(loaded.journal_tj().disk_view.domain_tight_wrt_index(
                loaded.journal_tj().build_lsn_au_index_from_first(loaded.journal.snapshot.first()),
                loaded.journal_tj().freshest_rec,
            ));
            assert(loaded.journal_tj().disk_view.bounded_inactive_lsns(
                loaded.journal_tj().build_lsn_au_index_from_first(loaded.journal.snapshot.first()),
                loaded.journal_tj().freshest_rec,
            ));
            assert(AllocationJournal::State::disk_domain_not_free(
                loaded.journal_tj().disk_view,
                loaded.mini_allocator,
            )) by {
                assert forall |addr: Address| #[trigger] loaded.journal_tj().disk_view.entries.dom().contains(addr)
                    implies !loaded.mini_allocator.can_allocate(addr) by {
                    assert(loaded.visible_records().dom().contains(addr));
                    assert(pre.persistent.live_persistent().dom().contains(addr));
                    assert(to_aus(loaded.disk.visible().dom()).contains(addr.au)) by {
                        let m = Map::new(
                            |addr| loaded.disk.visible().dom().contains(addr),
                            |addr: Address| addr.au,
                        );
                        assert(m.contains_key(addr));
                        assert(m[addr] == addr.au);
                        assert(m.values().contains(addr.au));
                    }
                    assert(loaded.mini_allocator == MiniAllocator::empty());
                    assert(!loaded.mini_allocator.allocs.contains_key(addr.au));
                }
            }
            assert(AllocationJournal::State::mini_allocator_follows_freshest_rec(
                loaded.journal_tj().freshest_rec,
                loaded.mini_allocator,
            ));
        }
        assert(loaded.inv());
        assert(pre.persistent.live_tj().disk_view.entries.dom()
            <= loaded.journal_disk_view().entries.dom()) by {
            assert forall |addr: Address| #[trigger] pre.persistent.live_tj().disk_view.entries.dom().contains(addr)
                implies loaded.journal_disk_view().entries.dom().contains(addr) by {
                assert(pre.persistent.live_tj().disk_view.entries.contains_key(addr));
                assert(pre.persistent.persistent.contains_key(addr));
                assert(loaded.visible_records().contains_key(addr));
            }
        }
    }

    #[inductive(read_for_recovery)]
    fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(query_end_lsn)]
    fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskJournal::State) {
        let cj_lbl = CachingDiskJournal::Label::Put{messages: lbl.arrow_Put_records()};
        CachingDiskJournal::State::inv_next(pre.ephemeral->v, new_ephemeral, cj_lbl);
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre.ephemeral->v, new_ephemeral, cj_lbl, step);
        match step {
            CachingDiskJournal::Step::put(new_journal) => {
                reveal(CachingDiskJournal::State::put);
                CachedJournal::State::put_effect(
                    pre.ephemeral->v.journal,
                    new_ephemeral.journal,
                    lbl.arrow_Put_records(),
                );
            },
            _ => {
                assert(false);
            },
        }
        assert(caching_disk_journal_accessible_aus(pre.ephemeral->v)
            <= caching_disk_journal_accessible_aus(new_ephemeral)) by {
            assert forall |au: AU| #[trigger] caching_disk_journal_accessible_aus(pre.ephemeral->v).contains(au)
                implies caching_disk_journal_accessible_aus(new_ephemeral).contains(au) by {
                assert(new_ephemeral.disk == pre.ephemeral->v.disk);
                assert(new_ephemeral.mini_allocator == pre.ephemeral->v.mini_allocator);
                assert(new_ephemeral.journal.snapshot == pre.ephemeral->v.journal.snapshot);
                assert(new_ephemeral.journal_disk_view() == pre.ephemeral->v.journal_disk_view());
            }
        }
        assert(pre.persistent.live_tj().disk_view.entries.dom()
            <= new_ephemeral.journal_disk_view().entries.dom()) by {
            assert forall |addr: Address| #[trigger] pre.persistent.live_tj().disk_view.entries.dom().contains(addr)
                implies new_ephemeral.journal_disk_view().entries.dom().contains(addr) by {
                assert(pre.ephemeral->v.journal_disk_view().entries.dom().contains(addr));
                assert(new_ephemeral.journal_disk_view() == pre.ephemeral->v.journal_disk_view());
            }
        }
        if pre.prepared is Some {
            assert(pre.prepared.unwrap().i().tj.disk_view.entries.dom()
                <= new_ephemeral.journal_disk_view().entries.dom()) by {
                assert forall |addr: Address| #[trigger] pre.prepared.unwrap().i().tj.disk_view.entries.dom().contains(addr)
                    implies new_ephemeral.journal_disk_view().entries.dom().contains(addr) by {
                    assert(pre.ephemeral->v.journal_disk_view().entries.dom().contains(addr));
                    assert(new_ephemeral.journal_disk_view() == pre.ephemeral->v.journal_disk_view());
                }
            }
            assert(pre.prepared.unwrap().i().tj.disk_view.is_sub_disk_with_newer_lsn(
                new_ephemeral.journal_tj().disk_view,
            ));
            assert(pre.prepared.unwrap().i().tj.freshest_rec is Some ==>
                pre.prepared.unwrap().i().tj.seq_end() <= new_ephemeral.journal_tj().seq_end()) by {
                assert(new_ephemeral.journal_tj() == pre.ephemeral->v.journal_tj());
            }
        }
    }

    #[inductive(load_index)]
    fn load_index_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskJournal::State) {
        let cj_lbl = CachingDiskJournal::Label::LoadIndex{
            discovered_aus: lbl.arrow_LoadIndex_discovered_aus(),
        };
        CachingDiskJournal::State::inv_next(pre.ephemeral->v, new_ephemeral, cj_lbl);
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre.ephemeral->v, new_ephemeral, cj_lbl, step);
        match step {
            CachingDiskJournal::Step::load_index(new_journal, reads) => {
                reveal(CachingDiskJournal::State::load_index);
                CachedJournal::State::load_index_effect(
                    pre.ephemeral->v.journal,
                    new_ephemeral.journal,
                    to_journal_records(reads),
                    lbl.arrow_LoadIndex_discovered_aus(),
                );
            },
            _ => {
                assert(false);
            },
        }
        assert(post.ephemeral is Known);
        assert(post.ephemeral->v == new_ephemeral);
        assert(new_ephemeral.disk == pre.ephemeral->v.disk);
        assert(new_ephemeral.journal.snapshot == pre.ephemeral->v.journal.snapshot);
        assert(new_ephemeral.journal_disk_view() == pre.ephemeral->v.journal_disk_view());
        assert(pre.persistent.live_tj().disk_view.entries.dom()
            <= new_ephemeral.journal_disk_view().entries.dom()) by {
            assert forall |addr: Address| #[trigger] pre.persistent.live_tj().disk_view.entries.dom().contains(addr)
                implies new_ephemeral.journal_disk_view().entries.dom().contains(addr) by {
                assert(pre.ephemeral->v.journal_disk_view().entries.dom().contains(addr));
            }
        }
        if pre.prepared is Some {
            assert(pre.prepared.unwrap().i().tj.disk_view.entries.dom()
                <= new_ephemeral.journal_disk_view().entries.dom()) by {
                assert forall |addr: Address| #[trigger] pre.prepared.unwrap().i().tj.disk_view.entries.dom().contains(addr)
                    implies new_ephemeral.journal_disk_view().entries.dom().contains(addr) by {
                    assert(pre.ephemeral->v.journal_disk_view().entries.dom().contains(addr));
                }
            }
            assert(pre.prepared.unwrap().i().tj.disk_view.is_sub_disk_with_newer_lsn(
                new_ephemeral.journal_tj().disk_view,
            ));
            assert(pre.prepared.unwrap().i().tj.freshest_rec is Some ==>
                pre.prepared.unwrap().i().tj.seq_end() <= new_ephemeral.journal_tj().seq_end()) by {
                assert(new_ephemeral.journal_tj() == pre.ephemeral->v.journal_tj());
            }
        }
    }

    #[inductive(observe_clean_aus)]
    fn observe_clean_aus_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskJournal::State) {
        let cj_lbl = CachingDiskJournal::Label::ObserveCleanAUs{
            aus: lbl.arrow_ObserveCleanAUs_aus(),
        };
        CachingDiskJournal::State::inv_next(pre.ephemeral->v, new_ephemeral, cj_lbl);
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre.ephemeral->v, new_ephemeral, cj_lbl, step);
        match step {
            CachingDiskJournal::Step::observe_clean_aus(new_journal) => {
                reveal(CachingDiskJournal::State::observe_clean_aus);
                CachedJournal::State::observe_clean_aus_effect(
                    pre.ephemeral->v.journal,
                    new_journal,
                    lbl.arrow_ObserveCleanAUs_aus(),
                );
            },
            _ => {
                assert(false);
            },
        }
        assert(post.ephemeral is Known);
        assert(post.ephemeral->v == new_ephemeral);
        assert(new_ephemeral.disk == pre.ephemeral->v.disk);
        assert(new_ephemeral.journal.snapshot == pre.ephemeral->v.journal.snapshot);
        assert(new_ephemeral.journal_disk_view() == pre.ephemeral->v.journal_disk_view());
        assert(pre.persistent.live_tj().disk_view.entries.dom()
            <= new_ephemeral.journal_disk_view().entries.dom()) by {
            assert forall |addr: Address| #[trigger] pre.persistent.live_tj().disk_view.entries.dom().contains(addr)
                implies new_ephemeral.journal_disk_view().entries.dom().contains(addr) by {
                assert(pre.ephemeral->v.journal_disk_view().entries.dom().contains(addr));
            }
        }
        if pre.prepared is Some {
            assert(pre.prepared.unwrap().i().tj.disk_view.entries.dom()
                <= new_ephemeral.journal_disk_view().entries.dom()) by {
                assert forall |addr: Address| #[trigger] pre.prepared.unwrap().i().tj.disk_view.entries.dom().contains(addr)
                    implies new_ephemeral.journal_disk_view().entries.dom().contains(addr) by {
                    assert(pre.ephemeral->v.journal_disk_view().entries.dom().contains(addr));
                }
            }
            assert(pre.prepared.unwrap().i().tj.disk_view.is_sub_disk_with_newer_lsn(
                new_ephemeral.journal_tj().disk_view,
            ));
            assert(pre.prepared.unwrap().i().tj.freshest_rec is Some ==>
                pre.prepared.unwrap().i().tj.seq_end() <= new_ephemeral.journal_tj().seq_end()) by {
                assert(new_ephemeral.journal_tj() == pre.ephemeral->v.journal_tj());
            }
        }
    }

    #[inductive(internal)]
    fn internal_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskJournal::State) {
        assert(CrashAwareCachingDiskJournal::State::internal(pre, post, lbl, new_ephemeral));
        assert(post.ephemeral == EphemeralCachingDiskJournal::Known{v: new_ephemeral});
        assert(post.frozen == pre.frozen);
        assert(post.prepared == pre.prepared);
        let cj_lbl = CachingDiskJournal::Label::Internal;
        CachingDiskJournal::State::inv_next(pre.ephemeral->v, new_ephemeral, cj_lbl);
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre.ephemeral->v, new_ephemeral, cj_lbl, step);
        assert(to_aus(pre.ephemeral->v.journal_disk_view().entries.dom())
            <= to_aus(new_ephemeral.journal_disk_view().entries.dom())) by {
            assert forall |au: AU| #[trigger] to_aus(pre.ephemeral->v.journal_disk_view().entries.dom()).contains(au)
                implies to_aus(new_ephemeral.journal_disk_view().entries.dom()).contains(au) by {
                let addr = choose |addr: Address|
                    pre.ephemeral->v.journal_disk_view().entries.dom().contains(addr) && addr.au == au;
                match step {
                    CachingDiskJournal::Step::caching_disk_internal(new_disk) => {
                        reveal(CachingDiskJournal::State::caching_disk_internal);
                        CachingDisk::State::internal_visible_unchanged(pre.ephemeral->v.disk, new_ephemeral.disk);
                        assert(new_ephemeral.journal_disk_view() == pre.ephemeral->v.journal_disk_view());
                    },
                    CachingDiskJournal::Step::load_index(new_journal, reads) => {
                        reveal(CachingDiskJournal::State::load_index);
                        assert(false);
                    },
                    CachingDiskJournal::Step::journal_marshal(new_journal, new_disk, new_addr, writes) => {
                        reveal(CachingDiskJournal::State::journal_marshal);
                        CachingDisk::State::access_visible_effect(
                            pre.ephemeral->v.disk,
                            new_ephemeral.disk,
                            Map::empty(),
                            writes,
                        );
                        assert(pre.ephemeral->v.visible_records().contains_key(addr));
                        assert(pre.ephemeral->v.disk.visible().contains_key(addr));
                        assert(new_ephemeral.disk.visible().contains_key(addr));
                        assert(new_ephemeral.visible_records().contains_key(addr));
                        assert(new_ephemeral.journal_disk_view().entries.dom().contains(addr));
                    },
                    CachingDiskJournal::Step::internal_noop() => {
                        reveal(CachingDiskJournal::State::internal_noop);
                        assert(new_ephemeral == pre.ephemeral->v);
                    },
                    _ => {
                        assert(false);
                    },
                }
                assert(to_aus(new_ephemeral.journal_disk_view().entries.dom()).contains(au)) by {
                    let m = Map::new(
                        |addr| new_ephemeral.journal_disk_view().entries.dom().contains(addr),
                        |addr: Address| addr.au,
                    );
                    assert(m.contains_key(addr));
                    assert(m[addr] == au);
                    assert(m.values().contains(au));
                }
            }
        }
        assert(pre.ephemeral->v.journal_disk_view().entries.dom()
            <= new_ephemeral.journal_disk_view().entries.dom()) by {
            assert forall |addr: Address| #[trigger] pre.ephemeral->v.journal_disk_view().entries.dom().contains(addr)
                implies new_ephemeral.journal_disk_view().entries.dom().contains(addr) by {
                match step {
                    CachingDiskJournal::Step::caching_disk_internal(new_disk) => {
                        reveal(CachingDiskJournal::State::caching_disk_internal);
                        CachingDisk::State::internal_visible_unchanged(pre.ephemeral->v.disk, new_ephemeral.disk);
                        assert(new_ephemeral.journal_disk_view() == pre.ephemeral->v.journal_disk_view());
                    },
                    CachingDiskJournal::Step::load_index(new_journal, reads) => {
                        reveal(CachingDiskJournal::State::load_index);
                        assert(false);
                    },
                    CachingDiskJournal::Step::journal_marshal(new_journal, new_disk, new_addr, writes) => {
                        reveal(CachingDiskJournal::State::journal_marshal);
                        CachingDisk::State::access_visible_effect(
                            pre.ephemeral->v.disk,
                            new_ephemeral.disk,
                            Map::empty(),
                            writes,
                        );
                        assert(pre.ephemeral->v.visible_records().contains_key(addr));
                        assert(pre.ephemeral->v.disk.visible().contains_key(addr));
                        assert(new_ephemeral.disk.visible().contains_key(addr));
                        assert(new_ephemeral.visible_records().contains_key(addr));
                    },
                    CachingDiskJournal::Step::internal_noop() => {
                        reveal(CachingDiskJournal::State::internal_noop);
                        assert(new_ephemeral == pre.ephemeral->v);
                    },
                    _ => {
                        assert(false);
                    },
                }
            }
        }
        assert(pre.persistent.live_tj().disk_view.entries.dom()
            <= new_ephemeral.journal_disk_view().entries.dom());
        if pre.frozen is Some || pre.prepared is Some {
            CachingDiskJournal::State::internal_extends_journal_view(pre.ephemeral->v, new_ephemeral);
            assert(new_ephemeral.journal.status is Some) by {
                match step {
                    CachingDiskJournal::Step::caching_disk_internal(new_disk) => {
                        reveal(CachingDiskJournal::State::caching_disk_internal);
                        assert(new_ephemeral.journal == pre.ephemeral->v.journal);
                    },
                    CachingDiskJournal::Step::load_index(new_journal, reads) => {
                        reveal(CachingDiskJournal::State::load_index);
                        assert(false);
                    },
                    CachingDiskJournal::Step::journal_marshal(new_journal, new_disk, new_addr, writes) => {
                        reveal(CachingDiskJournal::State::journal_marshal);
                        reveal(CachedJournal::State::next);
                        reveal(CachedJournal::State::next_by);
                        let journal_lbl = CachedJournal::Label::JournalMarshal{
                            writes: to_journal_records(writes),
                        };
                        let cj_step = choose |step: CachedJournal::Step|
                            CachedJournal::State::next_by(pre.ephemeral->v.journal, new_ephemeral.journal, journal_lbl, step);
                        match cj_step {
                            CachedJournal::Step::internal_journal_marshal(cut, addr) => {
                                reveal(CachedJournal::State::internal_journal_marshal);
                            },
                            _ => {
                                assert(false);
                            },
                        }
                    },
                    CachingDiskJournal::Step::internal_noop() => {
                        reveal(CachingDiskJournal::State::internal_noop);
                        assert(new_ephemeral == pre.ephemeral->v);
                    },
                    _ => {
                        assert(false);
                    },
                }
            }
            if pre.prepared is Some {
                assert(pre.prepared.unwrap().i().tj.disk_view.entries.dom()
                    <= new_ephemeral.journal_disk_view().entries.dom());
                assert(pre.prepared.unwrap().i().tj.disk_view.entries
                    <= new_ephemeral.journal_tj().disk_view.entries) by {
                    assert forall |addr: Address| #[trigger] pre.prepared.unwrap().i().tj.disk_view.entries.dom().contains(addr)
                        implies new_ephemeral.journal_tj().disk_view.entries.dom().contains(addr)
                            && pre.prepared.unwrap().i().tj.disk_view.entries[addr]
                                == new_ephemeral.journal_tj().disk_view.entries[addr] by {
                        assert(pre.prepared.unwrap().i().tj.disk_view.entries
                            <= pre.ephemeral->v.journal_tj().disk_view.entries);
                        assert(pre.ephemeral->v.journal_tj().disk_view.entries.dom().contains(addr));
                        assert(pre.prepared.unwrap().i().tj.disk_view.entries[addr]
                            == pre.ephemeral->v.journal_tj().disk_view.entries[addr]);
                        assert(pre.ephemeral->v.journal_tj().disk_view.entries
                            <= new_ephemeral.journal_tj().disk_view.entries);
                    }
                }
                assert(pre.prepared.unwrap().i().tj.disk_view.is_sub_disk_with_newer_lsn(
                    new_ephemeral.journal_tj().disk_view,
                ));
                assert(pre.prepared.unwrap().i().tj.freshest_rec is Some ==>
                    pre.prepared.unwrap().i().tj.seq_end() <= new_ephemeral.journal_tj().seq_end()) by {
                    if pre.prepared.unwrap().i().tj.freshest_rec is Some {
                        assert(pre.prepared.unwrap().i().tj.seq_end()
                            <= pre.ephemeral->v.journal_tj().seq_end());
                        assert(pre.ephemeral->v.journal_tj().seq_end()
                            <= new_ephemeral.journal_tj().seq_end());
                    }
                }
            }
            if pre.frozen is Some && pre.prepared is None {
                let frozen = pre.frozen.unwrap();
                assert(pre.ephemeral->v.frozen_snapshot_valid(frozen.snapshot, frozen.seq_end));
                match step {
                    CachingDiskJournal::Step::caching_disk_internal(new_disk) => {
                        reveal(CachingDiskJournal::State::caching_disk_internal);
                        CachingDisk::State::internal_visible_unchanged(pre.ephemeral->v.disk, new_ephemeral.disk);
                        assert(new_ephemeral.journal == pre.ephemeral->v.journal);
                        assert(new_ephemeral.journal_tj() == pre.ephemeral->v.journal_tj());
                        assert(new_ephemeral.frozen_snapshot_valid(frozen.snapshot, frozen.seq_end));
                    },
                    CachingDiskJournal::Step::internal_noop() => {
                        reveal(CachingDiskJournal::State::internal_noop);
                        assert(new_ephemeral == pre.ephemeral->v);
                        assert(new_ephemeral.frozen_snapshot_valid(frozen.snapshot, frozen.seq_end));
                    },
                    CachingDiskJournal::Step::journal_marshal(new_journal, new_disk, new_addr, writes) => {
                        reveal(CachingDiskJournal::State::journal_marshal);
                        reveal(CachedJournal::State::next);
                        reveal(CachedJournal::State::next_by);
                        let journal_lbl = CachedJournal::Label::JournalMarshal{
                            writes: to_journal_records(writes),
                        };
                        let cj_step = choose |step: CachedJournal::Step|
                            CachedJournal::State::next_by(pre.ephemeral->v.journal, new_ephemeral.journal, journal_lbl, step);
                        let (cut, addr) = match cj_step {
                            CachedJournal::Step::internal_journal_marshal(cut, addr) => {
                                reveal(CachedJournal::State::internal_journal_marshal);
                                (cut, addr)
                            },
                            _ => {
                                assert(false);
                                arbitrary()
                            },
                        };
                        let marshalled_msgs = pre.ephemeral->v.journal.status.unwrap().unmarshalled_tail.discard_recent(cut);
                        assert(new_ephemeral.journal.status.unwrap().lsn_au_index
                            == lsn_au_index_append_record(
                                pre.ephemeral->v.journal.status.unwrap().lsn_au_index,
                                marshalled_msgs,
                                addr.au,
                            ));
                        assert(new_ephemeral.journal.status is Some);
                        assert(new_ephemeral.journal_tj().seq_start()
                            == pre.ephemeral->v.journal_tj().seq_start());
                        assert(pre.ephemeral->v.journal_tj().seq_start() <= frozen.snapshot.boundary_lsn);
                        if frozen.snapshot.freshest_rec() is Some {
                            let root = frozen.snapshot.freshest_rec().unwrap();
                            assert(pre.ephemeral->v.journal_tj().disk_view.entries.contains_key(root));
                            assert(pre.ephemeral->v.journal_tj().disk_view.entries
                                <= new_ephemeral.journal_tj().disk_view.entries);
                            assert(new_ephemeral.journal_tj().disk_view.entries.contains_key(root));
                            assert(new_ephemeral.journal_tj().disk_view.entries[root]
                                == pre.ephemeral->v.journal_tj().disk_view.entries[root]);
                            assert(new_ephemeral.frozen_seq_end(frozen.snapshot)
                                == pre.ephemeral->v.frozen_seq_end(frozen.snapshot));
                            assert(frozen.seq_end <= pre.ephemeral->v.journal_tj().seq_end());
                            assert(pre.ephemeral->v.journal_tj().seq_end()
                                <= new_ephemeral.journal_tj().seq_end());
                            assert(pre.ephemeral->v.journal.status.unwrap().lsn_au_index.contains_key(
                                frozen.snapshot.boundary_lsn,
                            ));
                            assert(pre.ephemeral->v.journal.status.unwrap().lsn_au_index[frozen.snapshot.boundary_lsn]
                                == frozen.snapshot.first());
                            assert(frozen.snapshot.boundary_lsn < marshalled_msgs.seq_start) by {
                                assert(frozen.seq_end
                                    == pre.ephemeral->v.frozen_seq_end(frozen.snapshot));
                                assert(frozen.seq_end <= pre.ephemeral->v.journal_tj().seq_end());
                                assert(pre.ephemeral->v.journal_tj().seq_end()
                                    == pre.ephemeral->v.journal.marshalled_seq_end());
                                assert(marshalled_msgs.seq_start
                                    == pre.ephemeral->v.journal.marshalled_seq_end());
                            }
                            assert(!singleton_index(
                                marshalled_msgs.seq_start,
                                marshalled_msgs.seq_end,
                                addr.au,
                            ).contains_key(frozen.snapshot.boundary_lsn));
                            assert(new_ephemeral.lsn_au_index_or_empty().contains_key(
                                frozen.snapshot.boundary_lsn,
                            ));
                            assert(new_ephemeral.lsn_au_index_or_empty()[frozen.snapshot.boundary_lsn]
                                == frozen.snapshot.first());
                        } else {
                            assert(new_ephemeral.frozen_seq_end(frozen.snapshot)
                                == pre.ephemeral->v.frozen_seq_end(frozen.snapshot));
                        }
                        assert(new_ephemeral.frozen_snapshot_valid(frozen.snapshot, frozen.seq_end));
                    },
                    _ => {
                        assert(false);
                    },
                }
                assert(new_ephemeral.frozen_snapshot_valid(frozen.snapshot, frozen.seq_end));
                assert(post.frozen.unwrap() == frozen);
                assert(post.ephemeral->v == new_ephemeral);
                assert(post.ephemeral->v.frozen_snapshot_valid(
                    post.frozen.unwrap().snapshot,
                    post.frozen.unwrap().seq_end,
                ));
            }
        }
    }

    #[inductive(internal_alloc)]
    fn internal_alloc_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskJournal::State) {
        let cj_lbl = CachingDiskJournal::Label::InternalAlloc{
            allocs: lbl.arrow_InternalAlloc_allocs(),
            deallocs: lbl.arrow_InternalAlloc_deallocs(),
            prune_aus: lbl.arrow_InternalAlloc_prune_aus(),
        };
        CachingDiskJournal::State::inv_next(pre.ephemeral->v, new_ephemeral, cj_lbl);
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre.ephemeral->v, new_ephemeral, cj_lbl, step);
        match step {
            CachingDiskJournal::Step::mini_allocator_fill() => {
                reveal(CachingDiskJournal::State::mini_allocator_fill);
            },
            CachingDiskJournal::Step::mini_allocator_prune() => {
                reveal(CachingDiskJournal::State::mini_allocator_prune);
            },
            _ => {
                assert(false);
            },
        }
        assert(new_ephemeral.journal == pre.ephemeral->v.journal);
        assert(new_ephemeral.disk == pre.ephemeral->v.disk);
        assert(new_ephemeral.journal_disk_view() == pre.ephemeral->v.journal_disk_view());
    }

    #[inductive(query_lsn_persistence)]
    fn query_lsn_persistence_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(commit_start)]
    fn commit_start_inductive(pre: Self, post: Self, lbl: Label) {
        let frozen_image = CachingDiskJournalFrozenImage{
            snapshot: lbl.arrow_CommitStart_snapshot(),
            seq_end: lbl.arrow_CommitStart_seq_end(),
        };
        let cj_lbl = CachingDiskJournal::Label::FreezeForCommit{
            frozen: frozen_image.snapshot,
            seq_end: frozen_image.seq_end,
        };
        CachingDiskJournal::State::inv_next(pre.ephemeral->v, pre.ephemeral->v, cj_lbl);
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre.ephemeral->v, pre.ephemeral->v, cj_lbl, step);
        match step {
            CachingDiskJournal::Step::freeze_for_commit(reads) => {
                reveal(CachingDiskJournal::State::freeze_for_commit);
                reveal(CachedJournal::State::next);
                reveal(CachedJournal::State::next_by);
                let journal_lbl = CachedJournal::Label::FreezeForCommit{
                    frozen: frozen_image.snapshot,
                    reads: to_journal_records(reads),
                };
                let cj_step = choose |step: CachedJournal::Step|
                    CachedJournal::State::next_by(pre.ephemeral->v.journal, pre.ephemeral->v.journal, journal_lbl, step);
                match cj_step {
                    CachedJournal::Step::freeze_for_commit() => {
                        reveal(CachedJournal::State::freeze_for_commit);
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
        assert(pre.ephemeral->v.journal.status is Some);
        pre.ephemeral->v.freeze_for_commit_image_valid(
            frozen_image.snapshot,
            frozen_image.seq_end,
        );
        caching_disk_journal_freeze_image_facts(pre.ephemeral->v, frozen_image);
        assert(frozen_image.seq_end == pre.ephemeral->v.frozen_seq_end(frozen_image.snapshot));
        assert((JournalImage{
            tj: pre.ephemeral->v.frozen_tj(frozen_image.snapshot),
            first: frozen_image.snapshot.first(),
        }).valid_image());
    }

    #[inductive(commit_prepared)]
    fn commit_prepared_inductive(pre: Self, post: Self, lbl: Label, prepared_image: CachingDiskJournalImage) {
        let frozen = pre.frozen.unwrap();
        let cj_lbl = CachingDiskJournal::Label::CommitPrepared{
            frozen: frozen.snapshot,
            seq_end: frozen.seq_end,
            persistent: prepared_image.persistent,
        };
        assert(CrashAwareCachingDiskJournal::State::commit_prepared(pre, post, lbl, prepared_image));
        assert(CachingDiskJournal::State::next(pre.ephemeral->v, pre.ephemeral->v, cj_lbl));
        assert(post.prepared == Option::Some(prepared_image));
        assert(prepared_image.snapshot == frozen.snapshot);
        assert(prepared_image.seq_end == frozen.seq_end);
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre.ephemeral->v, pre.ephemeral->v, cj_lbl, step);
        match step {
            CachingDiskJournal::Step::commit_prepared() => {
                if frozen.snapshot.freshest_rec() is Some {
                    assert(frozen.seq_end <= pre.ephemeral->v.journal.clean_watermark());
                }
            },
            _ => { assert(false); },
        }
        assert(prepared_image.persistent == pre.ephemeral->v.disk.persistent);
        pre.ephemeral->v.frozen_snapshot_valid_image(frozen.snapshot, frozen.seq_end);
        let frozen_journal = JournalImage{
            tj: pre.ephemeral->v.frozen_tj(frozen.snapshot),
            first: frozen.snapshot.first(),
        };
        frozen_journal.valid_image_implies_tight_valid_image();
        assert(concrete_frozen_image(pre.ephemeral->v, frozen.snapshot).valid_image());
        pre.ephemeral->v.frozen_tight_domain_clean_watermark(frozen.snapshot, frozen.seq_end);
        pre.ephemeral->v.clean_watermark_disk_view_wf();
        pre.ephemeral->v.clean_watermark_persistent_records_eq();
        pre.ephemeral->v.frozen_tight_subdisk_clean_watermark(frozen.snapshot, frozen.seq_end);
        prepared_snapshot_image_matches_visible(pre.ephemeral->v, prepared_image, frozen.seq_end);
        visible_snapshot_image_matches_concrete_frozen(pre.ephemeral->v, frozen.snapshot, frozen.seq_end);
        assert(prepared_image.i()
            == snapshot_tight_image(pre.ephemeral->v.journal_disk_view().entries, frozen.snapshot));
        assert(snapshot_tight_image(pre.ephemeral->v.journal_disk_view().entries, frozen.snapshot)
            == concrete_frozen_image(pre.ephemeral->v, frozen.snapshot));
        assert(prepared_image.i() == concrete_frozen_image(pre.ephemeral->v, frozen.snapshot));
        assert(prepared_image.i().valid_image());
    }

    #[inductive(commit_complete)]
    fn commit_complete_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskJournal::State) {
        let frozen_image = pre.prepared.unwrap();
        let cj_lbl = CachingDiskJournal::Label::DiscardOld{
            start_lsn: frozen_image.snapshot.boundary_lsn,
            require_end: lbl.arrow_CommitComplete_require_end(),
        };
        CachingDiskJournal::State::inv_next(pre.ephemeral->v, new_ephemeral, cj_lbl);
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre.ephemeral->v, new_ephemeral, cj_lbl, step);
        match step {
            CachingDiskJournal::Step::discard_old(new_journal, new_disk) => {
                reveal(CachingDiskJournal::State::discard_old);
                let old_au_index = cj_lsn_au_index(pre.ephemeral->v.journal);
                let new_au_index = lsn_au_index_discard_up_to(
                    old_au_index,
                    frozen_image.snapshot.boundary_lsn,
                );
                let deallocs = old_au_index.values().difference(new_au_index.values());
                CachingDisk::State::forget_effect(
                    pre.ephemeral->v.disk,
                    new_ephemeral.disk,
                    deallocs,
                );
                let frozen_index = frozen_image.i().tj.build_lsn_au_index_from_first(
                    frozen_image.snapshot.first(),
                );
                frozen_image.i().tj.build_lsn_au_index_from_first_ensures(
                    frozen_image.snapshot.first(),
                );
                lsn_au_index_discard_up_to_ensures(
                    old_au_index,
                    frozen_image.snapshot.boundary_lsn,
                );
                if frozen_image.i().tj.freshest_rec is Some {
                    assert(frozen_index <= old_au_index) by {
                        frozen_image.i().tj.sub_disk_build_sub_lsn_au_index(
                            frozen_image.snapshot.first(),
                            pre.ephemeral->v.journal_tj(),
                            pre.ephemeral->v.journal.snapshot.first(),
                        );
                    }
                }
                assert(frozen_image.i().tj.disk_view.entries.dom()
                    <= new_ephemeral.journal_disk_view().entries.dom()) by {
                    assert forall |addr: Address| #[trigger] frozen_image.i().tj.disk_view.entries.dom().contains(addr)
                        implies new_ephemeral.journal_disk_view().entries.dom().contains(addr) by {
                        assert(frozen_image.i().tj.disk_view.entries.contains_key(addr));
                        if frozen_image.i().tj.freshest_rec is None {
                            assert(frozen_index.values().contains(addr.au)) by {
                                assert(frozen_image.i().valid_image());
                                assert(frozen_image.i().tj.disk_view.domain_au_bounded_wrt_index(
                                    frozen_index,
                                ));
                            }
                            assert(false);
                        } else {
                            assert(frozen_index.values().contains(addr.au)) by {
                                assert(frozen_image.i().valid_image());
                                assert(frozen_image.i().tj.disk_view.domain_au_bounded_wrt_index(
                                    frozen_index,
                                ));
                            }
                            let lsn = choose |lsn: LSN| #![auto]
                                frozen_index.contains_key(lsn) && frozen_index[lsn] == addr.au;
                            assert(frozen_index.contains_key(lsn));
                            assert(old_au_index.contains_key(lsn));
                            assert(old_au_index[lsn] == addr.au);
                            reveal(TruncatedJournal::au_domain_valid);
                            assert(frozen_image.i().tj.seq_start() <= lsn);
                            assert(frozen_image.snapshot.boundary_lsn <= lsn);
                            assert(new_au_index.contains_key(lsn));
                            assert(new_au_index[lsn] == addr.au);
                            assert(new_au_index.values().contains(addr.au));
                            assert(!deallocs.contains(addr.au));
                            assert(!addresses_in_aus(deallocs).contains(addr));
                            assert(frozen_image.i().tj.disk_view.entries
                                <= pre.ephemeral->v.journal_tj().disk_view.entries);
                            assert(pre.ephemeral->v.journal_tj().disk_view.entries.dom().contains(addr));
                            assert(pre.ephemeral->v.visible_records().contains_key(addr));
                            assert(pre.ephemeral->v.disk.visible().contains_key(addr));
                            assert(new_ephemeral.disk.visible().contains_key(addr));
                            assert(new_ephemeral.visible_records().contains_key(addr));
                        }
                    }
                }
            },
            _ => {
                assert(false);
            },
        }
    }

    #[inductive(crash)]
    fn crash_inductive(pre: Self, post: Self, lbl: Label) {}

    pub proof fn inv_next(pre: Self, post: Self, lbl: Label)
        requires
            pre.inv(),
            CrashAwareCachingDiskJournal::State::next(pre, post, lbl),
        ensures
            post.inv(),
    {
        reveal(CrashAwareCachingDiskJournal::State::next);
        reveal(CrashAwareCachingDiskJournal::State::next_by);

        let step = choose |step| CrashAwareCachingDiskJournal::State::next_by(pre, post, lbl, step);
        match step {
            CrashAwareCachingDiskJournal::Step::load_ephemeral() => {
                assert(CrashAwareCachingDiskJournal::State::load_ephemeral(pre, post, lbl)) by {
                }
                CrashAwareCachingDiskJournal::State::load_ephemeral_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::read_for_recovery() => {
                assert(CrashAwareCachingDiskJournal::State::read_for_recovery(pre, post, lbl)) by {
                }
                CrashAwareCachingDiskJournal::State::read_for_recovery_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::query_end_lsn() => {
                assert(CrashAwareCachingDiskJournal::State::query_end_lsn(pre, post, lbl)) by {
                }
                CrashAwareCachingDiskJournal::State::query_end_lsn_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::put(new_ephemeral) => {
                assert(CrashAwareCachingDiskJournal::State::put(pre, post, lbl, new_ephemeral)) by {
                }
                CrashAwareCachingDiskJournal::State::put_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::load_index(new_ephemeral) => {
                assert(CrashAwareCachingDiskJournal::State::load_index(pre, post, lbl, new_ephemeral)) by {
                }
                CrashAwareCachingDiskJournal::State::load_index_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::observe_clean_aus(new_ephemeral) => {
                assert(CrashAwareCachingDiskJournal::State::observe_clean_aus(pre, post, lbl, new_ephemeral)) by {
                }
                CrashAwareCachingDiskJournal::State::observe_clean_aus_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::internal(new_ephemeral) => {
                assert(CrashAwareCachingDiskJournal::State::internal(pre, post, lbl, new_ephemeral)) by {
                }
                CrashAwareCachingDiskJournal::State::internal_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::internal_alloc(new_ephemeral) => {
                assert(CrashAwareCachingDiskJournal::State::internal_alloc(pre, post, lbl, new_ephemeral)) by {
                }
                CrashAwareCachingDiskJournal::State::internal_alloc_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::query_lsn_persistence() => {
                assert(CrashAwareCachingDiskJournal::State::query_lsn_persistence(pre, post, lbl)) by {
                }
                CrashAwareCachingDiskJournal::State::query_lsn_persistence_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::commit_start() => {
                assert(CrashAwareCachingDiskJournal::State::commit_start(pre, post, lbl)) by {
                }
                CrashAwareCachingDiskJournal::State::commit_start_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::commit_prepared(prepared_image) => {
                assert(CrashAwareCachingDiskJournal::State::commit_prepared(pre, post, lbl, prepared_image)) by {
                }
                CrashAwareCachingDiskJournal::State::commit_prepared_inductive(pre, post, lbl, prepared_image);
            },
            CrashAwareCachingDiskJournal::Step::commit_complete(new_ephemeral) => {
                assert(CrashAwareCachingDiskJournal::State::commit_complete(pre, post, lbl, new_ephemeral)) by {
                }
                CrashAwareCachingDiskJournal::State::commit_complete_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::crash() => {
                assert(CrashAwareCachingDiskJournal::State::crash(pre, post, lbl)) by {
                }
                CrashAwareCachingDiskJournal::State::crash_inductive(pre, post, lbl);
            },
            _ => {
                assert(post.inv());
            },
        }
    }
}}

} // verus!
