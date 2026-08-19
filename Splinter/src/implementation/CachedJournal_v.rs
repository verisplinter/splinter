// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
use vstd::prelude::*;
use vstd::map::*;
use vstd::math::*;
use vstd::assert_maps_equal;

//use vstd::prelude_macros::*;
use verus_state_machines_macros::state_machine;

use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::disk::GenericDisk_v::{Address, AU, Pointer, to_aus, to_aus_domain};
use crate::journal::LinkedJournal_v::{DiskView, JournalRecord};
use crate::allocation_layer::AllocationJournal_v::{
    AUPageBounds, LsnAUIndex, lsn_au_index_append_record, lsn_au_index_discard_up_to,
};
use crate::allocation_layer::LikesJournal_v::*;

// this is a version of the journal where
// content does not live in the journal disk view but accessed through the cache
// to take just this we want to have an equivalent of crop but with lsnaddrindex

verus!{

#[verifier::ext_equal]
pub struct JournalRoot {
    pub freshest_rec: Address,
    pub first: AU,
}

pub open spec fn journal_root_pointer(root: Option<JournalRoot>) -> Pointer {
    if root is Some {
        Some(root.unwrap().freshest_rec)
    } else {
        None
    }
}

pub open spec fn journal_root_first(root: Option<JournalRoot>) -> AU {
    if root is Some {
        root.unwrap().first
    } else {
        0
    }
}

pub open spec fn addr_to_lsns(lsn_addr_index: LsnAddrIndex, addr: Address, bdy: LSN) -> Set<LSN>
{
    Set::new(|lsn| bdy <= lsn && lsn_addr_index.contains_key(lsn) && lsn_addr_index[lsn] == addr)
}

pub open spec fn maxmax_au(index: LsnAUIndex, au: AU, lsn: LSN) -> bool
{
    &&& index.contains_pair(lsn, au)
    &&& forall |other_lsn| (#[trigger] index.contains_key(other_lsn)
        && index[other_lsn] == au) ==> other_lsn <= lsn
}

pub open spec fn largest_lsn_plus_one_au(index: LsnAUIndex, au: AU) -> LSN
    recommends
        index.contains_value(au),
{
    let max_lsn = choose |lsn: LSN| maxmax_au(index, au, lsn);
    (max_lsn + 1) as nat
}

pub open spec fn page_walk_reads_cover(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
) -> bool
    decreases depth
{
    if root is None {
        true
    } else if depth == 0 {
        false
    } else {
        &&& reads.contains_key(root.unwrap())
        &&& page_walk_reads_cover(
            reads,
            boundary_lsn,
            reads[root.unwrap()].cropped_prior(boundary_lsn),
            (depth - 1) as nat,
        )
    }
}

pub open spec fn page_walk_reads_prefix(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
    next: Pointer,
) -> bool
    decreases depth
{
    if depth == 0 {
        root == next
    } else if root is Some {
        &&& reads.contains_key(root.unwrap())
        &&& page_walk_reads_prefix(
            reads,
            boundary_lsn,
            reads[root.unwrap()].cropped_prior(boundary_lsn),
            (depth - 1) as nat,
            next,
        )
    } else {
        next is None
    }
}

pub proof fn page_walk_reads_prefix_extend(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
    addr: Address,
    data: JournalRecord,
)
    requires
        page_walk_reads_prefix(reads, boundary_lsn, root, depth, Some(addr)),
        !reads.contains_key(addr),
    ensures
        page_walk_reads_prefix(
            reads.insert(addr, data),
            boundary_lsn,
            root,
            depth + 1,
            data.cropped_prior(boundary_lsn),
        ),
    decreases depth,
{
    if depth == 0 {
        assert(root == Some(addr));
        assert(reads.insert(addr, data)[addr] == data);
        assert((depth + 1) - 1 == depth);
        assert(page_walk_reads_prefix(
            reads.insert(addr, data),
            boundary_lsn,
            data.cropped_prior(boundary_lsn),
            depth,
            data.cropped_prior(boundary_lsn),
        ));
    } else {
        assert(root is Some);
        let root_addr = root.unwrap();
        assert(reads.contains_key(root_addr));
        assert(root_addr != addr);
        page_walk_reads_prefix_extend(
            reads,
            boundary_lsn,
            reads[root_addr].cropped_prior(boundary_lsn),
            (depth - 1) as nat,
            addr,
            data,
        );
        assert(reads.insert(addr, data)[root_addr] == reads[root_addr]);
        assert(reads.insert(addr, data)[root_addr].cropped_prior(boundary_lsn)
            == reads[root_addr].cropped_prior(boundary_lsn));
        assert((depth + 1) - 1 == depth);
        assert(page_walk_reads_prefix(
            reads.insert(addr, data),
            boundary_lsn,
            reads[root_addr].cropped_prior(boundary_lsn),
            depth,
            data.cropped_prior(boundary_lsn),
        ));
    }
}

pub proof fn page_walk_reads_prefix_complete(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
)
    requires
        page_walk_reads_prefix(reads, boundary_lsn, root, depth, None),
    ensures
        page_walk_reads_cover(reads, boundary_lsn, root, depth),
    decreases depth,
{
    if depth == 0 {
        assert(root is None);
    } else if root is Some {
        let addr = root.unwrap();
        page_walk_reads_prefix_complete(
            reads,
            boundary_lsn,
            reads[addr].cropped_prior(boundary_lsn),
            (depth - 1) as nat,
        );
    }
}

pub proof fn page_walk_reads_cover_monotonic_depth(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    small_depth: nat,
    large_depth: nat,
)
    requires
        page_walk_reads_cover(reads, boundary_lsn, root, small_depth),
        small_depth <= large_depth,
    ensures
        page_walk_reads_cover(reads, boundary_lsn, root, large_depth),
    decreases small_depth,
{
    if root is Some {
        if small_depth == 0 {
            assert(false);
        } else {
            assert(large_depth > 0);
            let addr = root.unwrap();
            let next = reads[addr].cropped_prior(boundary_lsn);
            page_walk_reads_cover_monotonic_depth(
                reads,
                boundary_lsn,
                next,
                (small_depth - 1) as nat,
                (large_depth - 1) as nat,
            );
        }
    }
}

pub open spec fn au_walk_reads_cover(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    page_depth: nat,
) -> bool
    decreases au_depth
{
    if root is None {
        true
    } else if au_depth == 0 {
        false
    } else {
        let addr = root.unwrap();
        if addr.au == first {
            page_walk_reads_cover(reads, boundary_lsn, root, page_depth)
        } else {
            let bottom = addr.first_page();
            &&& reads.contains_key(addr)
            &&& reads.contains_key(bottom)
            &&& au_walk_reads_cover(
                reads,
                boundary_lsn,
                reads[bottom].cropped_prior(boundary_lsn),
                first,
                (au_depth - 1) as nat,
                page_depth,
            )
        }
    }
}

pub proof fn au_walk_reads_cover_monotonic_page_depth(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    small_page_depth: nat,
    large_page_depth: nat,
)
    requires
        au_walk_reads_cover(reads, boundary_lsn, root, first, au_depth, small_page_depth),
        small_page_depth <= large_page_depth,
    ensures
        au_walk_reads_cover(reads, boundary_lsn, root, first, au_depth, large_page_depth),
    decreases au_depth,
{
    if root is Some && au_depth > 0 {
        let addr = root.unwrap();
        if addr.au == first {
            page_walk_reads_cover_monotonic_depth(
                reads,
                boundary_lsn,
                root,
                small_page_depth,
                large_page_depth,
            );
        } else {
            let bottom = addr.first_page();
            let next = reads[bottom].cropped_prior(boundary_lsn);
            au_walk_reads_cover_monotonic_page_depth(
                reads,
                boundary_lsn,
                next,
                first,
                (au_depth - 1) as nat,
                small_page_depth,
                large_page_depth,
            );
        }
    }
}

pub proof fn page_walk_reads_cover_contains_same_au_bottom(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    depth: nat,
)
    requires
        page_walk_reads_cover(reads, boundary_lsn, root, depth),
        root is Some,
        root.unwrap().au != first,
        (DiskView{boundary_lsn, entries}).pointer_is_upstream(root, first),
        forall |addr: Address| #[trigger] reads.contains_key(addr)
            && entries.contains_key(addr) ==> reads[addr] == entries[addr],
    ensures
        reads.contains_key(root.unwrap().first_page()),
        page_walk_reads_cover(
            reads,
            boundary_lsn,
            (DiskView{boundary_lsn, entries}).next(Some(root.unwrap().first_page())),
            (depth - 1) as nat,
        ),
    decreases root.unwrap().page,
{
    let dv = DiskView{boundary_lsn, entries};
    let addr = root.unwrap();
    assert(depth > 0);
    assert(reads.contains_key(addr));
    assert(entries.contains_key(addr));
    assert(reads[addr] == entries[addr]);
    assert(reads[addr].cropped_prior(boundary_lsn) == dv.next(root));
    if addr.page == 0 {
        assert(addr.first_page() == addr);
    } else {
        dv.nonfirst_pages(addr, first);
        assert(dv.entries[addr].prior_rec == Some(addr.previous()));
        assert(dv.entries[addr].cropped_prior(boundary_lsn) == Some(addr.previous()));
        assert(dv.next(root) == Some(addr.previous()));
        assert(addr.previous().au == addr.au);
        assert(addr.previous().page < addr.page);
        assert(dv.pointer_is_upstream(Some(addr.previous()), first));
        page_walk_reads_cover_contains_same_au_bottom(
            reads,
            entries,
            boundary_lsn,
            Some(addr.previous()),
            first,
            (depth - 1) as nat,
        );
        page_walk_reads_cover_monotonic_depth(
            reads,
            boundary_lsn,
            dv.next(Some(addr.first_page())),
            ((depth - 1) as nat - 1) as nat,
            (depth - 1) as nat,
        );
    }
}

pub proof fn page_walk_reads_cover_to_au_walk_reads_cover(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    depth: nat,
)
    requires
        page_walk_reads_cover(reads, boundary_lsn, root, depth),
        (DiskView{boundary_lsn, entries}).pointer_is_upstream(root, first),
        forall |addr: Address| #[trigger] reads.contains_key(addr)
            && entries.contains_key(addr) ==> reads[addr] == entries[addr],
    ensures
        au_walk_reads_cover(reads, boundary_lsn, root, first, depth, depth),
    decreases depth,
{
    let dv = DiskView{boundary_lsn, entries};
    if root is Some {
        assert(depth > 0);
        let addr = root.unwrap();
        if addr.au == first {
        } else {
            let bottom = addr.first_page();
            page_walk_reads_cover_contains_same_au_bottom(
                reads,
                entries,
                boundary_lsn,
                root,
                first,
                depth,
            );
            dv.bottom_properties(root, first);
            assert(reads.contains_key(addr));
            assert(reads.contains_key(bottom));
            assert(entries.contains_key(bottom));
            assert(reads[bottom] == entries[bottom]);
            let next = reads[bottom].cropped_prior(boundary_lsn);
            assert(next == dv.next(Some(bottom)));
            assert(dv.pointer_is_upstream(next, first));
            page_walk_reads_cover_to_au_walk_reads_cover(
                reads,
                entries,
                boundary_lsn,
                next,
                first,
                (depth - 1) as nat,
            );
            au_walk_reads_cover_monotonic_page_depth(
                reads,
                boundary_lsn,
                next,
                first,
                (depth - 1) as nat,
                (depth - 1) as nat,
                depth,
            );
        }
    }
}

pub open spec fn page_walk_addrs_in(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
    addrs: Set<Address>,
) -> bool
    decreases depth
{
    if root is None {
        true
    } else if depth == 0 {
        false
    } else {
        &&& addrs.contains(root.unwrap())
        &&& page_walk_addrs_in(
            reads,
            boundary_lsn,
            reads[root.unwrap()].cropped_prior(boundary_lsn),
            (depth - 1) as nat,
            addrs,
        )
    }
}

pub open spec fn au_walk_addrs_in(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    page_depth: nat,
    addrs: Set<Address>,
) -> bool
    decreases au_depth
{
    if root is None {
        true
    } else if au_depth == 0 {
        false
    } else {
        let addr = root.unwrap();
        if addr.au == first {
            page_walk_addrs_in(reads, boundary_lsn, root, page_depth, addrs)
        } else {
            let bottom = addr.first_page();
            &&& addrs.contains(addr)
            &&& addrs.contains(bottom)
            &&& au_walk_addrs_in(
                reads,
                boundary_lsn,
                reads[bottom].cropped_prior(boundary_lsn),
                first,
                (au_depth - 1) as nat,
                page_depth,
                addrs,
            )
        }
    }
}

pub proof fn page_walk_addrs_in_entries_subset(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
    addrs: Set<Address>,
)
    requires
        page_walk_reads_cover(reads, boundary_lsn, root, depth),
        (DiskView{boundary_lsn, entries}).decodable(root),
        (DiskView{boundary_lsn, entries}).acyclic(),
        forall |addr: Address| #[trigger] reads.contains_key(addr)
            && entries.contains_key(addr) ==> reads[addr] == entries[addr],
        forall |addr: Address| #[trigger] entries.contains_key(addr) ==> addrs.contains(addr),
    ensures
        page_walk_addrs_in(reads, boundary_lsn, root, depth, addrs),
    decreases depth,
{
    let dv = DiskView{boundary_lsn, entries};
    if root is Some && depth > 0 {
        let addr = root.unwrap();
        assert(reads.contains_key(addr));
        assert(entries.contains_key(addr));
        assert(addrs.contains(addr));
        assert(reads[addr] == entries[addr]);
        let next = reads[addr].cropped_prior(boundary_lsn);
        assert(next == dv.next(root));
        assert(dv.decodable(next));
        page_walk_addrs_in_entries_subset(
            reads,
            entries,
            boundary_lsn,
            next,
            (depth - 1) as nat,
            addrs,
        );
    }
}

pub proof fn au_walk_addrs_in_entries_subset(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    page_depth: nat,
    addrs: Set<Address>,
)
    requires
        au_walk_reads_cover(reads, boundary_lsn, root, first, au_depth, page_depth),
        (DiskView{boundary_lsn, entries}).pointer_is_upstream(root, first),
        forall |addr: Address| #[trigger] reads.contains_key(addr)
            && entries.contains_key(addr) ==> reads[addr] == entries[addr],
        forall |addr: Address| #[trigger] entries.contains_key(addr) ==> addrs.contains(addr),
    ensures
        au_walk_addrs_in(reads, boundary_lsn, root, first, au_depth, page_depth, addrs),
    decreases au_depth,
{
    let dv = DiskView{boundary_lsn, entries};
    if root is Some && au_depth > 0 {
        let addr = root.unwrap();
        if addr.au == first {
            page_walk_addrs_in_entries_subset(
                reads,
                entries,
                boundary_lsn,
                root,
                page_depth,
                addrs,
            );
        } else {
            let bottom = addr.first_page();
            assert(reads.contains_key(addr));
            assert(reads.contains_key(bottom));
            assert(entries.contains_key(addr));
            dv.bottom_properties(root, first);
            assert(entries.contains_key(bottom));
            assert(addrs.contains(addr));
            assert(addrs.contains(bottom));
            assert(reads[addr] == entries[addr]);
            assert(reads[bottom] == entries[bottom]);
            let next = reads[bottom].cropped_prior(boundary_lsn);
            assert(next == dv.next(Some(bottom)));
            assert(dv.pointer_is_upstream(next, first));
            au_walk_addrs_in_entries_subset(
                reads,
                entries,
                boundary_lsn,
                next,
                first,
                (au_depth - 1) as nat,
                page_depth,
                addrs,
            );
        }
    }
}

pub proof fn page_walk_reads_cover_restrict(
    reads: Map<Address, JournalRecord>,
    addrs: Set<Address>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
)
    requires
        page_walk_reads_cover(reads, boundary_lsn, root, depth),
        page_walk_addrs_in(reads, boundary_lsn, root, depth, addrs),
    ensures
        page_walk_reads_cover(reads.restrict(addrs), boundary_lsn, root, depth),
    decreases depth,
{
    if root is Some && depth > 0 {
        let addr = root.unwrap();
        let restricted = reads.restrict(addrs);
        assert(addrs.contains(addr));
        assert(reads.contains_key(addr));
        assert(restricted.contains_key(addr));
        assert(restricted[addr] == reads[addr]);
        let next = reads[addr].cropped_prior(boundary_lsn);
        assert(restricted[addr].cropped_prior(boundary_lsn) == next);
        page_walk_reads_cover_restrict(
            reads,
            addrs,
            boundary_lsn,
            next,
            (depth - 1) as nat,
        );
    }
}

pub proof fn au_walk_reads_cover_restrict(
    reads: Map<Address, JournalRecord>,
    addrs: Set<Address>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    page_depth: nat,
)
    requires
        au_walk_reads_cover(reads, boundary_lsn, root, first, au_depth, page_depth),
        au_walk_addrs_in(reads, boundary_lsn, root, first, au_depth, page_depth, addrs),
    ensures
        au_walk_reads_cover(
            reads.restrict(addrs),
            boundary_lsn,
            root,
            first,
            au_depth,
            page_depth,
        ),
    decreases au_depth,
{
    if root is Some && au_depth > 0 {
        let addr = root.unwrap();
        let restricted = reads.restrict(addrs);
        if addr.au == first {
            page_walk_reads_cover_restrict(reads, addrs, boundary_lsn, root, page_depth);
        } else {
            let bottom = addr.first_page();
            assert(addrs.contains(addr));
            assert(addrs.contains(bottom));
            assert(reads.contains_key(addr));
            assert(reads.contains_key(bottom));
            assert(restricted.contains_key(addr));
            assert(restricted.contains_key(bottom));
            assert(restricted[bottom] == reads[bottom]);
            let next = reads[bottom].cropped_prior(boundary_lsn);
            assert(restricted[bottom].cropped_prior(boundary_lsn) == next);
            au_walk_reads_cover_restrict(
                reads,
                addrs,
                boundary_lsn,
                next,
                first,
                (au_depth - 1) as nat,
                page_depth,
            );
        }
    }
}

pub proof fn page_walk_reads_cover_supermap(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
)
    requires
        reads <= entries,
        page_walk_reads_cover(reads, boundary_lsn, root, depth),
    ensures
        page_walk_reads_cover(entries, boundary_lsn, root, depth),
    decreases depth,
{
    if root is Some && depth > 0 {
        let addr = root.unwrap();
        assert(reads.contains_key(addr));
        assert(entries.contains_key(addr));
        assert(reads[addr] == entries[addr]);
        page_walk_reads_cover_supermap(
            reads,
            entries,
            boundary_lsn,
            reads[addr].cropped_prior(boundary_lsn),
            (depth - 1) as nat,
        );
    }
}

pub proof fn au_walk_reads_cover_supermap(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    page_depth: nat,
)
    requires
        reads <= entries,
        au_walk_reads_cover(reads, boundary_lsn, root, first, au_depth, page_depth),
    ensures
        au_walk_reads_cover(entries, boundary_lsn, root, first, au_depth, page_depth),
    decreases au_depth,
{
    if root is Some && au_depth > 0 {
        let addr = root.unwrap();
        if addr.au == first {
            page_walk_reads_cover_supermap(reads, entries, boundary_lsn, root, page_depth);
        } else {
            let bottom = addr.first_page();
            assert(reads.contains_key(addr));
            assert(reads.contains_key(bottom));
            assert(entries.contains_key(addr));
            assert(entries.contains_key(bottom));
            assert(reads[bottom] == entries[bottom]);
            au_walk_reads_cover_supermap(
                reads,
                entries,
                boundary_lsn,
                reads[bottom].cropped_prior(boundary_lsn),
                first,
                (au_depth - 1) as nat,
                page_depth,
            );
        }
    }
}

pub proof fn page_walk_reads_cover_sub_entries(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
)
    requires
        entries <= reads,
        page_walk_reads_cover(reads, boundary_lsn, root, depth),
        (DiskView{boundary_lsn, entries}).decodable(root),
        (DiskView{boundary_lsn, entries}).acyclic(),
    ensures
        page_walk_reads_cover(entries, boundary_lsn, root, depth),
    decreases depth,
{
    let dv = DiskView{boundary_lsn, entries};
    if root is Some && depth > 0 {
        let addr = root.unwrap();
        assert(entries.contains_key(addr));
        assert(reads.contains_key(addr));
        assert(reads[addr] == entries[addr]);
        let next = reads[addr].cropped_prior(boundary_lsn);
        assert(next == dv.next(root));
        assert(dv.decodable(next));
        page_walk_reads_cover_sub_entries(
            reads,
            entries,
            boundary_lsn,
            next,
            (depth - 1) as nat,
        );
    }
}

pub proof fn au_walk_reads_cover_sub_entries(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    page_depth: nat,
)
    requires
        entries <= reads,
        au_walk_reads_cover(reads, boundary_lsn, root, first, au_depth, page_depth),
        (DiskView{boundary_lsn, entries}).wf_addrs(),
        (DiskView{boundary_lsn, entries}).pointer_is_upstream(root, first),
    ensures
        au_walk_reads_cover(entries, boundary_lsn, root, first, au_depth, page_depth),
    decreases au_depth,
{
    let dv = DiskView{boundary_lsn, entries};
    if root is Some && au_depth > 0 {
        let addr = root.unwrap();
        if addr.au == first {
            page_walk_reads_cover_sub_entries(
                reads,
                entries,
                boundary_lsn,
                root,
                page_depth,
            );
        } else {
            let bottom = addr.first_page();
            assert(entries.contains_key(addr));
            assert(reads.contains_key(addr));
            assert(reads[addr] == entries[addr]);
            dv.bottom_properties(root, first);
            assert(dv.pointer_is_upstream(Some(bottom), first));
            assert(entries.contains_key(bottom));
            assert(reads.contains_key(bottom));
            assert(reads[bottom] == entries[bottom]);
            let next = reads[bottom].cropped_prior(boundary_lsn);
            assert(next == dv.next(Some(bottom)));
            assert(dv.buildable(next));
            assert(dv.pointer_is_upstream(next, first));
            au_walk_reads_cover_sub_entries(
                reads,
                entries,
                boundary_lsn,
                next,
                first,
                (au_depth - 1) as nat,
                page_depth,
            );
        }
    }
}

pub open spec fn build_lsn_au_index_from_reads_page_walk_depth(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
) -> LsnAUIndex
    decreases depth
{
    if root is None || depth == 0 {
        Map::empty()
    } else {
        let addr = root.unwrap();
        let curr_msgs = reads[addr].message_seq;
        let update = crate::allocation_layer::AllocationJournal_v::singleton_index(
            max(boundary_lsn as int, curr_msgs.seq_start as int) as nat,
            curr_msgs.seq_end,
            addr.au,
        );
        let next = reads[addr].cropped_prior(boundary_lsn);
        build_lsn_au_index_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            next,
            (depth - 1) as nat,
        ).union_prefer_right(update)
    }
}

pub open spec fn build_lsn_au_index_from_reads_au_walk_depth(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    page_depth: nat,
) -> LsnAUIndex
    decreases au_depth
{
    if root is None || au_depth == 0 {
        Map::empty()
    } else {
        let addr = root.unwrap();
        if addr.au == first {
            build_lsn_au_index_from_reads_page_walk_depth(reads, boundary_lsn, root, page_depth)
        } else {
            let bottom = addr.first_page();
            let first_lsn = reads[bottom].message_seq.seq_start;
            let last_lsn = reads[addr].message_seq.seq_end;
            let update = crate::allocation_layer::AllocationJournal_v::singleton_index(
                first_lsn,
                last_lsn,
                bottom.au,
            );
            let next = reads[bottom].cropped_prior(boundary_lsn);
            build_lsn_au_index_from_reads_au_walk_depth(
                reads,
                boundary_lsn,
                next,
                first,
                (au_depth - 1) as nat,
                page_depth,
            ).union_prefer_right(update)
        }
    }
}

pub proof fn build_lsn_au_index_from_reads_page_walk_values_in_reads(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
    au: AU,
)
    requires
        page_walk_reads_cover(reads, boundary_lsn, root, depth),
        build_lsn_au_index_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            root,
            depth,
        ).values().contains(au),
    ensures
        to_aus(reads.dom()).contains(au),
    decreases depth
{
    if root is Some && depth > 0 {
        let addr = root.unwrap();
        assert(reads.contains_key(addr));
        let curr_msgs = reads[addr].message_seq;
        let update = crate::allocation_layer::AllocationJournal_v::singleton_index(
            max(boundary_lsn as int, curr_msgs.seq_start as int) as nat,
            curr_msgs.seq_end,
            addr.au,
        );
        let next = reads[addr].cropped_prior(boundary_lsn);
        let sub_index = build_lsn_au_index_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            next,
            (depth - 1) as nat,
        );
        let index = build_lsn_au_index_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            root,
            depth,
        );
        assert(index == sub_index.union_prefer_right(update));
        let lsn = choose |lsn: LSN| #![auto] index.contains_key(lsn) && index[lsn] == au;
        if update.contains_key(lsn) {
            assert(update[lsn] == addr.au);
            assert(au == addr.au);
            to_aus_domain(reads.dom());
        } else {
            assert(sub_index.contains_key(lsn));
            assert(sub_index[lsn] == au);
            assert(sub_index.values().contains(au));
            build_lsn_au_index_from_reads_page_walk_values_in_reads(
                reads,
                boundary_lsn,
                next,
                (depth - 1) as nat,
                au,
            );
        }
    } else {
        assert(build_lsn_au_index_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            root,
            depth,
        ) == Map::<LSN, AU>::empty());
    }
}

pub proof fn build_lsn_au_index_from_reads_au_walk_values_in_reads(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    page_depth: nat,
    au: AU,
)
    requires
        au_walk_reads_cover(reads, boundary_lsn, root, first, au_depth, page_depth),
        build_lsn_au_index_from_reads_au_walk_depth(
            reads,
            boundary_lsn,
            root,
            first,
            au_depth,
            page_depth,
        ).values().contains(au),
    ensures
        to_aus(reads.dom()).contains(au),
    decreases au_depth
{
    if root is Some && au_depth > 0 {
        let addr = root.unwrap();
        if addr.au == first {
            build_lsn_au_index_from_reads_page_walk_values_in_reads(
                reads,
                boundary_lsn,
                root,
                page_depth,
                au,
            );
        } else {
            let bottom = addr.first_page();
            assert(reads.contains_key(addr));
            assert(reads.contains_key(bottom));
            let first_lsn = reads[bottom].message_seq.seq_start;
            let last_lsn = reads[addr].message_seq.seq_end;
            let update = crate::allocation_layer::AllocationJournal_v::singleton_index(
                first_lsn,
                last_lsn,
                bottom.au,
            );
            let next = reads[bottom].cropped_prior(boundary_lsn);
            let sub_index = build_lsn_au_index_from_reads_au_walk_depth(
                reads,
                boundary_lsn,
                next,
                first,
                (au_depth - 1) as nat,
                page_depth,
            );
            let index = build_lsn_au_index_from_reads_au_walk_depth(
                reads,
                boundary_lsn,
                root,
                first,
                au_depth,
                page_depth,
            );
            assert(index == sub_index.union_prefer_right(update));
            let lsn = choose |lsn: LSN| #![auto] index.contains_key(lsn) && index[lsn] == au;
            if update.contains_key(lsn) {
                assert(update[lsn] == bottom.au);
                assert(au == bottom.au);
                to_aus_domain(reads.dom());
            } else {
                assert(sub_index.contains_key(lsn));
                assert(sub_index[lsn] == au);
                assert(sub_index.values().contains(au));
                build_lsn_au_index_from_reads_au_walk_values_in_reads(
                    reads,
                    boundary_lsn,
                    next,
                    first,
                    (au_depth - 1) as nat,
                    page_depth,
                    au,
                );
            }
        }
    } else {
        assert(build_lsn_au_index_from_reads_au_walk_depth(
            reads,
            boundary_lsn,
            root,
            first,
            au_depth,
            page_depth,
        ) == Map::<LSN, AU>::empty());
    }
}

pub proof fn build_lsn_au_index_from_reads_page_walk_depth_supermap(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
)
    requires
        reads <= entries,
        page_walk_reads_cover(reads, boundary_lsn, root, depth),
    ensures
        build_lsn_au_index_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            root,
            depth,
        ) =~= build_lsn_au_index_from_reads_page_walk_depth(
            entries,
            boundary_lsn,
            root,
            depth,
        ),
    decreases depth
{
    if root is Some && depth > 0 {
        let addr = root.unwrap();
        assert(reads.contains_key(addr));
        assert(entries.contains_key(addr));
        assert(reads[addr] == entries[addr]);
        let next = reads[addr].cropped_prior(boundary_lsn);
        assert(next == entries[addr].cropped_prior(boundary_lsn));
        build_lsn_au_index_from_reads_page_walk_depth_supermap(
            reads,
            entries,
            boundary_lsn,
            next,
            (depth - 1) as nat,
        );
        assert_maps_equal!(
            build_lsn_au_index_from_reads_page_walk_depth(
                reads,
                boundary_lsn,
                root,
                depth,
            ),
            build_lsn_au_index_from_reads_page_walk_depth(
                entries,
                boundary_lsn,
                root,
                depth,
            ),
        );
    }
}

pub proof fn build_lsn_au_index_from_reads_au_walk_depth_supermap(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    page_depth: nat,
)
    requires
        reads <= entries,
        au_walk_reads_cover(reads, boundary_lsn, root, first, au_depth, page_depth),
    ensures
        build_lsn_au_index_from_reads_au_walk_depth(
            reads,
            boundary_lsn,
            root,
            first,
            au_depth,
            page_depth,
        ) =~= build_lsn_au_index_from_reads_au_walk_depth(
            entries,
            boundary_lsn,
            root,
            first,
            au_depth,
            page_depth,
        ),
    decreases au_depth
{
    if root is Some && au_depth > 0 {
        let addr = root.unwrap();
        if addr.au == first {
            build_lsn_au_index_from_reads_page_walk_depth_supermap(
                reads,
                entries,
                boundary_lsn,
                root,
                page_depth,
            );
        } else {
            let bottom = addr.first_page();
            assert(reads.contains_key(addr));
            assert(reads.contains_key(bottom));
            assert(entries.contains_key(addr));
            assert(entries.contains_key(bottom));
            assert(reads[addr] == entries[addr]);
            assert(reads[bottom] == entries[bottom]);
            let next = reads[bottom].cropped_prior(boundary_lsn);
            assert(next == entries[bottom].cropped_prior(boundary_lsn));
            build_lsn_au_index_from_reads_au_walk_depth_supermap(
                reads,
                entries,
                boundary_lsn,
                next,
                first,
                (au_depth - 1) as nat,
                page_depth,
            );
            assert_maps_equal!(
                build_lsn_au_index_from_reads_au_walk_depth(
                    reads,
                    boundary_lsn,
                    root,
                    first,
                    au_depth,
                    page_depth,
                ),
                build_lsn_au_index_from_reads_au_walk_depth(
                    entries,
                    boundary_lsn,
                    root,
                    first,
                    au_depth,
                    page_depth,
                ),
            );
        }
    }
}

pub proof fn page_walk_reads_cover_build_matches_full(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
)
    requires
        reads <= entries,
        page_walk_reads_cover(reads, boundary_lsn, root, depth),
        (DiskView{boundary_lsn, entries}).decodable(root),
        (DiskView{boundary_lsn, entries}).acyclic(),
    ensures ({
        let full_dv = DiskView{boundary_lsn, entries};
        build_lsn_au_index_from_reads_page_walk_depth(reads, boundary_lsn, root, depth)
            =~= full_dv.build_lsn_au_index_page_walk(root)
    }),
    decreases depth,
{
    let full_dv = DiskView{boundary_lsn, entries};
    if root is None {
        assert_maps_equal!(
            build_lsn_au_index_from_reads_page_walk_depth(reads, boundary_lsn, root, depth),
            full_dv.build_lsn_au_index_page_walk(root),
        );
    } else {
        assert(depth > 0);
        let addr = root.unwrap();
        assert(reads.contains_key(addr));
        assert(entries.contains_key(addr));
        assert(reads[addr] == entries[addr]);
        let next = reads[addr].cropped_prior(boundary_lsn);
        assert(next == full_dv.next(root));

        page_walk_reads_cover_build_matches_full(
            reads,
            entries,
            boundary_lsn,
            next,
            (depth - 1) as nat,
        );

        let curr_msgs = reads[addr].message_seq;
        let update = crate::allocation_layer::AllocationJournal_v::singleton_index(
            max(boundary_lsn as int, curr_msgs.seq_start as int) as nat,
            curr_msgs.seq_end,
            addr.au,
        );
        assert(update == crate::allocation_layer::AllocationJournal_v::singleton_index(
            max(boundary_lsn as int, entries[addr].message_seq.seq_start as int) as nat,
            entries[addr].message_seq.seq_end,
            addr.au,
        ));
        assert(build_lsn_au_index_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            root,
            depth,
        ) == build_lsn_au_index_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            next,
            (depth - 1) as nat,
        ).union_prefer_right(update));
        assert(full_dv.build_lsn_au_index_page_walk(root)
            == full_dv.build_lsn_au_index_page_walk(next).union_prefer_right(update));
        assert_maps_equal!(
            build_lsn_au_index_from_reads_page_walk_depth(reads, boundary_lsn, root, depth),
            full_dv.build_lsn_au_index_page_walk(root),
        );
    }
}

pub proof fn page_walk_reads_cover_addr_build_matches_full_by_value(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
)
    requires
        acyclic_reads(boundary_lsn, reads),
        page_walk_reads_cover(reads, boundary_lsn, root, depth),
        (DiskView{boundary_lsn, entries}).decodable(root),
        (DiskView{boundary_lsn, entries}).acyclic(),
        forall |addr: Address| #[trigger] reads.contains_key(addr)
            && entries.contains_key(addr) ==> reads[addr] == entries[addr],
    ensures ({
        let full_dv = DiskView{boundary_lsn, entries};
        build_lsn_addr_index_from_reads(reads, boundary_lsn, root)
            =~= full_dv.build_lsn_addr_index(root)
    }),
    decreases depth,
{
    let full_dv = DiskView{boundary_lsn, entries};
    if root is None {
        assert_maps_equal!(
            build_lsn_addr_index_from_reads(reads, boundary_lsn, root),
            full_dv.build_lsn_addr_index(root),
        );
    } else {
        assert(depth > 0);
        let addr = root.unwrap();
        assert(reads.contains_key(addr));
        assert(entries.contains_key(addr));
        assert(reads[addr] == entries[addr]);
        let next = reads[addr].cropped_prior(boundary_lsn);
        assert(next == full_dv.next(root));

        page_walk_reads_cover_addr_build_matches_full_by_value(
            reads,
            entries,
            boundary_lsn,
            next,
            (depth - 1) as nat,
        );

        let curr_msgs = reads[addr].message_seq;
        let start_lsn = max(boundary_lsn as int, curr_msgs.seq_start as int) as nat;
        let update = singleton_index(start_lsn, curr_msgs.seq_end, addr);
        assert(update == singleton_index(
            max(boundary_lsn as int, entries[addr].message_seq.seq_start as int) as nat,
            entries[addr].message_seq.seq_end,
            addr,
        ));
        build_lsn_addr_index_from_reads_step(reads, boundary_lsn, root, next, update);
        assert(build_lsn_addr_index_from_reads(reads, boundary_lsn, root)
            =~= build_lsn_addr_index_from_reads(reads, boundary_lsn, next)
                .union_prefer_right(update));
        assert(full_dv.build_lsn_addr_index(root)
            =~= full_dv.build_lsn_addr_index(next).union_prefer_right(update));
        assert_maps_equal!(
            build_lsn_addr_index_from_reads(reads, boundary_lsn, root),
            full_dv.build_lsn_addr_index(root),
        );
    }
}

pub proof fn page_walk_reads_cover_build_matches_full_by_value(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
)
    requires
        page_walk_reads_cover(reads, boundary_lsn, root, depth),
        (DiskView{boundary_lsn, entries}).decodable(root),
        (DiskView{boundary_lsn, entries}).acyclic(),
        forall |addr: Address| #[trigger] reads.contains_key(addr)
            && entries.contains_key(addr) ==> reads[addr] == entries[addr],
    ensures ({
        let full_dv = DiskView{boundary_lsn, entries};
        build_lsn_au_index_from_reads_page_walk_depth(reads, boundary_lsn, root, depth)
            =~= full_dv.build_lsn_au_index_page_walk(root)
    }),
    decreases depth,
{
    let full_dv = DiskView{boundary_lsn, entries};
    if root is None {
        assert_maps_equal!(
            build_lsn_au_index_from_reads_page_walk_depth(reads, boundary_lsn, root, depth),
            full_dv.build_lsn_au_index_page_walk(root),
        );
    } else {
        assert(depth > 0);
        let addr = root.unwrap();
        assert(reads.contains_key(addr));
        assert(entries.contains_key(addr));
        assert(reads[addr] == entries[addr]);
        let next = reads[addr].cropped_prior(boundary_lsn);
        assert(next == full_dv.next(root));

        page_walk_reads_cover_build_matches_full_by_value(
            reads,
            entries,
            boundary_lsn,
            next,
            (depth - 1) as nat,
        );

        let curr_msgs = reads[addr].message_seq;
        let update = crate::allocation_layer::AllocationJournal_v::singleton_index(
            max(boundary_lsn as int, curr_msgs.seq_start as int) as nat,
            curr_msgs.seq_end,
            addr.au,
        );
        assert(update == crate::allocation_layer::AllocationJournal_v::singleton_index(
            max(boundary_lsn as int, entries[addr].message_seq.seq_start as int) as nat,
            entries[addr].message_seq.seq_end,
            addr.au,
        ));
        assert(build_lsn_au_index_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            root,
            depth,
        ) == build_lsn_au_index_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            next,
            (depth - 1) as nat,
        ).union_prefer_right(update));
        assert(full_dv.build_lsn_au_index_page_walk(root)
            == full_dv.build_lsn_au_index_page_walk(next).union_prefer_right(update));
        assert_maps_equal!(
            build_lsn_au_index_from_reads_page_walk_depth(reads, boundary_lsn, root, depth),
            full_dv.build_lsn_au_index_page_walk(root),
        );
    }
}

pub proof fn au_walk_reads_cover_build_matches_full(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    page_depth: nat,
)
    requires
        reads <= entries,
        au_walk_reads_cover(reads, boundary_lsn, root, first, au_depth, page_depth),
        (DiskView{boundary_lsn, entries}).pointer_is_upstream(root, first),
    ensures ({
        let full_dv = DiskView{boundary_lsn, entries};
        build_lsn_au_index_from_reads_au_walk_depth(
            reads,
            boundary_lsn,
            root,
            first,
            au_depth,
            page_depth,
        ) =~= full_dv.build_lsn_au_index_au_walk(root, first)
    }),
    decreases au_depth,
{
    let full_dv = DiskView{boundary_lsn, entries};
    if root is None {
        assert_maps_equal!(
            build_lsn_au_index_from_reads_au_walk_depth(
                reads,
                boundary_lsn,
                root,
                first,
                au_depth,
                page_depth,
            ),
            full_dv.build_lsn_au_index_au_walk(root, first),
        );
    } else {
        assert(au_depth > 0);
        let addr = root.unwrap();
        if addr.au == first {
            page_walk_reads_cover_build_matches_full(
                reads,
                entries,
                boundary_lsn,
                root,
                page_depth,
            );
            assert(full_dv.build_lsn_au_index_au_walk(root, first)
                == full_dv.build_lsn_au_index_page_walk(root));
            assert_maps_equal!(
                build_lsn_au_index_from_reads_au_walk_depth(
                    reads,
                    boundary_lsn,
                    root,
                    first,
                    au_depth,
                    page_depth,
                ),
                full_dv.build_lsn_au_index_au_walk(root, first),
            );
        } else {
            let bottom = addr.first_page();
            assert(reads.contains_key(addr));
            assert(reads.contains_key(bottom));
            assert(entries.contains_key(addr));
            full_dv.bottom_properties(root, first);
            assert(entries.contains_key(bottom));
            assert(reads[addr] == entries[addr]);
            assert(reads[bottom] == entries[bottom]);
            assert(reads[bottom].cropped_prior(boundary_lsn) == full_dv.next(Some(bottom)));

            let next = reads[bottom].cropped_prior(boundary_lsn);
            au_walk_reads_cover_build_matches_full(
                reads,
                entries,
                boundary_lsn,
                next,
                first,
                (au_depth - 1) as nat,
                page_depth,
            );

            let first_lsn = reads[bottom].message_seq.seq_start;
            let last_lsn = reads[addr].message_seq.seq_end;
            let update = crate::allocation_layer::AllocationJournal_v::singleton_index(
                first_lsn,
                last_lsn,
                bottom.au,
            );
            assert(update == crate::allocation_layer::AllocationJournal_v::singleton_index(
                entries[bottom].message_seq.seq_start,
                entries[addr].message_seq.seq_end,
                bottom.au,
            ));
            assert(build_lsn_au_index_from_reads_au_walk_depth(
                reads,
                boundary_lsn,
                root,
                first,
                au_depth,
                page_depth,
            ) == build_lsn_au_index_from_reads_au_walk_depth(
                reads,
                boundary_lsn,
                next,
                first,
                (au_depth - 1) as nat,
                page_depth,
            ).union_prefer_right(update));
            assert(full_dv.build_lsn_au_index_au_walk(root, first)
                == full_dv.build_lsn_au_index_au_walk(full_dv.next(Some(bottom)), first)
                    .union_prefer_right(update));
            assert_maps_equal!(
                build_lsn_au_index_from_reads_au_walk_depth(
                    reads,
                    boundary_lsn,
                    root,
                    first,
                    au_depth,
                    page_depth,
                ),
                full_dv.build_lsn_au_index_au_walk(root, first),
            );
        }
    }
}

pub proof fn au_walk_reads_cover_build_matches_full_by_value(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    page_depth: nat,
)
    requires
        au_walk_reads_cover(reads, boundary_lsn, root, first, au_depth, page_depth),
        (DiskView{boundary_lsn, entries}).pointer_is_upstream(root, first),
        forall |addr: Address| #[trigger] reads.contains_key(addr)
            && entries.contains_key(addr) ==> reads[addr] == entries[addr],
    ensures ({
        let full_dv = DiskView{boundary_lsn, entries};
        build_lsn_au_index_from_reads_au_walk_depth(
            reads,
            boundary_lsn,
            root,
            first,
            au_depth,
            page_depth,
        ) =~= full_dv.build_lsn_au_index_au_walk(root, first)
    }),
    decreases au_depth,
{
    let full_dv = DiskView{boundary_lsn, entries};
    if root is None {
        assert_maps_equal!(
            build_lsn_au_index_from_reads_au_walk_depth(
                reads,
                boundary_lsn,
                root,
                first,
                au_depth,
                page_depth,
            ),
            full_dv.build_lsn_au_index_au_walk(root, first),
        );
    } else {
        assert(au_depth > 0);
        let addr = root.unwrap();
        if addr.au == first {
            page_walk_reads_cover_build_matches_full_by_value(
                reads,
                entries,
                boundary_lsn,
                root,
                page_depth,
            );
            assert(full_dv.build_lsn_au_index_au_walk(root, first)
                == full_dv.build_lsn_au_index_page_walk(root));
            assert_maps_equal!(
                build_lsn_au_index_from_reads_au_walk_depth(
                    reads,
                    boundary_lsn,
                    root,
                    first,
                    au_depth,
                    page_depth,
                ),
                full_dv.build_lsn_au_index_au_walk(root, first),
            );
        } else {
            let bottom = addr.first_page();
            assert(reads.contains_key(addr));
            assert(reads.contains_key(bottom));
            assert(entries.contains_key(addr));
            full_dv.bottom_properties(root, first);
            assert(entries.contains_key(bottom));
            assert(reads[addr] == entries[addr]);
            assert(reads[bottom] == entries[bottom]);
            assert(reads[bottom].cropped_prior(boundary_lsn) == full_dv.next(Some(bottom)));

            let next = reads[bottom].cropped_prior(boundary_lsn);
            au_walk_reads_cover_build_matches_full_by_value(
                reads,
                entries,
                boundary_lsn,
                next,
                first,
                (au_depth - 1) as nat,
                page_depth,
            );

            let first_lsn = reads[bottom].message_seq.seq_start;
            let last_lsn = reads[addr].message_seq.seq_end;
            let update = crate::allocation_layer::AllocationJournal_v::singleton_index(
                first_lsn,
                last_lsn,
                bottom.au,
            );
            assert(update == crate::allocation_layer::AllocationJournal_v::singleton_index(
                entries[bottom].message_seq.seq_start,
                entries[addr].message_seq.seq_end,
                bottom.au,
            ));
            assert(build_lsn_au_index_from_reads_au_walk_depth(
                reads,
                boundary_lsn,
                root,
                first,
                au_depth,
                page_depth,
            ) == build_lsn_au_index_from_reads_au_walk_depth(
                reads,
                boundary_lsn,
                next,
                first,
                (au_depth - 1) as nat,
                page_depth,
            ).union_prefer_right(update));
            assert(full_dv.build_lsn_au_index_au_walk(root, first)
                == full_dv.build_lsn_au_index_au_walk(full_dv.next(Some(bottom)), first)
                    .union_prefer_right(update));
            assert_maps_equal!(
                build_lsn_au_index_from_reads_au_walk_depth(
                    reads,
                    boundary_lsn,
                    root,
                    first,
                    au_depth,
                    page_depth,
                ),
                full_dv.build_lsn_au_index_au_walk(root, first),
            );
        }
    }
}

pub proof fn build_lsn_au_index_from_reads_au_walk_matches_full(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    page_depth: nat,
)
    requires
        reads <= entries,
        au_walk_reads_cover(reads, boundary_lsn, root, first, au_depth, page_depth),
        (DiskView{boundary_lsn, entries}).pointer_is_upstream(root, first),
    ensures ({
        let full_dv = DiskView{boundary_lsn, entries};
        build_lsn_au_index_from_reads_au_walk_depth(
            reads,
            boundary_lsn,
            root,
            first,
            au_depth,
            page_depth,
        )
            =~= full_dv.build_lsn_au_index_au_walk(root, first)
    }),
{
    au_walk_reads_cover_build_matches_full(
        reads,
        entries,
        boundary_lsn,
        root,
        first,
        au_depth,
        page_depth,
    );
}

pub proof fn build_lsn_au_index_from_reads_page_walk_values_in_sub_entries(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
    au: AU,
)
    requires
        entries <= reads,
        page_walk_reads_cover(reads, boundary_lsn, root, depth),
        (DiskView{boundary_lsn, entries}).decodable(root),
        (DiskView{boundary_lsn, entries}).acyclic(),
        build_lsn_au_index_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            root,
            depth,
        ).values().contains(au),
    ensures
        to_aus(entries.dom()).contains(au),
    decreases depth,
{
    let dv = DiskView{boundary_lsn, entries};
    let index = build_lsn_au_index_from_reads_page_walk_depth(
        reads,
        boundary_lsn,
        root,
        depth,
    );
    if root is Some && depth > 0 {
        let addr = root.unwrap();
        assert(entries.contains_key(addr));
        assert(reads.contains_key(addr));
        assert(reads[addr] == entries[addr]);
        let curr_msgs = reads[addr].message_seq;
        let update = crate::allocation_layer::AllocationJournal_v::singleton_index(
            max(boundary_lsn as int, curr_msgs.seq_start as int) as nat,
            curr_msgs.seq_end,
            addr.au,
        );
        let next = reads[addr].cropped_prior(boundary_lsn);
        let sub_index = build_lsn_au_index_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            next,
            (depth - 1) as nat,
        );
        assert(index == sub_index.union_prefer_right(update));
        let lsn = choose |lsn: LSN| #![auto] index.contains_key(lsn) && index[lsn] == au;
        if update.contains_key(lsn) {
            assert(update[lsn] == addr.au);
            assert(au == addr.au);
            to_aus_domain(entries.dom());
        } else {
            assert(sub_index.contains_key(lsn));
            assert(sub_index[lsn] == au);
            assert(sub_index.values().contains(au));
            assert(next == dv.next(root));
            assert(dv.decodable(next));
            build_lsn_au_index_from_reads_page_walk_values_in_sub_entries(
                reads,
                entries,
                boundary_lsn,
                next,
                (depth - 1) as nat,
                au,
            );
        }
    } else {
        assert(index == Map::<LSN, AU>::empty());
    }
}

pub proof fn build_lsn_au_index_from_reads_au_walk_values_in_sub_entries(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    page_depth: nat,
    au: AU,
)
    requires
        entries <= reads,
        au_walk_reads_cover(reads, boundary_lsn, root, first, au_depth, page_depth),
        (DiskView{boundary_lsn, entries}).wf_addrs(),
        (DiskView{boundary_lsn, entries}).pointer_is_upstream(root, first),
        build_lsn_au_index_from_reads_au_walk_depth(
            reads,
            boundary_lsn,
            root,
            first,
            au_depth,
            page_depth,
        ).values().contains(au),
    ensures
        to_aus(entries.dom()).contains(au),
    decreases au_depth,
{
    let dv = DiskView{boundary_lsn, entries};
    let index = build_lsn_au_index_from_reads_au_walk_depth(
        reads,
        boundary_lsn,
        root,
        first,
        au_depth,
        page_depth,
    );
    if root is Some && au_depth > 0 {
        let addr = root.unwrap();
        if addr.au == first {
            build_lsn_au_index_from_reads_page_walk_values_in_sub_entries(
                reads,
                entries,
                boundary_lsn,
                root,
                page_depth,
                au,
            );
        } else {
            let bottom = addr.first_page();
            assert(entries.contains_key(addr));
            assert(reads.contains_key(addr));
            assert(reads[addr] == entries[addr]);
            dv.bottom_properties(root, first);
            assert(dv.pointer_is_upstream(Some(bottom), first));
            assert(entries.contains_key(bottom));
            assert(reads.contains_key(bottom));
            assert(reads[bottom] == entries[bottom]);
            let first_lsn = reads[bottom].message_seq.seq_start;
            let last_lsn = reads[addr].message_seq.seq_end;
            let update = crate::allocation_layer::AllocationJournal_v::singleton_index(
                first_lsn,
                last_lsn,
                bottom.au,
            );
            let next = reads[bottom].cropped_prior(boundary_lsn);
            let sub_index = build_lsn_au_index_from_reads_au_walk_depth(
                reads,
                boundary_lsn,
                next,
                first,
                (au_depth - 1) as nat,
                page_depth,
            );
            assert(index == sub_index.union_prefer_right(update));
            let lsn = choose |lsn: LSN| #![auto] index.contains_key(lsn) && index[lsn] == au;
            if update.contains_key(lsn) {
                assert(update[lsn] == bottom.au);
                assert(au == bottom.au);
                to_aus_domain(entries.dom());
            } else {
                assert(sub_index.contains_key(lsn));
                assert(sub_index[lsn] == au);
                assert(sub_index.values().contains(au));
                assert(next == dv.next(Some(bottom)));
                assert(dv.buildable(next));
                assert(dv.pointer_is_upstream(next, first));
                build_lsn_au_index_from_reads_au_walk_values_in_sub_entries(
                    reads,
                    entries,
                    boundary_lsn,
                    next,
                    first,
                    (au_depth - 1) as nat,
                    page_depth,
                    au,
                );
            }
        }
    } else {
        assert(index == Map::<LSN, AU>::empty());
    }
}

pub open spec fn lsn_addr_index_to_au_index(index: LsnAddrIndex) -> LsnAUIndex
{
    Map::new(
        |lsn| index.contains_key(lsn),
        |lsn| index[lsn].au,
    )
}

pub open spec fn complete_lsn_range_for_addr(
    lsn_addr_index: LsnAddrIndex,
    bdy: LSN,
    addr: Address,
    start_lsn: LSN,
    end_lsn: LSN,
) -> bool
{
    &&& bdy <= start_lsn < end_lsn
    &&& forall |lsn: LSN|
        #![trigger lsn_addr_index.contains_key(lsn)]
        #![trigger lsn_addr_index[lsn]]
        bdy <= lsn ==> {
        &&& (lsn_addr_index.contains_key(lsn) && lsn_addr_index[lsn] == addr)
            <==> (start_lsn <= lsn < end_lsn)
    }
}

pub open spec fn lsn_index_domain_exact(
    lsn_addr_index: LsnAddrIndex,
    bdy: LSN,
    seq_end: LSN,
) -> bool
{
    forall |lsn: LSN| #[trigger] lsn_addr_index.contains_key(lsn)
        <==> (bdy <= lsn < seq_end)
}

pub open spec fn all_addrs_have_complete_lsn_ranges(
    lsn_addr_index: LsnAddrIndex,
    bdy: LSN,
) -> bool
{
    forall |addr: Address| #[trigger] lsn_addr_index.values().contains(addr)
        ==> exists |start_lsn: LSN, end_lsn: LSN|
            complete_lsn_range_for_addr(lsn_addr_index, bdy, addr, start_lsn, end_lsn)
}

pub open spec fn all_addrs_have_finite_lsn_sets(
    lsn_addr_index: LsnAddrIndex,
    bdy: LSN,
) -> bool
{
    forall |addr: Address| #[trigger] lsn_addr_index.values().contains(addr)
        ==> addr_to_lsns(lsn_addr_index, addr, bdy).finite()
}

pub open spec fn acyclic_reads(bdy: LSN, reads: Map<Address, JournalRecord>) -> bool
{
    DiskView{boundary_lsn: bdy, entries: reads}.acyclic()
}

pub open spec fn rank_of_reads(bdy: LSN, reads: Map<Address, JournalRecord>, root: Pointer) -> nat
    recommends acyclic_reads(bdy, reads)
{
    if root is Some && reads.contains_key(root.unwrap()) {
        DiskView{boundary_lsn: bdy, entries: reads}.the_ranking()[root.unwrap()] + 1
    } else {
        0
    }
}

pub open spec(checked) fn build_lsn_addr_index_from_reads_next_ptr(reads: Map<Address, JournalRecord>, 
    boundary_lsn: LSN, root: Pointer) -> Pointer
    decreases rank_of_reads(boundary_lsn, reads, root) when acyclic_reads(boundary_lsn, reads)
{
    if root is Some && reads.contains_key(root.unwrap()) {
        let next_ptr = reads[root.unwrap()].cropped_prior(boundary_lsn);
        build_lsn_addr_index_from_reads_next_ptr(reads, boundary_lsn, next_ptr)
    } else {
        root
    }
}

// maybe the decrease is on the rank of curr_end without peaking into curr_end?
pub open spec(checked) fn build_lsn_addr_index_from_reads(reads: Map<Address, JournalRecord>, 
    boundary_lsn: LSN, root: Pointer) -> LsnAddrIndex
    decreases rank_of_reads(boundary_lsn, reads, root) when acyclic_reads(boundary_lsn, reads)
{
    if root is Some && reads.contains_key(root.unwrap()) {
        let curr_msgs = reads[root.unwrap()].message_seq;
        let start_lsn = max(boundary_lsn as int, curr_msgs.seq_start as int) as nat;

        let update = singleton_index(start_lsn, curr_msgs.seq_end, root.unwrap());
        let next_ptr = reads[root.unwrap()].cropped_prior(boundary_lsn);
        let sub_index = build_lsn_addr_index_from_reads(reads, boundary_lsn, next_ptr);
        sub_index.union_prefer_right(update)
    } else {
        map!{}
    }
}

pub proof fn build_lsn_addr_index_from_reads_next_ptr_not_in_reads(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    ptr: Pointer,
)
requires
    acyclic_reads(boundary_lsn, reads),
    ptr == build_lsn_addr_index_from_reads_next_ptr(reads, boundary_lsn, root),
    ptr is Some,
ensures
    !reads.contains_key(ptr.unwrap()),
decreases rank_of_reads(boundary_lsn, reads, root)
{
    if root is Some && reads.contains_key(root.unwrap()) {
        let next_ptr = reads[root.unwrap()].cropped_prior(boundary_lsn);
        build_lsn_addr_index_from_reads_next_ptr_not_in_reads(reads, boundary_lsn, next_ptr, ptr);
    } else {
    }
}

pub proof fn build_lsn_addr_index_from_reads_next_ptr_after_insert(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    ptr1: Pointer,
    ptr2: Pointer,
    ptr2_data: JournalRecord,
)
requires
    ptr1 is Some,
    ptr2 is Some,
    acyclic_reads(boundary_lsn, reads),
    ptr2 == build_lsn_addr_index_from_reads_next_ptr(reads, boundary_lsn, ptr1),
    // inserted record matches the pointer and moves to its cropped prior
    ptr2_data.cropped_prior(boundary_lsn) is None
        || !reads.contains_key(ptr2_data.cropped_prior(boundary_lsn).unwrap()),
    acyclic_reads(boundary_lsn, reads.insert(ptr2.unwrap(), ptr2_data)),
ensures
    build_lsn_addr_index_from_reads_next_ptr(
        reads.insert(ptr2.unwrap(), ptr2_data),
        boundary_lsn,
        ptr1,
    ) == ptr2_data.cropped_prior(boundary_lsn)
decreases rank_of_reads(boundary_lsn, reads, ptr1)
{
    build_lsn_addr_index_from_reads_next_ptr_not_in_reads(reads, boundary_lsn, ptr1, ptr2);

    // Unfold the definition once on the updated reads.
    if reads.contains_key(ptr1.unwrap()) {
        let next_ptr = reads[ptr1.unwrap()].cropped_prior(boundary_lsn);
        build_lsn_addr_index_from_reads_next_ptr_after_insert(
            reads,
            boundary_lsn,
            next_ptr,
            ptr2,
            ptr2_data,
        );
        assert(build_lsn_addr_index_from_reads_next_ptr(
            reads.insert(ptr2.unwrap(), ptr2_data),
            boundary_lsn,
            ptr1,
        ) == build_lsn_addr_index_from_reads_next_ptr(
            reads.insert(ptr2.unwrap(), ptr2_data),
            boundary_lsn,
            next_ptr,
        ));
    } else {
        // next_ptr on missing root returns the root itself, and ptr2 == ptr1
        assert(build_lsn_addr_index_from_reads_next_ptr(
            reads.insert(ptr2.unwrap(), ptr2_data),
            boundary_lsn,
            ptr1,
        ) == build_lsn_addr_index_from_reads_next_ptr(
            reads.insert(ptr2.unwrap(), ptr2_data),
            boundary_lsn,
            ptr2,
        ));
    }

    // Now ptr2 is present in reads2, so the next pointer becomes ptr2_data.cropped_prior.
    assert(build_lsn_addr_index_from_reads_next_ptr(
        reads.insert(ptr2.unwrap(), ptr2_data),
        boundary_lsn,
        ptr2,
    ) == build_lsn_addr_index_from_reads_next_ptr(
        reads.insert(ptr2.unwrap(), ptr2_data),
        boundary_lsn,
        ptr2_data.cropped_prior(boundary_lsn),
    ));
}

pub proof fn build_lsn_addr_index_from_reads_extend_next_ptr(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    ptr2: Pointer,
    ptr2_data: JournalRecord,
)
requires
    ptr2 is Some,
    acyclic_reads(boundary_lsn, reads),
    ptr2 == build_lsn_addr_index_from_reads_next_ptr(reads, boundary_lsn, root),
    ptr2_data.wf(),
    ptr2_data.cropped_prior(boundary_lsn) is None
        || !reads.contains_key(ptr2_data.cropped_prior(boundary_lsn).unwrap()),
    lsn_disjoint(
        build_lsn_addr_index_from_reads(reads, boundary_lsn, root).dom(),
        max(boundary_lsn as int, ptr2_data.message_seq.seq_start as int) as nat,
        ptr2_data.message_seq.seq_end,
    ),
    acyclic_reads(boundary_lsn, reads.insert(ptr2.unwrap(), ptr2_data)),
ensures ({
    let start_lsn = max(boundary_lsn as int, ptr2_data.message_seq.seq_start as int) as nat;
    let end_lsn = ptr2_data.message_seq.seq_end;
    build_lsn_addr_index_from_reads(reads, boundary_lsn, root)
        .union_prefer_right(singleton_index(start_lsn, end_lsn, ptr2.unwrap()))
        =~= build_lsn_addr_index_from_reads(reads.insert(ptr2.unwrap(), ptr2_data), boundary_lsn, root)
})
decreases rank_of_reads(boundary_lsn, reads, root)
{
    if root is Some && reads.contains_key(root.unwrap()) {
        let curr_msgs = reads[root.unwrap()].message_seq;
        let start_lsn = max(boundary_lsn as int, curr_msgs.seq_start as int) as nat;
        let update = singleton_index(start_lsn, curr_msgs.seq_end, root.unwrap());
        let next_ptr = reads[root.unwrap()].cropped_prior(boundary_lsn);

        let start2 = max(boundary_lsn as int, ptr2_data.message_seq.seq_start as int) as nat;
        let end2 = ptr2_data.message_seq.seq_end;
        let update2 = singleton_index(start2, end2, ptr2.unwrap());

        let idx = build_lsn_addr_index_from_reads(reads, boundary_lsn, root);
        let sub_index = build_lsn_addr_index_from_reads(reads, boundary_lsn, next_ptr);
        assert(idx == sub_index.union_prefer_right(update));
        assert(lsn_disjoint(sub_index.dom(), start2, end2)) by {
            assert forall |lsn| start2 <= lsn < end2 implies !sub_index.dom().contains(lsn) by {
                if sub_index.dom().contains(lsn) {
                    assert(idx.dom().contains(lsn));
                }
            };
        };

        assert(ptr2 == build_lsn_addr_index_from_reads_next_ptr(reads, boundary_lsn, next_ptr));
        build_lsn_addr_index_from_reads_extend_next_ptr(
            reads,
            boundary_lsn,
            next_ptr,
            ptr2,
            ptr2_data,
        );

        // sub_index and idx computed above; use updated reads for sub_index2
        let sub_index2 = build_lsn_addr_index_from_reads(reads.insert(ptr2.unwrap(), ptr2_data), boundary_lsn, next_ptr);
        assert(sub_index.union_prefer_right(update2) == sub_index2);

        // commutation with disjoint ranges
        assert(idx.union_prefer_right(update2) == update2.union_prefer_right(idx)) by {
            assert forall |k| #[trigger] idx.union_prefer_right(update2).contains_key(k)
            implies idx.union_prefer_right(update2)[k] == update2.union_prefer_right(idx)[k] by {
                if update2.contains_key(k) {
                    assert(!idx.contains_key(k));
                }
            };
            assert forall |k| #[trigger] update2.union_prefer_right(idx).contains_key(k)
            implies idx.union_prefer_right(update2)[k] == update2.union_prefer_right(idx)[k] by {
                if update2.contains_key(k) {
                    assert(!idx.contains_key(k));
                }
            };
        };
        assert(idx.union_prefer_right(update2) == sub_index2.union_prefer_right(update)) by {
            assert forall |k| #[trigger] idx.union_prefer_right(update2).contains_key(k)
            implies idx.union_prefer_right(update2)[k] == sub_index2.union_prefer_right(update)[k] by {
                if update2.contains_key(k) {
                    assert(!idx.contains_key(k));
                    assert(sub_index2.contains_key(k));
                    assert(sub_index2[k] == update2[k]);
                    assert(!update.contains_key(k));
                } else if update.contains_key(k) {
                    assert(!update2.contains_key(k));
                    assert(idx.contains_key(k));
                    assert(idx[k] == update[k]);
                } else {
                    assert(!update2.contains_key(k));
                    assert(!update.contains_key(k));
                    if sub_index.contains_key(k) {
                        assert(idx.contains_key(k));
                        assert(idx[k] == sub_index[k]);
                        assert(sub_index2.contains_key(k));
                        assert(sub_index2[k] == sub_index[k]);
                    }
                }
            };
            assert forall |k| #[trigger] sub_index2.union_prefer_right(update).contains_key(k)
            implies idx.union_prefer_right(update2)[k] == sub_index2.union_prefer_right(update)[k] by {
                if update.contains_key(k) {
                    assert(idx.contains_key(k));
                    assert(idx[k] == update[k]);
                    assert(!update2.contains_key(k));
                } else if sub_index2.contains_key(k) {
                    if update2.contains_key(k) {
                        assert(!idx.contains_key(k));
                        assert(sub_index2[k] == update2[k]);
                    } else {
                        assert(sub_index.contains_key(k));
                        assert(idx.contains_key(k));
                        assert(idx[k] == sub_index[k]);
                    }
                }
            };
        };
        build_lsn_addr_index_from_reads_next_ptr_not_in_reads(reads, boundary_lsn, root, ptr2);
        assert(!reads.contains_key(ptr2.unwrap()));

        let reads2 = reads.insert(ptr2.unwrap(), ptr2_data);
        assert(root.unwrap() != ptr2.unwrap());
        assert(reads2[root.unwrap()] == reads[root.unwrap()]);
        assert(next_ptr == reads2[root.unwrap()].cropped_prior(boundary_lsn));
        assert(acyclic_reads(boundary_lsn, reads2));
        assert(build_lsn_addr_index_from_reads(reads2, boundary_lsn, root)
            =~= build_lsn_addr_index_from_reads(reads2, boundary_lsn, next_ptr).union_prefer_right(update)) by {
            build_lsn_addr_index_from_reads_step(reads2, boundary_lsn, root, next_ptr, update);
        };
        assert(sub_index2 == build_lsn_addr_index_from_reads(reads2, boundary_lsn, next_ptr));
    } else {
        // root is missing, so ptr2 == root
        assert(ptr2 == root);
        let reads2 = reads.insert(ptr2.unwrap(), ptr2_data);
        let start2 = max(boundary_lsn as int, ptr2_data.message_seq.seq_start as int) as nat;
        let end2 = ptr2_data.message_seq.seq_end;
        assert(build_lsn_addr_index_from_reads(reads, boundary_lsn, root) == Map::<LSN, Address>::empty());
        assert(build_lsn_addr_index_from_reads(reads2, boundary_lsn, root)
            == build_lsn_addr_index_from_reads(reads2, boundary_lsn, ptr2_data.cropped_prior(boundary_lsn))
                .union_prefer_right(singleton_index(start2, end2, ptr2.unwrap())));
        // ptr2_data.cropped_prior not in reads, so the sub-index is empty
        assert(build_lsn_addr_index_from_reads(reads2, boundary_lsn, ptr2_data.cropped_prior(boundary_lsn))
            == Map::<LSN, Address>::empty());
    }
}

pub proof fn build_lsn_addr_index_from_reads_step(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    next_ptr: Pointer,
    update: LsnAddrIndex,
)
requires
    acyclic_reads(boundary_lsn, reads),
    root is Some,
    reads.contains_key(root.unwrap()),
    next_ptr == reads[root.unwrap()].cropped_prior(boundary_lsn),
    update == singleton_index(
        max(boundary_lsn as int, reads[root.unwrap()].message_seq.seq_start as int) as nat,
        reads[root.unwrap()].message_seq.seq_end,
        root.unwrap(),
    ),
ensures
    build_lsn_addr_index_from_reads(reads, boundary_lsn, root)
        =~= build_lsn_addr_index_from_reads(reads, boundary_lsn, next_ptr)
            .union_prefer_right(update),
{
    let curr_msgs = reads[root.unwrap()].message_seq;
    let start_lsn = max(boundary_lsn as int, curr_msgs.seq_start as int) as nat;

    assert(build_lsn_addr_index_from_reads(reads, boundary_lsn, root)
        == build_lsn_addr_index_from_reads(reads, boundary_lsn, next_ptr)
            .union_prefer_right(update));
    assert(build_lsn_addr_index_from_reads(reads, boundary_lsn, root)
        =~= build_lsn_addr_index_from_reads(reads, boundary_lsn, next_ptr)
            .union_prefer_right(update));
}

pub proof fn build_lsn_addr_index_from_reads_values_in_reads(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    addr: Address,
)
requires
    acyclic_reads(boundary_lsn, reads),
    build_lsn_addr_index_from_reads(reads, boundary_lsn, root).values().contains(addr),
ensures
    reads.contains_key(addr),
decreases rank_of_reads(boundary_lsn, reads, root)
{
    if root is Some && reads.contains_key(root.unwrap()) {
        let curr_msgs = reads[root.unwrap()].message_seq;
        let start_lsn = max(boundary_lsn as int, curr_msgs.seq_start as int) as nat;
        let update = singleton_index(start_lsn, curr_msgs.seq_end, root.unwrap());
        let next_ptr = reads[root.unwrap()].cropped_prior(boundary_lsn);
        let idx = build_lsn_addr_index_from_reads(reads, boundary_lsn, root);
        let sub_index = build_lsn_addr_index_from_reads(reads, boundary_lsn, next_ptr);
        let lsn = choose |lsn: LSN| #![auto] idx.contains_key(lsn) && idx[lsn] == addr;
        if update.contains_key(lsn) {
        } else {
            build_lsn_addr_index_from_reads_values_in_reads(reads, boundary_lsn, next_ptr, addr);
        }
    } else {
    }
}

pub proof fn build_lsn_addr_index_from_reads_key_range(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    lsn: LSN,
)
requires
    acyclic_reads(boundary_lsn, reads),
    build_lsn_addr_index_from_reads(reads, boundary_lsn, root).contains_key(lsn),
ensures ({
    let index = build_lsn_addr_index_from_reads(reads, boundary_lsn, root);
    let addr = index[lsn];
    &&& reads.contains_key(addr)
    &&& max(boundary_lsn as int, reads[addr].message_seq.seq_start as int) as nat <= lsn
    &&& lsn < reads[addr].message_seq.seq_end
}),
decreases rank_of_reads(boundary_lsn, reads, root)
{
    if root is Some && reads.contains_key(root.unwrap()) {
        let curr = root.unwrap();
        let curr_msgs = reads[curr].message_seq;
        let start_lsn = max(boundary_lsn as int, curr_msgs.seq_start as int) as nat;
        let update = singleton_index(start_lsn, curr_msgs.seq_end, curr);
        let next_ptr = reads[curr].cropped_prior(boundary_lsn);
        let sub_index = build_lsn_addr_index_from_reads(reads, boundary_lsn, next_ptr);
        let index = build_lsn_addr_index_from_reads(reads, boundary_lsn, root);
        assert(index == sub_index.union_prefer_right(update));
        if update.contains_key(lsn) {
            assert(index[lsn] == update[lsn]);
            assert(update[lsn] == curr);
            assert(start_lsn <= lsn < curr_msgs.seq_end);
        } else {
            assert(sub_index.contains_key(lsn));
            assert(index[lsn] == sub_index[lsn]);
            build_lsn_addr_index_from_reads_key_range(reads, boundary_lsn, next_ptr, lsn);
        }
    } else {
        assert(build_lsn_addr_index_from_reads(reads, boundary_lsn, root) == Map::<LSN, Address>::empty());
        assert(false);
    }
}

pub proof fn lsn_addr_index_to_au_index_append_record(
    index: LsnAddrIndex,
    start: LSN,
    end: LSN,
    addr: Address,
)
    ensures
        lsn_addr_index_to_au_index(
            lsn_addr_index_append_record(index, start, end, addr),
        ) =~= lsn_addr_index_to_au_index(index).union_prefer_right(
            crate::allocation_layer::AllocationJournal_v::singleton_index(start, end, addr.au),
        ),
{
    let addr_update = singleton_index(start, end, addr);
    let au_update = crate::allocation_layer::AllocationJournal_v::singleton_index(start, end, addr.au);
    assert_maps_equal!(
        lsn_addr_index_to_au_index(lsn_addr_index_append_record(index, start, end, addr)),
        lsn_addr_index_to_au_index(index).union_prefer_right(au_update),
        lsn => {
            if au_update.contains_key(lsn) {
                assert(addr_update.contains_key(lsn));
                assert(addr_update[lsn].au == au_update[lsn]);
            } else if index.contains_key(lsn) {
                assert(lsn_addr_index_to_au_index(index).contains_key(lsn));
                assert(lsn_addr_index_to_au_index(index)[lsn] == index[lsn].au);
            }
        }
    );
}

pub proof fn build_lsn_addr_index_from_reads_to_au_index_page_walk_depth(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
)
    requires
        acyclic_reads(boundary_lsn, reads),
        page_walk_reads_cover(reads, boundary_lsn, root, depth),
    ensures
        lsn_addr_index_to_au_index(
            build_lsn_addr_index_from_reads(reads, boundary_lsn, root),
        ) =~= build_lsn_au_index_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            root,
            depth,
        ),
    decreases depth,
{
    if root is Some {
        assert(depth > 0);
        let addr = root.unwrap();
        assert(reads.contains_key(addr));
        let curr_msgs = reads[addr].message_seq;
        let start_lsn = max(boundary_lsn as int, curr_msgs.seq_start as int) as nat;
        let end_lsn = curr_msgs.seq_end;
        let next = reads[addr].cropped_prior(boundary_lsn);
        build_lsn_addr_index_from_reads_to_au_index_page_walk_depth(
            reads,
            boundary_lsn,
            next,
            (depth - 1) as nat,
        );
        let addr_index = build_lsn_addr_index_from_reads(reads, boundary_lsn, root);
        let sub_addr_index = build_lsn_addr_index_from_reads(reads, boundary_lsn, next);
        let au_index = build_lsn_au_index_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            root,
            depth,
        );
        let sub_au_index = build_lsn_au_index_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            next,
            (depth - 1) as nat,
        );
        assert(addr_index == lsn_addr_index_append_record(sub_addr_index, start_lsn, end_lsn, addr));
        assert(au_index == sub_au_index.union_prefer_right(
            crate::allocation_layer::AllocationJournal_v::singleton_index(start_lsn, end_lsn, addr.au),
        ));
        lsn_addr_index_to_au_index_append_record(sub_addr_index, start_lsn, end_lsn, addr);
        assert_maps_equal!(
            lsn_addr_index_to_au_index(addr_index),
            au_index,
            lsn => {}
        );
    } else {
        assert_maps_equal!(
            lsn_addr_index_to_au_index(build_lsn_addr_index_from_reads(reads, boundary_lsn, root)),
            build_lsn_au_index_from_reads_page_walk_depth(reads, boundary_lsn, root, depth),
            lsn => {}
        );
    }
}

pub proof fn build_lsn_addr_index_from_reads_to_au_index_au_walk_depth(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    page_depth: nat,
)
    requires
        acyclic_reads(boundary_lsn, reads),
        page_walk_reads_cover(reads, boundary_lsn, root, page_depth),
        au_walk_reads_cover(reads, boundary_lsn, root, first, au_depth, page_depth),
        (DiskView{boundary_lsn, entries}).pointer_is_upstream(root, first),
        forall |addr: Address| #[trigger] reads.contains_key(addr)
            && entries.contains_key(addr) ==> reads[addr] == entries[addr],
    ensures
        lsn_addr_index_to_au_index(
            build_lsn_addr_index_from_reads(reads, boundary_lsn, root),
        ) =~= build_lsn_au_index_from_reads_au_walk_depth(
            reads,
            boundary_lsn,
            root,
            first,
            au_depth,
            page_depth,
        ),
{
    let full_dv = DiskView{boundary_lsn, entries};
    build_lsn_addr_index_from_reads_to_au_index_page_walk_depth(
        reads,
        boundary_lsn,
        root,
        page_depth,
    );
    page_walk_reads_cover_build_matches_full_by_value(
        reads,
        entries,
        boundary_lsn,
        root,
        page_depth,
    );
    au_walk_reads_cover_build_matches_full_by_value(
        reads,
        entries,
        boundary_lsn,
        root,
        first,
        au_depth,
        page_depth,
    );
    full_dv.build_lsn_au_index_equiv_page_walk(root, first);
    assert_maps_equal!(
        lsn_addr_index_to_au_index(
            build_lsn_addr_index_from_reads(reads, boundary_lsn, root),
        ),
        build_lsn_au_index_from_reads_au_walk_depth(
            reads,
            boundary_lsn,
            root,
            first,
            au_depth,
            page_depth,
        ),
        lsn => {}
    );
}

pub struct JournalSnapshot {
    pub boundary_lsn: LSN,
    pub root: Option<JournalRoot>,
}

impl JournalSnapshot {
    pub open spec fn freshest_rec(self) -> Pointer {
        journal_root_pointer(self.root)
    }

    pub open spec fn first(self) -> AU {
        journal_root_first(self.root)
    }
}

pub open spec fn freeze_reads_for_seq_end(
    frozen: JournalSnapshot,
    frozen_seq_end: LSN,
) -> Map<Address, JournalRecord>
{
    if frozen.freshest_rec() is Some {
        Map::empty().insert(
            frozen.freshest_rec().unwrap(),
            JournalRecord{
                message_seq: MsgHistory{
                    msgs: Map::empty(),
                    seq_start: frozen.boundary_lsn,
                    seq_end: frozen_seq_end,
                },
                prior_rec: None,
            },
        )
    } else {
        Map::empty()
    }
}

pub open spec fn build_au_page_bounds_from_reads_page_walk_depth(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
) -> AUPageBounds
    decreases depth
{
    if root is None || depth == 0 {
        Map::empty()
    } else {
        let addr = root.unwrap();
        let prior = build_au_page_bounds_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            reads[addr].cropped_prior(boundary_lsn),
            (depth - 1) as nat,
        );
        let page = if prior.contains_key(addr.au) && addr.page <= prior[addr.au] {
            prior[addr.au]
        } else {
            addr.page
        };
        prior.insert(addr.au, page)
    }
}

pub open spec fn au_page_bounds_observe_addr(bounds: AUPageBounds, addr: Address) -> AUPageBounds
{
    let page = if bounds.contains_key(addr.au) && addr.page <= bounds[addr.au] {
        bounds[addr.au]
    } else {
        addr.page
    };
    bounds.insert(addr.au, page)
}

pub open spec fn build_au_page_bounds_from_reads_au_walk_depth(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    page_depth: nat,
) -> AUPageBounds
    decreases au_depth
{
    if root is None || au_depth == 0 {
        Map::empty()
    } else {
        let addr = root.unwrap();
        if addr.au == first {
            build_au_page_bounds_from_reads_page_walk_depth(
                reads,
                boundary_lsn,
                root,
                page_depth,
            )
        } else {
            let bottom = addr.first_page();
            let prior = build_au_page_bounds_from_reads_au_walk_depth(
                reads,
                boundary_lsn,
                reads[bottom].cropped_prior(boundary_lsn),
                first,
                (au_depth - 1) as nat,
                page_depth,
            );
            prior.insert(addr.au, addr.page)
        }
    }
}

pub proof fn build_au_page_bounds_from_reads_page_walk_depth_supermap(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
)
    requires
        reads <= entries,
        page_walk_reads_cover(reads, boundary_lsn, root, depth),
    ensures
        build_au_page_bounds_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            root,
            depth,
        ) =~= build_au_page_bounds_from_reads_page_walk_depth(
            entries,
            boundary_lsn,
            root,
            depth,
        ),
    decreases depth
{
    if root is Some && depth > 0 {
        let addr = root.unwrap();
        assert(reads.contains_key(addr));
        assert(entries.contains_key(addr));
        assert(reads[addr] == entries[addr]);
        let next = reads[addr].cropped_prior(boundary_lsn);
        assert(next == entries[addr].cropped_prior(boundary_lsn));
        build_au_page_bounds_from_reads_page_walk_depth_supermap(
            reads,
            entries,
            boundary_lsn,
            next,
            (depth - 1) as nat,
        );
        let reads_prior = build_au_page_bounds_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            next,
            (depth - 1) as nat,
        );
        let entries_prior = build_au_page_bounds_from_reads_page_walk_depth(
            entries,
            boundary_lsn,
            next,
            (depth - 1) as nat,
        );
        assert(reads_prior =~= entries_prior);
        assert_maps_equal!(
            build_au_page_bounds_from_reads_page_walk_depth(
                reads,
                boundary_lsn,
                root,
                depth,
            ),
            build_au_page_bounds_from_reads_page_walk_depth(
                entries,
                boundary_lsn,
                root,
                depth,
            ),
            au => {
                if reads_prior.contains_key(addr.au) {
                    assert(entries_prior.contains_key(addr.au));
                    assert(reads_prior[addr.au] == entries_prior[addr.au]);
                }
                if entries_prior.contains_key(addr.au) {
                    assert(reads_prior.contains_key(addr.au));
                    assert(reads_prior[addr.au] == entries_prior[addr.au]);
                }
            }
        );
    }
}

pub proof fn build_au_page_bounds_from_reads_au_walk_depth_supermap(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    page_depth: nat,
)
    requires
        reads <= entries,
        au_walk_reads_cover(reads, boundary_lsn, root, first, au_depth, page_depth),
    ensures
        build_au_page_bounds_from_reads_au_walk_depth(
            reads,
            boundary_lsn,
            root,
            first,
            au_depth,
            page_depth,
        ) =~= build_au_page_bounds_from_reads_au_walk_depth(
            entries,
            boundary_lsn,
            root,
            first,
            au_depth,
            page_depth,
        ),
    decreases au_depth
{
    if root is Some && au_depth > 0 {
        let addr = root.unwrap();
        if addr.au == first {
            build_au_page_bounds_from_reads_page_walk_depth_supermap(
                reads,
                entries,
                boundary_lsn,
                root,
                page_depth,
            );
        } else {
            let bottom = addr.first_page();
            assert(reads.contains_key(addr));
            assert(reads.contains_key(bottom));
            assert(entries.contains_key(addr));
            assert(entries.contains_key(bottom));
            assert(reads[addr] == entries[addr]);
            assert(reads[bottom] == entries[bottom]);
            let next = reads[bottom].cropped_prior(boundary_lsn);
            assert(next == entries[bottom].cropped_prior(boundary_lsn));
            build_au_page_bounds_from_reads_au_walk_depth_supermap(
                reads,
                entries,
                boundary_lsn,
                next,
                first,
                (au_depth - 1) as nat,
                page_depth,
            );
            let reads_prior = build_au_page_bounds_from_reads_au_walk_depth(
                reads,
                boundary_lsn,
                next,
                first,
                (au_depth - 1) as nat,
                page_depth,
            );
            let entries_prior = build_au_page_bounds_from_reads_au_walk_depth(
                entries,
                boundary_lsn,
                next,
                first,
                (au_depth - 1) as nat,
                page_depth,
            );
            assert(reads_prior =~= entries_prior);
            assert_maps_equal!(
                build_au_page_bounds_from_reads_au_walk_depth(
                    reads,
                    boundary_lsn,
                    root,
                    first,
                    au_depth,
                    page_depth,
                ),
                build_au_page_bounds_from_reads_au_walk_depth(
                    entries,
                    boundary_lsn,
                    root,
                    first,
                    au_depth,
                    page_depth,
                ),
                au => {}
            );
        }
    }
}

pub proof fn build_lsn_addr_index_from_reads_values_bounded_by_page_bounds(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
    addr: Address,
)
    requires
        acyclic_reads(boundary_lsn, reads),
        page_walk_reads_cover(reads, boundary_lsn, root, depth),
        build_lsn_addr_index_from_reads(reads, boundary_lsn, root).values().contains(addr),
    ensures
        build_au_page_bounds_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            root,
            depth,
        ).contains_key(addr.au),
        addr.page <= build_au_page_bounds_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            root,
            depth,
        )[addr.au],
    decreases rank_of_reads(boundary_lsn, reads, root),
{
    if root is Some && reads.contains_key(root.unwrap()) {
        let curr = root.unwrap();
        let curr_msgs = reads[curr].message_seq;
        let start_lsn = max(boundary_lsn as int, curr_msgs.seq_start as int) as nat;
        let update = singleton_index(start_lsn, curr_msgs.seq_end, curr);
        let next = reads[curr].cropped_prior(boundary_lsn);
        let index = build_lsn_addr_index_from_reads(reads, boundary_lsn, root);
        let sub_index = build_lsn_addr_index_from_reads(reads, boundary_lsn, next);
        let bounds = build_au_page_bounds_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            root,
            depth,
        );
        let prior = build_au_page_bounds_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            next,
            (depth - 1) as nat,
        );
        assert(depth > 0);
        assert(index == lsn_addr_index_append_record(sub_index, start_lsn, curr_msgs.seq_end, curr));
        let lsn = choose |lsn: LSN| #![auto] index.contains_key(lsn) && index[lsn] == addr;
        if update.contains_key(lsn) {
            assert(update[lsn] == curr);
            assert(index[lsn] == curr);
            assert(addr == curr);
            assert(bounds.contains_key(addr.au));
            if prior.contains_key(addr.au) && addr.page <= prior[addr.au] {
                assert(bounds[addr.au] == prior[addr.au]);
            } else {
                assert(bounds[addr.au] == addr.page);
            }
        } else {
            assert(sub_index.contains_key(lsn));
            assert(sub_index[lsn] == addr);
            assert(sub_index.values().contains(addr));
            build_lsn_addr_index_from_reads_values_bounded_by_page_bounds(
                reads,
                boundary_lsn,
                next,
                (depth - 1) as nat,
                addr,
            );
            assert(prior.contains_key(addr.au));
            assert(addr.page <= prior[addr.au]);
            assert(bounds.contains_key(addr.au));
            if addr.au == curr.au {
                if prior.contains_key(curr.au) && curr.page <= prior[curr.au] {
                    assert(bounds[addr.au] == prior[addr.au]);
                } else {
                    assert(bounds[addr.au] == curr.page);
                    assert(prior[addr.au] < curr.page);
                    assert(addr.page <= curr.page);
                }
            } else {
                assert(bounds[addr.au] == prior[addr.au]);
            }
        }
    } else {
        assert(build_lsn_addr_index_from_reads(reads, boundary_lsn, root) == Map::<LSN, Address>::empty());
    }
}

pub proof fn build_au_page_bounds_from_reads_page_walk_depth_matches_disk(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
)
    requires
        page_walk_reads_cover(reads, boundary_lsn, root, depth),
        (DiskView{boundary_lsn, entries}).decodable(root),
        (DiskView{boundary_lsn, entries}).acyclic(),
        forall |a: Address| #[trigger] reads.contains_key(a)
            && entries.contains_key(a) ==> reads[a] == entries[a],
    ensures
        build_au_page_bounds_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            root,
            depth,
        ) =~= (DiskView{boundary_lsn, entries}).build_au_page_bounds_page_walk(root),
    decreases depth,
{
    let dv = DiskView{boundary_lsn, entries};
    if root is Some {
        assert(depth > 0);
        let addr = root.unwrap();
        assert(reads.contains_key(addr));
        assert(entries.contains_key(addr));
        assert(reads[addr] == entries[addr]);
        let next = reads[addr].cropped_prior(boundary_lsn);
        assert(dv.next(root) == next);
        assert(dv.decodable(next));
        build_au_page_bounds_from_reads_page_walk_depth_matches_disk(
            reads,
            entries,
            boundary_lsn,
            next,
            (depth - 1) as nat,
        );
        let reads_prior = build_au_page_bounds_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            next,
            (depth - 1) as nat,
        );
        let disk_prior = dv.build_au_page_bounds_page_walk(next);
        assert(reads_prior =~= disk_prior);
        assert_maps_equal!(
            build_au_page_bounds_from_reads_page_walk_depth(
                reads,
                boundary_lsn,
                root,
                depth,
            ),
            dv.build_au_page_bounds_page_walk(root),
            au => {
                if reads_prior.contains_key(addr.au) {
                    assert(disk_prior.contains_key(addr.au));
                    assert(reads_prior[addr.au] == disk_prior[addr.au]);
                }
                if disk_prior.contains_key(addr.au) {
                    assert(reads_prior.contains_key(addr.au));
                    assert(reads_prior[addr.au] == disk_prior[addr.au]);
                }
            }
        );
    }
}

pub proof fn build_au_page_bounds_from_reads_au_walk_depth_matches_disk(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    page_depth: nat,
)
    requires
        au_walk_reads_cover(reads, boundary_lsn, root, first, au_depth, page_depth),
        (DiskView{boundary_lsn, entries}).pointer_is_upstream(root, first),
        forall |a: Address| #[trigger] reads.contains_key(a)
            && entries.contains_key(a) ==> reads[a] == entries[a],
    ensures
        build_au_page_bounds_from_reads_au_walk_depth(
            reads,
            boundary_lsn,
            root,
            first,
            au_depth,
            page_depth,
        ) =~= (DiskView{boundary_lsn, entries}).build_au_page_bounds_au_walk(root, first),
    decreases au_depth,
{
    let dv = DiskView{boundary_lsn, entries};
    if root is Some {
        assert(au_depth > 0);
        let addr = root.unwrap();
        if addr.au == first {
            assert(page_walk_reads_cover(reads, boundary_lsn, root, page_depth));
            build_au_page_bounds_from_reads_page_walk_depth_matches_disk(
                reads,
                entries,
                boundary_lsn,
                root,
                page_depth,
            );
            assert_maps_equal!(
                build_au_page_bounds_from_reads_au_walk_depth(
                    reads,
                    boundary_lsn,
                    root,
                    first,
                    au_depth,
                    page_depth,
                ),
                dv.build_au_page_bounds_au_walk(root, first),
                au => {}
            );
        } else {
            let bottom = addr.first_page();
            assert(reads.contains_key(addr));
            assert(reads.contains_key(bottom));
            assert(entries.contains_key(addr));
            dv.bottom_properties(root, first);
            assert(dv.pointer_is_upstream(Some(bottom), first));
            assert(entries.contains_key(bottom));
            assert(reads[bottom] == entries[bottom]);
            let next = reads[bottom].cropped_prior(boundary_lsn);
            assert(dv.next(Some(bottom)) == next);
            assert(dv.pointer_is_upstream(next, first));
            build_au_page_bounds_from_reads_au_walk_depth_matches_disk(
                reads,
                entries,
                boundary_lsn,
                next,
                first,
                (au_depth - 1) as nat,
                page_depth,
            );
            let reads_prior = build_au_page_bounds_from_reads_au_walk_depth(
                reads,
                boundary_lsn,
                next,
                first,
                (au_depth - 1) as nat,
                page_depth,
            );
            let disk_prior = dv.build_au_page_bounds_au_walk(next, first);
            assert(reads_prior =~= disk_prior);
            assert_maps_equal!(
                build_au_page_bounds_from_reads_au_walk_depth(
                    reads,
                    boundary_lsn,
                    root,
                    first,
                    au_depth,
                    page_depth,
                ),
                dv.build_au_page_bounds_au_walk(root, first),
                au => {}
            );
        }
    }
}

pub proof fn build_lsn_addr_index_from_reads_values_bounded_by_au_page_bounds(
    reads: Map<Address, JournalRecord>,
    entries: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    page_depth: nat,
    addr: Address,
)
    requires
        acyclic_reads(boundary_lsn, reads),
        page_walk_reads_cover(reads, boundary_lsn, root, page_depth),
        au_walk_reads_cover(reads, boundary_lsn, root, first, au_depth, page_depth),
        (DiskView{boundary_lsn, entries}).pointer_is_upstream(root, first),
        forall |a: Address| #[trigger] reads.contains_key(a)
            && entries.contains_key(a) ==> reads[a] == entries[a],
        build_lsn_addr_index_from_reads(reads, boundary_lsn, root).values().contains(addr),
    ensures
        build_au_page_bounds_from_reads_au_walk_depth(
            reads,
            boundary_lsn,
            root,
            first,
            au_depth,
            page_depth,
        ).contains_key(addr.au),
        addr.page <= build_au_page_bounds_from_reads_au_walk_depth(
            reads,
            boundary_lsn,
            root,
            first,
            au_depth,
            page_depth,
        )[addr.au],
{
    build_lsn_addr_index_from_reads_values_bounded_by_page_bounds(
        reads,
        boundary_lsn,
        root,
        page_depth,
        addr,
    );
    let dv = DiskView{boundary_lsn, entries};
    build_au_page_bounds_from_reads_page_walk_depth_matches_disk(
        reads,
        entries,
        boundary_lsn,
        root,
        page_depth,
    );
    build_au_page_bounds_from_reads_au_walk_depth_matches_disk(
        reads,
        entries,
        boundary_lsn,
        root,
        first,
        au_depth,
        page_depth,
    );
    dv.build_au_page_bounds_equiv_page_walk(root, first);
    let page_bounds = build_au_page_bounds_from_reads_page_walk_depth(
        reads,
        boundary_lsn,
        root,
        page_depth,
    );
    let au_bounds = build_au_page_bounds_from_reads_au_walk_depth(
        reads,
        boundary_lsn,
        root,
        first,
        au_depth,
        page_depth,
    );
    assert(au_bounds =~= page_bounds);
}

pub struct JournalStatus {
    pub unmarshalled_tail: MsgHistory, // in memory journal
    pub lsn_au_index: LsnAUIndex,
    pub au_page_bounds: AUPageBounds,
    pub clean_watermark_au_page_bounds: AUPageBounds,
    pub clean_watermark_lsn: LSN,
}

state_machine!{ CachedJournal {
    fields{
        pub snapshot: JournalSnapshot,
        pub status: Option<JournalStatus>,
    }

    #[invariant]
    pub open spec(checked) fn wf(self) -> bool
    {
        self.status is Some ==> {
            &&& self.seq_start() <= self.seq_end()
            &&& self.status.unwrap().unmarshalled_tail.wf()
            &&& self.seq_start() <= self.clean_watermark() <= self.marshalled_seq_end()
            &&& self.status.unwrap().clean_watermark_au_page_bounds.dom()
                <= self.status.unwrap().au_page_bounds.dom()
            &&& forall |au: AU| #[trigger] self.status.unwrap()
                .clean_watermark_au_page_bounds.contains_key(au) ==>
                self.status.unwrap().clean_watermark_au_page_bounds[au]
                    <= self.status.unwrap().au_page_bounds[au]
        }
    }

    pub open spec(checked) fn seq_start(self) -> LSN
    {
        self.snapshot.boundary_lsn
    }

    pub open spec(checked) fn marshalled_seq_end(self) -> LSN
    recommends self.status is Some
    {
        self.status.unwrap().unmarshalled_tail.seq_start
    }

    pub open spec(checked) fn clean_watermark(self) -> LSN
    recommends self.status is Some
    {
        self.status.unwrap().clean_watermark_lsn
    }

    pub open spec(checked) fn seq_end(self) -> LSN
    recommends self.status is Some
    {
        self.status.unwrap().unmarshalled_tail.seq_end
    }
    
    pub open spec(checked) fn can_discard_to(self, lsn: LSN) -> bool
    recommends self.status is Some
    {
        self.seq_start() <= lsn <= self.seq_end()
    }

    pub enum Label
    {
        LoadIndex{reads: Map<Address, JournalRecord>, discovered_aus: Set<AU>},
        ReadForRecovery{messages: MsgHistory, reads: Map<Address, JournalRecord>},
        FreezeForCommit{frozen: JournalSnapshot, reads: Map<Address, JournalRecord>},
        ObserveCleanAUs{aus: Set<AU>},
        QueryEndLsn{end_lsn: LSN},
        Put{messages: MsgHistory},
        DiscardOld{start_lsn: LSN, require_end: LSN, deallocs: Set<AU>},
        JournalMarshal{writes: Map<Address, JournalRecord>},
        Internal{},
    }

    transition!{ read_for_recovery(lbl: Label, start_lsn: LSN, addr: Address) {
        require pre.status is Some;
        require let Label::ReadForRecovery{messages, reads} = lbl;

        require reads.contains_key(addr);
        let record = reads[addr];
        let cropped = record.message_seq.maybe_discard_old(pre.snapshot.boundary_lsn);
        require start_lsn == cropped.seq_start;
        require start_lsn < record.message_seq.seq_end;
        require pre.status.unwrap().lsn_au_index.contains_key(start_lsn);
        require pre.status.unwrap().lsn_au_index[start_lsn] == addr.au;
        let bounds = pre.status.unwrap().au_page_bounds;
        require bounds.contains_key(addr.au);
        require addr.page <= bounds[addr.au];
        require messages == cropped;
    }}

    transition!{ freeze_for_commit(lbl: Label) {
        require pre.status is Some;
        require let Label::FreezeForCommit{frozen, reads} = lbl;

        let index = pre.status.unwrap().lsn_au_index;
        let bounds = pre.status.unwrap().au_page_bounds;
        require pre.seq_start() <= frozen.boundary_lsn;
        require frozen.boundary_lsn <= pre.seq_end();

        require frozen.freshest_rec() is Some ==> {
            let root = frozen.freshest_rec().unwrap();
            &&& reads.contains_key(root)
            &&& frozen.boundary_lsn < reads[root].message_seq.seq_end
            &&& index.contains_key(frozen.boundary_lsn)
            &&& frozen.first() == index[frozen.boundary_lsn]
            &&& index.contains_value(root.au)
            &&& frozen.boundary_lsn < largest_lsn_plus_one_au(index, root.au)
            &&& bounds.contains_key(root.au)
            &&& root.page <= bounds[root.au]
        };

    }}

    transition!{ query_end_lsn(lbl: Label) {
        require pre.status is Some;
        require lbl is QueryEndLsn;
        require lbl->end_lsn == pre.seq_end();
    }}

    transition!{ advance_watermark(lbl: Label, target_lsn: LSN) {
        require pre.status is Some;
        require lbl is ObserveCleanAUs;
        require pre.clean_watermark() < target_lsn <= pre.marshalled_seq_end();

        let index = pre.status.unwrap().lsn_au_index;
        let flushed_lsns = Set::new(|lsn: LSN| pre.clean_watermark() <= lsn < target_lsn);
        require lbl->aus == index.restrict(flushed_lsns).values();

        update status = Some(JournalStatus{
            clean_watermark_lsn: target_lsn,
            clean_watermark_au_page_bounds: pre.status.unwrap().clean_watermark_au_page_bounds
                .union_prefer_right(pre.status.unwrap().au_page_bounds.restrict(lbl->aus)),
            ..pre.status.unwrap()
        });
    }}

    transition!{ put(lbl: Label) {
        require pre.status is Some;
        require let Label::Put{messages} = lbl;
        require messages.wf();
        require messages.seq_start == pre.seq_end();
        update status = Some(JournalStatus{unmarshalled_tail: pre.status.unwrap().unmarshalled_tail.concat(messages), ..pre.status.unwrap()});
    }}

    transition!{ discard_old(lbl: Label) {
        require pre.status is Some;
        require let Label::DiscardOld{start_lsn, require_end, deallocs} = lbl;

        require require_end == pre.seq_end(); // pre.marshalled_seq_end();
        require pre.seq_start() <= start_lsn <= require_end;

        let new_lsn_au_index = lsn_au_index_discard_up_to(pre.status.unwrap().lsn_au_index, start_lsn);
        let new_clean_watermark = if start_lsn > pre.clean_watermark() { start_lsn } else { pre.clean_watermark() };

        require deallocs == pre.status.unwrap().lsn_au_index.values().difference(new_lsn_au_index.values());

        let new_root = if pre.marshalled_seq_end() <= start_lsn {
            None
        } else {
            Some(JournalRoot{
                freshest_rec: pre.snapshot.freshest_rec().unwrap(),
                first: new_lsn_au_index[start_lsn],
            })
        };
        require new_root is Some ==> new_lsn_au_index.contains_key(start_lsn);

        update snapshot = JournalSnapshot{boundary_lsn: start_lsn, root: new_root};
        update status = Some(JournalStatus{
            lsn_au_index: new_lsn_au_index,
            au_page_bounds: pre.status.unwrap().au_page_bounds.restrict(new_lsn_au_index.values()),
            clean_watermark_au_page_bounds: pre.status.unwrap().clean_watermark_au_page_bounds
                .restrict(new_lsn_au_index.values()),
            clean_watermark_lsn: new_clean_watermark,
            unmarshalled_tail: pre.status.unwrap().unmarshalled_tail.bounded_discard(start_lsn),
            ..pre.status.unwrap()
        });
    }}

    transition!{ internal_journal_marshal(lbl: Label, cut: LSN, addr: Address) {
        require pre.status is Some;
        require lbl is JournalMarshal;

        require pre.marshalled_seq_end() < cut;
        require pre.status.unwrap().unmarshalled_tail.can_discard_to(cut);

        let marshalled_msgs = pre.status.unwrap().unmarshalled_tail.discard_recent(cut);
        let new_record = JournalRecord{message_seq: marshalled_msgs, prior_rec: pre.snapshot.freshest_rec()};
        require lbl->writes == Map::empty().insert(addr, new_record);

        let new_first = if pre.snapshot.root is None { addr.au } else { pre.snapshot.first() };
        update snapshot = JournalSnapshot{root: Some(JournalRoot{freshest_rec: addr, first: new_first}), ..pre.snapshot};
        update status = Some(JournalStatus{
            lsn_au_index: lsn_au_index_append_record(pre.status.unwrap().lsn_au_index, marshalled_msgs, addr.au),
            au_page_bounds: au_page_bounds_observe_addr(pre.status.unwrap().au_page_bounds, addr),
            clean_watermark_au_page_bounds: pre.status.unwrap().clean_watermark_au_page_bounds,
            unmarshalled_tail:  pre.status.unwrap().unmarshalled_tail.discard_old(cut),
            // Marshal only dirties cache pages; cleaning/flush advances watermark later.
            clean_watermark_lsn: pre.status.unwrap().clean_watermark_lsn,
        });
    }}

    transition!{ load_index(lbl: Label, au_depth: nat, page_depth: nat) {
        require pre.status is None;
        require let Label::LoadIndex{reads, discovered_aus} = lbl;

        let ptr = pre.snapshot.freshest_rec();
        let bdy = pre.snapshot.boundary_lsn;
        let first = pre.snapshot.first();

        require au_walk_reads_cover(reads, bdy, ptr, first, au_depth, page_depth);

        let root_seq_end = if ptr is Some { reads[ptr.unwrap()].message_seq.seq_end } else { bdy };
        let seq_end = if bdy <= root_seq_end { root_seq_end } else { bdy };
        let lsn_au_index = build_lsn_au_index_from_reads_au_walk_depth(
            reads,
            bdy,
            ptr,
            first,
            au_depth,
            page_depth,
        );
        let au_page_bounds = build_au_page_bounds_from_reads_au_walk_depth(
            reads,
            bdy,
            ptr,
            first,
            au_depth,
            page_depth,
        );
        let clean_watermark_lsn = seq_end;
        require discovered_aus == lsn_au_index.values();

        update status = Some(JournalStatus{
            lsn_au_index,
            au_page_bounds,
            clean_watermark_au_page_bounds: au_page_bounds,
            unmarshalled_tail: MsgHistory::empty_history_at(seq_end),
            clean_watermark_lsn,
        });
    }}

    // this makes it so that we can't really initialize everything in a single transition
    init!{ initialize(snapshot: JournalSnapshot) {        
        init snapshot = snapshot;
        init status = None;
    }}

    #[inductive(read_for_recovery)]
    fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label, start_lsn: LSN, addr: Address) { }
    
    #[inductive(freeze_for_commit)]
    fn freeze_for_commit_inductive(pre: Self, post: Self, lbl: Label) { }
    
    #[inductive(query_end_lsn)]
    fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(advance_watermark)]
    fn advance_watermark_inductive(pre: Self, post: Self, lbl: Label, target_lsn: LSN) { }
    
    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label) { }
    
    #[inductive(discard_old)]
    fn discard_old_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(internal_journal_marshal)]
    fn internal_journal_marshal_inductive(pre: Self, post: Self, lbl: Label, cut: LSN, addr: Address) {
        assert(post.status.unwrap().clean_watermark_au_page_bounds.dom()
            <= post.status.unwrap().au_page_bounds.dom()) by {
            assert forall |au: AU| #[trigger] post.status.unwrap()
                .clean_watermark_au_page_bounds.dom().contains(au)
                implies post.status.unwrap().au_page_bounds.dom().contains(au) by {
                assert(pre.wf());
                assert(pre.status.unwrap().clean_watermark_au_page_bounds.dom()
                    <= pre.status.unwrap().au_page_bounds.dom());
            }
        }
        assert forall |au: AU| #[trigger] post.status.unwrap()
            .clean_watermark_au_page_bounds.contains_key(au)
            implies post.status.unwrap().clean_watermark_au_page_bounds[au]
                <= post.status.unwrap().au_page_bounds[au] by {
            assert(pre.wf());
            assert(pre.status.unwrap().clean_watermark_au_page_bounds[au]
                <= pre.status.unwrap().au_page_bounds[au]);
            if au == addr.au {
                if addr.page <= pre.status.unwrap().au_page_bounds[au] {
                    assert(post.status.unwrap().au_page_bounds[au]
                        == pre.status.unwrap().au_page_bounds[au]);
                } else {
                    assert(pre.status.unwrap().au_page_bounds[au] < addr.page);
                    assert(post.status.unwrap().au_page_bounds[au] == addr.page);
                }
            } else {
                assert(post.status.unwrap().au_page_bounds[au]
                    == pre.status.unwrap().au_page_bounds[au]);
            }
        }
    }
    
    #[inductive(load_index)]
    fn load_index_inductive(pre: Self, post: Self, lbl: Label, au_depth: nat, page_depth: nat) { }
    
    #[inductive(initialize)]
    pub fn initialize_inductive(post: Self, snapshot: JournalSnapshot) {
    }

    pub proof fn inv_next(pre: Self, post: Self, lbl: CachedJournal::Label)
        requires
            pre.wf(),
            CachedJournal::State::next(pre, post, lbl),
        ensures
            post.wf(),
    {
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);

        let step = choose |step| CachedJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachedJournal::Step::read_for_recovery(start_lsn, addr) => {
                CachedJournal::State::read_for_recovery_inductive(pre, post, lbl, start_lsn, addr);
            },
            CachedJournal::Step::freeze_for_commit() => {
                CachedJournal::State::freeze_for_commit_inductive(pre, post, lbl);
            },
            CachedJournal::Step::query_end_lsn() => {
                CachedJournal::State::query_end_lsn_inductive(pre, post, lbl);
            },
            CachedJournal::Step::advance_watermark(target_lsn) => {
                CachedJournal::State::advance_watermark_inductive(pre, post, lbl, target_lsn);
            },
            CachedJournal::Step::put() => {
                CachedJournal::State::put_inductive(pre, post, lbl);
            },
            CachedJournal::Step::discard_old() => {
                CachedJournal::State::discard_old_inductive(pre, post, lbl);
            },
            CachedJournal::Step::internal_journal_marshal(cut, addr) => {
                CachedJournal::State::internal_journal_marshal_inductive(pre, post, lbl, cut, addr);
            },
            CachedJournal::Step::load_index(au_depth, page_depth) => {
                CachedJournal::State::load_index_inductive(pre, post, lbl, au_depth, page_depth);
            },
            _ => {
                assert(post.wf());
            },
        }
    }

    pub proof fn status_some_next_effect(pre: Self, post: Self, lbl: CachedJournal::Label)
        requires
            CachedJournal::State::next(pre, post, lbl),
        ensures
            post.status is Some,
    {
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let step = choose |step| CachedJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachedJournal::Step::read_for_recovery(start_lsn, addr) => {
            },
            CachedJournal::Step::freeze_for_commit() => {
            },
            CachedJournal::Step::query_end_lsn() => {
            },
            CachedJournal::Step::advance_watermark(target_lsn) => {
            },
            CachedJournal::Step::put() => {
            },
            CachedJournal::Step::discard_old() => {
            },
            CachedJournal::Step::internal_journal_marshal(cut, addr) => {
            },
            CachedJournal::Step::load_index(au_depth, page_depth) => {
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn load_index_effect(
        pre: Self,
        post: Self,
        reads: Map<Address, JournalRecord>,
        discovered_aus: Set<AU>,
    )
        requires
            CachedJournal::State::next(
                pre,
                post,
                CachedJournal::Label::LoadIndex{reads, discovered_aus},
            ),
        ensures
            pre.status is None,
            post.snapshot == pre.snapshot,
            post.status is Some,
            discovered_aus == post.status.unwrap().lsn_au_index.values(),
            exists |au_depth: nat, page_depth: nat| {
                &&& #[trigger] CachedJournal::State::load_index(
                    pre,
                    post,
                    CachedJournal::Label::LoadIndex{reads, discovered_aus},
                    au_depth,
                    page_depth,
                )
                &&& post.status.unwrap().au_page_bounds
                    == build_au_page_bounds_from_reads_au_walk_depth(
                        reads,
                        pre.snapshot.boundary_lsn,
                        pre.snapshot.freshest_rec(),
                        pre.snapshot.first(),
                        au_depth,
                        page_depth,
                    )
            },
    {
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let lbl = CachedJournal::Label::LoadIndex{reads, discovered_aus};
        let step = choose |step| CachedJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachedJournal::Step::load_index(au_depth, page_depth) => {
                assert(exists |au_depth: nat, page_depth: nat| {
                    &&& #[trigger] CachedJournal::State::load_index(
                        pre,
                        post,
                        lbl,
                        au_depth,
                        page_depth,
                    )
                    &&& post.status.unwrap().au_page_bounds
                        == build_au_page_bounds_from_reads_au_walk_depth(
                            reads,
                            pre.snapshot.boundary_lsn,
                            pre.snapshot.freshest_rec(),
                            pre.snapshot.first(),
                            au_depth,
                            page_depth,
                        )
                });
            },
            _ => { assert(false); },
        }
    }

    pub proof fn load_index_with_restricted_reads(
        pre: Self,
        post: Self,
        reads: Map<Address, JournalRecord>,
        addrs: Set<Address>,
        discovered_aus: Set<AU>,
        au_depth: nat,
        page_depth: nat,
    )
        requires
            CachedJournal::State::load_index(
                pre,
                post,
                CachedJournal::Label::LoadIndex{reads, discovered_aus},
                au_depth,
                page_depth,
            ),
            au_walk_addrs_in(
                reads,
                pre.snapshot.boundary_lsn,
                pre.snapshot.freshest_rec(),
                pre.snapshot.first(),
                au_depth,
                page_depth,
                addrs,
            ),
        ensures
            CachedJournal::State::next(
                pre,
                post,
                CachedJournal::Label::LoadIndex{
                    reads: reads.restrict(addrs),
                    discovered_aus,
                },
            ),
    {
        let lbl = CachedJournal::Label::LoadIndex{reads, discovered_aus};
        let ptr = pre.snapshot.freshest_rec();
        let bdy = pre.snapshot.boundary_lsn;
        let first = pre.snapshot.first();
        let sub_reads = reads.restrict(addrs);
        let sub_lbl = CachedJournal::Label::LoadIndex{
            reads: sub_reads,
            discovered_aus,
        };
        assert(CachedJournal::State::load_index(
            pre,
            post,
            lbl,
            au_depth,
            page_depth,
        )) by {
        }
        assert(au_walk_reads_cover(reads, bdy, ptr, first, au_depth, page_depth));
        au_walk_reads_cover_restrict(reads, addrs, bdy, ptr, first, au_depth, page_depth);
        assert(au_walk_reads_cover(sub_reads, bdy, ptr, first, au_depth, page_depth));
        assert(sub_reads <= reads);
        build_lsn_au_index_from_reads_au_walk_depth_supermap(
            sub_reads,
            reads,
            bdy,
            ptr,
            first,
            au_depth,
            page_depth,
        );
        build_au_page_bounds_from_reads_au_walk_depth_supermap(
            sub_reads,
            reads,
            bdy,
            ptr,
            first,
            au_depth,
            page_depth,
        );
        assert(build_lsn_au_index_from_reads_au_walk_depth(
            sub_reads,
            bdy,
            ptr,
            first,
            au_depth,
            page_depth,
        ) =~= build_lsn_au_index_from_reads_au_walk_depth(
            reads,
            bdy,
            ptr,
            first,
            au_depth,
            page_depth,
        ));
        assert(build_au_page_bounds_from_reads_au_walk_depth(
            sub_reads,
            bdy,
            ptr,
            first,
            au_depth,
            page_depth,
        ) =~= build_au_page_bounds_from_reads_au_walk_depth(
            reads,
            bdy,
            ptr,
            first,
            au_depth,
            page_depth,
        ));
        if ptr is Some {
            assert(addrs.contains(ptr.unwrap()));
            assert(sub_reads.contains_key(ptr.unwrap()));
            assert(reads.contains_key(ptr.unwrap()));
            assert(sub_reads[ptr.unwrap()] == reads[ptr.unwrap()]);
        }
        assert(CachedJournal::State::load_index(
            pre,
            post,
            sub_lbl,
            au_depth,
            page_depth,
        )) by {
        }
        assert(CachedJournal::State::next_by(
            pre,
            post,
            sub_lbl,
            CachedJournal::Step::load_index(au_depth, page_depth),
        )) by {
            reveal(CachedJournal::State::next_by);
        }
        reveal(CachedJournal::State::next);
    }

    pub proof fn load_index_discovered_aus_in_reads(
        pre: Self,
        post: Self,
        reads: Map<Address, JournalRecord>,
        discovered_aus: Set<AU>,
    )
        requires
            CachedJournal::State::next(
                pre,
                post,
                CachedJournal::Label::LoadIndex{reads, discovered_aus},
            ),
        ensures
            discovered_aus <= to_aus(reads.dom()),
    {
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let lbl = CachedJournal::Label::LoadIndex{reads, discovered_aus};
        let step = choose |step| CachedJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachedJournal::Step::load_index(au_depth, page_depth) => {
                let ptr = pre.snapshot.freshest_rec();
                let bdy = pre.snapshot.boundary_lsn;
                let first = pre.snapshot.first();
                let lsn_au_index = build_lsn_au_index_from_reads_au_walk_depth(
                    reads,
                    bdy,
                    ptr,
                    first,
                    au_depth,
                    page_depth,
                );
                assert(discovered_aus == lsn_au_index.values());
                assert forall |au: AU| #[trigger] discovered_aus.contains(au)
                    implies to_aus(reads.dom()).contains(au) by {
                    build_lsn_au_index_from_reads_au_walk_values_in_reads(
                        reads,
                        bdy,
                        ptr,
                        first,
                        au_depth,
                        page_depth,
                        au,
                    );
                }
            },
            _ => { assert(false); },
        }
    }

    pub proof fn load_index_matches_full(
        pre: Self,
        post: Self,
        reads: Map<Address, JournalRecord>,
        discovered_aus: Set<AU>,
        entries: Map<Address, JournalRecord>,
    )
        requires
            CachedJournal::State::next(
                pre,
                post,
                CachedJournal::Label::LoadIndex{reads, discovered_aus},
            ),
            forall |addr: Address| #[trigger] reads.contains_key(addr)
                && entries.contains_key(addr) ==> reads[addr] == entries[addr],
            (DiskView{boundary_lsn: pre.snapshot.boundary_lsn, entries}).pointer_is_upstream(
                pre.snapshot.freshest_rec(),
                pre.snapshot.first(),
            ),
        ensures
            post.status is Some,
            post.status.unwrap().lsn_au_index =~= (DiskView{
                boundary_lsn: pre.snapshot.boundary_lsn,
                entries,
            }).build_lsn_au_index_au_walk(pre.snapshot.freshest_rec(), pre.snapshot.first()),
            post.status.unwrap().unmarshalled_tail.seq_start == (DiskView{
                boundary_lsn: pre.snapshot.boundary_lsn,
                entries,
            }).seq_end(pre.snapshot.freshest_rec()),
    {
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let lbl = CachedJournal::Label::LoadIndex{reads, discovered_aus};
        let step = choose |step| CachedJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachedJournal::Step::load_index(au_depth, page_depth) => {
                let ptr = pre.snapshot.freshest_rec();
                let bdy = pre.snapshot.boundary_lsn;
                let first = pre.snapshot.first();
                assert(au_walk_reads_cover(reads, bdy, ptr, first, au_depth, page_depth));
                au_walk_reads_cover_build_matches_full_by_value(
                    reads,
                    entries,
                    bdy,
                    ptr,
                    first,
                    au_depth,
                    page_depth,
                );
                let full_dv = DiskView{boundary_lsn: bdy, entries};
                if ptr is Some {
                    let root = ptr.unwrap();
                    assert(reads.contains_key(root));
                    assert(entries.contains_key(root));
                    assert(reads[root] == entries[root]);
                    assert(full_dv.block_in_bounds(ptr));
                    assert(bdy <= entries[root].message_seq.seq_end);
                }
            },
            _ => { assert(false); },
        }
    }

    pub proof fn load_index_matches_loose_full(
        pre: Self,
        post: Self,
        reads: Map<Address, JournalRecord>,
        discovered_aus: Set<AU>,
        entries: Map<Address, JournalRecord>,
    )
        requires
            CachedJournal::State::next(
                pre,
                post,
                CachedJournal::Label::LoadIndex{reads, discovered_aus},
            ),
            forall |addr: Address| #[trigger] reads.contains_key(addr)
                && entries.contains_key(addr) ==> reads[addr] == entries[addr],
            (DiskView{boundary_lsn: pre.snapshot.boundary_lsn, entries}).path_decodable(
                pre.snapshot.freshest_rec(),
            ),
            (DiskView{boundary_lsn: pre.snapshot.boundary_lsn, entries}).path_build_tight(
                pre.snapshot.freshest_rec(),
            ).pointer_is_upstream(pre.snapshot.freshest_rec(), pre.snapshot.first()),
        ensures
            post.status is Some,
            post.status.unwrap().lsn_au_index =~= (DiskView{
                boundary_lsn: pre.snapshot.boundary_lsn,
                entries,
            }).loose_build_lsn_au_index_au_walk(pre.snapshot.freshest_rec(), pre.snapshot.first()),
            post.status.unwrap().unmarshalled_tail.seq_start == (DiskView{
                boundary_lsn: pre.snapshot.boundary_lsn,
                entries,
            }).path_build_tight(pre.snapshot.freshest_rec()).seq_end(pre.snapshot.freshest_rec()),
    {
        let loose_dv = DiskView{boundary_lsn: pre.snapshot.boundary_lsn, entries};
        let tight_dv = loose_dv.path_build_tight(pre.snapshot.freshest_rec());
        loose_dv.path_build_tight_is_sub_disk(pre.snapshot.freshest_rec());
        assert forall |addr: Address| #[trigger] reads.contains_key(addr)
            && tight_dv.entries.contains_key(addr)
            implies reads[addr] == tight_dv.entries[addr] by {
            assert(tight_dv.entries <= entries);
            assert(entries.contains_key(addr));
            assert(tight_dv.entries[addr] == entries[addr]);
        }
        CachedJournal::State::load_index_matches_full(
            pre,
            post,
            reads,
            discovered_aus,
            tight_dv.entries,
        );
        loose_dv.loose_build_lsn_au_index_au_walk_matches_tight(
            pre.snapshot.freshest_rec(),
            pre.snapshot.first(),
        );
        assert(DiskView{
            boundary_lsn: pre.snapshot.boundary_lsn,
            entries: tight_dv.entries,
        } == tight_dv);
        assert_maps_equal!(
            post.status.unwrap().lsn_au_index,
            loose_dv.loose_build_lsn_au_index_au_walk(
                pre.snapshot.freshest_rec(),
                pre.snapshot.first(),
            )
        );
    }

    pub proof fn put_effect(pre: Self, post: Self, messages: MsgHistory)
        requires
            CachedJournal::State::next(pre, post, CachedJournal::Label::Put{messages}),
        ensures
            pre.status is Some,
            post.snapshot == pre.snapshot,
            post.status is Some,
            post.status.unwrap().lsn_au_index == pre.status.unwrap().lsn_au_index,
            post.status.unwrap().au_page_bounds == pre.status.unwrap().au_page_bounds,
            post.status.unwrap().clean_watermark_lsn
                == pre.status.unwrap().clean_watermark_lsn,
            post.status.unwrap().unmarshalled_tail
                == pre.status.unwrap().unmarshalled_tail.concat(messages),
    {
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let lbl = CachedJournal::Label::Put{messages};
        let step = choose |step| CachedJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachedJournal::Step::put() => {},
            _ => { assert(false); },
        }
    }

    pub proof fn observe_clean_aus_effect(pre: Self, post: Self, aus: Set<AU>)
        requires
            CachedJournal::State::next(pre, post, CachedJournal::Label::ObserveCleanAUs{aus}),
        ensures
            pre.status is Some,
            post.snapshot == pre.snapshot,
            post.status is Some,
            post.status.unwrap().lsn_au_index == pre.status.unwrap().lsn_au_index,
            post.status.unwrap().au_page_bounds == pre.status.unwrap().au_page_bounds,
            post.status.unwrap().unmarshalled_tail == pre.status.unwrap().unmarshalled_tail,
            pre.clean_watermark() <= post.clean_watermark(),
    {
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let lbl = CachedJournal::Label::ObserveCleanAUs{aus};
        let step = choose |step| CachedJournal::State::next_by(pre, post, lbl, step);
        match step {
            CachedJournal::Step::advance_watermark(target_lsn) => {
            },
            _ => { assert(false); },
        }
    }
}}

} // end of verus
