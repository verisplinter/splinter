// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::prelude::*;
use vstd::math;
use vstd::map::*;
use vstd::assert_maps_equal;

use verus_state_machines_macros::state_machine;

use crate::abstract_system::MsgHistory_v::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::MiniAllocator_v::*;
use crate::disk::GenericDisk_v::AU;
use crate::disk::GenericDisk_v::*;
use crate::allocation_layer::LikesJournal_v;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::{DiskView, TruncatedJournal};

verus! {

#[verifier::ext_equal]
pub struct JournalMetadata {
    pub boundary_lsn: LSN,
    pub seq_end: LSN,
    pub freshest_rec: Pointer,
    pub first: AU,
}

impl JournalMetadata {
    pub open spec(checked) fn empty() -> Self {
        Self { boundary_lsn: 0, seq_end: 0, freshest_rec: None, first: 0 }
    }

}

#[verifier::ext_equal]
pub struct JournalImage {
    pub tj: TruncatedJournal,
    pub first: AU,
}

impl JournalImage {
    pub open spec(checked) fn wf(self) -> bool {
        self.tight_tj().wf()
    }

    pub open spec(checked) fn accessible_aus(self) -> Set<AU> {
        to_aus(self.tj.disk_view.entries.dom())
    }

    pub open spec fn tight_tj(self) -> TruncatedJournal {
        TruncatedJournal{
            freshest_rec: self.tj.freshest_rec,
            disk_view: self.tj.disk_view.path_build_tight(self.tj.freshest_rec),
        }
    }

    pub open spec(checked) fn empty() -> Self {
        Self { tj: TruncatedJournal::mkfs(), first: 0 }
    }

    pub open spec fn indexed_witnesses_are_tight(self) -> bool {
        let tight = self.tight_tj();
        let tight_index = tight.build_lsn_au_index_from_first(self.first);
        let tight_bounds = tight.disk_view.build_au_page_bounds_au_walk(tight.freshest_rec, self.first);
        forall |addr: Address, lsn: LSN|
            #![trigger self.tj.disk_view.entries.contains_key(addr), tight_index.contains_key(lsn)]
        {
            let record = self.tj.disk_view.entries[addr];
            &&& self.tj.disk_view.entries.contains_key(addr)
            &&& tight_bounds.contains_key(addr.au)
            &&& addr.page <= tight_bounds[addr.au]
            &&& self.tj.seq_start() < record.message_seq.seq_end
            &&& record.message_seq.contains(lsn)
            &&& tight_index.contains_key(lsn)
            &&& tight_index[lsn] == addr.au
        } ==> tight.disk_view.entries.contains_key(addr)
    }

    pub open spec fn bounded_live_entries_are_tight(self) -> bool {
        let tight = self.tight_tj();
        let tight_bounds = tight.disk_view.build_au_page_bounds_au_walk(tight.freshest_rec, self.first);
        forall |addr: Address|
        {
            let record = self.tj.disk_view.entries[addr];
            &&& #[trigger] self.tj.disk_view.entries.contains_key(addr)
            &&& tight_bounds.contains_key(addr.au)
            &&& addr.page <= tight_bounds[addr.au]
            &&& self.tj.seq_start() < record.message_seq.seq_end
        } ==> tight.disk_view.entries.contains_key(addr)
    }

    pub open spec fn au_page_bounds_covered(self) -> bool {
        let tight = self.tight_tj();
        let tight_index = tight.build_lsn_au_index_from_first(self.first);
        let tight_bounds = tight.disk_view.build_au_page_bounds_au_walk(
            tight.freshest_rec,
            self.first,
        );
        forall |addr: Address| {
            &&& #[trigger] tight_index.values().contains(addr.au)
            &&& tight_bounds.contains_key(addr.au)
            &&& addr.page <= tight_bounds[addr.au]
        } ==> self.tj.disk_view.entries.contains_key(addr)
    }

    pub proof fn indexed_au_page_bound_addr_in_disk_image(self, addr: Address)
        requires
            self.valid_image(),
            self.tight_tj().build_lsn_au_index_from_first(self.first).values().contains(addr.au),
            self.tight_tj().disk_view.build_au_page_bounds_au_walk(
                self.tight_tj().freshest_rec,
                self.first,
            ).contains_key(addr.au),
            addr.page <= self.tight_tj().disk_view.build_au_page_bounds_au_walk(
                self.tight_tj().freshest_rec,
                self.first,
            )[addr.au],
        ensures
            self.tj.disk_view.entries.contains_key(addr),
    {
        assert(self.au_page_bounds_covered());
    }

    pub open spec fn valid_image(self) -> bool {
        let tight = self.tight_tj();
        // AU: mini allocator
        &&& self.tj.disk_view.wf_addrs()
        &&& self.tj.disk_view.path_decodable(self.tj.freshest_rec)
        // AU specific
        &&& (self.tj.freshest_rec is None ==> self.first == 0)
        // AU pages are internally linked on the reachable path.
        &&& tight.disk_view.internal_au_pages_fully_linked()
        &&& tight.disk_view.has_unique_lsns()
        &&& tight.freshest_rec is Some ==> tight.disk_view.valid_first_au(self.first)
        &&& {
            let tight_index = tight.build_lsn_au_index_from_first(self.first);
            // AU specific: domain of the image to be bounded by index AU values
            &&& self.tj.disk_view.domain_au_bounded_wrt_index(tight_index)
            &&& tight.disk_view.bounded_inactive_lsns(tight_index, tight.freshest_rec)
        }
        &&& self.bounded_live_entries_are_tight()
        &&& self.au_page_bounds_covered()
    }

    pub proof fn empty_is_valid_image()
        ensures
            Self::empty().valid_image(),
    {
        TruncatedJournal::mkfs_ensures();
        let image = Self::empty();
        let tight = image.tight_tj();
        assert(tight == image.tj);
        let tight_index = tight.build_lsn_au_index_from_first(image.first);
        let ranking = Map::<Address, nat>::empty();
        assert(image.tj.disk_view.path_valid_ranking(image.tj.freshest_rec, ranking));
        assert(image.tj.disk_view.path_decodable(image.tj.freshest_rec));
        assert(tight.decodable());
        reveal(DiskView::pages_allocated_in_lsn_order);

    }

    pub proof fn valid_image_implies_tight_valid_image(self)
        requires
            self.valid_image(),
        ensures
            self.tj.disk_view.path_decodable(self.tj.freshest_rec),
            self.tight_tj().decodable(),
            self.tight_tj().disk_view.wf_addrs(),
            self.tight_tj().disk_view.pointer_is_upstream(self.tight_tj().freshest_rec, self.first),
            ({
                let tight = self.tight_tj();
                tight.disk_view.domain_au_bounded_wrt_index(
                    tight.build_lsn_au_index_from_first(self.first),
                )
            }),
    {
        let loose = self.tj.disk_view;
        let tight = self.tight_tj();
        let tight_index = tight.build_lsn_au_index_from_first(self.first);
        loose.path_build_tight_decodable(self.tj.freshest_rec);
        assert(tight.decodable());
        loose.path_build_tight_is_sub_disk(self.tj.freshest_rec);
        assert(tight.disk_view.is_sub_disk(loose));
        assert(tight.disk_view.wf_addrs()) by {
            assert forall |addr: Address| #[trigger] tight.disk_view.entries.contains_key(addr)
                implies addr.wf() by {
                assert(loose.entries.contains_key(addr));
                assert(loose.wf_addrs());
            }
        }
        assert(tight.disk_view.domain_au_bounded_wrt_index(tight_index)) by {
            assert forall |addr: Address| #[trigger] tight.disk_view.entries.dom().contains(addr)
                implies tight_index.values().contains(addr.au) by {
                assert(loose.entries.contains_key(addr));
                assert(loose.domain_au_bounded_wrt_index(tight_index));
            }
        }
        assert(tight.disk_view.pointer_is_upstream(tight.freshest_rec, self.first));
    }

    pub proof fn valid_image_implies_tight_seq_bounds(self)
        requires
            self.valid_image(),
        ensures
            self.tight_tj().seq_start() == self.tj.seq_start(),
            self.tight_tj().seq_end() == self.tj.seq_end(),
    {
        self.valid_image_implies_tight_valid_image();
        let root = self.tj.freshest_rec;
        let tight = self.tight_tj();
        assert(tight.seq_start() == self.tj.seq_start());
        if root is Some {
            let addr = root.unwrap();
            assert(self.tj.disk_view.path_build_tight(root).entries.contains_key(addr));
            assert(tight.disk_view.entries.contains_key(addr));
            assert(tight.disk_view.entries[addr] == self.tj.disk_view.entries[addr]);
            assert(tight.seq_end() == self.tj.seq_end());
        } else {
            assert(tight.seq_end() == tight.disk_view.boundary_lsn);
            assert(self.tj.seq_end() == self.tj.disk_view.boundary_lsn);
        }
    }

}

pub type LsnAUIndex = Map<LSN, AU>;
pub type AUPageBounds = Map<AU, Page>;

pub open spec fn addrs_in_aus(aus: Set<AU>) -> Set<Address> {
    Set::new(|addr: Address| aus.contains(addr.au))
}

pub open spec fn maps_agree_on<V>(addrs: Set<Address>, left: Map<Address, V>, right: Map<Address, V>) -> bool {
    left.restrict(addrs) == right.restrict(addrs)
}

// Removed (checked) due to lambda being total
pub open spec   /*(checked)*/
fn lsn_au_index_discard_up_to(lsn_au_index: LsnAUIndex, bdy: LSN) -> (out:
    LsnAUIndex)  //     ensures  //         out.len(lsn_au_index),  //         forall |k| out.contains_key(k) :: bdy <= k,  //         forall |k| lsn_au_index.contains_key(k) && bdy <= k ==> out.contains_key(k),
{
    Map::new(|lsn| lsn_au_index.contains_key(lsn) && bdy <= lsn, |lsn| lsn_au_index[lsn])
}

pub proof fn lsn_au_index_discard_up_to_ensures(lsn_au_index: LsnAUIndex, bdy: LSN)
    ensures
        ({
            let out = lsn_au_index_discard_up_to(lsn_au_index, bdy);
            &&& out <= lsn_au_index
            &&& forall|k|
                out.contains_key(k) ==> bdy <= k
                &&& forall|k| lsn_au_index.contains_key(k) && bdy <= k ==> out.contains_key(k)
        }),
{
}

// TODO(jonh): duplicates text in LikesJournal_v. Eww.
pub open spec(checked) fn singleton_index(start_lsn: LSN, end_lsn: LSN, value: AU) -> (index:
    LsnAUIndex) {
    Map::new(|lsn| start_lsn <= lsn < end_lsn, |lsn| value)
}

// Update lsnAUIndex with additional lsn's from a new record
pub open spec(checked) fn lsn_au_index_append_record(
    lsn_au_index: LsnAUIndex,
    msgs: MsgHistory,
    au: AU,
) -> (out: LsnAUIndex)
    recommends
        msgs.wf(),
        msgs.seq_start < msgs.seq_end,  // nonempty history
// ensures LinkedJournal::lsn_disjoint(lsn_au_index.dom(), msgs)
//      ==> out.values() == lsn_au_index.values() + set![au]

{
    // msgs is complete map from seqStart to seqEnd
    let update = singleton_index(msgs.seq_start, msgs.seq_end, au);
    let out = lsn_au_index.union_prefer_right(update);
    // assertion here in dafny original
    out
}

pub proof fn lsn_au_index_append_record_ensures(
    lsn_au_index: LsnAUIndex,
    msgs: MsgHistory,
    au: AU,
)
    requires
        msgs.wf(),
        msgs.seq_start < msgs.seq_end,
    ensures
        LikesJournal_v::lsn_disjoint(lsn_au_index.dom(), msgs.seq_start, msgs.seq_end) ==>
            lsn_au_index_append_record(lsn_au_index, msgs, au).values()
                == lsn_au_index.values() + set![au],
{
    let out = lsn_au_index_append_record(lsn_au_index, msgs, au);
    if LikesJournal_v::lsn_disjoint(lsn_au_index.dom(), msgs.seq_start, msgs.seq_end) {
        let sum = lsn_au_index.values() + set![au];
        assert forall |a| #[trigger] sum.contains(a) implies out.values().contains(a) by {
            if lsn_au_index.values().contains(a) {
                let lsn = choose |lsn| #![auto] lsn_au_index.contains_key(lsn) && lsn_au_index[lsn] == a;
                assert(out.contains_key(lsn));
                assert(out[lsn] == a);
            } else {
                assert(out.contains_key(msgs.seq_start));
                assert(out[msgs.seq_start] == au);
            }
        }
        assert forall |a| #[trigger] out.values().contains(a) implies sum.contains(a) by {
            let lsn = choose |lsn| #![auto] out.contains_key(lsn) && out[lsn] == a;
            let update = singleton_index(msgs.seq_start, msgs.seq_end, au);
            if update.contains_key(lsn) {
                assert(a == au);
            } else {
                assert(lsn_au_index.contains_key(lsn));
                assert(lsn_au_index[lsn] == a);
            }
        }
    }
}

pub open spec(checked) fn contiguous_lsns(
    lsn_au_index: LsnAUIndex,
    lsn1: LSN,
    lsn2: LSN,
    lsn3: LSN,
) -> bool {
    ({
        &&& lsn1 <= lsn2 <= lsn3
        &&& lsn_au_index.contains_key(lsn1)
        &&& lsn_au_index.contains_key(lsn3)
        &&& lsn_au_index[lsn1] == lsn_au_index[lsn3]
    }) ==> {
        &&& lsn_au_index.contains_key(lsn2)
        &&& lsn_au_index[lsn1] == lsn_au_index[lsn2]
    }
}

pub open spec(checked) fn aus_hold_contiguous_lsns(lsn_au_index: LsnAUIndex) -> bool {
    forall|lsn1, lsn2, lsn3| contiguous_lsns(lsn_au_index, lsn1, lsn2, lsn3)
}

pub open spec(checked) fn au_addrs_past_pointer(ptr: Pointer) -> Set<Address> {
    if ptr is None {
        Set::empty()
    } else {
        Set::new(|addr: Address| ptr.unwrap().after_page(addr))
    }
}

impl DiskView {
    pub open spec fn path_valid_ranking(self, root: Pointer, ranking: Ranking) -> bool
        decreases if root is Some && ranking.contains_key(root.unwrap()) {
            ranking[root.unwrap()] + 1
        } else {
            0
        }
    {
        match root {
            None => true,
            Some(addr) => {
                if !self.entries.contains_key(addr) || !ranking.contains_key(addr) {
                    false
                } else {
                    let record = self.entries[addr];
                    let next = record.cropped_prior(self.boundary_lsn);
                    &&& record.wf()
                    &&& self.boundary_lsn < record.message_seq.seq_end
                    &&& record.has_link(self.boundary_lsn)
                    &&& next is Some ==> {
                        let next_addr = next.unwrap();
                        &&& self.entries.contains_key(next_addr)
                        &&& self.entries[next_addr].wf()
                        &&& self.entries[next_addr].message_seq.can_concat(record.message_seq)
                        &&& ranking.contains_key(next_addr)
                        &&& ranking[next_addr] < ranking[addr]
                    }
                    &&& self.path_valid_ranking(next, ranking)
                }
            },
        }
    }

    pub proof fn path_valid_ranking_equation(self, root: Pointer, ranking: Ranking)
        ensures
            self.path_valid_ranking(root, ranking) == match root {
                None => true,
                Some(addr) => {
                    if !self.entries.contains_key(addr) || !ranking.contains_key(addr) {
                        false
                    } else {
                        let record = self.entries[addr];
                        let next = record.cropped_prior(self.boundary_lsn);
                        &&& record.wf()
                        &&& self.boundary_lsn < record.message_seq.seq_end
                        &&& record.has_link(self.boundary_lsn)
                        &&& next is Some ==> {
                            let next_addr = next.unwrap();
                            &&& self.entries.contains_key(next_addr)
                            &&& self.entries[next_addr].wf()
                            &&& self.entries[next_addr].message_seq.can_concat(record.message_seq)
                            &&& ranking.contains_key(next_addr)
                            &&& ranking[next_addr] < ranking[addr]
                        }
                        &&& self.path_valid_ranking(next, ranking)
                    }
                },
            },
    {
    }

    pub open spec fn path_decodable(self, root: Pointer) -> bool
    {
        exists |ranking: Ranking| self.path_valid_ranking(root, ranking)
    }

    pub open spec fn path_build_tight_with_ranking(self, root: Pointer, ranking: Ranking) -> DiskView
        recommends
            self.path_valid_ranking(root, ranking),
        decreases if root is Some && ranking.contains_key(root.unwrap()) {
            ranking[root.unwrap()] + 1
        } else {
            0
        }
    {
        decreases_when(self.path_valid_ranking(root, ranking));
        decreases_by(Self::path_build_tight_with_ranking_decreases);
        match root {
            None => DiskView{boundary_lsn: self.boundary_lsn, entries: Map::empty()},
            Some(addr) => {
                let record = self.entries[addr];
                let tail = self.path_build_tight_with_ranking(record.cropped_prior(self.boundary_lsn), ranking);
                DiskView{
                    boundary_lsn: self.boundary_lsn,
                    entries: tail.entries.insert(addr, record),
                }
            },
        }
    }

    #[verifier(decreases_by)]
    pub proof fn path_build_tight_with_ranking_decreases(self, root: Pointer, ranking: Ranking) {
        match root {
            None => {},
            Some(addr) => {
                assert(self.entries.contains_key(addr));
                assert(ranking.contains_key(addr));
                let next = self.entries[addr].cropped_prior(self.boundary_lsn);
                if next is Some {
                    assert(ranking.contains_key(next.unwrap()));
                    assert(ranking[next.unwrap()] < ranking[addr]);
                }
            },
        }
    }

    pub open spec fn path_build_tight(self, root: Pointer) -> DiskView
        recommends
            self.path_decodable(root),
    {
        if self.path_decodable(root) {
            let ranking = choose |ranking: Ranking| self.path_valid_ranking(root, ranking);
            self.path_build_tight_with_ranking(root, ranking)
        } else {
            DiskView{boundary_lsn: self.boundary_lsn, entries: Map::empty()}
        }
    }

    pub proof fn path_build_tight_with_ranking_is_sub_disk(self, root: Pointer, ranking: Ranking)
        requires
            self.path_valid_ranking(root, ranking),
        ensures
            self.path_build_tight_with_ranking(root, ranking).is_sub_disk(self),
        decreases if root is Some && ranking.contains_key(root.unwrap()) {
            ranking[root.unwrap()] + 1
        } else {
            0
        }
    {
        match root {
            None => {},
            Some(addr) => {
                let next = self.entries[addr].cropped_prior(self.boundary_lsn);
                self.path_build_tight_with_ranking_is_sub_disk(next, ranking);
                let tight = self.path_build_tight_with_ranking(root, ranking);
                let tail = self.path_build_tight_with_ranking(next, ranking);
                assert(tail.entries <= self.entries);
                assert(tight.entries <= self.entries) by {
                    assert forall |a: Address| #[trigger] tight.entries.contains_key(a)
                        implies self.entries.contains_key(a) && tight.entries[a] == self.entries[a] by {
                        if a == addr {
                        } else {
                            assert(tail.entries.contains_key(a));
                        }
                    }
                }
            },
        }
    }

    pub proof fn path_build_tight_with_ranking_irrelevant(
        self,
        root: Pointer,
        ranking1: Ranking,
        ranking2: Ranking,
    )
        requires
            self.path_valid_ranking(root, ranking1),
            self.path_valid_ranking(root, ranking2),
        ensures
            self.path_build_tight_with_ranking(root, ranking1)
                == self.path_build_tight_with_ranking(root, ranking2),
        decreases if root is Some && ranking1.contains_key(root.unwrap()) {
            ranking1[root.unwrap()] + 1
        } else {
            0
        },
    {
        match root {
            None => {},
            Some(addr) => {
                let record = self.entries[addr];
                let next = record.cropped_prior(self.boundary_lsn);
                self.path_build_tight_with_ranking_irrelevant(next, ranking1, ranking2);
                let tight1 = self.path_build_tight_with_ranking(root, ranking1);
                let tight2 = self.path_build_tight_with_ranking(root, ranking2);
                let tail1 = self.path_build_tight_with_ranking(next, ranking1);
                let tail2 = self.path_build_tight_with_ranking(next, ranking2);
                assert(tail1 == tail2);
                assert_maps_equal!(
                    tight1.entries,
                    tight2.entries,
                    a => {
                        if tight1.entries.contains_key(a) {
                            if a != addr {
                                assert(tail1.entries.contains_key(a));
                                assert(tail2.entries.contains_key(a));
                            }
                        }
                        if tight2.entries.contains_key(a) {
                            if a != addr {
                                assert(tail2.entries.contains_key(a));
                                assert(tail1.entries.contains_key(a));
                            }
                        }
                    }
                );
            },
        }
    }

    pub proof fn path_build_tight_uses_ranking(self, root: Pointer, ranking: Ranking)
        requires
            self.path_valid_ranking(root, ranking),
        ensures
            self.path_build_tight(root) == self.path_build_tight_with_ranking(root, ranking),
    {
        let chosen = choose |chosen: Ranking| self.path_valid_ranking(root, chosen);
        self.path_build_tight_with_ranking_irrelevant(root, chosen, ranking);
    }

    pub proof fn path_build_tight_none_empty(self)
        ensures
            self.path_build_tight(None).entries =~= Map::<Address, LinkedJournal_v::JournalRecord>::empty(),
    {
        let ranking = choose |ranking: Ranking| self.path_valid_ranking(None, ranking);
        self.path_build_tight_uses_ranking(None, ranking);
        assert_maps_equal!(
            self.path_build_tight(None).entries,
            Map::<Address, LinkedJournal_v::JournalRecord>::empty()
        );
    }

    pub proof fn path_build_tight_is_sub_disk(self, root: Pointer)
        requires
            self.path_decodable(root),
        ensures
            self.path_build_tight(root).is_sub_disk(self),
    {
        let ranking = choose |ranking: Ranking| self.path_valid_ranking(root, ranking);
        self.path_build_tight_with_ranking_is_sub_disk(root, ranking);
        self.path_build_tight_uses_ranking(root, ranking);
    }

    pub proof fn path_build_tight_with_ranking_entry_rank_le(
        self,
        root: Pointer,
        ranking: Ranking,
        addr: Address,
    )
        requires
            self.path_valid_ranking(root, ranking),
            root is Some,
            self.path_build_tight_with_ranking(root, ranking).entries.contains_key(addr),
        ensures
            ranking.contains_key(addr),
            ranking[addr] <= ranking[root.unwrap()],
        decreases if root is Some && ranking.contains_key(root.unwrap()) {
            ranking[root.unwrap()] + 1
        } else {
            0
        },
    {
        let root_addr = root.unwrap();
        if addr == root_addr {
            assert(ranking.contains_key(addr));
        } else {
            let record = self.entries[root_addr];
            let next = record.cropped_prior(self.boundary_lsn);
            let tail = self.path_build_tight_with_ranking(next, ranking);
            assert(tail.entries.contains_key(addr));
            assert(next is Some);
            self.path_build_tight_with_ranking_entry_rank_le(next, ranking, addr);
            assert(ranking[addr] <= ranking[next.unwrap()]);
            assert(ranking[next.unwrap()] < ranking[root_addr]);
        }
    }

    pub proof fn path_build_tight_with_ranking_extends_same(
        self,
        big: DiskView,
        root: Pointer,
        ranking: Ranking,
    )
        requires
            self.path_valid_ranking(root, ranking),
            self.boundary_lsn == big.boundary_lsn,
            self.entries <= big.entries,
        ensures
            big.path_build_tight_with_ranking(root, ranking)
                == self.path_build_tight_with_ranking(root, ranking),
        decreases if root is Some && ranking.contains_key(root.unwrap()) {
            ranking[root.unwrap()] + 1
        } else {
            0
        },
    {
        assert(self.is_sub_disk(big));
        big.path_valid_ranking_lifts_from_sub_disk(self, root, ranking);
        assert(big.path_valid_ranking(root, ranking));
        match root {
            None => {},
            Some(addr) => {
                assert(self.entries.contains_key(addr));
                assert(big.entries.contains_key(addr));
                assert(big.entries[addr] == self.entries[addr]);
                let record = self.entries[addr];
                let next = record.cropped_prior(self.boundary_lsn);
                assert(big.entries[addr].cropped_prior(big.boundary_lsn) == next);
                self.path_build_tight_with_ranking_extends_same(big, next, ranking);
                let self_tail = self.path_build_tight_with_ranking(next, ranking);
                let big_tail = big.path_build_tight_with_ranking(next, ranking);
                assert(self_tail == big_tail);
                assert_maps_equal!(
                    self.path_build_tight_with_ranking(root, ranking).entries,
                    self_tail.entries.insert(addr, record)
                );
                assert_maps_equal!(
                    big.path_build_tight_with_ranking(root, ranking).entries,
                    big_tail.entries.insert(addr, record)
                );
                assert_maps_equal!(
                    big.path_build_tight_with_ranking(root, ranking).entries,
                    self.path_build_tight_with_ranking(root, ranking).entries,
                    a => {
                        if big.path_build_tight_with_ranking(root, ranking).entries.contains_key(a) {
                            if a != addr {
                                assert(big_tail.entries.insert(addr, record).contains_key(a));
                                assert(big_tail.entries.contains_key(a));
                                assert(self_tail.entries.contains_key(a));
                            }
                        }
                        if self.path_build_tight_with_ranking(root, ranking).entries.contains_key(a) {
                            if a != addr {
                                assert(self_tail.entries.insert(addr, record).contains_key(a));
                                assert(self_tail.entries.contains_key(a));
                                assert(big_tail.entries.contains_key(a));
                            }
                        }
                    }
                );
            },
        }
    }

    pub proof fn path_build_tight_extends_same(
        self,
        big: DiskView,
        root: Pointer,
    )
        requires
            self.path_decodable(root),
            self.boundary_lsn == big.boundary_lsn,
            self.entries <= big.entries,
        ensures
            big.path_build_tight(root) == self.path_build_tight(root),
    {
        let ranking = choose |ranking: Ranking| self.path_valid_ranking(root, ranking);
        assert(self.is_sub_disk(big));
        big.path_valid_ranking_lifts_from_sub_disk(self, root, ranking);
        self.path_build_tight_with_ranking_extends_same(big, root, ranking);
        self.path_build_tight_uses_ranking(root, ranking);
        big.path_build_tight_uses_ranking(root, ranking);
    }

    pub proof fn path_build_tight_with_ranking_preserves_path_valid_ranking(
        self,
        root: Pointer,
        ranking: Ranking,
    )
        requires
            self.path_valid_ranking(root, ranking),
        ensures
            self.path_build_tight_with_ranking(root, ranking).path_valid_ranking(root, ranking),
        decreases if root is Some && ranking.contains_key(root.unwrap()) {
            ranking[root.unwrap()] + 1
        } else {
            0
        },
    {
        match root {
            None => {},
            Some(addr) => {
                let record = self.entries[addr];
                let next = record.cropped_prior(self.boundary_lsn);
                self.path_build_tight_with_ranking_preserves_path_valid_ranking(next, ranking);
                let tight = self.path_build_tight_with_ranking(root, ranking);
                let tail = self.path_build_tight_with_ranking(next, ranking);
                if next is Some {
                    assert(tail.is_sub_disk(tight)) by {
                        assert(tail.boundary_lsn == tight.boundary_lsn);
                        assert(tail.entries <= tight.entries) by {
                            assert forall |a: Address| #[trigger] tail.entries.contains_key(a)
                                implies tight.entries.contains_key(a)
                                    && tight.entries[a] == tail.entries[a] by {
                                if a == addr {
                                    self.path_build_tight_with_ranking_entry_rank_le(next, ranking, a);
                                    assert(ranking[a] <= ranking[next.unwrap()]);
                                    assert(ranking[next.unwrap()] < ranking[addr]);
                                    assert(false);
                                }
                            }
                        }
                    }
                    tight.path_valid_ranking_lifts_from_sub_disk(tail, next, ranking);
                    assert(tail.entries.contains_key(next.unwrap()));
                    assert(tight.entries.contains_key(next.unwrap()));
                    assert(tight.entries[next.unwrap()] == tail.entries[next.unwrap()]);
                    assert(tight.path_valid_ranking(next, ranking));
                }

                tight.path_valid_ranking_equation(root, ranking);
                assert(tight.path_valid_ranking(root, ranking));
            },
        }
    }

    pub proof fn path_build_tight_path_decodable(self, root: Pointer)
        requires
            self.path_decodable(root),
        ensures
            self.path_build_tight(root).path_decodable(root),
    {
        let ranking = choose |ranking: Ranking| self.path_valid_ranking(root, ranking);
        self.path_build_tight_with_ranking_preserves_path_valid_ranking(root, ranking);
        self.path_build_tight_uses_ranking(root, ranking);
        assert(self.path_build_tight(root).path_valid_ranking(root, ranking));
    }

    pub proof fn path_build_tight_with_ranking_decodable(
        self,
        root: Pointer,
        ranking: Ranking,
    )
        requires
            self.path_valid_ranking(root, ranking),
        ensures
            ({
                let tight = self.path_build_tight_with_ranking(root, ranking);
                &&& tight.wf()
                &&& tight.is_nondangling_pointer(root)
                &&& tight.block_in_bounds(root)
                &&& tight.valid_ranking(ranking)
                &&& tight.acyclic()
                &&& (TruncatedJournal{freshest_rec: root, disk_view: tight}).decodable()
            }),
        decreases if root is Some && ranking.contains_key(root.unwrap()) {
            ranking[root.unwrap()] + 1
        } else {
            0
        },
    {
        match root {
            None => {
                let tight = self.path_build_tight_with_ranking(root, ranking);
                assert(tight.entries =~= Map::<Address, LinkedJournal_v::JournalRecord>::empty());
                assert(tight.entries_wf());
                assert(tight.nondangling_pointers());
                assert(tight.blocks_can_concat());
                assert(tight.blocks_each_have_link());
                assert(tight.wf());
                assert(tight.valid_ranking(ranking));
                assert(tight.acyclic());
                assert((TruncatedJournal{freshest_rec: root, disk_view: tight}).decodable());
            },
            Some(addr) => {
                let record = self.entries[addr];
                let next = record.cropped_prior(self.boundary_lsn);
                self.path_build_tight_with_ranking_decodable(next, ranking);
                let tail = self.path_build_tight_with_ranking(next, ranking);
                let tight = self.path_build_tight_with_ranking(root, ranking);

                assert(tail.wf());
                assert(tail.valid_ranking(ranking));
                assert(tail.is_nondangling_pointer(next));
                assert(tail.block_in_bounds(next));
                assert(tail.acyclic());
                assert(tight.entries == tail.entries.insert(addr, record));
                assert(!tail.entries.contains_key(addr)) by {
                    if tail.entries.contains_key(addr) {
                        if next is None {
                            assert(tail.entries =~= Map::<Address, LinkedJournal_v::JournalRecord>::empty());
                            assert(false);
                        } else {
                            self.path_build_tight_with_ranking_entry_rank_le(next, ranking, addr);
                            assert(ranking[addr] <= ranking[next.unwrap()]);
                            assert(ranking[next.unwrap()] < ranking[addr]);
                            assert(false);
                        }
                    }
                }

                assert(tight.entries_wf()) by {
                    assert forall |a: Address| #[trigger] tight.entries.contains_key(a)
                        implies tight.entries[a].wf() by {
                        if a == addr {
                            assert(record.wf());
                        } else {
                            assert(tail.entries.contains_key(a));
                            assert(tight.entries[a] == tail.entries[a]);
                        }
                    }
                }
                assert(tight.nondangling_pointers()) by {
                    assert forall |a: Address| #[trigger] tight.entries.contains_key(a)
                        implies tight.is_nondangling_pointer(tight.entries[a].cropped_prior(tight.boundary_lsn)) by {
                        if a == addr {
                            assert(tight.entries[a] == record);
                            assert(tight.boundary_lsn == self.boundary_lsn);
                            if next is Some {
                                assert(tail.entries.contains_key(next.unwrap()));
                                assert(tight.entries.contains_key(next.unwrap()));
                            }
                        } else {
                            assert(tail.entries.contains_key(a));
                            assert(tight.entries[a] == tail.entries[a]);
                            let prior = tail.entries[a].cropped_prior(tail.boundary_lsn);
                            assert(tail.is_nondangling_pointer(prior));
                            if prior is Some {
                                assert(tail.entries.contains_key(prior.unwrap()));
                                assert(tight.entries.contains_key(prior.unwrap()));
                            }
                        }
                    }
                }
                assert(tight.blocks_can_concat()) by {
                    assert forall |a: Address| #[trigger] tight.entries.contains_key(a)
                        implies tight.this_block_can_concat(a) by {
                        if a == addr {
                            assert(tight.entries[a] == record);
                            assert(tight.boundary_lsn == self.boundary_lsn);
                            if next is Some {
                                assert(tight.entries.contains_key(next.unwrap()));
                                assert(tight.entries[next.unwrap()] == tail.entries[next.unwrap()]);
                                assert(tail.entries[next.unwrap()] == self.entries[next.unwrap()]);
                            }
                        } else {
                            assert(tail.entries.contains_key(a));
                            assert(tight.entries[a] == tail.entries[a]);
                            let prior = tail.entries[a].cropped_prior(tail.boundary_lsn);
                            assert(tail.this_block_can_concat(a));
                            if prior is Some {
                                assert(tail.entries.contains_key(prior.unwrap()));
                                assert(prior.unwrap() != addr);
                                assert(tight.entries.contains_key(prior.unwrap()));
                                assert(tight.entries[prior.unwrap()] == tail.entries[prior.unwrap()]);
                            }
                        }
                    }
                }
                assert(tight.blocks_each_have_link()) by {
                    assert forall |a: Address| #[trigger] tight.entries.contains_key(a)
                        implies tight.entries[a].has_link(tight.boundary_lsn) by {
                        if a == addr {
                            assert(tight.entries[a] == record);
                            assert(tight.boundary_lsn == self.boundary_lsn);
                        } else {
                            assert(tail.entries.contains_key(a));
                            assert(tight.entries[a] == tail.entries[a]);
                            assert(tail.entries[a].has_link(tail.boundary_lsn));
                            assert(tail.boundary_lsn == tight.boundary_lsn);
                        }
                    }
                }
                assert(tight.wf());

                assert(tight.is_nondangling_pointer(root));
                assert(tight.block_in_bounds(root)) by {
                    assert(tight.entries.contains_key(addr));
                    assert(tight.entries[addr] == record);
                    assert(tight.boundary_lsn == self.boundary_lsn);
                }

                assert(tight.valid_ranking(ranking)) by {
                    assert(tight.entries.dom().subset_of(ranking.dom())) by {
                        assert forall |a: Address| #[trigger] tight.entries.dom().contains(a)
                            implies ranking.dom().contains(a) by {
                            self.path_build_tight_with_ranking_entry_rank_le(root, ranking, a);
                            assert(ranking.contains_key(a));
                        }
                    }
                    assert forall |a: Address| #[trigger] tight.entries.contains_key(a)
                        && tight.entries[a].cropped_prior(tight.boundary_lsn) is Some
                        implies ranking[tight.entries[a].cropped_prior(tight.boundary_lsn).unwrap()]
                            < ranking[a] by {
                        if a == addr {
                            assert(tight.entries[a] == record);
                            assert(tight.boundary_lsn == self.boundary_lsn);
                        } else {
                            assert(tail.entries.contains_key(a));
                            assert(tight.entries[a] == tail.entries[a]);
                            let prior = tail.entries[a].cropped_prior(tail.boundary_lsn);
                            assert(prior == tight.entries[a].cropped_prior(tight.boundary_lsn));
                            assert(tail.valid_ranking(ranking));
                        }
                    }
                }
                assert(tight.acyclic());
                assert((TruncatedJournal{freshest_rec: root, disk_view: tight}).decodable());
            },
        }
    }

    pub proof fn path_build_tight_decodable(self, root: Pointer)
        requires
            self.path_decodable(root),
        ensures
            ({
                let tight = self.path_build_tight(root);
                &&& tight.wf()
                &&& tight.is_nondangling_pointer(root)
                &&& tight.block_in_bounds(root)
                &&& tight.acyclic()
                &&& (TruncatedJournal{freshest_rec: root, disk_view: tight}).decodable()
            }),
    {
        let ranking = choose |ranking: Ranking| self.path_valid_ranking(root, ranking);
        self.path_build_tight_with_ranking_decodable(root, ranking);
        self.path_build_tight_uses_ranking(root, ranking);
    }

    pub proof fn path_build_tight_with_ranking_idempotent(
        self,
        root: Pointer,
        ranking: Ranking,
    )
        requires
            self.path_valid_ranking(root, ranking),
        ensures
            ({
                let tight = self.path_build_tight_with_ranking(root, ranking);
                tight.path_build_tight_with_ranking(root, ranking) == tight
            }),
        decreases if root is Some && ranking.contains_key(root.unwrap()) {
            ranking[root.unwrap()] + 1
        } else {
            0
        },
    {
        match root {
            None => {},
            Some(addr) => {
                let record = self.entries[addr];
                let next = record.cropped_prior(self.boundary_lsn);
                self.path_build_tight_with_ranking_idempotent(next, ranking);
                self.path_build_tight_with_ranking_preserves_path_valid_ranking(next, ranking);
                let tight = self.path_build_tight_with_ranking(root, ranking);
                let tail = self.path_build_tight_with_ranking(next, ranking);
                self.path_build_tight_with_ranking_preserves_path_valid_ranking(root, ranking);
                assert(tight.path_valid_ranking(root, ranking));
                if next is Some {
                    assert(tail.is_sub_disk(tight)) by {
                        assert(tail.boundary_lsn == tight.boundary_lsn);
                        assert(tail.entries <= tight.entries) by {
                            assert forall |a: Address| #[trigger] tail.entries.contains_key(a)
                                implies tight.entries.contains_key(a)
                                    && tight.entries[a] == tail.entries[a] by {
                                if a == addr {
                                    self.path_build_tight_with_ranking_entry_rank_le(next, ranking, a);
                                    assert(ranking[a] <= ranking[next.unwrap()]);
                                    assert(ranking[next.unwrap()] < ranking[addr]);
                                    assert(false);
                                }
                            }
                        }
                    }
                    tail.path_build_tight_with_ranking_extends_same(tight, next, ranking);
                    assert(tight.path_build_tight_with_ranking(next, ranking) == tail);
                }
                assert(tight.entries[addr] == record);
                assert(tight.entries[addr].cropped_prior(tight.boundary_lsn) == next);
                let tight_tail = tight.path_build_tight_with_ranking(next, ranking);
                assert(tight_tail == tail);
                assert_maps_equal!(
                    tight.path_build_tight_with_ranking(root, ranking).entries,
                    tight_tail.entries.insert(addr, record)
                );
                assert_maps_equal!(
                    tight.entries,
                    tail.entries.insert(addr, record)
                );
                assert_maps_equal!(
                    tight.path_build_tight_with_ranking(root, ranking).entries,
                    tight.entries,
                    a => {
                        if tight.path_build_tight_with_ranking(root, ranking).entries.contains_key(a) {
                            if a != addr {
                                assert(tight_tail.entries.insert(addr, record).contains_key(a));
                                assert(tight.path_build_tight_with_ranking(next, ranking).entries.contains_key(a));
                                assert(tail.entries.contains_key(a));
                            }
                        }
                        if tight.entries.contains_key(a) {
                            if a != addr {
                                assert(tail.entries.insert(addr, record).contains_key(a));
                                assert(tail.entries.contains_key(a));
                                assert(tight.path_build_tight_with_ranking(next, ranking).entries.contains_key(a));
                            }
                        }
                    }
                );
            },
        }
    }

    pub proof fn path_build_tight_idempotent(self, root: Pointer)
        requires
            self.path_decodable(root),
        ensures
            self.path_build_tight(root).path_build_tight(root) == self.path_build_tight(root),
    {
        let tight = self.path_build_tight(root);
        let ranking = choose |ranking: Ranking| self.path_valid_ranking(root, ranking);
        self.path_build_tight_uses_ranking(root, ranking);
        self.path_build_tight_with_ranking_preserves_path_valid_ranking(root, ranking);
        self.path_build_tight_with_ranking_idempotent(root, ranking);
        tight.path_build_tight_uses_ranking(root, ranking);
        assert(tight.path_build_tight(root) == tight.path_build_tight_with_ranking(root, ranking));
        assert(tight.path_build_tight(root) == tight);
    }

    pub proof fn path_build_tight_preserved_in_superdisk(self, big: DiskView, root: Pointer)
        requires
            self.path_decodable(root),
            self.path_build_tight(root) == self,
            self.is_sub_disk(big),
        ensures
            big.path_decodable(root),
            big.path_build_tight(root) == self,
    {
        let ranking = choose |ranking: Ranking| self.path_valid_ranking(root, ranking);
        big.path_valid_ranking_lifts_from_sub_disk(self, root, ranking);
        assert(big.path_valid_ranking(root, ranking));
        assert(big.path_decodable(root));
        self.path_build_tight_extends_same(big, root);
        assert(big.path_build_tight(root) == self.path_build_tight(root));
        assert(big.path_build_tight(root) == self);
    }

    pub proof fn path_build_tight_prepend_record(
        self,
        big: DiskView,
        root: Pointer,
        new_addr: Address,
        new_record: LinkedJournal_v::JournalRecord,
    )
        requires
            self.path_decodable(root),
            self.path_build_tight(root) == self,
            self.boundary_lsn == big.boundary_lsn,
            self.entries <= big.entries,
            big.path_decodable(Some(new_addr)),
            big.entries.contains_key(new_addr),
            big.entries[new_addr] == new_record,
            new_record.cropped_prior(self.boundary_lsn) == root,
            !self.entries.contains_key(new_addr),
        ensures
            big.path_build_tight(Some(new_addr)).entries
                =~= self.entries.insert(new_addr, new_record),
    {
        self.path_build_tight_extends_same(big, root);
        assert(big.path_build_tight(root) == self);

        let ranking = choose |ranking: Ranking| big.path_valid_ranking(Some(new_addr), ranking);

        assert(big.path_valid_ranking(root, ranking));
        big.path_build_tight_uses_ranking(Some(new_addr), ranking);
        big.path_build_tight_uses_ranking(root, ranking);

        let tail = big.path_build_tight_with_ranking(root, ranking);
        assert(tail == self);
        assert(big.entries[new_addr].cropped_prior(big.boundary_lsn) == root);
        assert_maps_equal!(
            big.path_build_tight(Some(new_addr)).entries,
            self.entries.insert(new_addr, new_record),
            addr => {
                if big.path_build_tight(Some(new_addr)).entries.contains_key(addr) {
                    if addr == new_addr {
                    } else {
                        assert(tail.entries.contains_key(addr));
                        assert(self.entries.contains_key(addr));
                    }
                }
                if self.entries.insert(new_addr, new_record).contains_key(addr) {
                    if addr == new_addr {
                        assert(big.path_build_tight(Some(new_addr)).entries.contains_key(addr));
                    } else {
                        assert(self.entries.contains_key(addr));
                        assert(tail.entries.contains_key(addr));
                        assert(big.path_build_tight(Some(new_addr)).entries.contains_key(addr));
                    }
                }
            }
        );
    }

    pub proof fn path_build_tight_with_ranking_equals_build_tight(
        self,
        root: Pointer,
        ranking: Ranking,
    )
        requires
            self.decodable(root),
            self.acyclic(),
            self.block_in_bounds(root),
            self.path_valid_ranking(root, ranking),
        ensures
            self.path_build_tight_with_ranking(root, ranking) == self.build_tight(root),
        decreases self.the_rank_of(root),
    {
        if root is None {
        } else {
            let addr = root.unwrap();
            let next = self.entries[addr].cropped_prior(self.boundary_lsn);
            assert(self.decodable(next)) by {
                assert(self.wf());
                assert(self.nondangling_pointers());
            }
            assert(self.block_in_bounds(next)) by {
                let record = self.entries[addr];
                assert(record.has_link(self.boundary_lsn));
                assert(self.this_block_can_concat(addr));
                if next is Some {
                    assert(self.entries[next.unwrap()].message_seq.can_concat(record.message_seq));
                    assert(self.entries[next.unwrap()].message_seq.seq_end == record.message_seq.seq_start);
                    assert(self.boundary_lsn < record.message_seq.seq_start);
                }
            }
            self.path_build_tight_with_ranking_equals_build_tight(next, ranking);
            self.build_tight_shape(root);
            assert_maps_equal!(
                self.path_build_tight_with_ranking(root, ranking).entries,
                self.build_tight(root).entries,
                a => {
                    if self.path_build_tight_with_ranking(root, ranking).entries.contains_key(a) {
                        if a != addr {
                            assert(self.path_build_tight_with_ranking(next, ranking).entries.contains_key(a));
                            assert(self.build_tight(next).entries.contains_key(a));
                        }
                    }
                    if self.build_tight(root).entries.contains_key(a) {
                        if a != addr {
                            assert(self.build_tight(next).entries.contains_key(a));
                            assert(self.path_build_tight_with_ranking(next, ranking).entries.contains_key(a));
                        }
                    }
                }
            );
        }
    }

    pub proof fn path_build_tight_equals_build_tight(self, root: Pointer)
        requires
            self.decodable(root),
            self.acyclic(),
            self.block_in_bounds(root),
        ensures
            self.path_build_tight(root) == self.build_tight(root),
    {
        self.decodable_implies_path_decodable(root);
        let ranking = choose |ranking: Ranking| self.path_valid_ranking(root, ranking);
        self.path_build_tight_with_ranking_equals_build_tight(root, ranking);
        self.path_build_tight_uses_ranking(root, ranking);
    }

    pub proof fn path_valid_ranking_from_decodable(self, root: Pointer, ranking: Ranking)
        requires
            self.decodable(root),
            self.acyclic(),
            self.block_in_bounds(root),
            self.valid_ranking(ranking),
        ensures
            self.path_valid_ranking(root, ranking),
        decreases if root is Some && ranking.contains_key(root.unwrap()) {
            ranking[root.unwrap()] + 1
        } else {
            0
        },
    {
        match root {
            None => {},
            Some(addr) => {
                let record = self.entries[addr];
                let next = record.cropped_prior(self.boundary_lsn);
                assert(self.entries.contains_key(addr));
                assert(ranking.contains_key(addr));
                assert(record.wf());
                assert(record.has_link(self.boundary_lsn));
                assert(self.boundary_lsn < record.message_seq.seq_end) by {
                    assert(self.block_in_bounds(root));
                }
                if next is Some {
                    let next_addr = next.unwrap();
                    assert(self.entries.contains_key(next_addr));
                    assert(self.entries[next_addr].wf());
                    assert(self.entries[next_addr].message_seq.can_concat(record.message_seq));
                    assert(ranking.contains_key(next_addr));
                    assert(ranking[next_addr] < ranking[addr]);
                    assert(self.decodable(next)) by {
                        assert(self.wf());
                        assert(self.nondangling_pointers());
                    }
                    assert(self.block_in_bounds(next)) by {
                        assert(record.has_link(self.boundary_lsn));
                        assert(self.this_block_can_concat(addr));
                        assert(self.entries[next_addr].message_seq.can_concat(record.message_seq));
                        assert(self.entries[next_addr].message_seq.seq_end == record.message_seq.seq_start);
                        assert(self.boundary_lsn < record.message_seq.seq_start);
                    }
                    self.path_valid_ranking_from_decodable(next, ranking);
                    assert(self.path_valid_ranking(next, ranking));
                }

                self.path_valid_ranking_equation(root, ranking);
                assert(self.path_valid_ranking(root, ranking));
            },
        }
    }

    pub proof fn decodable_implies_path_decodable(self, root: Pointer)
        requires
            self.decodable(root),
            self.acyclic(),
            self.block_in_bounds(root),
        ensures
            self.path_decodable(root),
    {
        let ranking = self.the_ranking();
        self.path_valid_ranking_from_decodable(root, ranking);
        assert(self.path_valid_ranking(root, ranking));
    }

    pub proof fn path_valid_ranking_lifts_from_sub_disk(self, sub: DiskView, root: Pointer, ranking: Ranking)
        requires
            sub.path_valid_ranking(root, ranking),
            sub.is_sub_disk(self),
        ensures
            self.path_valid_ranking(root, ranking),
        decreases if root is Some && ranking.contains_key(root.unwrap()) {
            ranking[root.unwrap()] + 1
        } else {
            0
        },
    {
        match root {
            None => {},
            Some(addr) => {
                let record = sub.entries[addr];
                let next = record.cropped_prior(sub.boundary_lsn);
                assert(sub.entries.contains_key(addr));
                assert(self.entries.contains_key(addr));
                assert(self.entries[addr] == record);
                assert(self.boundary_lsn == sub.boundary_lsn);
                if next is Some {
                    let next_addr = next.unwrap();
                    assert(sub.entries.contains_key(next_addr));
                    assert(self.entries.contains_key(next_addr));
                    assert(self.entries[next_addr] == sub.entries[next_addr]);
                    self.path_valid_ranking_lifts_from_sub_disk(sub, next, ranking);
                    assert(self.path_valid_ranking(next, ranking));
                }

                self.path_valid_ranking_equation(root, ranking);
                assert(self.path_valid_ranking(root, ranking));
            },
        }
    }

    pub proof fn sub_disk_decodable_implies_path_decodable(self, sub: DiskView, root: Pointer)
        requires
            sub.decodable(root),
            sub.acyclic(),
            sub.block_in_bounds(root),
            sub.is_sub_disk(self),
        ensures
            self.path_decodable(root),
    {
        let ranking = sub.the_ranking();
        sub.path_valid_ranking_from_decodable(root, ranking);
        self.path_valid_ranking_lifts_from_sub_disk(sub, root, ranking);
        assert(self.path_valid_ranking(root, ranking));
    }

    pub proof fn decodable_sub_disk_path_build_tight_matches_build_tight(
        self,
        sub: DiskView,
        root: Pointer,
    )
        requires
            sub.decodable(root),
            sub.acyclic(),
            sub.block_in_bounds(root),
            sub.is_sub_disk(self),
        ensures
            self.path_decodable(root),
            sub.path_decodable(root),
            self.path_build_tight(root) == sub.path_build_tight(root),
            sub.path_build_tight(root) == sub.build_tight(root),
            self.path_build_tight(root) == sub.build_tight(root),
    {
        self.sub_disk_decodable_implies_path_decodable(sub, root);
        sub.decodable_implies_path_decodable(root);
        sub.path_build_tight_extends_same(self, root);
        sub.path_build_tight_equals_build_tight(root);
        assert(self.path_build_tight(root) == sub.path_build_tight(root));
        assert(sub.path_build_tight(root) == sub.build_tight(root));
    }

    pub open spec(checked) fn path_build_lsn_au_index_au_walk(self, root: Pointer, first: AU) -> LsnAUIndex
        recommends
            self.path_decodable(root),
            self.path_build_tight(root).pointer_is_upstream(root, first),
    {
        self.path_build_tight(root).build_lsn_au_index_au_walk(root, first)
    }

    pub open spec(checked) fn path_build_au_page_bounds_au_walk(self, root: Pointer, first: AU) -> AUPageBounds
        recommends
            self.path_decodable(root),
            self.path_build_tight(root).pointer_is_upstream(root, first),
    {
        self.path_build_tight(root).build_au_page_bounds_au_walk(root, first)
    }

    pub proof fn path_build_bookkeeping_matches_tight(self, root: Pointer, first: AU)
        requires
            self.path_decodable(root),
            self.path_build_tight(root).pointer_is_upstream(root, first),
        ensures
            self.path_build_lsn_au_index_au_walk(root, first)
                == self.path_build_tight(root).build_lsn_au_index_au_walk(root, first),
            self.path_build_au_page_bounds_au_walk(root, first)
                == self.path_build_tight(root).build_au_page_bounds_au_walk(root, first),
    {
    }

    proof fn build_au_page_bounds_page_walk_sub_disk_equal(self, big: DiskView, root: Pointer)
        requires
            self.decodable(root),
            big.decodable(root),
            big.acyclic(),
            self.is_sub_disk(big),
        ensures
            self.build_au_page_bounds_page_walk(root) == big.build_au_page_bounds_page_walk(root),
        decreases self.the_rank_of(root),
    {
        assert forall|addr| #[trigger] self.entries.contains_key(addr)
        implies big.entries.contains_key(addr) by {}

        assert(self.valid_ranking(big.the_ranking()));
        if root is Some {
            self.build_au_page_bounds_page_walk_sub_disk_equal(big, self.next(root));
            assert(self.next(root) == big.next(root));
            let addr = root.unwrap();
            let self_prior = self.build_au_page_bounds_page_walk(self.next(root));
            let big_prior = big.build_au_page_bounds_page_walk(self.next(root));
            assert(self_prior == big_prior);
            assert(big.entries[addr] == self.entries[addr]);
            assert(self.build_au_page_bounds_page_walk(root)
                == self_prior.insert(
                    addr.au,
                    if self_prior.contains_key(addr.au) && addr.page <= self_prior[addr.au] {
                        self_prior[addr.au]
                    } else {
                        addr.page
                    },
                ));
            assert(big.build_au_page_bounds_page_walk(root)
                == big_prior.insert(
                    addr.au,
                    if big_prior.contains_key(addr.au) && addr.page <= big_prior[addr.au] {
                        big_prior[addr.au]
                    } else {
                        addr.page
                    },
                ));
        }
    }

    #[verifier(decreases_by)]
    pub proof fn loose_build_lsn_au_index_page_walk_with_ranking_decreases(
        self,
        root: Pointer,
        ranking: Ranking,
    )
    {
        match root {
            None => {},
            Some(addr) => {
                assert(self.entries.contains_key(addr));
                assert(ranking.contains_key(addr));
                let next = self.entries[addr].cropped_prior(self.boundary_lsn);
                if next is Some {
                    assert(ranking.contains_key(next.unwrap()));
                    assert(ranking[next.unwrap()] < ranking[addr]);
                }
            },
        }
    }

    pub open spec fn loose_build_lsn_au_index_page_walk_with_ranking(
        self,
        root: Pointer,
        ranking: Ranking,
    ) -> LsnAUIndex
        recommends
            self.path_valid_ranking(root, ranking),
        decreases if root is Some && ranking.contains_key(root.unwrap()) {
            ranking[root.unwrap()] + 1
        } else {
            0
        }
    {
        decreases_when(self.path_valid_ranking(root, ranking));
        decreases_by(Self::loose_build_lsn_au_index_page_walk_with_ranking_decreases);
        match root {
            None => Map::empty(),
            Some(addr) => {
                let record = self.entries[addr];
                let update = singleton_index(
                    math::max(self.boundary_lsn as int, record.message_seq.seq_start as int) as nat,
                    record.message_seq.seq_end,
                    addr.au,
                );
                self.loose_build_lsn_au_index_page_walk_with_ranking(
                    record.cropped_prior(self.boundary_lsn),
                    ranking,
                ).union_prefer_right(update)
            },
        }
    }

    pub open spec fn loose_build_lsn_au_index_au_walk(self, root: Pointer, first: AU) -> LsnAUIndex
        recommends
            self.path_decodable(root),
            self.path_build_tight(root).pointer_is_upstream(root, first),
    {
        if self.path_decodable(root) {
            let ranking = choose |ranking: Ranking| self.path_valid_ranking(root, ranking);
            self.loose_build_lsn_au_index_page_walk_with_ranking(root, ranking)
        } else {
            Map::empty()
        }
    }

    pub proof fn loose_build_lsn_au_index_page_walk_with_ranking_matches_tight(
        self,
        root: Pointer,
        ranking: Ranking,
    )
        requires
            self.path_valid_ranking(root, ranking),
        ensures
            self.loose_build_lsn_au_index_page_walk_with_ranking(root, ranking)
                == self.path_build_tight_with_ranking(root, ranking).build_lsn_au_index_page_walk(root),
        decreases if root is Some && ranking.contains_key(root.unwrap()) {
            ranking[root.unwrap()] + 1
        } else {
            0
        }
    {
        self.path_build_tight_with_ranking_decodable(root, ranking);
        match root {
            None => {},
            Some(addr) => {
                let record = self.entries[addr];
                let next = record.cropped_prior(self.boundary_lsn);
                self.loose_build_lsn_au_index_page_walk_with_ranking_matches_tight(next, ranking);

                let tail = self.path_build_tight_with_ranking(next, ranking);
                let tight = self.path_build_tight_with_ranking(root, ranking);
                assert(tight.entries == tail.entries.insert(addr, record));
                assert(tight.boundary_lsn == self.boundary_lsn);
                assert(tight.entries[addr] == record);
                assert(tight.next(root) == next);
                assert(tail.is_sub_disk(tight)) by {
                    assert forall |a: Address| #[trigger] tail.entries.contains_key(a)
                        implies tight.entries.contains_key(a) && tight.entries[a] == tail.entries[a] by {
                        assert(a != addr) by {
                            if a == addr {
                                if next is None {
                                    assert(tail.entries =~= Map::<Address, LinkedJournal_v::JournalRecord>::empty());
                                } else {
                                    self.path_build_tight_with_ranking_entry_rank_le(next, ranking, addr);
                                    assert(ranking[addr] <= ranking[next.unwrap()]);
                                    assert(ranking[next.unwrap()] < ranking[addr]);
                                }
                                assert(false);
                            }
                        }
                    }
                }
                self.path_build_tight_with_ranking_decodable(next, ranking);
                assert(tail.decodable(next));
                assert(tail.is_sub_disk_with_newer_lsn(tight));
                tail.build_lsn_au_index_page_walk_sub_disk(tight, next);
                assert(tail.build_lsn_au_index_page_walk(next)
                    == tight.build_lsn_au_index_page_walk(next));

                let update = singleton_index(
                    math::max(self.boundary_lsn as int, record.message_seq.seq_start as int) as nat,
                    record.message_seq.seq_end,
                    addr.au,
                );
                assert(self.loose_build_lsn_au_index_page_walk_with_ranking(root, ranking)
                    == self.loose_build_lsn_au_index_page_walk_with_ranking(next, ranking)
                        .union_prefer_right(update));
                assert(tight.build_lsn_au_index_page_walk(root)
                    == tight.build_lsn_au_index_page_walk(next).union_prefer_right(update));
            },
        }
    }

    pub proof fn loose_build_lsn_au_index_au_walk_matches_tight(
        self,
        root: Pointer,
        first: AU,
    )
        requires
            self.path_decodable(root),
            self.path_build_tight(root).pointer_is_upstream(root, first),
        ensures
            self.loose_build_lsn_au_index_au_walk(root, first)
                == self.path_build_tight(root).build_lsn_au_index_au_walk(root, first),
    {
        let ranking = choose |ranking: Ranking| self.path_valid_ranking(root, ranking);
        self.path_build_tight_uses_ranking(root, ranking);
        self.loose_build_lsn_au_index_page_walk_with_ranking_matches_tight(root, ranking);
        let tight = self.path_build_tight(root);
        tight.build_lsn_au_index_equiv_page_walk(root, first);
        assert(self.loose_build_lsn_au_index_au_walk(root, first)
            == self.loose_build_lsn_au_index_page_walk_with_ranking(root, ranking));
        assert(tight.build_lsn_au_index_page_walk(root)
            == tight.build_lsn_au_index_au_walk(root, first));
    }

    #[verifier(decreases_by)]
    pub proof fn loose_build_au_page_bounds_page_walk_with_ranking_decreases(
        self,
        root: Pointer,
        ranking: Ranking,
    )
    {
        match root {
            None => {},
            Some(addr) => {
                assert(self.entries.contains_key(addr));
                assert(ranking.contains_key(addr));
                let next = self.entries[addr].cropped_prior(self.boundary_lsn);
                if next is Some {
                    assert(ranking.contains_key(next.unwrap()));
                    assert(ranking[next.unwrap()] < ranking[addr]);
                }
            },
        }
    }

    pub open spec fn loose_build_au_page_bounds_page_walk_with_ranking(
        self,
        root: Pointer,
        ranking: Ranking,
    ) -> AUPageBounds
        recommends
            self.path_valid_ranking(root, ranking),
        decreases if root is Some && ranking.contains_key(root.unwrap()) {
            ranking[root.unwrap()] + 1
        } else {
            0
        }
    {
        decreases_when(self.path_valid_ranking(root, ranking));
        decreases_by(Self::loose_build_au_page_bounds_page_walk_with_ranking_decreases);
        match root {
            None => Map::empty(),
            Some(addr) => {
                let record = self.entries[addr];
                let prior = self.loose_build_au_page_bounds_page_walk_with_ranking(
                    record.cropped_prior(self.boundary_lsn),
                    ranking,
                );
                let page = if prior.contains_key(addr.au) && addr.page <= prior[addr.au] {
                    prior[addr.au]
                } else {
                    addr.page
                };
                prior.insert(addr.au, page)
            },
        }
    }

    pub open spec fn loose_build_au_page_bounds_au_walk(self, root: Pointer, first: AU) -> AUPageBounds
        recommends
            self.path_decodable(root),
            self.path_build_tight(root).pointer_is_upstream(root, first),
    {
        if self.path_decodable(root) {
            let ranking = choose |ranking: Ranking| self.path_valid_ranking(root, ranking);
            self.loose_build_au_page_bounds_page_walk_with_ranking(root, ranking)
        } else {
            Map::empty()
        }
    }

    pub proof fn loose_build_au_page_bounds_page_walk_with_ranking_matches_tight(
        self,
        root: Pointer,
        ranking: Ranking,
    )
        requires
            self.path_valid_ranking(root, ranking),
        ensures
            self.loose_build_au_page_bounds_page_walk_with_ranking(root, ranking)
                == self.path_build_tight_with_ranking(root, ranking).build_au_page_bounds_page_walk(root),
        decreases if root is Some && ranking.contains_key(root.unwrap()) {
            ranking[root.unwrap()] + 1
        } else {
            0
        }
    {
        self.path_build_tight_with_ranking_decodable(root, ranking);
        match root {
            None => {},
            Some(addr) => {
                let record = self.entries[addr];
                let next = record.cropped_prior(self.boundary_lsn);
                self.loose_build_au_page_bounds_page_walk_with_ranking_matches_tight(next, ranking);

                let tail = self.path_build_tight_with_ranking(next, ranking);
                let tight = self.path_build_tight_with_ranking(root, ranking);
                assert(tight.entries == tail.entries.insert(addr, record));
                assert(tight.boundary_lsn == self.boundary_lsn);
                assert(tight.entries[addr] == record);
                assert(tight.next(root) == next);
                assert(tail.is_sub_disk(tight)) by {
                    assert forall |a: Address| #[trigger] tail.entries.contains_key(a)
                        implies tight.entries.contains_key(a) && tight.entries[a] == tail.entries[a] by {
                        assert(a != addr) by {
                            if a == addr {
                                if next is None {
                                    assert(tail.entries =~= Map::<Address, LinkedJournal_v::JournalRecord>::empty());
                                } else {
                                    self.path_build_tight_with_ranking_entry_rank_le(next, ranking, addr);
                                    assert(ranking[addr] <= ranking[next.unwrap()]);
                                    assert(ranking[next.unwrap()] < ranking[addr]);
                                }
                                assert(false);
                            }
                        }
                    }
                }
                self.path_build_tight_with_ranking_decodable(next, ranking);
                assert(tail.decodable(next));
                tail.build_au_page_bounds_page_walk_sub_disk_equal(tight, next);
                assert(tail.build_au_page_bounds_page_walk(next)
                    == tight.build_au_page_bounds_page_walk(next));

                let loose_prior = self.loose_build_au_page_bounds_page_walk_with_ranking(next, ranking);
                let tight_prior = tight.build_au_page_bounds_page_walk(next);
                assert(loose_prior == tight_prior);
                assert(self.loose_build_au_page_bounds_page_walk_with_ranking(root, ranking)
                    == loose_prior.insert(
                        addr.au,
                        if loose_prior.contains_key(addr.au) && addr.page <= loose_prior[addr.au] {
                            loose_prior[addr.au]
                        } else {
                            addr.page
                        },
                    ));
                assert(tight.build_au_page_bounds_page_walk(root)
                    == tight_prior.insert(
                        addr.au,
                        if tight_prior.contains_key(addr.au) && addr.page <= tight_prior[addr.au] {
                            tight_prior[addr.au]
                        } else {
                            addr.page
                        },
                    ));
            },
        }
    }

    pub proof fn loose_build_au_page_bounds_au_walk_matches_tight(
        self,
        root: Pointer,
        first: AU,
    )
        requires
            self.path_decodable(root),
            self.path_build_tight(root).pointer_is_upstream(root, first),
        ensures
            self.loose_build_au_page_bounds_au_walk(root, first)
                == self.path_build_tight(root).build_au_page_bounds_au_walk(root, first),
    {
        let ranking = choose |ranking: Ranking| self.path_valid_ranking(root, ranking);
        self.path_build_tight_uses_ranking(root, ranking);
        self.loose_build_au_page_bounds_page_walk_with_ranking_matches_tight(root, ranking);
        let tight = self.path_build_tight(root);
        tight.build_au_page_bounds_equiv_page_walk(root, first);
        assert(self.loose_build_au_page_bounds_au_walk(root, first)
            == self.loose_build_au_page_bounds_page_walk_with_ranking(root, ranking));
    }

    pub proof fn build_tight_entry_lsn_bounded(self, root: Pointer, addr: Address)
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
                self.build_tight_entry_lsn_bounded(self.next(root), addr);
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

    pub open spec fn tight_domain(self, index: LsnAUIndex, root: Pointer) -> Set<Address>
    {
        Set::new( |addr: Address| {
                &&& self.entries.contains_key(addr)
                &&& index.values().contains(addr.au)
                &&& !au_addrs_past_pointer(root).contains(addr)
            }
        )
    }

    pub open spec fn domain_au_bounded_wrt_index(self, index: LsnAUIndex) -> bool {
        forall|addr|
            #[trigger] self.entries.dom().contains(addr) ==> {
                &&& index.values().contains(addr.au)
            }
    }

    pub open spec fn domain_tight_wrt_index(self, index: LsnAUIndex, root: Pointer) -> bool {
        forall|addr|
            #[trigger] self.entries.dom().contains(addr) ==> {
                &&& index.values().contains(addr.au)
                &&& root is Some ==> !root.unwrap().after_page(addr)
            }
    }

    pub open spec fn bounded_inactive_lsns(self, index: LsnAUIndex, root: Pointer) -> bool {
        forall|addr, lsn|
            ({
                &&& self.entries.dom().contains(addr)
                &&& self.entries[addr].message_seq.contains(lsn)
                &&& index.values().contains(addr.au)
                &&& !index.contains_key(lsn)
                &&& root is Some ==> !root.unwrap().after_page(addr)
            }) ==> lsn < self.boundary_lsn
    }

    #[verifier(opaque)]
    pub closed spec(checked) fn index_keys_exist_valid_entries(
        self,
        lsn_au_index: LsnAUIndex,
    ) -> bool
        recommends
            self.wf(),
    {
        forall|lsn|
            #[trigger]
            lsn_au_index.contains_key(lsn) ==> exists|addr: Address|
                addr.wf() && addr.au == lsn_au_index[lsn] && #[trigger]
                self.addr_supports_lsn(addr, lsn)
    }

    // one-off explicit instantiation lemma for use in predicates where reveal is verboten.
    pub proof fn instantiate_index_keys_exist_valid_entries(
        self,
        lsn_au_index: LsnAUIndex,
        lsn: LSN,
    ) -> (addr: Address)
        requires
            self.wf(),
            lsn_au_index.contains_key(lsn),
            self.index_keys_exist_valid_entries(lsn_au_index),
        ensures
            addr.wf(),
            lsn_au_index[lsn] == addr.au,
            self.addr_supports_lsn(addr, lsn),
    {
        reveal(DiskView::index_keys_exist_valid_entries);
        let addr = choose|addr: Address|
            addr.wf() && addr.au == lsn_au_index[lsn] && #[trigger]
            self.addr_supports_lsn(addr, lsn);
        addr
    }

    pub open spec(checked) fn build_lsn_au_index_page_walk(self, root: Pointer) -> LsnAUIndex
        recommends
            self.decodable(root),
            self.acyclic(),
        decreases
            self.the_rank_of(root),  // TODO(chris): this when clause isn't working!
        when {
            // TODO(chris): oh look, &&&s not ,s! Let's run with that!
            &&& self.decodable(root)
            &&& self.acyclic()
        }
    {
        if root is None {
            Map::empty()
        } else {
            let curr_msgs = self.entries[root.unwrap()].message_seq;
            let update = singleton_index(
                math::max(self.boundary_lsn as int, curr_msgs.seq_start as int) as nat,
                curr_msgs.seq_end,
                root.unwrap().au,
            );
            self.build_lsn_au_index_page_walk(self.next(root)).union_prefer_right(update)
        }
    }

    // I think you could prove this by connecting from page_walk to au_walk, thence to
    // lsn_addr_index, thence via index_domain_valid. But... ew.
    pub proof fn build_lsn_au_index_page_walk_domain(self, root: Pointer)
        requires
            self.decodable(root),
            self.acyclic(),
        ensures
            forall|lsn|
                self.build_lsn_au_index_page_walk(root).contains_key(lsn) <==> (self.tj_at(
                    root,
                ).seq_start() <= lsn < self.tj_at(root).seq_end()),
        decreases self.the_rank_of(root),
    {
        // TODO(chris) Another great application of spec ensures. (Also frustrating absence; spent
        // a dozen lines discovering the trigger on top of the dozen lines setting this silly thing
        // up)
        if root is Some {
            self.build_lsn_au_index_page_walk_domain(self.next(root));
            let prior_result = self.build_lsn_au_index_page_walk(self.next(root));  // trigger mctriggerface that we'd get for free in spec ensures
        }
    }

    // TODO(jonh): this lemma should just be an ensures on build_lsn_au_index_page_walk.
    pub proof fn build_lsn_au_index_page_walk_consistency(self, root: Pointer)
        requires
            self.decodable(root),
            self.acyclic(),
        ensures
            self.build_lsn_addr_index(root).dom() =~= self.build_lsn_au_index_page_walk(root).dom(),
            forall |lsn| self.build_lsn_addr_index(root).contains_key(lsn) ==>
                #[trigger] self.build_lsn_addr_index(root)[lsn].au == self.build_lsn_au_index_page_walk(root)[lsn],
        decreases self.the_rank_of(root)
    {
        if root is Some {
            self.build_lsn_au_index_page_walk_consistency(self.next(root));
        }
    }

    pub proof fn build_lsn_au_index_page_walk_exist_valid_entries(self, root: Pointer)
        requires
            self.decodable(root),
            self.acyclic(),
            self.wf_addrs(),
        ensures
            self.index_keys_exist_valid_entries(self.build_lsn_au_index_page_walk(root)),
        decreases self.the_rank_of(root),
    {
        reveal(DiskView::index_keys_exist_valid_entries);
        if root is Some {
            let curr_msgs = self.entries[root.unwrap()].message_seq;
            let update = singleton_index(
                math::max(self.boundary_lsn as int, curr_msgs.seq_start as int) as nat,
                curr_msgs.seq_end,
                root.unwrap().au,
            );
            assert forall|lsn| update.contains_key(lsn) implies exists|addr: Address|
                addr.wf() && addr.au == update[lsn] && #[trigger]
                self.addr_supports_lsn(addr, lsn) by {
                assert(self.addr_supports_lsn(root.unwrap(), lsn));
            }
            assert(self.index_keys_exist_valid_entries(update));
            self.build_lsn_au_index_page_walk_exist_valid_entries(self.next(root));
        }
    }

    pub open spec(checked) fn build_au_page_bounds_page_walk(self, root: Pointer) -> AUPageBounds
        recommends
            self.decodable(root),
            self.acyclic(),
        decreases self.the_rank_of(root),
        when {
            &&& self.decodable(root)
            &&& self.acyclic()
        }
    {
        if root is None {
            Map::empty()
        } else {
            let addr = root.unwrap();
            let prior = self.build_au_page_bounds_page_walk(self.next(root));
            let page = if prior.contains_key(addr.au) && addr.page <= prior[addr.au] {
                prior[addr.au]
            } else {
                addr.page
            };
            prior.insert(addr.au, page)
        }
    }

    #[verifier(decreases_by)]
    pub proof fn build_au_page_bounds_au_walk_helper(self, root: Pointer, first: AU) {
        match root {
            None => {},
            Some(addr) => {
                if addr.au == first {
                } else {
                    let bottom = first_page(root);
                    self.bottom_properties(root, first);
                    self.transitive_ranking(bottom.unwrap(), root.unwrap(), first);
                }
            },
        }
    }

    #[verifier(decreases_by)]
    pub proof fn build_lsn_au_index_au_walk_helper(self, root: Pointer, first: AU) {
        match root {
            None => {},
            Some(addr) => {
                if addr.au == first {
                } else {
                    // Nine lines of boilerplate to insert this one line in the right place. :v/
                    let bottom = first_page(root);
                    self.bottom_properties(root, first);
                    self.transitive_ranking(bottom.unwrap(), root.unwrap(), first);
                }
            },
        }
    }

    pub open spec /*(checked)*/ fn build_au_page_bounds_au_walk(self, root: Pointer, first: AU) -> AUPageBounds
        recommends
            self.pointer_is_upstream(root, first),
            self.acyclic(),
            self.internal_au_pages_fully_linked(),
        decreases self.the_rank_of(root),
    {
        decreases_when(
            {
                root is Some ==> ({
                    &&& self.pointer_is_upstream(root, first)
                    &&& self.acyclic()
                    &&& self.internal_au_pages_fully_linked()
                })
            },
        );
        decreases_by(Self::build_au_page_bounds_au_walk_helper);
        match root {
            None => map![],
            Some(addr) => {
                if addr.au == first {
                    self.build_au_page_bounds_page_walk(root)
                } else {
                    let bottom = first_page(root);
                    let prior_result = self.build_au_page_bounds_au_walk(self.next(bottom), first);
                    prior_result.insert(addr.au, addr.page)
                }
            },
        }
    }

    pub open spec(checked) fn entries_bounded_by_au_page_bounds(self, bounds: AUPageBounds) -> Map<Address, LinkedJournal_v::JournalRecord>
    {
        self.entries.restrict(Set::new(|addr: Address| {
            &&& self.entries.contains_key(addr)
            &&& bounds.contains_key(addr.au)
            &&& addr.page <= bounds[addr.au]
            &&& self.boundary_lsn < self.entries[addr].message_seq.seq_end
        }))
    }

    pub proof fn same_au_live_page_in_build_tight(self, root: Pointer, addr: Address)
        requires
            self.decodable(root),
            self.acyclic(),
            self.internal_au_pages_fully_linked(),
            root is Some,
            self.entries.contains_key(addr),
            addr.au == root.unwrap().au,
            addr.page <= root.unwrap().page,
            self.boundary_lsn < self.entries[addr].message_seq.seq_end,
        ensures
            self.build_tight(root).entries.contains_key(addr),
        decreases root.unwrap().page - addr.page,
    {
        let root_addr = root.unwrap();
        if addr == root_addr {
            assert(self.build_tight(root).entries.contains_key(addr));
        } else {
            assert(addr.page < root_addr.page);
            reveal(DiskView::pages_allocated_in_lsn_order);

            assert(self.pages_allocated_in_lsn_order());
            assert(self.entries[addr].message_seq.seq_end
                <= self.entries[root_addr].message_seq.seq_start);
            assert(self.boundary_lsn < self.entries[root_addr].message_seq.seq_start);
            assert(self.entries[root_addr].has_link(self.boundary_lsn));
            assert(self.entries[root_addr].cropped_prior(self.boundary_lsn) is Some);
            assert(self.entries[root_addr].prior_rec is Some);
            assert(root_addr.page != 0);
            assert(self.nonzero_pages_point_backward());
            assert(self.entries[root_addr].prior_rec == Some(root_addr.previous()));
            let prior = root_addr.previous();
            assert(self.next(root) == Some(prior));
            assert(self.entries.contains_key(prior));
            assert(addr.page <= prior.page);
            if addr == prior {
                assert(self.boundary_lsn < self.entries[prior].message_seq.seq_end);
            } else {
                assert(addr.page < prior.page);
                assert(self.entries[addr].message_seq.seq_end
                    <= self.entries[prior].message_seq.seq_start);
                assert(self.boundary_lsn < self.entries[prior].message_seq.seq_start);
                assert(self.boundary_lsn < self.entries[prior].message_seq.seq_end);
            }
            self.same_au_live_page_in_build_tight(Some(prior), addr);
            self.build_tight_shape(root);
            assert(self.build_tight(self.next(root)).entries.contains_key(addr));
            assert(self.build_tight(root).entries.contains_key(addr));
        }
    }

    pub proof fn build_tight_entry_bounded_by_page_walk(self, root: Pointer, addr: Address)
        requires
            self.decodable(root),
            self.acyclic(),
            root is Some ==> self.upstream(root.unwrap()),
            self.build_tight(root).entries.contains_key(addr),
        ensures
            self.build_au_page_bounds_page_walk(root).contains_key(addr.au),
            addr.page <= self.build_au_page_bounds_page_walk(root)[addr.au],
            self.boundary_lsn < self.entries[addr].message_seq.seq_end,
        decreases self.the_rank_of(root),
    {
        self.build_tight_entry_lsn_bounded(root, addr);
        if root is Some {
            let root_addr = root.unwrap();
            if addr == root_addr {
            } else {
                self.build_tight_shape(root);
                assert(self.build_tight(self.next(root)).entries.contains_key(addr));
                if self.next(root) is Some {
                    assert(self.upstream(self.next(root).unwrap()));
                }
                self.build_tight_entry_bounded_by_page_walk(self.next(root), addr);
            }
        } else {
            assert(false);
        }
    }

    pub proof fn build_tight_entry_value(self, root: Pointer, addr: Address)
        requires
            self.decodable(root),
            self.acyclic(),
            self.build_tight(root).entries.contains_key(addr),
        ensures
            self.entries.contains_key(addr),
            self.build_tight(root).entries[addr] == self.entries[addr],
        decreases self.the_rank_of(root),
    {
        self.build_tight_ensures(root);
        if root is Some {
            if addr == root.unwrap() {
            } else {
                self.build_tight_shape(root);
                assert(self.build_tight(self.next(root)).entries.contains_key(addr));
                self.build_tight_entry_value(self.next(root), addr);
            }
        } else {
            assert(false);
        }
    }

    pub proof fn build_au_page_bounds_page_walk_domain_matches_build_tight(self, root: Pointer, first: AU)
        requires
            self.pointer_is_upstream(root, first),
        ensures
            self.entries_bounded_by_au_page_bounds(self.build_au_page_bounds_page_walk(root))
                == self.build_tight(root).entries,
        decreases self.the_rank_of(root),
    {
        if root is Some {
            if self.next(root) is Some {
                let root_addr = root.unwrap();
                let next_addr = self.next(root).unwrap();
                assert(self.boundary_lsn < self.entries[root_addr].message_seq.seq_start);
                assert(self.this_block_can_concat(root_addr));
                assert(self.entries[next_addr].message_seq.can_concat(self.entries[root_addr].message_seq));
                assert(self.entries[next_addr].message_seq.seq_end
                    == self.entries[root_addr].message_seq.seq_start);
                assert(self.upstream(next_addr));
            }
            assert(self.pointer_is_upstream(self.next(root), first));
            self.build_au_page_bounds_page_walk_domain_matches_build_tight(self.next(root), first);
        }
        assert_maps_equal!(
            self.entries_bounded_by_au_page_bounds(self.build_au_page_bounds_page_walk(root)),
            self.build_tight(root).entries,
            addr => {
                if self.entries_bounded_by_au_page_bounds(self.build_au_page_bounds_page_walk(root)).contains_key(addr) {
                    if root is Some {
                        let root_addr = root.unwrap();
                        if addr.au == root_addr.au && addr.page <= root_addr.page {
                            self.same_au_live_page_in_build_tight(root, addr);
                        } else {
                            assert(self.build_au_page_bounds_page_walk(self.next(root)).contains_key(addr.au));
                            assert(addr.page <= self.build_au_page_bounds_page_walk(self.next(root))[addr.au]);
                            assert(self.entries_bounded_by_au_page_bounds(
                                self.build_au_page_bounds_page_walk(self.next(root))).contains_key(addr));
                            assert(self.build_tight(self.next(root)).entries.contains_key(addr));
                            self.build_tight_shape(root);
                        }
                    } else {
                        assert(false);
                    }
                }
                if self.build_tight(root).entries.contains_key(addr) {
                    self.build_tight_entry_bounded_by_page_walk(root, addr);
                    assert(self.entries.contains_key(addr));
                    assert(self.entries_bounded_by_au_page_bounds(
                        self.build_au_page_bounds_page_walk(root)).contains_key(addr));
                }
            }
        );
    }

    pub proof fn build_tight_au_prefix_shape(self, root: Pointer, first: AU)
        requires
            self.pointer_is_upstream(root, first),
            root is Some,
            root.unwrap().au != first,
        ensures
            ({
                let bottom = first_page(root);
                forall |addr: Address| #[trigger] self.build_tight(root).entries.contains_key(addr) <==>
                    ({
                        &&& self.entries.contains_key(addr)
                        &&& addr.au == root.unwrap().au
                        &&& addr.page <= root.unwrap().page
                        &&& self.boundary_lsn < self.entries[addr].message_seq.seq_end
                    } || self.build_tight(self.next(bottom)).entries.contains_key(addr))
            }),
        decreases root.unwrap().page,
    {
        let root_addr = root.unwrap();
        let bottom = first_page(root);
        self.nonfirst_properties(root, first);
        if root_addr.page == 0 {
            assert(bottom == root);
            self.build_tight_shape(root);
            assert forall |addr: Address| #[trigger] self.build_tight(root).entries.contains_key(addr) <==>
                ({
                    &&& self.entries.contains_key(addr)
                    &&& addr.au == root_addr.au
                    &&& addr.page <= root_addr.page
                    &&& self.boundary_lsn < self.entries[addr].message_seq.seq_end
                } || self.build_tight(self.next(bottom)).entries.contains_key(addr)) by {
                if self.build_tight(root).entries.contains_key(addr) {
                    if addr == root_addr {
                        assert(self.upstream(root_addr));
                    } else {
                        assert(self.build_tight(self.next(root)).entries.contains_key(addr));
                    }
                }
                if ({
                    &&& self.entries.contains_key(addr)
                    &&& addr.au == root_addr.au
                    &&& addr.page <= root_addr.page
                    &&& self.boundary_lsn < self.entries[addr].message_seq.seq_end
                } || self.build_tight(self.next(bottom)).entries.contains_key(addr)) {
                    if addr == root_addr {
                        assert(self.build_tight(root).entries.contains_key(addr));
                    } else if self.build_tight(self.next(bottom)).entries.contains_key(addr) {
                        assert(self.build_tight(self.next(root)).entries.contains_key(addr));
                        assert(self.build_tight(root).entries.contains_key(addr));
                    } else {
                        assert(addr.au == root_addr.au);
                        assert(addr.page <= root_addr.page);
                        assert(addr.page == root_addr.page);
                        assert(addr == root_addr);
                        assert(false);
                    }
                }
            }
        } else {
            let prior = root_addr.previous();
            assert(self.next(root) == Some(prior));
            assert(prior.au == root_addr.au);
            assert(prior.page < root_addr.page);
            assert(first_page(Some(prior)) == bottom);
            assert(self.pointer_is_upstream(Some(prior), first));
            self.build_tight_au_prefix_shape(Some(prior), first);
            self.build_tight_shape(root);
            assert forall |addr: Address| #[trigger] self.build_tight(root).entries.contains_key(addr) <==>
                ({
                    &&& self.entries.contains_key(addr)
                    &&& addr.au == root_addr.au
                    &&& addr.page <= root_addr.page
                    &&& self.boundary_lsn < self.entries[addr].message_seq.seq_end
                } || self.build_tight(self.next(bottom)).entries.contains_key(addr)) by {
                if self.build_tight(root).entries.contains_key(addr) {
                    if addr == root_addr {
                        assert(self.upstream(root_addr));
                    } else {
                        assert(self.build_tight(self.next(root)).entries.contains_key(addr));
                        assert(self.build_tight(Some(prior)).entries.contains_key(addr));
                    }
                }
                if ({
                    &&& self.entries.contains_key(addr)
                    &&& addr.au == root_addr.au
                    &&& addr.page <= root_addr.page
                    &&& self.boundary_lsn < self.entries[addr].message_seq.seq_end
                } || self.build_tight(self.next(bottom)).entries.contains_key(addr)) {
                    if addr == root_addr {
                        assert(self.build_tight(root).entries.contains_key(addr));
                    } else if addr.au == root_addr.au && addr.page <= root_addr.page {
                        assert(addr.page <= prior.page);
                        assert(self.build_tight(Some(prior)).entries.contains_key(addr));
                        assert(self.build_tight(self.next(root)).entries.contains_key(addr));
                        assert(self.build_tight(root).entries.contains_key(addr));
                    } else {
                        assert(self.build_tight(self.next(bottom)).entries.contains_key(addr));
                        assert(self.build_tight(Some(prior)).entries.contains_key(addr));
                        assert(self.build_tight(self.next(root)).entries.contains_key(addr));
                        assert(self.build_tight(root).entries.contains_key(addr));
                    }
                }
            }
        }
    }

    pub proof fn build_tight_tail_no_current_au(self, root: Pointer, first: AU, addr: Address)
        requires
            self.pointer_is_upstream(root, first),
            root is Some,
            root.unwrap().au != first,
            self.build_tight(self.next(first_page(root))).entries.contains_key(addr),
        ensures
            addr.au != root.unwrap().au,
    {
        let bottom = first_page(root);
        let prior_result = self.build_lsn_au_index_au_walk(self.next(bottom), first);
        let prior_addr_index = self.build_lsn_addr_index(self.next(bottom));
        self.bottom_properties(root, first);
        self.build_tight_domain_is_build_lsn_addr_index_range(self.next(bottom));
        let lsn = choose |lsn| #![auto]
            prior_addr_index.contains_key(lsn) && prior_addr_index[lsn] == addr;
        self.build_lsn_au_index_equiv_page_walk(self.next(bottom), first);
        self.build_lsn_au_index_page_walk_consistency(self.next(bottom));
        self.lemma_next_au_doesnt_intersect(root, first, prior_result);
        assert(prior_result.contains_key(lsn));
        assert(prior_result[lsn] == addr.au);
        assert(addr.au != root.unwrap().au);
    }

    pub proof fn build_au_page_bounds_au_walk_domain_matches_build_tight(self, root: Pointer, first: AU)
        requires
            self.pointer_is_upstream(root, first),
        ensures
            self.entries_bounded_by_au_page_bounds(self.build_au_page_bounds_au_walk(root, first))
                == self.build_tight(root).entries,
        decreases self.the_rank_of(root),
    {
        match root {
            None => {
                assert_maps_equal!(
                    self.entries_bounded_by_au_page_bounds(self.build_au_page_bounds_au_walk(root, first)),
                    self.build_tight(root).entries
                );
            },
            Some(addr) => {
                if addr.au == first {
                    self.build_au_page_bounds_page_walk_domain_matches_build_tight(root, first);
                } else {
                    let bottom = first_page(root);
                    self.bottom_properties(root, first);
                    self.transitive_ranking(bottom.unwrap(), root.unwrap(), first);
                    self.build_au_page_bounds_au_walk_domain_matches_build_tight(self.next(bottom), first);
                    self.build_tight_au_prefix_shape(root, first);
                    assert_maps_equal!(
                        self.entries_bounded_by_au_page_bounds(self.build_au_page_bounds_au_walk(root, first)),
                        self.build_tight(root).entries,
                        key => {
                            if self.entries_bounded_by_au_page_bounds(
                                self.build_au_page_bounds_au_walk(root, first)).contains_key(key) {
                                if key.au == addr.au {
                                    self.same_au_live_page_in_build_tight(root, key);
                                } else {
                                    assert(self.entries_bounded_by_au_page_bounds(
                                        self.build_au_page_bounds_au_walk(self.next(bottom), first)).contains_key(key));
                                    assert(self.build_tight(self.next(bottom)).entries.contains_key(key));
                                    assert(self.build_tight(root).entries.contains_key(key));
                                }
                            }
                            if self.build_tight(root).entries.contains_key(key) {
                                self.build_tight_entry_value(root, key);
                                if key.au == addr.au {
                                    if self.build_tight(self.next(bottom)).entries.contains_key(key) {
                                        self.build_tight_tail_no_current_au(root, first, key);
                                    }
                                    self.build_tight_entry_lsn_bounded(root, key);
                                    assert(key.page <= addr.page);
                                    assert(self.entries_bounded_by_au_page_bounds(
                                        self.build_au_page_bounds_au_walk(root, first)).contains_key(key));
                                } else {
                                    assert(self.build_tight(self.next(bottom)).entries.contains_key(key));
                                    assert(self.entries_bounded_by_au_page_bounds(
                                        self.build_au_page_bounds_au_walk(self.next(bottom), first)).contains_key(key));
                                    assert(self.entries_bounded_by_au_page_bounds(
                                        self.build_au_page_bounds_au_walk(root, first)).contains_key(key));
                                }
                                assert(self.entries_bounded_by_au_page_bounds(
                                    self.build_au_page_bounds_au_walk(root, first))[key] == self.entries[key]);
                                assert(self.build_tight(root).entries[key] == self.entries[key]);
                            }
                        }
                    );
                }
            },
        }
    }

    pub proof fn build_au_page_bounds_page_walk_dom_has_entry(self, root: Pointer, first: AU)
        requires
            self.pointer_is_upstream(root, first),
        ensures
            forall |au: AU| #[trigger] self.build_au_page_bounds_page_walk(root).dom().contains(au) ==>
                exists |addr: Address| #![auto] {
                    &&& self.entries_bounded_by_au_page_bounds(self.build_au_page_bounds_page_walk(root)).contains_key(addr)
                    &&& addr.au == au
                },
        decreases self.the_rank_of(root),
    {
        if root is Some {
            let root_addr = root.unwrap();
            assert(self.upstream(root_addr));
            assert(self.entries_bounded_by_au_page_bounds(
                self.build_au_page_bounds_page_walk(root)).contains_key(root_addr));
            if self.next(root) is Some {
                let next_addr = self.next(root).unwrap();
                assert(self.boundary_lsn < self.entries[root_addr].message_seq.seq_start);
                assert(self.this_block_can_concat(root_addr));
                assert(self.entries[next_addr].message_seq.seq_end
                    == self.entries[root_addr].message_seq.seq_start);
                assert(self.upstream(next_addr));
            }
            assert(self.pointer_is_upstream(self.next(root), first));
            self.build_au_page_bounds_page_walk_dom_has_entry(self.next(root), first);
            assert forall |au: AU| #[trigger] self.build_au_page_bounds_page_walk(root).dom().contains(au)
                implies exists |addr: Address| #![auto] {
                    &&& self.entries_bounded_by_au_page_bounds(self.build_au_page_bounds_page_walk(root)).contains_key(addr)
                    &&& addr.au == au
                } by {
                if au == root_addr.au {
                    assert(self.entries_bounded_by_au_page_bounds(
                        self.build_au_page_bounds_page_walk(root)).contains_key(root_addr));
                } else {
                    let witness = choose |addr: Address| #![auto] {
                        &&& self.entries_bounded_by_au_page_bounds(
                            self.build_au_page_bounds_page_walk(self.next(root))).contains_key(addr)
                        &&& addr.au == au
                    };
                    assert(self.entries_bounded_by_au_page_bounds(
                        self.build_au_page_bounds_page_walk(root)).contains_key(witness));
                }
            }
        }
    }

    pub proof fn first_page_tail_no_same_au(self, root: Pointer, first: AU, addr: Address)
        requires
            self.pointer_is_upstream(root, first),
            root is Some,
            root.unwrap().page == 0,
            self.build_tight(self.next(root)).entries.contains_key(addr),
        ensures
            addr.au != root.unwrap().au,
    {
        let root_addr = root.unwrap();
        if addr.au == root_addr.au {
            self.build_tight_ranks(root);
            if addr == root_addr {
                assert(false);
            } else {
                assert(root_addr.page < addr.page);
                if self.next(root) is Some {
                    let next_addr = self.next(root).unwrap();
                    assert(self.decodable(self.next(root))) by {
                        assert(self.nondangling_pointers());
                    }
                    self.build_tight_entry_value(self.next(root), addr);
                    assert(self.entries.contains_key(addr));
                    assert(self.decodable(Some(addr)));
                    assert(self.upstream(root_addr));
                    self.same_au_live_page_in_build_tight(Some(addr), root_addr);
                    self.build_tight_shape(Some(addr));
                    assert(self.build_tight(self.next(Some(addr))).entries.contains_key(root_addr));
                    self.build_tight_ranks(Some(addr));
                    assert(false);
                } else {
                    assert(false);
                }
            }
        }
    }

    pub proof fn build_au_page_bounds_page_walk_root_bound(self, root: Pointer, first: AU)
        requires
            self.pointer_is_upstream(root, first),
            root is Some,
        ensures
            self.build_au_page_bounds_page_walk(root).contains_key(root.unwrap().au),
            self.build_au_page_bounds_page_walk(root)[root.unwrap().au] <= root.unwrap().page,
        decreases self.the_rank_of(root),
    {
        let root_addr = root.unwrap();
        if self.next(root) is Some {
            let next_addr = self.next(root).unwrap();
            assert(self.boundary_lsn < self.entries[root_addr].message_seq.seq_start);
            assert(self.this_block_can_concat(root_addr));
            assert(self.entries[next_addr].message_seq.seq_end
                == self.entries[root_addr].message_seq.seq_start);
            assert(self.upstream(next_addr));
        }
        assert(self.pointer_is_upstream(self.next(root), first));
        if root_addr.page == 0 {
            if self.build_au_page_bounds_page_walk(self.next(root)).contains_key(root_addr.au) {
                self.build_au_page_bounds_page_walk_dom_has_entry(self.next(root), first);
                let witness = choose |addr: Address| #![auto] {
                    &&& self.entries_bounded_by_au_page_bounds(
                        self.build_au_page_bounds_page_walk(self.next(root))).contains_key(addr)
                    &&& addr.au == root_addr.au
                };
                self.build_au_page_bounds_page_walk_domain_matches_build_tight(self.next(root), first);
                assert(self.build_tight(self.next(root)).entries.contains_key(witness));
                self.first_page_tail_no_same_au(root, first, witness);
                assert(false);
            }
        } else {
            if self.next(root) is Some {
                assert(self.nonzero_pages_point_backward());
                assert(self.entries[root_addr].prior_rec == Some(root_addr.previous()));
                assert(self.next(root) == Some(root_addr.previous()));
                assert(self.next(root).unwrap().au == root_addr.au);
                self.build_au_page_bounds_page_walk_root_bound(self.next(root), first);
                assert(self.build_au_page_bounds_page_walk(self.next(root))[root_addr.au]
                    <= self.next(root).unwrap().page);
                assert(self.next(root).unwrap().page < root_addr.page);
            } else {
            }
        }
        let prior = self.build_au_page_bounds_page_walk(self.next(root));
        if prior.contains_key(root_addr.au) {
            if root_addr.page == 0 {
                assert(false);
            } else {
                assert(prior[root_addr.au] < root_addr.page);
            }
            assert(!(root_addr.page <= prior[root_addr.au]));
        }
        assert(self.build_au_page_bounds_page_walk(root)[root_addr.au] == root_addr.page);
    }

    pub proof fn build_au_page_bounds_au_walk_dom_has_entry(self, root: Pointer, first: AU)
        requires
            self.pointer_is_upstream(root, first),
        ensures
            forall |au: AU| #[trigger] self.build_au_page_bounds_au_walk(root, first).dom().contains(au) ==>
                exists |addr: Address| {
                    &&& #[trigger] self.entries_bounded_by_au_page_bounds(self.build_au_page_bounds_au_walk(root, first)).contains_key(addr)
                    &&& addr.au == au
                },
        decreases self.the_rank_of(root),
    {
        match root {
            None => {},
            Some(addr) => {
                if addr.au == first {
                    self.build_au_page_bounds_page_walk_dom_has_entry(root, first);
                } else {
                    let bottom = first_page(root);
                    self.bottom_properties(root, first);
                    self.transitive_ranking(bottom.unwrap(), root.unwrap(), first);
                    self.build_au_page_bounds_au_walk_dom_has_entry(self.next(bottom), first);
                    assert(self.upstream(addr));
                    assert(self.entries_bounded_by_au_page_bounds(
                        self.build_au_page_bounds_au_walk(root, first)).contains_key(addr));
                    assert forall |au: AU| #[trigger] self.build_au_page_bounds_au_walk(root, first).dom().contains(au)
                        implies exists |witness: Address| {
                            &&& #[trigger] self.entries_bounded_by_au_page_bounds(self.build_au_page_bounds_au_walk(root, first)).contains_key(witness)
                            &&& witness.au == au
                        } by {
                        if au == addr.au {
                            assert(self.entries_bounded_by_au_page_bounds(
                                self.build_au_page_bounds_au_walk(root, first)).contains_key(addr));
                        } else {
                            let witness = choose |witness: Address| {
                                &&& #[trigger] self.entries_bounded_by_au_page_bounds(
                                    self.build_au_page_bounds_au_walk(self.next(bottom), first)).contains_key(witness)
                                &&& witness.au == au
                            };
                            assert(self.entries_bounded_by_au_page_bounds(
                                self.build_au_page_bounds_au_walk(root, first)).contains_key(witness));
                        }
                    }
                }
            },
        }
    }

    pub proof fn build_au_page_bounds_au_walk_root_bound(self, root: Pointer, first: AU)
        requires
            self.pointer_is_upstream(root, first),
            root is Some,
        ensures
            self.build_au_page_bounds_au_walk(root, first).contains_key(root.unwrap().au),
            self.build_au_page_bounds_au_walk(root, first)[root.unwrap().au] <= root.unwrap().page,
        decreases self.the_rank_of(root),
    {
        if root.unwrap().au == first {
            self.build_au_page_bounds_page_walk_root_bound(root, first);
        } else {
            assert(self.build_au_page_bounds_au_walk(root, first)[root.unwrap().au]
                == root.unwrap().page);
        }
    }

    pub proof fn build_au_page_bounds_page_walk_bound_has_entry(self, root: Pointer, first: AU, au: AU)
        requires
            self.pointer_is_upstream(root, first),
            self.build_au_page_bounds_page_walk(root).contains_key(au),
        ensures
            ({
                let bounds = self.build_au_page_bounds_page_walk(root);
                let addr = Address{au, page: bounds[au]};
                &&& self.entries.contains_key(addr)
                &&& self.boundary_lsn < self.entries[addr].message_seq.seq_end
            }),
        decreases self.the_rank_of(root),
    {
        assert(root is Some);
        let root_addr = root.unwrap();
        let bounds = self.build_au_page_bounds_page_walk(root);
        if au == root_addr.au {
            self.build_au_page_bounds_page_walk_root_bound(root, first);
            assert(bounds[au] == root_addr.page);
            assert(self.entries.contains_key(root_addr));
            assert(self.boundary_lsn < self.entries[root_addr].message_seq.seq_end);
        } else {
            let prior = self.build_au_page_bounds_page_walk(self.next(root));
            assert(prior.contains_key(au));
            assert(bounds[au] == prior[au]);
            assert(self.pointer_is_upstream(self.next(root), first));
            self.build_au_page_bounds_page_walk_bound_has_entry(self.next(root), first, au);
        }
    }

    pub proof fn build_au_page_bounds_au_walk_bound_has_entry(self, root: Pointer, first: AU, au: AU)
        requires
            self.pointer_is_upstream(root, first),
            self.build_au_page_bounds_au_walk(root, first).contains_key(au),
        ensures
            ({
                let bounds = self.build_au_page_bounds_au_walk(root, first);
                let addr = Address{au, page: bounds[au]};
                &&& self.entries.contains_key(addr)
                &&& self.boundary_lsn < self.entries[addr].message_seq.seq_end
            }),
        decreases self.the_rank_of(root),
    {
        match root {
            None => {
                assert(false);
            },
            Some(root_addr) => {
                if root_addr.au == first {
                    self.build_au_page_bounds_page_walk_bound_has_entry(root, first, au);
                } else if au == root_addr.au {
                    assert(self.build_au_page_bounds_au_walk(root, first)[au] == root_addr.page);
                    assert(self.entries.contains_key(root_addr));
                    assert(self.boundary_lsn < self.entries[root_addr].message_seq.seq_end);
                } else {
                    let bottom = first_page(root);
                    self.bottom_properties(root, first);
                    self.transitive_ranking(bottom.unwrap(), root.unwrap(), first);
                    let prior = self.build_au_page_bounds_au_walk(self.next(bottom), first);
                    assert(prior.contains_key(au));
                    assert(self.build_au_page_bounds_au_walk(root, first)[au] == prior[au]);
                    assert(self.pointer_is_upstream(self.next(bottom), first));
                    self.build_au_page_bounds_au_walk_bound_has_entry(self.next(bottom), first, au);
                }
            },
        }
    }

    pub proof fn build_au_page_bounds_equiv_page_walk(self, root: Pointer, first: AU)
        requires
            self.pointer_is_upstream(root, first),
        ensures
            self.build_au_page_bounds_au_walk(root, first)
                == self.build_au_page_bounds_page_walk(root),
    {
        let au_bounds = self.build_au_page_bounds_au_walk(root, first);
        let page_bounds = self.build_au_page_bounds_page_walk(root);
        self.build_au_page_bounds_au_walk_domain_matches_build_tight(root, first);
        self.build_au_page_bounds_page_walk_domain_matches_build_tight(root, first);

        assert_maps_equal!(au_bounds, page_bounds, au => {
            if au_bounds.contains_key(au) {
                self.build_au_page_bounds_au_walk_bound_has_entry(root, first, au);
                let addr = Address{au, page: au_bounds[au]};
                assert(self.entries_bounded_by_au_page_bounds(au_bounds).contains_key(addr));
                assert(self.build_tight(root).entries.contains_key(addr));
                assert(self.entries_bounded_by_au_page_bounds(page_bounds).contains_key(addr));
                assert(page_bounds.contains_key(au));
                assert(au_bounds[au] <= page_bounds[au]);
            }
            if page_bounds.contains_key(au) {
                self.build_au_page_bounds_page_walk_bound_has_entry(root, first, au);
                let addr = Address{au, page: page_bounds[au]};
                assert(self.entries_bounded_by_au_page_bounds(page_bounds).contains_key(addr));
                assert(self.build_tight(root).entries.contains_key(addr));
                assert(self.entries_bounded_by_au_page_bounds(au_bounds).contains_key(addr));
                assert(au_bounds.contains_key(au));
                assert(page_bounds[au] <= au_bounds[au]);
            }
        });
    }

    pub open spec   /*(checked)*/
    fn build_lsn_au_index_au_walk(self, root: Pointer, first: AU) -> LsnAUIndex
        recommends
            self.pointer_is_upstream(root, first),
            self.acyclic(),
            self.internal_au_pages_fully_linked(),
        decreases self.the_rank_of(root),
    {
        // NOTE(Jialin): if we don't take the root is Some into account when writing the decreases when,
        // verifier can't seem to infer that root is None is the base case and returns map![]
        // unable to prove that calling this with None returns an empty map without changes to the decreases when
        decreases_when(
            {
                root is Some ==> ({
                    &&& self.pointer_is_upstream(root, first)
                    &&& self.acyclic()
                    &&& self.internal_au_pages_fully_linked()
                })
            },
        );
        decreases_by(Self::build_lsn_au_index_au_walk_helper);
        match root {
            None => map![],
            Some(addr) => {
                if addr.au == first {
                    self.build_lsn_au_index_page_walk(root)
                } else {
                    // Jump over all the intermediate pages in the AU; we know how they're laid out already.
                    let bottom = first_page(root);
                    let last_lsn = self.entries[root.unwrap()].message_seq.seq_end;
                    let first_lsn = self.entries[bottom.unwrap()].message_seq.seq_start;
                    let update = singleton_index(first_lsn, last_lsn, bottom.unwrap().au);
                    let prior_result = self.build_lsn_au_index_au_walk(self.next(bottom), first);
                    prior_result.union_prefer_right(update)
                }
            },
        }
    }

    pub proof fn build_lsn_au_index_equiv_page_walk(self, root: Pointer, first: AU)
        requires
            self.pointer_is_upstream(root, first)
        ensures
            self.build_lsn_au_index_au_walk(root, first) =~= self.build_lsn_au_index_page_walk(
                root,
            ),
        decreases self.the_rank_of(root),
    {
        match root {
            None => {},
            Some(addr) => {
                if addr.au == first {
                } else {
                    self.build_lsn_au_index_equiv_page_walk(self.next(root), first);
                    // TODO(andrea): rediscovering this is brutal. I copy-pasted the definition
                    // three times before realizing I hadn't satisfied decreases_by. This should
                    // have been dispatched in the spec fn.  Aaargh.
                    self.bottom_properties(root, first);
                    //                     let bottom = first_page(root);
                    //                     let last_lsn = dv.entries[root.unwrap()].message_seq.seq_end;
                    //                     let first_lsn = dv.entries[bottom.unwrap()].message_seq.seq_start;
                    //                     let update = singleton_index(first_lsn, last_lsn, bottom.unwrap().au);
                    //                     let prior_result = Self::build_lsn_au_index_au_walk(dv, dv.next(bottom), first);
                    //                     let output = prior_result.union_prefer_right(update);
                    //                     assert( output == Self::build_lsn_au_index_au_walk(dv, root, first) );
                    if 0 < root.unwrap().page {  // zero case is easy; au-walk and page-walk do the same thing
                        assert(self.next(root) is Some) by   /*contradiction*/ {
                            if self.next(root) is None {
                                assert(self.addr_supports_lsn(root.unwrap(), self.boundary_lsn));  // witness
                                assert(false);
                            }
                        }
                        self.bottom_properties(self.next(root), first);
                    }
                }
            },
        }
    }

    proof fn build_lsn_au_index_page_walk_sub_disk_subset(self, big: DiskView, root: Pointer)
        requires
            self.decodable(root),
            big.decodable(root),
            big.acyclic(),
            self.is_sub_disk_with_newer_lsn(big),
        ensures
            self.build_lsn_au_index_page_walk(root) <= big.build_lsn_au_index_page_walk(root),
        decreases self.the_rank_of(root),
    {
        assert forall|addr| #[trigger] self.entries.contains_key(addr)
        implies big.entries.contains_key(addr) by {}  // trigger for ranking

        assert(self.valid_ranking(big.the_ranking()));
        if root is Some {
            self.build_lsn_au_index_page_walk_sub_disk_subset(big, self.next(root));
            self.build_lsn_au_index_page_walk_domain(self.next(root));
        }
        assert(self.build_lsn_au_index_page_walk(root) <= big.build_lsn_au_index_page_walk(root)) by {
            assert forall |lsn: LSN| #[trigger] self.build_lsn_au_index_page_walk(root).contains_key(lsn)
                implies big.build_lsn_au_index_page_walk(root).contains_key(lsn)
                    && self.build_lsn_au_index_page_walk(root)[lsn]
                        == big.build_lsn_au_index_page_walk(root)[lsn] by {
            }
        }
    }

    proof fn build_lsn_au_index_page_walk_sub_disk_equal(self, big: DiskView, root: Pointer)
        requires
            self.decodable(root),
            big.decodable(root),
            big.acyclic(),
            self.is_sub_disk(big),
        ensures
            self.build_lsn_au_index_page_walk(root) == big.build_lsn_au_index_page_walk(root),
        decreases self.the_rank_of(root),
    {
        assert forall|addr| #[trigger] self.entries.contains_key(addr)
        implies big.entries.contains_key(addr) by {}  // trigger for ranking

        assert(self.valid_ranking(big.the_ranking()));
        if root is Some {
            self.build_lsn_au_index_page_walk_sub_disk_equal(big, self.next(root));
            assert(self.next(root) == big.next(root));
            let curr_msgs = self.entries[root.unwrap()].message_seq;
            let update = singleton_index(
                math::max(self.boundary_lsn as int, curr_msgs.seq_start as int) as nat,
                curr_msgs.seq_end,
                root.unwrap().au,
            );
            assert(big.boundary_lsn == self.boundary_lsn);
            assert(big.entries[root.unwrap()] == self.entries[root.unwrap()]);
            assert(self.build_lsn_au_index_page_walk(root)
                == self.build_lsn_au_index_page_walk(self.next(root)).union_prefer_right(update));
            assert(big.build_lsn_au_index_page_walk(root)
                == big.build_lsn_au_index_page_walk(self.next(root)).union_prefer_right(update));
        }
    }

    pub proof fn build_lsn_au_index_page_walk_sub_disk(self, big: DiskView, root: Pointer)
        requires
            self.decodable(root),
            big.decodable(root),
            big.acyclic(),
            self.is_sub_disk_with_newer_lsn(big),
        ensures
            self.build_lsn_au_index_page_walk(root) <= big.build_lsn_au_index_page_walk(root),
            self.is_sub_disk(big) ==> self.build_lsn_au_index_page_walk(root) == big.build_lsn_au_index_page_walk(root)
    {
        self.build_lsn_au_index_page_walk_sub_disk_subset(big, root);
        if self.is_sub_disk(big) {
            self.build_lsn_au_index_page_walk_sub_disk_equal(big, root);
        }
    }

    pub proof fn build_commutes_over_append_record(
        self,
        root: Pointer,
        msgs: MsgHistory,
        new_addr: Address,
    )
        requires
            self.tj_at(root).decodable(),
            self.tj_at(root).seq_end() == msgs.seq_start,
            msgs.wf(),
            !msgs.is_empty(),
            !self.entries.contains_key(new_addr),
        ensures
            ({
                let old_au_idx = self.build_lsn_au_index_page_walk(root);  // super-let, please
                let au_update = singleton_index(msgs.seq_start, msgs.seq_end, new_addr.au);
                let incremental_idx = old_au_idx.union_prefer_right(au_update);
                let appended_tj = self.tj_at(root).append_record(new_addr, msgs);
                let built_idx = appended_tj.disk_view.build_lsn_au_index_page_walk(
                    appended_tj.freshest_rec,
                );
                incremental_idx
                    =~= built_idx  // remember, kids, the tilde is a proof strategy!

            }),
        decreases self.the_rank_of(root),
    {
        let appended_tj = self.tj_at(root).append_record(new_addr, msgs);
        assert(appended_tj.disk_view.valid_ranking(self.tj_at(root).marshal_ranking(new_addr)));  // witness to acyclic
        self.build_lsn_au_index_page_walk_sub_disk(appended_tj.disk_view, root);
    }

    pub proof fn bottom_properties(self, root: Pointer, first: AU)
        requires
            self.pointer_is_upstream(root, first),
            root is Some,
            root.unwrap().au != first,
        ensures  // TODO wish I had a superlet for bottom=first_page(root) here

            self.next(first_page(root)) is Some,  // else root.au == first
            self.decodable(self.next(first_page(root))),  // because decodable-ity is recursive
            self.buildable(self.next(first_page(root))),
            // a couple uglies I threw in to complete lemma_aus_hold_contiguous_lsns
            self.pointer_is_upstream(first_page(root), first),
            self.tj_at(self.next(first_page(root))).seq_end() <= self.tj_at(root).seq_end(),
        decreases self.the_rank_of(root),
    {
        if self.next(root) is None {
            assert(self.addr_supports_lsn(root.unwrap(), self.boundary_lsn));
            assert(false);
        }
        if root.unwrap().page != 0 {
            //             assert( dv.entries.contains_key(first_page(root).unwrap()) );
            //             assert( Self::au_page_links_to_prior(dv, root.unwrap()) );
            self.bottom_properties(self.next(root), first);
        }
    }

    pub open spec(checked) fn upstream(self, addr: Address) -> bool {
        &&& self.entries.contains_key(addr)
        &&& self.boundary_lsn < self.entries[addr].message_seq.seq_end
    }

    // NB talking about dv.next() is painful because we have to reason about interactions
    // with a moving dv.boundary. Maybe easier to break down the reasoning into pointers
    // (which don't change) and layer the boundary reasoning on top.
    pub open spec(checked) fn nonzero_pages_point_backward(self) -> bool
        recommends
            self.wf(),
    {
        forall|addr: Address|
            #![auto]
            ({
                &&& addr.page != 0
                &&& self.entries.contains_key(addr)
            }) ==> self.entries[addr].prior_rec == Some(addr.previous())
    }

    // Profiling suggested this quantifier is trigger happy
    // Changing from close to open bc we need it in the refinement proof
    #[verifier(opaque)]
    pub open spec(checked) fn pages_allocated_in_lsn_order(self) -> bool
        recommends
            self.wf(),
    {
        forall|alo: Address, ahi: Address|
            #![auto]
            ({
                &&& alo.au == ahi.au
                &&& alo.page < ahi.page
                &&& self.entries.contains_key(alo)
                &&& self.entries.contains_key(ahi)
            }) ==> self.entries[alo].message_seq.seq_end <= self.entries[ahi].message_seq.seq_start
    }

    pub open spec(checked) fn internal_au_pages_fully_linked(self) -> bool
        recommends
            self.wf(),
    {
        &&& self.nonzero_pages_point_backward()
        &&& self.pages_allocated_in_lsn_order()
    }

    pub proof fn nonfirst_properties(self, root: Pointer, first: AU)
        requires
            self.pointer_is_upstream(root, first),
            root is Some,
            root.unwrap().au != first,
        ensures
            forall|ptr: Pointer|
                #![auto]
                ptr is Some && ptr.unwrap().au == root.unwrap().au && ptr.unwrap().page
                    <= root.unwrap().page ==> self.pointer_is_upstream(ptr, first),
            forall|ptr: Pointer|
                #![auto]
                ptr is Some && ptr.unwrap().au == root.unwrap().au && 0 < ptr.unwrap().page
                    <= root.unwrap().page ==> self.next(ptr) is Some && self.next(ptr).unwrap().au
                    == root.unwrap().au,
        decreases self.the_rank_of(root),
    {
        if self.next(root) is None {
            assert(self.addr_supports_lsn(root.unwrap(), self.boundary_lsn));
            assert(false);
        }
        if root.unwrap().page != 0 {
            self.nonfirst_properties(self.next(root), first);
        }
    }

    pub proof fn transitive_ranking(self, root: Address, later: Address, first: AU)
        requires
            self.pointer_is_upstream(Some(later), first),
            self.decodable(Some(root)),
            self.acyclic(),
            root.au != first,
            root.au == later.au,
            root.page <= later.page,
            self.internal_au_pages_fully_linked(),  // should be less than <= bc it's enough to prove termination, cause later is already < caller's root

        ensures
            self.the_rank_of(Some(root)) <= self.the_rank_of(Some(later)),
        decreases later.page,
    {
        if root == later {
            assert(self.decodable(Some(later)));
            return ;
        }//Self::nonfirst_decodable(dv, Some(later), first);

        let prior = self.next(Some(later));
        //         assert( dv.entries.contains_key(later) );    // todo deleteme
        //         assert( dv.entries[later].prior_rec is Some );
        //         assert( prior is Some );
        //         assert( prior.unwrap().page + 1 == later.page );
        self.nonfirst_properties(Some(later), first);
        self.transitive_ranking(root, prior.unwrap(), first);
    }

    pub open spec fn has_unique_lsns(self) -> bool {
        forall|lsn, addr1, addr2|
            self.addr_supports_lsn(addr1, lsn) && self.addr_supports_lsn(addr2, lsn) ==> addr1
                == addr2
    }

    pub open spec fn pointer_is_upstream(self, root: Pointer, first: AU) -> bool {
        &&& self.decodable(root)
        &&& self.acyclic()
        &&& self.internal_au_pages_fully_linked()
        &&& self.has_unique_lsns()
        &&& root is Some ==> self.valid_first_au(first)
        &&& root is Some ==> self.upstream(root.unwrap())
    }

    pub open spec(checked) fn wf_addrs(self) -> bool {
        forall|addr| #[trigger] self.entries.contains_key(addr) ==> addr.wf()
    }

    pub open spec(checked) fn valid_first_au(self, first: AU) -> bool {
        exists|addr: Address|
            #![auto]
            addr.au == first && self.addr_supports_lsn(addr, self.boundary_lsn)
    }

    pub proof fn lemma_aus_hold_contiguous_lsns(self, root: Pointer, first: AU)
        requires
            self.pointer_is_upstream(root, first),
        ensures
            self.tj_at(root).au_domain_valid(self.build_lsn_au_index_au_walk(root, first)),
            aus_hold_contiguous_lsns(self.build_lsn_au_index_au_walk(root, first)),
        decreases self.the_rank_of(root),
    {
        let lsn_au_index = self.build_lsn_au_index_au_walk(root, first);
        match root {
            None => {},
            Some(addr) => {
                if addr.au == first {
                    self.lemma_aus_hold_contiguous_lsns_first_page(root, first);
                } else {
                    let bottom = first_page(root);
                    //                     let last_lsn = dv.entries[root.unwrap()].message_seq.seq_end;
                    let first_lsn = self.entries[bottom.unwrap()].message_seq.seq_start;
                    //                     let update = singleton_index(first_lsn, last_lsn, bottom.unwrap().au);
                    let prior_result = self.build_lsn_au_index_au_walk(self.next(bottom), first);
                    self.bottom_properties(root, first);
                    self.transitive_ranking(bottom.unwrap(), root.unwrap(), first);
                    self.lemma_aus_hold_contiguous_lsns(self.next(bottom), first);
                    assert forall|lsn1, lsn2, lsn3|
                        contiguous_lsns(lsn_au_index, lsn1, lsn2, lsn3) by {
                        if ({
                            &&& lsn1 <= lsn2 <= lsn3
                            &&& lsn_au_index.contains_key(lsn1)
                            &&& lsn_au_index.contains_key(lsn3)
                            &&& lsn_au_index[lsn1] == lsn_au_index[lsn3]
                        }) {
                            if lsn1 < first_lsn {  // recursive case
                                if !prior_result.contains_key(lsn3)  {  // lsn3 is in bottom.au, tho? Nope.
                                    self.lemma_next_au_doesnt_intersect(root, first, prior_result);
                                    assert(false);
                                }
                                assert(contiguous_lsns(prior_result, lsn1, lsn2, lsn3));  // trigger
                            }
                        }
                    }
                }
            },
        }
    }

    pub proof fn nonfirst_pages(self, addr: Address, first: AU)
        requires
            self.pointer_is_upstream(Some(addr), first),
            addr.au != first,
        ensures
            self.boundary_lsn < self.entries[addr].message_seq.seq_start,
    {
        // assert( dv.boundary_lsn < dv.entries[addr].message_seq.seq_end );  // documentation; by pointer_is_upstream
        if self.entries[addr].message_seq.seq_start <= self.boundary_lsn {
            assert(self.addr_supports_lsn(addr, self.boundary_lsn));  // trigger
            //            assert( Self::valid_first_au(dv, addr.au) );  // documentation
            //            assert( Self::valid_first_au(dv, first) );    // documentation
            assert(false);  // lsns unique
        }
    }

    pub proof fn build_lsn_addr_index_returns_upstream_pages(self, root: Pointer, first: AU)
        requires
            self.has_unique_lsns(),
            self.internal_au_pages_fully_linked(),
            self.buildable(root),
            self.valid_first_au(first),
        ensures
            ({
                let lsn_addr_index = self.build_lsn_addr_index(root);
                forall|lsn|
                    #![auto]
                    lsn_addr_index.contains_key(lsn) && lsn_addr_index[lsn].au != first
                        ==> self.pointer_is_upstream(Some(lsn_addr_index[lsn]), first)
            }),
        decreases self.the_rank_of(root),  // when self.buildable(root)

    {
        let lsn_addr_index = self.build_lsn_addr_index(root);
        if root is Some {
            self.build_lsn_addr_index_returns_upstream_pages(self.next(root), first);
            // ugly trigger block. want to just trigger on alpha-substituted definition of build_lsn_addr_index
            let curr_msgs = self.entries[root.unwrap()].message_seq;
            let start_lsn = math::max(self.boundary_lsn as int, curr_msgs.seq_start as int) as nat;
            let update = LikesJournal_v::singleton_index(
                start_lsn,
                curr_msgs.seq_end,
                root.unwrap(),
            );
            assert(lsn_addr_index == self.build_lsn_addr_index(self.next(root)).union_prefer_right(
                update,
            ));
            //             assert forall |lsn| lsn_addr_index.contains_key(lsn) && lsn_addr_index[lsn].au != first
            //             implies Self::pointer_is_upstream(dv, Some(lsn_addr_index[lsn]), first) by {
            // // //                 if update.contains_key(lsn) {
            // // //                 //if dv.build_lsn_addr_index(dv.next(root)).contains_key(lsn) {
            // // //                     assert( lsn_addr_index[lsn] == root.unwrap() );
            // // //                     assert( Self::pointer_is_upstream(dv, Some(lsn_addr_index[lsn]), first) );
            // // //                 } else {
            // // //                     assert( dv.build_lsn_addr_index(dv.next(root)).contains_key(lsn) );
            // // //                     assert( dv.build_lsn_addr_index(dv.next(root))[lsn] ==
            // // //                             lsn_addr_index[lsn] );
            // // //                     assert( dv.build_lsn_addr_index(dv.next(root))[lsn].au != first );
            // // //                     assert( Self::pointer_is_upstream(dv, Some(lsn_addr_index[lsn]), first) );
            // // //                 }
            //             }
        }
    }

    pub proof fn upstream_pages(self, earlier: Address, later: Address, first: AU)
        requires
            self.pointer_is_upstream(Some(later), first),
            later.au != first,
            earlier.au == later.au,
            earlier.page <= later.page,
        ensures
            self.pointer_is_upstream(Some(earlier), first),
        decreases later.page - earlier.page,
    {
        if earlier.page < later.page {
            let prior = later.previous();
            self.nonfirst_pages(later, first);
            assert(self.upstream(prior));
            assert(self.pointer_is_upstream(Some(prior), first));
            self.upstream_pages(earlier, prior, first);
        }
    }

    pub proof fn lemma_next_au_doesnt_intersect(
        self,
        root: Pointer,
        first: AU,
        prior_result: LsnAUIndex,
    )
        requires
            self.pointer_is_upstream(root, first),
            root is Some,
            root.unwrap().au != first,
            prior_result == self.build_lsn_au_index_au_walk(self.next(first_page(root)), first),
        ensures
            forall|lsn|
                #![auto]
                prior_result.contains_key(lsn) ==> prior_result[lsn] != root.unwrap().au,
    {
        let bottom = first_page(root);
        let prior_addr_index = self.tj_at(self.next(bottom)).build_lsn_addr_index();
        self.bottom_properties(root, first);
        self.build_lsn_addr_all_decodable(self.next(bottom));
        self.build_lsn_au_index_equiv_page_walk(self.next(bottom), first);
        self.build_lsn_au_index_page_walk_consistency(self.next(bottom));
        self.build_lsn_addr_index_returns_upstream_pages(self.next(bottom), first);
        assert forall|lsn| prior_result.contains_key(lsn) implies #[trigger]
        prior_result[lsn] != root.unwrap().au by {
            let addr = prior_addr_index[lsn];
            if addr.au == root.unwrap().au {
                if addr.au != first {
                    let addr0 = Address { au: addr.au, page: 0 };
                    let addrp = self.next(bottom).unwrap();
                    self.upstream_pages(addr0, addr, first);
                    self.transitive_ranking(addr0, addr, first);
                    let prior_last = (self.entries[addrp].message_seq.seq_end - 1) as nat;
                    assert(lsn <= prior_last) by {
                        reveal(TruncatedJournal::index_domain_valid);

                        self.build_lsn_addr_index_domain_valid(self.next(bottom));
                    }
                    self.tj_at(self.next(bottom)).build_lsn_addr_honors_rank(prior_addr_index);
                    assert(prior_addr_index.contains_key(prior_last));  // trigger build_lsn_addr_honors_rank
                    assert(false);
                }
                assert(addr.au == first);
                assert(false);
            }
        }
    }

    // TODO(jonh): if we had spec ensures, this would be a nice conclusion to build_lsn_au_index_page_walk
    pub proof fn au_index_page_supports_lsn(self, root: Pointer, lsn: LSN)
        requires
            self.decodable(root),
            self.acyclic(),
            self.build_lsn_au_index_page_walk(root).contains_key(lsn),
        ensures
            exists|addr|
                #![auto]
                self.addr_supports_lsn(addr, lsn) && addr.au == self.build_lsn_au_index_page_walk(
                    root,
                )[lsn],
        decreases self.the_rank_of(root),
    {
        if root is Some {
            let curr_msgs = self.entries[root.unwrap()].message_seq;
            let update = singleton_index(
                math::max(self.boundary_lsn as int, curr_msgs.seq_start as int) as nat,
                curr_msgs.seq_end,
                root.unwrap().au,
            );
            if update.contains_key(lsn) {
                assert(self.addr_supports_lsn(root.unwrap(), lsn));  // witness to ensures exists trigger
            } else {
                self.au_index_page_supports_lsn(self.next(root), lsn);
            }
        }
    }

    pub proof fn first_contains_boundary(self, root: Pointer, first: AU)
        requires
            self.decodable(root),
            self.acyclic(),
            self.valid_first_au(first),
            self.has_unique_lsns(),
            root is Some,
            self.upstream(root.unwrap()),
        ensures
            self.build_lsn_au_index_page_walk(root)[self.boundary_lsn] == first,
    {
        let addr = choose|addr: Address|
            #![auto]
            addr.au == first && self.addr_supports_lsn(addr, self.boundary_lsn);
        self.build_lsn_au_index_page_walk_domain(root);
        self.au_index_page_supports_lsn(root, self.boundary_lsn);
    }

    pub proof fn lemma_aus_hold_contiguous_lsns_first_page(self, root: Pointer, first: AU)
        requires
            self.pointer_is_upstream(root, first),
            self.has_unique_lsns(),
            root is Some,
            root.unwrap().au == first,
        ensures
            ({
                // TODO sure want that super-let here, for lsn_au_index.
                let lsn_au_index = self.build_lsn_au_index_page_walk(root);
                &&& forall|lsn|
                    #![auto]
                    lsn_au_index.contains_key(lsn) ==> lsn_au_index[lsn] == root.unwrap().au
                    &&& self.tj_at(root).au_domain_valid(lsn_au_index)
                    &&& aus_hold_contiguous_lsns(lsn_au_index)
            }),
        decreases self.the_rank_of(root),
    {
        let lsn_au_index = self.build_lsn_au_index_page_walk(root);
        if root is None {
        } else if self.next(root) is None {
            assert(self.build_lsn_au_index_page_walk(self.next(root)) =~= Map::empty());  // trigger
        } else if root.unwrap().page == 0 {
            // If there's a valid pointer exiting here, and we're at page 0, then we're not the
            // first au, are we?
            //assert( dv.addr_supports_lsn(lsn_au_index[dv.boundary_lsn], dv.boundary_lsn) );
            assert(exists|addr: Address|
                #![auto]
                addr.au == first && self.addr_supports_lsn(addr, self.boundary_lsn));
            let first_page = choose|addr: Address|
                #![auto]
                addr.au == first && self.addr_supports_lsn(addr, self.boundary_lsn);
            assert(self.addr_supports_lsn(first_page, self.boundary_lsn));
            self.first_contains_boundary(root, first);
            assert(lsn_au_index[self.boundary_lsn] == first);
            assert(self.entries[root.unwrap()].message_seq.seq_end
                <= self.entries[first_page].message_seq.seq_start) by {
                reveal(DiskView::pages_allocated_in_lsn_order);

            }
            assert(false);
        } else {
            self.lemma_aus_hold_contiguous_lsns_first_page(self.next(root), first);  // recurse!
        }
    }

    pub proof fn addr_supports_lsn_consistent_with_index(self, index: LsnAUIndex, lsn: LSN, addr: Address)
        requires
            self.wf(),
            self.wf_addrs(),
            self.has_unique_lsns(),
            self.index_keys_exist_valid_entries(index),
            self.addr_supports_lsn(addr, lsn),
            index.contains_key(lsn),
        ensures
            index[lsn] == addr.au
    {
        let _ = self.instantiate_index_keys_exist_valid_entries(index, lsn);
    }

    pub proof fn boundary_crossing_entry_in_build_tight(
        self,
        root: Pointer,
        first: AU,
        index: LsnAUIndex,
        addr: Address,
    )
        requires
            self.wf(),
            self.wf_addrs(),
            self.decodable(root),
            self.acyclic(),
            self.pointer_is_upstream(root, first),
            self.domain_au_bounded_wrt_index(index),
            self.bounded_inactive_lsns(index, root),
            index == self.build_lsn_au_index_au_walk(root, first),
            self.entries.contains_key(addr),
            root is Some ==> !root.unwrap().after_page(addr),
            self.boundary_lsn < self.entries[addr].message_seq.seq_end,
        ensures
            self.build_tight(root).entries.contains_key(addr),
    {
        let lsn = if self.entries[addr].message_seq.seq_start <= self.boundary_lsn {
            self.boundary_lsn
        } else {
            self.entries[addr].message_seq.seq_start
        };
        assert(self.entries[addr].message_seq.contains(lsn));
        assert(self.addr_supports_lsn(addr, lsn));
        if !index.contains_key(lsn) {
            assert(index.values().contains(addr.au));
            assert(lsn < self.boundary_lsn);
            assert(false);
        }
        if root is None {
            assert(self.build_lsn_au_index_au_walk(root, first) == Map::<LSN, AU>::empty());
            assert(index == Map::<LSN, AU>::empty());
            assert(false);
        }
        self.build_lsn_au_index_equiv_page_walk(root, first);
        self.build_lsn_au_index_page_walk_exist_valid_entries(root);
        assert(index =~= self.build_lsn_au_index_page_walk(root));
        assert(self.index_keys_exist_valid_entries(index));
        self.addr_supports_lsn_consistent_with_index(index, lsn, addr);
        assert(index[lsn] == addr.au);

        self.build_lsn_au_index_page_walk_consistency(root);
        let addr_index = self.build_lsn_addr_index(root);
        assert(addr_index.contains_key(lsn));
        assert(addr_index[lsn].au == index[lsn]);
        assert(addr_index[lsn].au == addr.au);
        self.build_lsn_addr_index_domain_valid(root);
        self.instantiate_index_keys_map_to_valid_entries(addr_index, lsn);
        assert(self.addr_supports_lsn(addr_index[lsn], lsn));
        assert(self.has_unique_lsns());
        assert(addr_index[lsn] == addr);
        self.build_tight_domain_is_build_lsn_addr_index_range(root);
        assert(addr_index.values().contains(addr));
        assert(self.build_tight(root).entries.dom().contains(addr));
    }
}

impl TruncatedJournal {
    pub open spec fn au_domain_valid(self, lsn_au_index: LsnAUIndex) -> bool {
        forall|lsn| lsn_au_index.contains_key(lsn) <==> (self.seq_start() <= lsn < self.seq_end())
    }

    pub open spec(checked) fn empty_at(boundary_lsn: LSN) -> Self {
        TruncatedJournal{
            freshest_rec: None,
            disk_view: DiskView{boundary_lsn, entries: map![]},
        }
    }

    pub proof fn empty_at_ensures(boundary_lsn: LSN)
        ensures
            Self::empty_at(boundary_lsn).wf(),
            Self::empty_at(boundary_lsn).seq_start() == boundary_lsn,
            Self::empty_at(boundary_lsn).seq_end() == boundary_lsn,
            Self::empty_at(boundary_lsn).freshest_rec is None,
            Self::empty_at(boundary_lsn).disk_view.entries.dom() =~= Set::<Address>::empty(),
    {
        assert(Self::empty_at(boundary_lsn).disk_view.valid_ranking(map![]));
    }

    pub open spec fn boundary_au(self, boundary_lsn: LSN) -> AU {
        if self.freshest_rec is None {
            0
        } else {
            let addr = choose |addr: Address| #![auto] addr.wf() && self.disk_view.addr_supports_lsn(addr, boundary_lsn);
            addr.au
        }
    }

    #[verifier(recommends_by)]
    pub proof fn build_lsn_au_index_helper(self, boundary_lsn: LSN) {
        let first = self.boundary_au(boundary_lsn);
        match self.freshest_rec {
            None => {},
            Some(addr) => {
                if addr.au == first {
                } else {
                    self.disk_view.bottom_properties(self.freshest_rec, first);
                    self.disk_view.transitive_ranking(
                        self.freshest_rec.unwrap().first_page(),
                        self.freshest_rec.unwrap(),
                        first,
                    );
                }
            },
        }
    }

    #[verifier(recommends_by)]
    pub proof fn build_lsn_au_index_from_first_helper(self, first: AU) {
        match self.freshest_rec {
            None => {},
            Some(addr) => {
                if addr.au == first {
                } else {
                    self.disk_view.bottom_properties(self.freshest_rec, first);
                    self.disk_view.transitive_ranking(
                        self.freshest_rec.unwrap().first_page(),
                        self.freshest_rec.unwrap(),
                        first,
                    );
                }
            },
        }
    }

    pub open spec(checked) fn build_lsn_au_index(self, boundary_lsn: LSN) -> LsnAUIndex
        recommends
            self.disk_view.pointer_is_upstream(self.freshest_rec, self.boundary_au(boundary_lsn)),
    {
        recommends_by(Self::build_lsn_au_index_helper);
        self.disk_view.build_lsn_au_index_au_walk(self.freshest_rec, self.boundary_au(boundary_lsn))
    }

    pub open spec(checked) fn build_lsn_au_index_from_first(self, first: AU) -> LsnAUIndex
        recommends
            self.disk_view.pointer_is_upstream(self.freshest_rec, first),
    {
        recommends_by(Self::build_lsn_au_index_from_first_helper);
        self.disk_view.build_lsn_au_index_au_walk(self.freshest_rec, first)
    }

    pub proof fn build_lsn_au_index_from_first_ensures(self, first: AU)
        requires
            self.disk_view.wf_addrs(),
            self.disk_view.pointer_is_upstream(self.freshest_rec, first),
        ensures
            ({
                let index = self.build_lsn_au_index_from_first(first);
                &&& self.au_domain_valid(index)
                &&& aus_hold_contiguous_lsns(index)
                &&& self.disk_view.index_keys_exist_valid_entries(index)
                &&& self.freshest_rec is Some ==> {
                    &&& index.contains_key(self.seq_start())
                    &&& index[self.seq_start()] == first
                }
            }),
    {
        self.disk_view.lemma_aus_hold_contiguous_lsns(self.freshest_rec, first);
        self.disk_view.build_lsn_au_index_equiv_page_walk(self.freshest_rec, first);
        self.disk_view.build_lsn_au_index_page_walk_exist_valid_entries(self.freshest_rec);
        if self.freshest_rec is Some {
            self.disk_view.first_contains_boundary(self.freshest_rec, first);
        }
    }

    pub proof fn boundary_au_matches_first(self, first: AU)
        requires
            self.freshest_rec is Some,
            self.disk_view.wf_addrs(),
            self.disk_view.pointer_is_upstream(self.freshest_rec, first),
        ensures
            self.boundary_au(self.seq_start()) == first,
    {
        let chosen = choose |addr: Address| #![auto]
            addr.wf() && self.disk_view.addr_supports_lsn(addr, self.seq_start());
        assert(self.boundary_au(self.seq_start()) == chosen.au);

        assert(self.disk_view.valid_first_au(first));
        let first_addr = choose |addr: Address| #![auto]
            addr.au == first && self.disk_view.addr_supports_lsn(addr, self.seq_start());
        assert(self.disk_view.addr_supports_lsn(first_addr, self.seq_start()));
        assert(self.disk_view.entries.contains_key(first_addr));
        assert(first_addr.wf());
        assert(self.disk_view.has_unique_lsns());
        assert(chosen == first_addr);
    }

    pub proof fn sub_disk_build_sub_lsn_au_index(self, first: AU, big: Self, big_first: AU)
        requires
            big.disk_view.wf_addrs(),
            big.disk_view.pointer_is_upstream(big.freshest_rec, big_first),
            self.disk_view.pointer_is_upstream(self.freshest_rec, first),
            self.disk_view.is_sub_disk(big.disk_view) || self.disk_view.is_sub_disk_with_newer_lsn(
                big.disk_view,
            ),
            self.seq_end() <= big.seq_end(),
        ensures
            self.build_lsn_au_index_from_first(first) <= big.build_lsn_au_index_from_first(big_first),
    {
        let index = self.build_lsn_au_index_from_first(first);
        let big_index = big.build_lsn_au_index_from_first(big_first);

        assert forall|addr| #[trigger] self.disk_view.entries.contains_key(addr)
            implies big.disk_view.entries.contains_key(addr) by {}
        assert(self.disk_view.wf_addrs());

        self.build_lsn_au_index_from_first_ensures(first);
        big.build_lsn_au_index_from_first_ensures(big_first);
        assert(index.dom() <= big_index.dom());

        assert forall|lsn| index.contains_key(lsn)
        implies #[trigger] index[lsn] == big_index[lsn] by {
            reveal(DiskView::index_keys_exist_valid_entries);
            let addr = choose|addr: Address|
                addr.wf() && addr.au == index[lsn] && #[trigger]
                self.disk_view.addr_supports_lsn(addr, lsn);
            assert(big.disk_view.addr_supports_lsn(addr, lsn));
        }
    }

    pub open spec(checked) fn valid_structure(self, index: LsnAUIndex, first: AU) -> bool {
        &&& self.wf()
        &&& self.disk_view.wf_addrs()
        &&& self.disk_view.pointer_is_upstream(self.freshest_rec, first)
        &&& self.disk_view.bounded_inactive_lsns(index, self.freshest_rec)
        &&& index == self.build_lsn_au_index_from_first(first)
    }

    pub open spec(checked) fn valid_subrange(self, index: LsnAUIndex, first: AU,
        sub_start: LSN, sub_freshest_rec: Pointer, sub_first: AU) -> bool
        recommends self.valid_structure(index, first)
    {
        let dv = self.disk_view;
        let sub_tj = dv.tj_at(sub_freshest_rec);

        &&& self.seq_start() <= sub_start
        &&& dv.decodable(sub_freshest_rec)
        &&& sub_freshest_rec is Some ==> sub_tj.seq_end() <= self.seq_end()
        &&& sub_freshest_rec is Some ==> sub_start < sub_tj.seq_end()
        &&& sub_freshest_rec is Some ==> {
            &&& index.contains_key(sub_start) 
            &&& index[sub_start] == sub_first
        }
    }

    pub proof fn subrange_preserves_pointer_is_upstream(self: Self, index: LsnAUIndex, first: AU, 
        sub_start: LSN, sub_freshest_rec: Pointer, sub_first: AU)
    requires 
        self.valid_structure(index, first),
        self.valid_subrange(index, first, sub_start, sub_freshest_rec, sub_first),
    ensures 
        self.disk_view.discard_old(sub_start).pointer_is_upstream(sub_freshest_rec, sub_first)
    {
        let dv = self.disk_view;
        let sub_dv = self.disk_view.discard_old(sub_start);

        assert(sub_dv.decodable(sub_freshest_rec));
        assert(sub_dv.valid_ranking(dv.the_ranking()));
        assert(sub_dv.acyclic());

        assert(sub_dv.internal_au_pages_fully_linked()) by {
            reveal(DiskView::pages_allocated_in_lsn_order);

        }

        assert(sub_dv.has_unique_lsns()) by {
            assert(forall|lsn, addr| sub_dv.addr_supports_lsn(addr, lsn) 
                ==> dv.addr_supports_lsn(addr, lsn));
        }

        if sub_freshest_rec is Some {
            self.build_lsn_au_index_from_first_ensures(first);
            assert(index.contains_key(sub_start));
            let first_addr = dv.instantiate_index_keys_exist_valid_entries(index, sub_start);
            assert(sub_dv.addr_supports_lsn(first_addr, sub_start));
        }
    }

    pub proof fn sub_disk_preserves_pointer_is_upstream(self: Self, index: LsnAUIndex, first: AU,
        sub_start: LSN, sub_freshest_rec: Pointer, sub_first: AU) -> (sub_dv: DiskView)
    requires 
        self.valid_structure(index, first),
        self.valid_subrange(index, first, sub_start, sub_freshest_rec, sub_first),
    ensures
        ({
            let dv = self.disk_view;
            let sub_end = dv.tj_at(sub_freshest_rec).seq_end();
            let sub_lsns = Set::new(|lsn| sub_start <= lsn < sub_end);
            let sub_domain = dv.tight_domain(index.restrict(sub_lsns), sub_freshest_rec);
            &&& sub_dv == DiskView{boundary_lsn: sub_start, entries: dv.entries.restrict(sub_domain)}
            &&& sub_dv.decodable(sub_freshest_rec)
            &&& sub_dv.acyclic()
            &&& sub_dv.internal_au_pages_fully_linked()
            &&& sub_dv.has_unique_lsns()
            &&& sub_dv.pointer_is_upstream(sub_freshest_rec, sub_first)
            &&& sub_dv.build_lsn_au_index_au_walk(sub_freshest_rec, sub_first) == index.restrict(sub_lsns)
        })
    {
        let dv = self.disk_view;
        let sub_end = dv.tj_at(sub_freshest_rec).seq_end();
        let sub_lsns = Set::new(|lsn| sub_start <= lsn < sub_end);
        let sub_index = index.restrict(sub_lsns);

        let sub_domain = dv.tight_domain(sub_index, sub_freshest_rec);
        let sub_dv = DiskView{boundary_lsn: sub_start, entries: dv.entries.restrict(sub_domain)}; 

        self.build_lsn_au_index_from_first_ensures(first);

        reveal(DiskView::pages_allocated_in_lsn_order);

        assert forall|addr| #[trigger] sub_dv.entries.contains_key(addr)
        implies sub_dv.is_nondangling_pointer(
            sub_dv.entries[addr].cropped_prior(sub_dv.boundary_lsn),
        ) by {
            let head = dv.entries[addr];
            let prior_ptr = head.cropped_prior(sub_dv.boundary_lsn);
            if prior_ptr is Some {
                if addr.au == prior_ptr.unwrap().au {
                    if addr.after_page(prior_ptr.unwrap()) {
                        assert(false);
                    }
                } else {
                    let lsn = head.message_seq.seq_start;
                    // equivalent to dv.entries[prior_ptr.unwrap()].message_seq.seq_end
                    let prior_lsn = (lsn - 1) as nat;
                    assert(sub_dv.boundary_lsn < lsn);
                    reveal(DiskView::index_keys_exist_valid_entries);

                    if sub_index.contains_key(lsn) {
                        assert(sub_index.contains_key(prior_lsn));
                        assert(dv.addr_supports_lsn(prior_ptr.unwrap(), prior_lsn));
                        assert(sub_dv.is_nondangling_pointer(prior_ptr));
                    } else if index.contains_key(lsn) {
                        assert(lsn >= sub_end);
                        let in_range = choose |in_range| #[trigger] sub_index.contains_key(in_range) && sub_index[in_range] == addr.au;
                        assert(in_range <= prior_lsn <= lsn);
                        assert(index.contains_key(in_range));
                        assert(index[in_range] == addr.au);
                        assert(index[lsn] == addr.au);
                        assert(index[prior_lsn] == addr.au); // prior_lsn also == next_ptr.unwrap().au
                        assert(false);
                    } else {
                        assert(dv.entries[addr].message_seq.contains(lsn)); // trigger
                        assert(lsn < sub_dv.boundary_lsn);
                        assert(false);
                    }
                }
            }
        }

        assert(sub_dv.nondangling_pointers());

        if sub_freshest_rec is Some {
            let last_lsn = (sub_end - 1) as nat;
            assert(dv.addr_supports_lsn(sub_freshest_rec.unwrap(), last_lsn));
            dv.addr_supports_lsn_consistent_with_index(index, last_lsn, sub_freshest_rec.unwrap());
            assert(sub_index.contains_key(last_lsn)); // trigger
            assert(sub_dv.is_nondangling_pointer(sub_freshest_rec));

            // valid first_au
            assert(index.contains_key(sub_start));
            let first_addr = dv.instantiate_index_keys_exist_valid_entries(index, sub_start);
            assert(first_addr.au == index[sub_start]);
            assert(sub_index.contains_key(sub_start));
            assert(sub_dv.addr_supports_lsn(first_addr, sub_start));
            assert(sub_dv.valid_first_au(index[sub_start]));
        }

        assert(sub_dv.decodable(sub_freshest_rec));
        assert(sub_dv.valid_ranking(dv.the_ranking()));
        assert(sub_dv.acyclic());
        assert(sub_dv.internal_au_pages_fully_linked());
        assert(sub_dv.has_unique_lsns()) by {
            assert(forall|lsn, addr|
                sub_dv.addr_supports_lsn(addr, lsn) ==> dv.addr_supports_lsn(addr, lsn));
        }

        assert(sub_dv.pointer_is_upstream(sub_freshest_rec, sub_first));

        let sub_tj = TruncatedJournal{disk_view: sub_dv, freshest_rec: sub_freshest_rec};
        sub_tj.build_lsn_au_index_from_first_ensures(sub_first);
        if sub_freshest_rec is Some {
            sub_tj.sub_disk_build_sub_lsn_au_index(sub_first, self, first);
            assert(sub_tj.build_lsn_au_index_from_first(sub_first).dom() =~= sub_index.dom());
        }
        assert(sub_tj.build_lsn_au_index_from_first(sub_first) =~= sub_index);
        sub_dv
    }

    pub proof fn sub_disk_preserves_bounded_inactive_lsns(self: Self, index: LsnAUIndex, first: AU,
        sub_tj: Self, sub_first: AU)
    requires
        self.valid_structure(index, first),
        sub_tj.disk_view.pointer_is_upstream(sub_tj.freshest_rec, sub_first),
        self.seq_start() <= sub_tj.seq_start(),
        sub_tj.seq_end() <= self.seq_end(),
        sub_tj.disk_view.is_sub_disk_with_newer_lsn(self.disk_view),
    ensures
        sub_tj.disk_view.bounded_inactive_lsns(sub_tj.build_lsn_au_index_from_first(sub_first), sub_tj.freshest_rec)
    {
        let dv = self.disk_view;
        let sub_dv = sub_tj.disk_view;
        let sub_index = sub_tj.build_lsn_au_index_from_first(sub_first);

        assert(forall |addr| sub_dv.entries.contains_key(addr) ==> dv.entries.contains_key(addr));
        assert(sub_dv.wf_addrs());

        sub_tj.build_lsn_au_index_from_first_ensures(sub_first);
        sub_tj.sub_disk_build_sub_lsn_au_index(sub_first, self, first);
        assert(sub_index <= index);

        assert forall|addr, lsn|
            ({
                &&& sub_dv.entries.dom().contains(addr)
                &&& sub_dv.entries[addr].message_seq.contains(lsn)
                &&& sub_index.values().contains(addr.au) 
                &&& !sub_index.contains_key(lsn)
                &&& sub_tj.freshest_rec is Some ==> !sub_tj.freshest_rec.unwrap().after_page(addr)
            })
        implies lsn < sub_dv.boundary_lsn
        by {
            let in_range_lsn = choose |in_range_lsn| sub_index.contains_key(in_range_lsn) 
                && #[trigger] sub_index[in_range_lsn] == addr.au;
            assert(index.contains_key(in_range_lsn));
            assert(index[in_range_lsn] == addr.au);
            assert(sub_tj.freshest_rec is Some);

            if lsn >= sub_tj.seq_end() {
                let last_lsn = (sub_tj.seq_end() - 1) as nat;
                self.build_lsn_au_index_from_first_ensures(first);
                assert(index.contains_key(last_lsn)); // trigger
                assert(dv.entries.contains_key(sub_tj.freshest_rec.unwrap())); // trigger
                dv.addr_supports_lsn_consistent_with_index(index, last_lsn, sub_tj.freshest_rec.unwrap());

                assert(addr.au != sub_tj.freshest_rec.unwrap().au) by {
                    reveal(DiskView::pages_allocated_in_lsn_order);

                }

                if index.contains_key(lsn) {
                    assert(dv.entries.contains_key(addr));
                    assert(dv.entries[addr].contains_lsn(dv.boundary_lsn, lsn));
                    dv.addr_supports_lsn_consistent_with_index(index, lsn, addr);
                    assert(contiguous_lsns(index, in_range_lsn, last_lsn, lsn));
                    assert(index[last_lsn] == addr.au);
                    assert(false);
                } else {
                    assert(self.freshest_rec is Some);
                    if self.freshest_rec.unwrap().after_page(addr) {
                        let end = (self.seq_end() - 1) as nat;
                        assert(index.contains_key(end));
                        dv.addr_supports_lsn_consistent_with_index(index, end, self.freshest_rec.unwrap());
                        assert(in_range_lsn <= last_lsn <= end);
                        assert(contiguous_lsns(index, in_range_lsn, last_lsn, end));
                        assert(index[last_lsn] == addr.au);
                        assert(false);
                    } 
                    assert(dv.entries.dom().contains(addr)); // trigger
                    assert(lsn < dv.boundary_lsn);
                    assert(lsn < sub_dv.boundary_lsn);
                }
            }
        }
    }
}

impl MiniAllocator {
    // next address for root
    pub open spec(checked) fn tight_next_addr(self, root: Pointer, addr: Address) -> bool {
        &&& self.can_allocate(addr)
        &&& (self.curr is None ==> {
            &&& self.allocs[addr.au].all_pages_free()
            &&& addr.page == 0
        })
        &&& (self.curr is Some && root is Some ==> addr == root.unwrap().next())
    }
}

state_machine!{ AllocationJournal {
    fields {
        // Root pointer into the single allocation-owned backing disk.
        pub freshest_rec: Pointer,
        pub unmarshalled_tail: MsgHistory,

        // Allocation-owned backing view. This may contain unreachable junk records
        // in owned AUs.
        pub disk_view: DiskView,

        // lsnAUAddrIndex maps in-repr lsn's to their AU addr
        pub lsn_au_index: LsnAUIndex,

        // Upper page bound for every semantically visible journal AU.
        // Lower cropping is represented by disk_view.boundary_lsn.
        pub au_page_bounds: AUPageBounds,

        pub mini_allocator: MiniAllocator,
    }

    pub enum Label
    {
        ReadForRecovery{messages: MsgHistory},
        FreezeForCommit{frozen_journal: JournalMetadata},
        QueryEndLsn{end_lsn: LSN},
        Put{messages: MsgHistory},
        DiscardOld{start_lsn: LSN, require_end: LSN, deallocs: Set<AU>},
        InternalAllocations{allocs: Set<AU>, deallocs: Set<AU>},
    }

    pub open spec(checked) fn wf(self) -> bool {
        &&& self.unmarshalled_tail.wf()
        &&& self.disk_view.wf_addrs()
        &&& self.mini_allocator.wf()
    }

    pub open spec(checked) fn semantic_wf(self) -> bool {
        let semantic_dv = self.tj().disk_view;
        &&& self.disk_view.path_decodable(self.freshest_rec)
        &&& semantic_dv.wf()
        &&& semantic_dv.acyclic()
        &&& semantic_dv.is_nondangling_pointer(self.freshest_rec)
        &&& semantic_dv.block_in_bounds(self.freshest_rec)
        &&& self.unmarshalled_tail.wf()
        &&& semantic_dv.seq_start() <= semantic_dv.seq_end(self.freshest_rec)
        &&& semantic_dv.seq_end(self.freshest_rec) == self.unmarshalled_tail.seq_start
        &&& self.disk_view.wf_addrs()
        &&& self.mini_allocator.wf()
    }

    pub open spec(checked) fn accessible_aus(self) -> Set<AU> {
        to_aus(self.disk_view.entries.dom()) + self.mini_allocator.allocs.dom()
    }

    transition!{ read_for_recovery(lbl: Label, start_lsn: LSN, addr: Address) {
        require let Label::ReadForRecovery{messages} = lbl;

        let record = pre.disk_view.entries[addr];
        let cropped = record.message_seq.maybe_discard_old(pre.seq_start());

        require pre.disk_view.entries.contains_key(addr);
        require pre.au_page_bounds.contains_key(addr.au);
        require addr.page <= pre.au_page_bounds[addr.au];
        require pre.seq_start() < record.message_seq.seq_end;
        require start_lsn == cropped.seq_start;
        require start_lsn < record.message_seq.seq_end;
        require pre.lsn_au_index.contains_key(start_lsn);
        require pre.lsn_au_index[start_lsn] == addr.au;
        require messages == cropped;
    } }

    transition!{ freeze_for_commit(lbl: Label) {
        require lbl is FreezeForCommit;

        let frozen_journal = lbl->frozen_journal;
        let new_bdy = frozen_journal.boundary_lsn;
        let frozen_root = frozen_journal.freshest_rec;

        require pre.frozen_metadata_valid(frozen_journal);
        require frozen_root is None ==> {
            &&& frozen_journal.boundary_lsn == frozen_journal.seq_end
            &&& new_bdy <= pre.seq_end()
        };
    } }

    transition!{ query_end_lsn(lbl: Label) {
        require lbl is QueryEndLsn;
        require lbl->end_lsn == pre.seq_end();
    } }

    transition!{ put(lbl: Label) {
        require let Label::Put{messages} = lbl;
        require messages.wf();
        require messages.seq_start == pre.seq_end();
        update unmarshalled_tail = pre.unmarshalled_tail.concat(messages);
    } }

    transition!{ discard_old(lbl: Label) {
        require lbl is DiscardOld;

        let start_lsn = lbl->start_lsn;
        let require_end = lbl->require_end;
        let deallocs = lbl.arrow_DiscardOld_deallocs();

        require require_end == pre.seq_end();
        require pre.seq_start() <= start_lsn <= require_end;

        let new_lsn_au_index = lsn_au_index_discard_up_to(pre.lsn_au_index, start_lsn);
        let discarded_aus = pre.lsn_au_index.values().difference(new_lsn_au_index.values());
        let post_freshest_rec =
            if start_lsn < pre.marshalled_seq_end() { pre.freshest_rec } else { None };
        let post_disk_view = DiskView{
            boundary_lsn: start_lsn,
            ..Self::disk_view_without_aus(pre.disk_view, discarded_aus)
        };

        require deallocs == discarded_aus;

        update freshest_rec = post_freshest_rec;
        update unmarshalled_tail = pre.unmarshalled_tail.bounded_discard(start_lsn);
        update disk_view = post_disk_view;
        update lsn_au_index = new_lsn_au_index;
        update au_page_bounds = Self::au_page_bounds_restrict(pre.au_page_bounds, new_lsn_au_index.values());
        update mini_allocator = pre.mini_allocator.prune(discarded_aus);
        // note that these AUs refine to free (in the frozen freeset)
    } }

    transition!{ internal_journal_marshal(lbl: Label, cut: LSN, addr: Address) {
        require lbl is InternalAllocations;
        require lbl->allocs == Set::<AU>::empty();
        require lbl.arrow_InternalAllocations_deallocs() == Set::<AU>::empty();
        require pre.mini_allocator.tight_next_addr(pre.freshest_rec, addr);

        require pre.unmarshalled_tail.seq_start < cut;
        require pre.unmarshalled_tail.can_discard_to(cut);
        let marshalled_msgs = pre.unmarshalled_tail.discard_recent(cut);

        update freshest_rec = Some(addr);
        update unmarshalled_tail = pre.unmarshalled_tail.discard_old(cut);
        update disk_view = DiskView{
            entries: pre.disk_view.entries.insert(addr, LinkedJournal_v::JournalRecord {
                message_seq: marshalled_msgs,
                prior_rec: pre.freshest_rec,
            }),
            ..pre.disk_view
        };
        update lsn_au_index = lsn_au_index_append_record(pre.lsn_au_index, marshalled_msgs, addr.au);
        update au_page_bounds = pre.au_page_bounds.insert(addr.au, addr.page);
        update mini_allocator = pre.mini_allocator.allocate(addr);
    } }

    transition!{ internal_mini_allocator_fill(lbl: Label, post_disk_view: DiskView) {
        require lbl is InternalAllocations;
        require let Label::InternalAllocations{allocs, deallocs} = lbl;
        require deallocs == Set::<AU>::empty();
        require allocs.disjoint(pre.mini_allocator.allocs.dom());
        require allocs.disjoint(pre.lsn_au_index.values());

        let post_allocator = pre.mini_allocator.add_aus(allocs);
        require post_disk_view.wf_addrs();
        require pre.disk_view.is_sub_disk(post_disk_view);
        require Self::disk_domain_bounded_by_owned_aus(
            post_disk_view,
            pre.lsn_au_index,
            post_allocator,
        );
        require forall |addr: Address| {
            &&& #[trigger] post_disk_view.entries.contains_key(addr)
            &&& !pre.disk_view.entries.contains_key(addr)
        } ==> allocs.contains(addr.au);

        update disk_view = post_disk_view;
        update mini_allocator = pre.mini_allocator.add_aus(allocs);
    } }

    transition!{ internal_mini_allocator_prune(lbl: Label, prune_aus: Set<AU>) {
        require lbl is InternalAllocations;
        require lbl->allocs == Set::<AU>::empty();
        let deallocs = lbl.arrow_InternalAllocations_deallocs();
        require deallocs <= prune_aus;
        require forall |au| #![auto] prune_aus.contains(au) ==> {
            &&& pre.mini_allocator.can_remove(au)
        };
        require forall |au| #![auto] deallocs.contains(au) ==> {
            &&& pre.mini_allocator.allocs.contains_key(au)
            &&& pre.mini_allocator.allocs[au].all_pages_free()
        };
        require forall |addr: Address| {
            &&& #[trigger] pre.disk_view.entries.contains_key(addr)
            &&& prune_aus.contains(addr.au)
            &&& !deallocs.contains(addr.au)
        } ==> pre.lsn_au_index.values().contains(addr.au);

        update disk_view = Self::disk_view_without_aus(pre.disk_view, deallocs);
        update mini_allocator = pre.mini_allocator.prune(prune_aus);
    } }

    transition!{ internal_no_op(lbl: Label) {
        require lbl is InternalAllocations;
        require lbl->allocs == Set::<AU>::empty();
        require lbl.arrow_InternalAllocations_deallocs() == Set::<AU>::empty();
    } }

    init!{ initialize(image: JournalImage) {
        require image.valid_image();
        let mini_allocator = MiniAllocator::empty();
        init freshest_rec = image.tj.freshest_rec;
        init unmarshalled_tail = MsgHistory::empty_history_at(image.tj.seq_end());
        init disk_view = image.tj.disk_view;
        init lsn_au_index = image.tj.disk_view.loose_build_lsn_au_index_au_walk(image.tj.freshest_rec, image.first);
        init au_page_bounds = image.tj.disk_view.loose_build_au_page_bounds_au_walk(image.tj.freshest_rec, image.first);
        init mini_allocator = mini_allocator;
    } }

    //////////////////////////////////////////////////////////////////////////////
    // AllocationJournalRefinement stuff
    //

    pub open spec(checked) fn au_page_bounds_restrict(bounds: AUPageBounds, aus: Set<AU>) -> AUPageBounds
    {
        Map::new(
            |au| bounds.contains_key(au) && aus.contains(au),
            |au| bounds[au],
        )
    }

    pub open spec(checked) fn au_page_bounds_match_index(self) -> bool
    {
        self.au_page_bounds.dom() =~= self.lsn_au_index.values()
    }

    pub open spec(checked) fn au_page_bounds_follow_freshest_rec(self) -> bool
    {
        self.freshest_rec is Some ==> {
            let root = self.freshest_rec.unwrap();
            &&& self.au_page_bounds.contains_key(root.au)
            &&& self.au_page_bounds[root.au] == root.page
        }
    }

    pub open spec(checked) fn lsn_au_index_before_tail(self) -> bool
    {
        forall |lsn: LSN| #[trigger] self.lsn_au_index.contains_key(lsn)
            ==> lsn < self.unmarshalled_tail.seq_start
    }

    pub open spec fn tj(self) -> TruncatedJournal
    {
        TruncatedJournal{
            freshest_rec: self.freshest_rec,
            disk_view: self.disk_view.path_build_tight(self.freshest_rec),
        }
    }

    pub open spec(checked) fn seq_start(self) -> LSN
    {
        self.disk_view.boundary_lsn
    }

    pub open spec(checked) fn seq_end(self) -> LSN
    {
        self.unmarshalled_tail.seq_end
    }

    pub open spec(checked) fn marshalled_seq_end(self) -> LSN
    {
        if self.freshest_rec is Some && self.disk_view.entries.contains_key(self.freshest_rec.unwrap()) {
            self.disk_view.entries[self.freshest_rec.unwrap()].message_seq.seq_end
        } else {
            self.seq_start()
        }
    }

    pub open spec(checked) fn mini_allocator_follows_freshest_rec(root: Pointer, allocator: MiniAllocator) -> bool
    {
        allocator.curr is Some ==> {
            &&& root is Some
            &&& root.unwrap().au == allocator.curr.unwrap()
            // &&& forall |addr| freshest_rec.unwrap().after_page(addr) ==> #[trigger] allocator.can_allocate(addr)
        }
    }

    pub open spec(checked) fn disk_domain_bounded_by_owned_aus(
        dv: DiskView,
        lsn_au_index: LsnAUIndex,
        allocator: MiniAllocator,
    ) -> bool
    {
        forall |addr| #[trigger] dv.entries.dom().contains(addr) ==> {
            ||| lsn_au_index.values().contains(addr.au)
            ||| allocator.all_aus().contains(addr.au)
        }
    }

    pub open spec(checked) fn disk_view_without_aus(dv: DiskView, aus: Set<AU>) -> DiskView
    {
        DiskView{
            entries: Map::new(
                |addr: Address| dv.entries.contains_key(addr) && !aus.contains(addr.au),
                |addr: Address| dv.entries[addr],
            ),
            ..dv
        }
    }

    pub open spec(checked) fn disk_domain_not_free(dv: DiskView, allocator: MiniAllocator) -> bool
    {
        forall |addr| #[trigger] dv.entries.dom().contains(addr) ==> {
            &&& !allocator.can_allocate(addr)
        }
    }

    pub open spec(checked) fn bounded_live_entries_are_semantic(self) -> bool
    {
        forall |addr: Address| {
            &&& #[trigger] self.disk_view.entries.contains_key(addr)
            &&& self.au_page_bounds.contains_key(addr.au)
            &&& addr.page <= self.au_page_bounds[addr.au]
            &&& self.disk_view.boundary_lsn < self.disk_view.entries[addr].message_seq.seq_end
        } ==> self.tj().disk_view.entries.contains_key(addr)
    }

    pub open spec fn indexed_lsn_witnesses_are_semantic(self) -> bool
    {
        forall |addr: Address, lsn: LSN|
            #![trigger self.disk_view.entries.contains_key(addr), self.lsn_au_index.contains_key(lsn)]
        {
            let record = self.disk_view.entries[addr];
            &&& self.disk_view.entries.contains_key(addr)
            &&& self.au_page_bounds.contains_key(addr.au)
            &&& addr.page <= self.au_page_bounds[addr.au]
            &&& self.seq_start() < record.message_seq.seq_end
            &&& record.message_seq.contains(lsn)
            &&& self.lsn_au_index.contains_key(lsn)
            &&& self.lsn_au_index[lsn] == addr.au
        } ==> self.tj().disk_view.entries.contains_key(addr)
    }

    pub open spec(checked) fn semantic_entries_bounded_by_au_page_bounds(self) -> bool
    {
        forall |addr: Address| #[trigger] self.tj().disk_view.entries.contains_key(addr) ==> {
            &&& self.au_page_bounds.contains_key(addr.au)
            &&& addr.page <= self.au_page_bounds[addr.au]
        }
    }

    pub open spec(checked) fn au_page_bounds_covered(self) -> bool
    {
        forall |addr: Address| {
            &&& #[trigger] self.lsn_au_index.values().contains(addr.au)
            &&& self.au_page_bounds.contains_key(addr.au)
            &&& addr.page <= self.au_page_bounds[addr.au]
        } ==> self.disk_view.entries.contains_key(addr)
    }

    pub proof fn indexed_au_page_bound_addr_in_disk_image(self, addr: Address)
        requires
            self.semantic_inv(),
            self.lsn_au_index.values().contains(addr.au),
            self.au_page_bounds.contains_key(addr.au),
            addr.page <= self.au_page_bounds[addr.au],
        ensures
            self.disk_view.entries.contains_key(addr),
    {
        assert(self.au_page_bounds_covered());
    }

    pub open spec(checked) fn indexed_aus_not_all_pages_free(self) -> bool
    {
        forall |au: AU| {
            &&& #[trigger] self.lsn_au_index.values().contains(au)
            &&& self.mini_allocator.allocs.contains_key(au)
        } ==> !self.mini_allocator.allocs[au].all_pages_free()
    }

    pub open spec(checked) fn valid_acyclic_subdisk(self, sub_disk: DiskView) -> bool
    {
        &&& sub_disk.is_sub_disk(self.disk_view)
        &&& sub_disk.wf()
        &&& sub_disk.acyclic()
        &&& sub_disk.is_nondangling_pointer(self.freshest_rec)
        &&& sub_disk.block_in_bounds(self.freshest_rec)
    }

    pub open spec(checked) fn has_valid_acyclic_subdisk(self) -> bool
    {
        self.valid_acyclic_subdisk(self.tj().disk_view)
    }

    pub proof fn path_tj_matches_semantic_build_tight(self)
        requires
            self.has_valid_acyclic_subdisk(),
            self.disk_view.path_decodable(self.freshest_rec),
        ensures
            self.tj().wf(),
            self.tj().decodable(),
            self.tj().disk_view.is_sub_disk(self.disk_view),
    {
        let semantic = self.tj().disk_view;
        let semantic_tj = TruncatedJournal{
            freshest_rec: self.freshest_rec,
            disk_view: semantic,
        };
        let root = self.freshest_rec;

        assert(self.valid_acyclic_subdisk(semantic));
        assert(semantic.decodable(root));
        assert(self.tj().disk_view == semantic);
        assert(self.tj() == semantic_tj);
        assert(semantic_tj.wf());
        assert(semantic_tj.decodable());
        assert(self.tj().wf());
        assert(self.tj().decodable());
        self.disk_view.path_build_tight_is_sub_disk(root);
        assert(self.tj().disk_view.is_sub_disk(self.disk_view));
    }

    pub proof fn tj_view_is_valid_acyclic_subdisk(self)
        requires
            self.semantic_wf(),
        ensures
            self.valid_acyclic_subdisk(self.tj().disk_view),
            self.has_valid_acyclic_subdisk(),
            self.tj().wf(),
            self.tj().decodable(),
            self.tj().disk_view.is_sub_disk(self.disk_view),
    {
        self.disk_view.path_build_tight_is_sub_disk(self.freshest_rec);
        assert(self.tj().disk_view.is_sub_disk(self.disk_view));
        assert(self.tj().disk_view.wf());
        assert(self.tj().disk_view.acyclic());
        assert(self.tj().disk_view.is_nondangling_pointer(self.freshest_rec));
        assert(self.tj().disk_view.block_in_bounds(self.freshest_rec));
        assert(self.valid_acyclic_subdisk(self.tj().disk_view));
        self.path_tj_matches_semantic_build_tight();
    }

    pub proof fn tj_view_preserved_in_post_disk(pre: Self, post: Self)
        requires
            pre.semantic_inv(),
            post.freshest_rec == pre.freshest_rec,
            pre.tj().disk_view.is_sub_disk(post.disk_view),
        ensures
            post.disk_view.path_decodable(post.freshest_rec),
            post.tj().disk_view == pre.tj().disk_view,
            post.tj() == pre.tj(),
            post.tj().disk_view.is_sub_disk(post.disk_view),
    {
        let root = pre.freshest_rec;
        let pre_tight_dv = pre.tj().disk_view;

        assert(pre.disk_view.path_decodable(root));
        pre.disk_view.path_build_tight_path_decodable(root);
        pre.disk_view.path_build_tight_idempotent(root);
        assert(pre_tight_dv == pre.disk_view.path_build_tight(root));
        assert(pre_tight_dv.path_decodable(root));
        assert(pre_tight_dv.path_build_tight(root) == pre_tight_dv);
        pre_tight_dv.path_build_tight_preserved_in_superdisk(post.disk_view, root);
        assert(post.disk_view.path_build_tight(post.freshest_rec) == pre_tight_dv);
        assert(post.tj().disk_view == pre_tight_dv);
        assert(post.tj() == pre.tj());
    }

    pub open spec fn semantic_journal_structure(
        disk_view: DiskView,
        freshest_rec: Pointer,
        lsn_au_index: LsnAUIndex,
        first: AU,
    ) -> bool {
        &&& disk_view.internal_au_pages_fully_linked()
        &&& disk_view.has_unique_lsns()
        &&& freshest_rec is Some ==> disk_view.valid_first_au(first)
        &&& disk_view.domain_au_bounded_wrt_index(lsn_au_index)
        &&& disk_view.bounded_inactive_lsns(lsn_au_index, freshest_rec)
        &&& lsn_au_index == disk_view.build_lsn_au_index_au_walk(freshest_rec, first)
    }

    pub open spec fn frozen_lsns(self, frozen: JournalMetadata) -> Set<LSN>
    {
        Set::new(|lsn: LSN| frozen.boundary_lsn <= lsn < frozen.seq_end)
    }

    pub open spec fn frozen_lsn_au_index(self, frozen: JournalMetadata) -> LsnAUIndex
    {
        self.lsn_au_index.restrict(self.frozen_lsns(frozen))
    }

    pub open spec fn frozen_domain(self, frozen: JournalMetadata) -> Set<Address>
    {
        addrs_in_aus(self.frozen_lsn_au_index(frozen).values())
    }

    pub open spec fn frozen_loose_domain(self, frozen: JournalMetadata) -> Set<Address>
    {
        self.frozen_domain(frozen)
    }

    pub open spec fn frozen_prefix_domain(self, frozen: JournalMetadata) -> Set<Address>
    {
        let tight = self.frozen_image(frozen).tight_tj();
        let tight_bounds = tight.disk_view.build_au_page_bounds_au_walk(
            tight.freshest_rec,
            frozen.first,
        );
        Set::new(|addr: Address| {
            &&& self.frozen_loose_domain(frozen).contains(addr)
            &&& tight_bounds.contains_key(addr.au)
            &&& addr.page <= tight_bounds[addr.au]
        })
    }

    pub open spec fn frozen_tj(self, frozen: JournalMetadata) -> TruncatedJournal
    {
        TruncatedJournal{
            freshest_rec: frozen.freshest_rec,
            disk_view: DiskView{
                boundary_lsn: frozen.boundary_lsn,
                entries: self.disk_view.entries.restrict(self.frozen_domain(frozen)),
            },
        }
    }

    pub open spec fn frozen_image(self, frozen: JournalMetadata) -> JournalImage
    {
        JournalImage{tj: self.frozen_tj(frozen), first: frozen.first}
    }

    pub open spec fn acceptable_frozen_image(
        self,
        frozen: JournalMetadata,
        image: JournalImage,
    ) -> bool
    {
        &&& image.valid_image()
        &&& image.first == frozen.first
        &&& image.tj.freshest_rec == frozen.freshest_rec
        &&& image.tj.disk_view.boundary_lsn == frozen.boundary_lsn
        &&& image.tj.seq_end() == frozen.seq_end
        &&& image.tj.disk_view.entries.dom() <= self.frozen_loose_domain(frozen)
        &&& maps_agree_on(
            self.frozen_prefix_domain(frozen),
            image.tj.disk_view.entries,
            self.disk_view.entries,
        )
    }

    pub open spec(checked) fn frozen_metadata_valid(self, frozen: JournalMetadata) -> bool
    {
        &&& self.seq_start() <= frozen.boundary_lsn <= frozen.seq_end <= self.seq_end()
        &&& frozen.freshest_rec is None ==> {
            &&& frozen.first == 0
            &&& frozen.boundary_lsn == frozen.seq_end
        }
        &&& frozen.freshest_rec is Some ==> {
            let root = frozen.freshest_rec.unwrap();
            &&& frozen.boundary_lsn < frozen.seq_end
            &&& self.lsn_au_index.contains_key(frozen.boundary_lsn)
            &&& self.lsn_au_index[frozen.boundary_lsn] == frozen.first
            &&& self.lsn_au_index.contains_key((frozen.seq_end - 1) as nat)
            &&& self.lsn_au_index[(frozen.seq_end - 1) as nat] == root.au
            &&& self.disk_view.entries.contains_key(root)
            &&& self.disk_view.entries[root].message_seq.seq_end == frozen.seq_end
            &&& self.disk_view.entries[root].message_seq.contains((frozen.seq_end - 1) as nat)
            &&& self.au_page_bounds.contains_key(root.au)
            &&& root.page <= self.au_page_bounds[root.au]
        }
    }

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.wf()
        &&& self.lsn_au_index_before_tail()
        &&& Self::disk_domain_bounded_by_owned_aus(
            self.disk_view,
            self.lsn_au_index,
            self.mini_allocator,
        )
    }

    pub open spec fn semantic_inv(self) -> bool {
        let semantic_dv = self.tj().disk_view;
        let first = if self.freshest_rec is Some {
            self.lsn_au_index[self.seq_start()]
        } else {
            0
        };
        let computed_index = semantic_dv.build_lsn_au_index_au_walk(self.freshest_rec, first);
        &&& self.wf()
        &&& self.semantic_wf()
        &&& semantic_dv.decodable(self.freshest_rec)
        &&& semantic_dv.wf_addrs()
        &&& self.au_page_bounds_match_index()
        &&& self.au_page_bounds_follow_freshest_rec()
        &&& self.freshest_rec is Some ==> self.lsn_au_index.contains_key(self.seq_start())
        &&& Self::semantic_journal_structure(semantic_dv, self.freshest_rec, computed_index, first)
        &&& self.lsn_au_index == computed_index
        &&& self.has_valid_acyclic_subdisk()
        &&& self.tj().disk_view.domain_tight_wrt_index(self.lsn_au_index, self.freshest_rec)
        &&& Self::disk_domain_bounded_by_owned_aus(
            self.disk_view,
            self.lsn_au_index,
            self.mini_allocator,
        )
        &&& Self::disk_domain_not_free(semantic_dv, self.mini_allocator)
        &&& Self::mini_allocator_follows_freshest_rec(self.freshest_rec, self.mini_allocator)
        &&& self.bounded_live_entries_are_semantic()
        &&& self.indexed_lsn_witnesses_are_semantic()
        &&& self.semantic_entries_bounded_by_au_page_bounds()
        &&& self.au_page_bounds_covered()
        &&& self.indexed_aus_not_all_pages_free()
    }

    pub proof fn semantic_entry_not_after_freshest(self, addr: Address)
        requires
            self.semantic_inv(),
            self.tj().disk_view.entries.contains_key(addr),
        ensures
            self.freshest_rec is Some ==> !self.freshest_rec.unwrap().after_page(addr),
    {
        assert(self.tj().disk_view.domain_tight_wrt_index(self.lsn_au_index, self.freshest_rec));
        assert(self.tj().disk_view.entries.dom().contains(addr));
        if self.freshest_rec is Some {
            assert(!self.freshest_rec.unwrap().after_page(addr));
        }
    }

    pub proof fn tj_inherits_semantic_structure(self)
        requires
            self.semantic_inv(),
        ensures
            self.tj().decodable(),
            ({
                let first = if self.freshest_rec is Some {
                    self.lsn_au_index[self.seq_start()]
                } else {
                    0
                };
                &&& self.tj().disk_view.pointer_is_upstream(self.freshest_rec, first)
                &&& self.tj().disk_view.domain_au_bounded_wrt_index(self.lsn_au_index)
                &&& self.tj().disk_view.bounded_inactive_lsns(self.lsn_au_index, self.freshest_rec)
                &&& self.lsn_au_index == self.tj().build_lsn_au_index_from_first(first)
            }),
            Self::disk_domain_not_free(self.tj().disk_view, self.mini_allocator),
    {
        let first = if self.freshest_rec is Some {
            self.lsn_au_index[self.seq_start()]
        } else {
            0
        };
        let computed_index = self.tj().disk_view.build_lsn_au_index_au_walk(self.freshest_rec, first);
        assert(Self::semantic_journal_structure(self.tj().disk_view, self.freshest_rec, computed_index, first));
        assert(self.lsn_au_index == computed_index);
        assert(self.tj().disk_view.pointer_is_upstream(self.freshest_rec, first));
        assert(self.tj().disk_view.domain_au_bounded_wrt_index(self.lsn_au_index));
        assert(self.tj().disk_view.bounded_inactive_lsns(self.lsn_au_index, self.freshest_rec));
        self.tj().build_lsn_au_index_from_first_ensures(first);
        assert(self.lsn_au_index == self.tj().build_lsn_au_index_from_first(first));
        assert(self.tj().decodable());
        assert(Self::disk_domain_not_free(self.tj().disk_view, self.mini_allocator));
    }

    pub proof fn discard_old_tj_is_newer_subdisk(pre: Self, post: Self, lbl: Label)
        requires
            pre.semantic_inv(),
            post.inv(),
            Self::discard_old(pre, post, lbl),
        ensures
            post.semantic_inv(),
            post.tj().disk_view.is_sub_disk_with_newer_lsn(pre.tj().disk_view),
    {
        let start_lsn = lbl->start_lsn;
        let deallocs = lbl.arrow_DiscardOld_deallocs();
        let pre_first = if pre.tj().freshest_rec is Some {
            pre.lsn_au_index[pre.tj().seq_start()]
        } else {
            0
        };
        let post_first = if post.tj().freshest_rec is Some {
            post.lsn_au_index[post.tj().seq_start()]
        } else {
            0
        };

        pre.tj_inherits_semantic_structure();
        assert(pre.tj().disk_view.boundary_lsn <= post.tj().disk_view.boundary_lsn);

        if start_lsn < pre.tj().seq_end() {
            let pre_dv = pre.tj().disk_view;
            let new_tj = post.tj();
            assert(pre.tj().valid_structure(pre.lsn_au_index, pre_first));
            assert(new_tj.freshest_rec == pre.tj().freshest_rec);
            pre.tj().build_lsn_au_index_from_first_ensures(pre_first);

            assert(pre.lsn_au_index.contains_key(start_lsn));
            lsn_au_index_discard_up_to_ensures(pre.lsn_au_index, start_lsn);
            assert(post.lsn_au_index.contains_key(start_lsn));
            assert(post_first == post.lsn_au_index[start_lsn]);
            assert(post.lsn_au_index[start_lsn] == pre.lsn_au_index[start_lsn]);

            assert(pre.tj().valid_subrange(
                pre.lsn_au_index,
                pre_first,
                start_lsn,
                new_tj.freshest_rec,
                post_first,
            )) by {
                assert(pre.tj().seq_start() <= start_lsn);
                assert(pre_dv.decodable(new_tj.freshest_rec));
                assert(new_tj.freshest_rec is Some);
                assert(pre_dv.tj_at(new_tj.freshest_rec).seq_end() <= pre.tj().seq_end());
                assert(start_lsn < pre_dv.tj_at(new_tj.freshest_rec).seq_end());
            }

            let sub_dv = pre.tj().sub_disk_preserves_pointer_is_upstream(
                pre.lsn_au_index,
                pre_first,
                start_lsn,
                new_tj.freshest_rec,
                post_first,
            );
            let sub_tj = TruncatedJournal{freshest_rec: new_tj.freshest_rec, disk_view: sub_dv};
            let sub_end = pre_dv.tj_at(new_tj.freshest_rec).seq_end();
            let sub_lsns = Set::new(|lsn: LSN| start_lsn <= lsn < sub_end);
            let sub_index = pre.lsn_au_index.restrict(sub_lsns);
            let sub_domain = pre_dv.tight_domain(sub_index, new_tj.freshest_rec);
            lsn_au_index_discard_up_to_ensures(pre.lsn_au_index, start_lsn);
            pre.tj().build_lsn_au_index_from_first_ensures(pre_first);
            assert(sub_end == pre.tj().seq_end());
            assert(post.lsn_au_index =~= sub_index) by {
                assert forall |lsn: LSN| #[trigger] post.lsn_au_index.contains_key(lsn)
                    <==> sub_index.contains_key(lsn) by {
                    if post.lsn_au_index.contains_key(lsn) {
                        assert(pre.lsn_au_index.contains_key(lsn));
                        assert(start_lsn <= lsn);
                        assert(pre.tj().seq_start() <= lsn < pre.tj().seq_end());
                        assert(sub_lsns.contains(lsn));
                    }
                    if sub_index.contains_key(lsn) {
                        assert(pre.lsn_au_index.contains_key(lsn));
                        assert(sub_lsns.contains(lsn));
                        assert(start_lsn <= lsn);
                        assert(post.lsn_au_index.contains_key(lsn));
                    }
                }
                assert forall |lsn: LSN| #[trigger] post.lsn_au_index.contains_key(lsn)
                    implies post.lsn_au_index[lsn] == sub_index[lsn] by {
                }
            }
            assert(sub_dv == DiskView{
                boundary_lsn: start_lsn,
                entries: pre_dv.entries.restrict(sub_domain),
            });

            assert(sub_dv.entries <= post.disk_view.entries) by {
                assert forall |addr: Address| #[trigger] sub_dv.entries.contains_key(addr)
                    implies post.disk_view.entries.contains_key(addr)
                        && post.disk_view.entries[addr] == sub_dv.entries[addr] by {
                    assert(sub_domain.contains(addr));
                    assert(pre_dv.entries.contains_key(addr));
                    assert(pre.disk_view.entries.contains_key(addr));
                    assert(post.lsn_au_index.values().contains(addr.au));
                    assert(!deallocs.contains(addr.au));
                    assert(post.disk_view.entries.contains_key(addr));
                    assert(post.disk_view.entries[addr] == pre.disk_view.entries[addr]);
                    assert(pre_dv.entries[addr] == pre.disk_view.entries[addr]);
                }
            }
            post.disk_view.decodable_sub_disk_path_build_tight_matches_build_tight(
                sub_dv,
                new_tj.freshest_rec,
            );
            assert(post.tj().disk_view == post.disk_view.path_build_tight(new_tj.freshest_rec));
            assert(post.disk_view.path_build_tight(new_tj.freshest_rec)
                == sub_dv.build_tight(new_tj.freshest_rec));
            assert(post.tj() == sub_tj.build_tight());
            let tight_sub_dv = sub_dv.build_tight(new_tj.freshest_rec);
            sub_dv.build_tight_ensures(new_tj.freshest_rec);
            assert(tight_sub_dv.wf());
            assert(tight_sub_dv.is_sub_disk(sub_dv));
            tight_sub_dv.sub_disk_ranking(sub_dv);
            assert(tight_sub_dv.acyclic());
            assert(tight_sub_dv.internal_au_pages_fully_linked()) by {
                assert(tight_sub_dv.nonzero_pages_point_backward()) by {
                    assert forall |addr: Address|
                        ({
                            &&& addr.page != 0
                            &&& #[trigger] tight_sub_dv.entries.contains_key(addr)
                        }) implies tight_sub_dv.entries[addr].prior_rec == Some(addr.previous()) by {
                        assert(sub_dv.entries.contains_key(addr));
                        assert(tight_sub_dv.entries[addr] == sub_dv.entries[addr]);
                        assert(sub_dv.nonzero_pages_point_backward());
                    }
                }
                reveal(DiskView::pages_allocated_in_lsn_order);

                assert(tight_sub_dv.pages_allocated_in_lsn_order()) by {
                    assert forall |alo: Address, ahi: Address|
                        ({
                            &&& alo.au == ahi.au
                            &&& alo.page < ahi.page
                            &&& #[trigger] tight_sub_dv.entries.contains_key(alo)
                            &&& #[trigger] tight_sub_dv.entries.contains_key(ahi)
                        }) implies tight_sub_dv.entries[alo].message_seq.seq_end
                            <= tight_sub_dv.entries[ahi].message_seq.seq_start by {
                        assert(sub_dv.entries.contains_key(alo));
                        assert(sub_dv.entries.contains_key(ahi));
                        assert(tight_sub_dv.entries[alo] == sub_dv.entries[alo]);
                        assert(tight_sub_dv.entries[ahi] == sub_dv.entries[ahi]);
                        assert(sub_dv.pages_allocated_in_lsn_order());
                    }
                }
            }
            assert(tight_sub_dv.has_unique_lsns()) by {
                assert forall |lsn, addr1, addr2|
                    tight_sub_dv.addr_supports_lsn(addr1, lsn)
                    && tight_sub_dv.addr_supports_lsn(addr2, lsn)
                    implies addr1 == addr2 by {
                    assert(sub_dv.addr_supports_lsn(addr1, lsn));
                    assert(sub_dv.addr_supports_lsn(addr2, lsn));
                    assert(sub_dv.has_unique_lsns());
                }
            }
            if new_tj.freshest_rec is Some {
                assert(sub_dv.valid_first_au(post_first));
                let first_addr = choose |addr: Address| #![auto]
                    addr.au == post_first && sub_dv.addr_supports_lsn(addr, sub_dv.boundary_lsn);
                assert(sub_dv.entries.contains_key(first_addr));
                assert(!new_tj.freshest_rec.unwrap().after_page(first_addr)) by {
                    assert(sub_index.values().contains(first_addr.au));
                    assert(sub_dv.entries.contains_key(first_addr));
                }
                assert(sub_dv.boundary_lsn < sub_dv.entries[first_addr].message_seq.seq_end);
                sub_dv.boundary_crossing_entry_in_build_tight(
                    new_tj.freshest_rec,
                    post_first,
                    sub_index,
                    first_addr,
                );
                assert(tight_sub_dv.entries.contains_key(first_addr));
                assert(tight_sub_dv.entries[first_addr] == sub_dv.entries[first_addr]);
                assert(tight_sub_dv.boundary_lsn == sub_dv.boundary_lsn);
                assert(tight_sub_dv.addr_supports_lsn(first_addr, tight_sub_dv.boundary_lsn));
                assert(tight_sub_dv.valid_first_au(post_first));
                assert(tight_sub_dv.entries.contains_key(new_tj.freshest_rec.unwrap()));
                assert(tight_sub_dv.upstream(new_tj.freshest_rec.unwrap()));
            }
            assert(tight_sub_dv.pointer_is_upstream(new_tj.freshest_rec, post_first));
            let tight_sub_tj = TruncatedJournal{freshest_rec: new_tj.freshest_rec, disk_view: tight_sub_dv};
            let built_index = tight_sub_tj.build_lsn_au_index_from_first(post_first);
            assert(sub_tj.disk_view.pointer_is_upstream(sub_tj.freshest_rec, post_first));
            sub_tj.build_lsn_au_index_from_first_ensures(post_first);
            tight_sub_tj.build_lsn_au_index_from_first_ensures(post_first);
            sub_dv.build_lsn_au_index_equiv_page_walk(new_tj.freshest_rec, post_first);
            tight_sub_dv.build_lsn_au_index_equiv_page_walk(new_tj.freshest_rec, post_first);
            tight_sub_dv.build_lsn_au_index_page_walk_sub_disk(sub_dv, new_tj.freshest_rec);
            assert(sub_dv.build_lsn_au_index_page_walk(new_tj.freshest_rec)
                == tight_sub_dv.build_lsn_au_index_page_walk(new_tj.freshest_rec));
            assert(built_index == sub_index);
            assert(built_index == post.lsn_au_index);
            assert(tight_sub_dv.domain_au_bounded_wrt_index(built_index)) by {
                assert forall |addr: Address| #[trigger] tight_sub_dv.entries.dom().contains(addr)
                    implies built_index.values().contains(addr.au) by {
                    assert(sub_dv.entries.contains_key(addr));
                    assert(sub_dv.domain_au_bounded_wrt_index(sub_index));
                }
            }
            if new_tj.freshest_rec is Some {
                pre.tj().sub_disk_preserves_bounded_inactive_lsns(
                    pre.lsn_au_index,
                    pre_first,
                    sub_tj,
                    post_first,
                );
            }
            assert(tight_sub_dv.bounded_inactive_lsns(built_index, new_tj.freshest_rec)) by {
                assert forall |addr: Address, lsn: LSN|
                    ({
                        &&& tight_sub_dv.entries.dom().contains(addr)
                        &&& tight_sub_dv.entries[addr].message_seq.contains(lsn)
                        &&& built_index.values().contains(addr.au)
                        &&& !built_index.contains_key(lsn)
                        &&& new_tj.freshest_rec is Some ==> !new_tj.freshest_rec.unwrap().after_page(addr)
                    }) implies lsn < tight_sub_dv.boundary_lsn by {
                    assert(sub_dv.entries.contains_key(addr));
                    assert(tight_sub_dv.entries[addr] == sub_dv.entries[addr]);
                    assert(sub_dv.bounded_inactive_lsns(sub_index, new_tj.freshest_rec));
                }
            }
            assert(post.tj().disk_view == tight_sub_dv);
            assert(post.tj().disk_view.is_sub_disk(sub_dv));
            assert(sub_dv.is_sub_disk(post.disk_view));
            assert(post.tj().disk_view.is_sub_disk(post.disk_view)) by {
                DiskView::sub_disk_transitive_auto();
            }
            assert(post.tj().disk_view == tight_sub_dv);
            assert(post.tj().disk_view.decodable(post.freshest_rec));
            assert(post.tj().disk_view.acyclic());
            assert(post.tj().disk_view.block_in_bounds(post.freshest_rec));
            post.disk_view.sub_disk_decodable_implies_path_decodable(
                post.tj().disk_view,
                post.freshest_rec,
            );
            assert(post.disk_view.path_decodable(post.freshest_rec));
            assert(post.tj().disk_view.entries <= pre.tj().disk_view.entries) by {
                assert forall |addr: Address| #[trigger] post.tj().disk_view.entries.contains_key(addr)
                    implies pre.tj().disk_view.entries.contains_key(addr)
                        && post.tj().disk_view.entries[addr] == pre.tj().disk_view.entries[addr] by {
                    assert(sub_dv.entries.contains_key(addr));
                }
            }
        } else {
            post.disk_view.path_build_tight_none_empty();
            assert(post.tj().freshest_rec is None);
            assert(post.tj().disk_view.entries =~= Map::<Address, LinkedJournal_v::JournalRecord>::empty());
            assert(post.tj().disk_view.entries <= pre.tj().disk_view.entries);
            let ranking = Map::<Address, nat>::empty();
            assert(post.disk_view.path_valid_ranking(post.freshest_rec, ranking));
            assert(post.disk_view.path_decodable(post.freshest_rec));
            assert(post.tj().disk_view.wf());
            assert(post.tj().disk_view.valid_ranking(ranking));
            assert(post.tj().disk_view.acyclic());
        }
        assert(post.semantic_wf());
        if post.freshest_rec is Some {
            assert(post.lsn_au_index.contains_key(post.seq_start()));
        }
        assert(post.has_valid_acyclic_subdisk()) by {
            post.tj_view_is_valid_acyclic_subdisk();
        }
        assert(post.semantic_entries_bounded_by_au_page_bounds()) by {
            assert forall |addr: Address| #[trigger] post.tj().disk_view.entries.contains_key(addr) implies {
                &&& post.au_page_bounds.contains_key(addr.au)
                &&& addr.page <= post.au_page_bounds[addr.au]
            } by {
                if start_lsn < pre.tj().seq_end() {
                    assert(post.tj().disk_view.domain_tight_wrt_index(post.lsn_au_index, post.freshest_rec));
                    assert(post.lsn_au_index.values().contains(addr.au));
                    assert(post.au_page_bounds_match_index());
                    if post.freshest_rec is Some && post.freshest_rec.unwrap().after_page(addr) {
                        assert(false);
                    }
                } else {
                    assert(false);
                }
            }
        }
        assert(post.bounded_live_entries_are_semantic()) by {
            assert forall |addr: Address| ({
                let record = post.disk_view.entries[addr];
                &&& #[trigger] post.disk_view.entries.contains_key(addr)
                &&& post.au_page_bounds.contains_key(addr.au)
                &&& addr.page <= post.au_page_bounds[addr.au]
                &&& post.disk_view.boundary_lsn < record.message_seq.seq_end
            }) implies post.tj().disk_view.entries.contains_key(addr) by {
                if start_lsn < pre.tj().seq_end() {
                    let pre_dv = pre.tj().disk_view;
                    let root = post.freshest_rec;
                    let sub_lsns = Set::new(|lsn: LSN| start_lsn <= lsn < pre.tj().seq_end());
                    let sub_index = pre.lsn_au_index.restrict(sub_lsns);
                    let sub_domain = pre_dv.tight_domain(sub_index, root);
                    assert(pre.disk_view.entries.contains_key(addr));
                    assert(pre.disk_view.entries[addr] == post.disk_view.entries[addr]);
                    assert(pre.au_page_bounds.contains_key(addr.au));
                    assert(pre.au_page_bounds[addr.au] == post.au_page_bounds[addr.au]);
                    assert(pre.bounded_live_entries_are_semantic());
                    assert(pre.tj().disk_view.entries.contains_key(addr));
                    assert(pre_dv.entries.contains_key(addr));
                    assert(post.au_page_bounds_match_index());
                    assert(post.lsn_au_index.values().contains(addr.au));
                    assert(sub_index.values().contains(addr.au));
                    if root is Some && root.unwrap().after_page(addr) {
                        assert(addr.au == root.unwrap().au);
                        assert(post.au_page_bounds_follow_freshest_rec());
                        assert(post.au_page_bounds[root.unwrap().au] == root.unwrap().page);
                        assert(addr.page <= post.au_page_bounds[addr.au]);
                        assert(root.unwrap().page < addr.page);
                        assert(false);
                    }
                    assert(sub_domain.contains(addr));
                    let sub_dv = DiskView{boundary_lsn: start_lsn, entries: pre_dv.entries.restrict(sub_domain)};
                    assert(sub_dv.entries.contains_key(addr));
                    assert(sub_dv.entries[addr] == post.disk_view.entries[addr]);
                    let post_tight = post.tj().disk_view;
                    assert(sub_dv.decodable(root));
                    assert(sub_dv.acyclic());
                    assert(sub_dv.pointer_is_upstream(root, post.lsn_au_index[post.seq_start()]));
                    assert(sub_dv.domain_au_bounded_wrt_index(sub_index));
                    assert(sub_dv.bounded_inactive_lsns(sub_index, root));
                    assert(sub_dv.build_lsn_au_index_au_walk(root, post.lsn_au_index[post.seq_start()]) == sub_index);
                    sub_dv.boundary_crossing_entry_in_build_tight(
                        root,
                        post.lsn_au_index[post.seq_start()],
                        sub_index,
                        addr,
                    );
                    assert(post_tight.entries.contains_key(addr));
                } else {
                    assert(!post.au_page_bounds.contains_key(addr.au)) by {
                        if post.au_page_bounds.contains_key(addr.au) {
                            assert(post.au_page_bounds_match_index());
                            let lsn = choose |lsn: LSN| #[trigger] post.lsn_au_index.contains_key(lsn)
                                && post.lsn_au_index[lsn] == addr.au;
                            assert(pre.lsn_au_index.contains_key(lsn));
                            pre.tj().build_lsn_au_index_from_first_ensures(pre_first);

                            assert(lsn < pre.tj().seq_end());
                            assert(start_lsn <= lsn);
                            assert(false);
                        }
                    }
                    assert(false);
                }
            }
        }
        assert(post.indexed_lsn_witnesses_are_semantic()) by {
            assert forall |addr: Address, lsn: LSN| ({
                let record = post.disk_view.entries[addr];
                &&& #[trigger] post.disk_view.entries.contains_key(addr)
                &&& post.au_page_bounds.contains_key(addr.au)
                &&& addr.page <= post.au_page_bounds[addr.au]
                &&& post.seq_start() < record.message_seq.seq_end
                &&& record.message_seq.contains(lsn)
                &&& #[trigger] post.lsn_au_index.contains_key(lsn)
                &&& post.lsn_au_index[lsn] == addr.au
            }) implies post.tj().disk_view.entries.contains_key(addr) by {
                assert(post.bounded_live_entries_are_semantic());
            }
        }
        assert(post.au_page_bounds_covered());
        assert(post.indexed_aus_not_all_pages_free()) by {
            assert forall |au: AU| {
                &&& #[trigger] post.lsn_au_index.values().contains(au)
                &&& post.mini_allocator.allocs.contains_key(au)
            } implies !post.mini_allocator.allocs[au].all_pages_free() by {
                assert(!deallocs.contains(au)) by {
                    if deallocs.contains(au) {
                        assert(!post.lsn_au_index.values().contains(au));
                        assert(false);
                    }
                }
                assert(pre.lsn_au_index.values().contains(au)) by {
                    let lsn = choose |lsn: LSN| #![trigger post.lsn_au_index.contains_key(lsn)] {
                        post.lsn_au_index.contains_key(lsn) && post.lsn_au_index[lsn] == au
                    };
                    assert(post.lsn_au_index.contains_key(lsn));
                    assert(pre.lsn_au_index.contains_key(lsn));
                    assert(pre.lsn_au_index[lsn] == au);
                }
                assert(post.mini_allocator == pre.mini_allocator.prune(deallocs));
                assert(post.mini_allocator.allocs[au] == pre.mini_allocator.allocs[au]);
                assert(pre.indexed_aus_not_all_pages_free());
            }
        }
        assert(post.semantic_inv()) by {
            let semantic_dv = post.tj().disk_view;
            let first = if post.freshest_rec is Some {
                post.lsn_au_index[post.seq_start()]
            } else {
                0
            };
            let computed_index = semantic_dv.build_lsn_au_index_au_walk(post.freshest_rec, first);
            if start_lsn < pre.tj().seq_end() {
                reveal(DiskView::pages_allocated_in_lsn_order);

                assert(semantic_dv.pages_allocated_in_lsn_order()) by {
                    assert forall |alo: Address, ahi: Address|
                        ({
                            &&& alo.au == ahi.au
                            &&& alo.page < ahi.page
                            &&& #[trigger] semantic_dv.entries.contains_key(alo)
                            &&& #[trigger] semantic_dv.entries.contains_key(ahi)
                        }) implies semantic_dv.entries[alo].message_seq.seq_end
                            <= semantic_dv.entries[ahi].message_seq.seq_start by {
                        assert(semantic_dv.entries <= pre.tj().disk_view.entries);
                        assert(pre.tj().disk_view.entries.contains_key(alo));
                        assert(pre.tj().disk_view.entries.contains_key(ahi));
                        assert(semantic_dv.entries[alo] == pre.tj().disk_view.entries[alo]);
                        assert(semantic_dv.entries[ahi] == pre.tj().disk_view.entries[ahi]);
                        assert(pre.tj().disk_view.pages_allocated_in_lsn_order());
                    }
                }
                assert(semantic_dv.internal_au_pages_fully_linked());
                assert(semantic_dv.pointer_is_upstream(post.freshest_rec, first));
                assert(post.lsn_au_index == computed_index);
                assert(semantic_dv.domain_au_bounded_wrt_index(computed_index));
                assert(semantic_dv.bounded_inactive_lsns(computed_index, post.freshest_rec));
                assert(computed_index == semantic_dv.build_lsn_au_index_au_walk(post.freshest_rec, first));
                assert(Self::semantic_journal_structure(semantic_dv, post.freshest_rec, computed_index, first));
            } else {
                assert(semantic_dv.entries =~= Map::<Address, LinkedJournal_v::JournalRecord>::empty());
                assert(computed_index == Map::<LSN, AU>::empty());
                assert(post.lsn_au_index == computed_index);
                reveal(DiskView::pages_allocated_in_lsn_order);

                assert(semantic_dv.pages_allocated_in_lsn_order());
                assert(semantic_dv.internal_au_pages_fully_linked());
                assert(Self::semantic_journal_structure(semantic_dv, post.freshest_rec, computed_index, first)) by {
                    assert(semantic_dv.internal_au_pages_fully_linked());
                    assert(semantic_dv.pointer_is_upstream(post.freshest_rec, first));
                    assert(semantic_dv.domain_au_bounded_wrt_index(computed_index));
                    assert(semantic_dv.bounded_inactive_lsns(computed_index, post.freshest_rec));
                    assert(computed_index == semantic_dv.build_lsn_au_index_au_walk(post.freshest_rec, first));
                }
            }
        }
    }

    pub proof fn semantic_entry_seq_end_bounded_by_journal_end(self, addr: Address)
        requires
            self.semantic_inv(),
            self.tj().disk_view.entries.contains_key(addr),
        ensures
            self.tj().disk_view.entries[addr].message_seq.seq_end <= self.tj().seq_end(),
    {
        self.tj_inherits_semantic_structure();
        let record = self.tj().disk_view.entries[addr];
        if record.message_seq.seq_end > self.tj().seq_end() {
            assert(self.tj().wf());
            let bad_lsn = if record.message_seq.seq_start <= self.tj().seq_end() {
                self.tj().seq_end()
            } else {
                record.message_seq.seq_start
            };
            assert(record.message_seq.contains(bad_lsn));
            let first = if self.freshest_rec is Some {
                self.lsn_au_index[self.seq_start()]
            } else {
                0
            };
            self.tj().build_lsn_au_index_from_first_ensures(first);
            assert(!self.lsn_au_index.contains_key(bad_lsn));
            assert(self.tj().disk_view.domain_au_bounded_wrt_index(self.lsn_au_index));
            assert(self.lsn_au_index.values().contains(addr.au));
            self.semantic_entry_not_after_freshest(addr);
            assert(self.tj().disk_view.bounded_inactive_lsns(self.lsn_au_index, self.freshest_rec));
            assert(bad_lsn < self.tj().disk_view.boundary_lsn);
            assert(self.tj().disk_view.boundary_lsn <= self.tj().seq_end());
            assert(false);
        }
    }

    #[inductive(freeze_for_commit)]
    fn freeze_for_commit_inductive(pre: Self, post: Self, lbl: Label) {
    }

    #[inductive(read_for_recovery)]
    fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label, start_lsn: LSN, addr: Address) { }

    #[inductive(query_end_lsn)]
    fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label) {
    }

    #[inductive(internal_mini_allocator_fill)]
    fn internal_mini_allocator_fill_inductive(pre: Self, post: Self, lbl: Label, post_disk_view: DiskView) {
        assert(post.mini_allocator.wf()) by {
            assert forall |au| #[trigger] post.mini_allocator.allocs.contains_key(au)
                implies post.mini_allocator.allocs[au].wf() && post.mini_allocator.allocs[au].au == au by {
                if pre.mini_allocator.allocs.contains_key(au) {
                    assert(pre.mini_allocator.wf());
                } else {
                    assert(lbl->allocs.contains(au));
                }
            }
            if post.mini_allocator.curr is Some {
                assert(pre.mini_allocator.curr is Some);
                assert(pre.mini_allocator.wf());
            }
        }
        assert(post.wf());
        assert(post.lsn_au_index_before_tail());
        assert(Self::disk_domain_bounded_by_owned_aus(
            post.disk_view,
            post.lsn_au_index,
            post.mini_allocator,
        ));
        assert(post.inv());
    }

    #[inductive(internal_mini_allocator_prune)]
    fn internal_mini_allocator_prune_inductive(pre: Self, post: Self, lbl: Label, prune_aus: Set<AU>) {
        let deallocs = lbl.arrow_InternalAllocations_deallocs();

        pre.mini_allocator.prune_preserves_wf(prune_aus);
        assert(post.wf());
        assert(post.lsn_au_index_before_tail());

        assert(Self::disk_domain_bounded_by_owned_aus(
            post.disk_view,
            post.lsn_au_index,
            post.mini_allocator,
        )) by {
            assert forall |addr: Address| #[trigger] post.disk_view.entries.dom().contains(addr)
                implies post.lsn_au_index.values().contains(addr.au)
                    || post.mini_allocator.all_aus().contains(addr.au) by {
                assert(pre.disk_view.entries.contains_key(addr));
                assert(Self::disk_domain_bounded_by_owned_aus(
                    pre.disk_view,
                    pre.lsn_au_index,
                    pre.mini_allocator,
                ));
                if pre.lsn_au_index.values().contains(addr.au) {
                    let lsn = choose |lsn| #[trigger] pre.lsn_au_index.contains_key(lsn)
                        && pre.lsn_au_index[lsn] == addr.au;
                    assert(post.lsn_au_index.contains_key(lsn));
                    assert(post.lsn_au_index[lsn] == addr.au);
                } else {
                    assert(pre.mini_allocator.all_aus().contains(addr.au));
                    if prune_aus.contains(addr.au) {
                        assert(!deallocs.contains(addr.au));
                        assert(pre.lsn_au_index.values().contains(addr.au));
                        assert(false);
                    } else {
                        assert(post.mini_allocator.all_aus()
                            == pre.mini_allocator.all_aus().difference(prune_aus));
                        assert(post.mini_allocator.all_aus().contains(addr.au));
                    }
                }
            }
        }
        assert(post.inv());
    }

    pub proof fn internal_mini_allocator_fill_tj_unchanged(
        pre: Self,
        post: Self,
        lbl: Label,
        post_disk_view: DiskView,
    )
        requires
            pre.semantic_inv(),
            AllocationJournal::State::next_by(
                pre,
                post,
                lbl,
                AllocationJournal::Step::internal_mini_allocator_fill(post_disk_view),
            ),
        ensures
            post.tj() == pre.tj(),
            post.disk_view.path_decodable(post.freshest_rec),
            post.tj().disk_view == pre.tj().disk_view,
            post.tj().disk_view.is_sub_disk(post.disk_view),
    {
        reveal(AllocationJournal::State::next_by);
        let root = pre.tj().freshest_rec;
        let pre_tight_dv = pre.tj().disk_view;

        pre.tj_view_is_valid_acyclic_subdisk();
        assert(pre_tight_dv.is_sub_disk(pre.disk_view));
        assert(pre_tight_dv.is_sub_disk(post.disk_view)) by {
            DiskView::sub_disk_transitive_auto();
            assert(pre_tight_dv.is_sub_disk(pre.disk_view));
            assert(pre.disk_view.is_sub_disk(post.disk_view));
        }
        assert(post.freshest_rec == pre.freshest_rec);
        assert(root == post.freshest_rec);
        assert(post.au_page_bounds == pre.au_page_bounds);
        Self::tj_view_preserved_in_post_disk(pre, post);
    }

    pub proof fn internal_mini_allocator_prune_tj_unchanged(
        pre: Self,
        post: Self,
        lbl: Label,
        prune_aus: Set<AU>,
    )
        requires
            pre.semantic_inv(),
            AllocationJournal::State::next_by(
                pre,
                post,
                lbl,
                AllocationJournal::Step::internal_mini_allocator_prune(prune_aus),
            ),
        ensures
            post.tj() == pre.tj(),
            post.disk_view.path_decodable(post.freshest_rec),
            post.tj().disk_view == pre.tj().disk_view,
            post.tj().disk_view.is_sub_disk(post.disk_view),
    {
        reveal(AllocationJournal::State::next_by);
        let deallocs = lbl.arrow_InternalAllocations_deallocs();
        let root = pre.tj().freshest_rec;
        let pre_tight_dv = pre.tj().disk_view;

        assert forall |addr: Address| #[trigger] pre_tight_dv.entries.contains_key(addr)
            implies !deallocs.contains(addr.au) by {
            if deallocs.contains(addr.au) {
                assert(pre_tight_dv.wf_addrs());
                assert(addr.wf());
                assert(pre.mini_allocator.allocs.contains_key(addr.au));
                assert(pre.mini_allocator.allocs[addr.au].all_pages_free());
                assert(pre.mini_allocator.wf());
                assert(pre.mini_allocator.allocs[addr.au].au == addr.au);
                assert(pre.mini_allocator.allocs[addr.au].allocated == Set::<Address>::empty());
                assert(pre.mini_allocator.allocs[addr.au].allocated == Set::<Address>::empty());
                assert(pre.mini_allocator.allocs[addr.au].is_free_addr(addr));
                assert(pre.mini_allocator.can_allocate(addr));
                assert(Self::disk_domain_not_free(pre_tight_dv, pre.mini_allocator));
                assert(false);
            }
        }

        assert(pre_tight_dv.is_sub_disk(pre.disk_view)) by {
            pre.tj_view_is_valid_acyclic_subdisk();
        }
        assert(pre_tight_dv.is_sub_disk(post.disk_view)) by {
            assert(pre_tight_dv.boundary_lsn == post.disk_view.boundary_lsn);
            assert(pre_tight_dv.entries <= post.disk_view.entries) by {
                assert forall |addr: Address| #[trigger] pre_tight_dv.entries.contains_key(addr)
                    implies post.disk_view.entries.contains_key(addr)
                        && post.disk_view.entries[addr] == pre_tight_dv.entries[addr] by {
                    assert(pre.disk_view.entries.contains_key(addr));
                    assert(!deallocs.contains(addr.au));
                }
            }
        }

        assert(post.freshest_rec == pre.freshest_rec);
        assert(root == post.freshest_rec);
        assert(post.au_page_bounds == pre.au_page_bounds);
        Self::tj_view_preserved_in_post_disk(pre, post);
    }

    #[inductive(discard_old)]
    fn discard_old_inductive(pre: Self, post: Self, lbl: Label) {
        let start_lsn = lbl->start_lsn;
        let deallocs = lbl.arrow_DiscardOld_deallocs();
        let new_lsn_au_index = lsn_au_index_discard_up_to(pre.lsn_au_index, start_lsn);
        let discarded_aus = pre.lsn_au_index.values().difference(new_lsn_au_index.values());
        assert(deallocs == discarded_aus);

        pre.mini_allocator.prune_preserves_wf(discarded_aus);
        assert(post.disk_view.wf_addrs()) by {
            assert forall |addr| #[trigger] post.disk_view.entries.contains_key(addr)
                implies addr.wf() by {
                assert(pre.disk_view.entries.contains_key(addr));
                assert(pre.disk_view.wf_addrs());
            }
        }
        assert(post.wf());
        assert(post.lsn_au_index_before_tail()) by {
            lsn_au_index_discard_up_to_ensures(pre.lsn_au_index, start_lsn);
            assert forall |lsn: LSN| #[trigger] post.lsn_au_index.contains_key(lsn)
                implies lsn < post.unmarshalled_tail.seq_start by {
                assert(pre.lsn_au_index.contains_key(lsn));
                assert(pre.lsn_au_index_before_tail());
                assert(lsn < pre.unmarshalled_tail.seq_start);
                if pre.unmarshalled_tail.seq_start <= start_lsn {
                    assert(start_lsn <= lsn);
                    assert(post.unmarshalled_tail.seq_start == start_lsn);
                    assert(false);
                } else {
                    assert(post.unmarshalled_tail == pre.unmarshalled_tail);
                }
            }
        }
        assert(Self::disk_domain_bounded_by_owned_aus(
            post.disk_view,
            post.lsn_au_index,
            post.mini_allocator,
        )) by {
            assert forall |addr: Address| #[trigger] post.disk_view.entries.dom().contains(addr)
                implies post.lsn_au_index.values().contains(addr.au)
                    || post.mini_allocator.all_aus().contains(addr.au) by {
                assert(pre.disk_view.entries.contains_key(addr));
                assert(Self::disk_domain_bounded_by_owned_aus(
                    pre.disk_view,
                    pre.lsn_au_index,
                    pre.mini_allocator,
                ));
                if pre.lsn_au_index.values().contains(addr.au) {
                    if !post.lsn_au_index.values().contains(addr.au) {
                        assert(discarded_aus.contains(addr.au));
                        assert(deallocs.contains(addr.au));
                        assert(!post.disk_view.entries.contains_key(addr));
                        assert(false);
                    }
                } else {
                    assert(pre.mini_allocator.all_aus().contains(addr.au));
                    if discarded_aus.contains(addr.au) {
                        assert(deallocs.contains(addr.au));
                        assert(!post.disk_view.entries.contains_key(addr));
                        assert(false);
                    } else {
                        assert(post.mini_allocator.all_aus()
                            == pre.mini_allocator.all_aus().difference(discarded_aus));
                        assert(post.mini_allocator.all_aus().contains(addr.au));
                    }
                }
            }
        }
        assert( post.inv() );
    }

    pub proof fn internal_journal_marshal_view_preserves(
        pre: Self,
        post: Self,
        lbl: Label,
        cut: LSN,
        addr: Address,
    )
        requires
            pre.semantic_inv(),
            Self::internal_journal_marshal(pre, post, lbl, cut, addr),
        ensures
            post.disk_view.wf_addrs(),
            post.tj() == pre.tj().append_record(addr, pre.unmarshalled_tail.discard_recent(cut)),
            post.wf(),
            post.tj().disk_view.decodable(post.tj().freshest_rec),
            post.tj().disk_view.block_in_bounds(post.tj().freshest_rec),
            post.tj().disk_view.acyclic(),
    {
        let msgs = pre.unmarshalled_tail.discard_recent(cut);
        let new_record = LinkedJournal_v::JournalRecord {
            message_seq: msgs,
            prior_rec: pre.tj().freshest_rec,
        };
        let pre_dv = pre.tj().disk_view;
        let pre_root = pre.tj().freshest_rec;
        let post_dv = post.tj().disk_view;
        let post_root = post.tj().freshest_rec;
        pre.tj_inherits_semantic_structure();

        assert(!pre_dv.entries.contains_key(addr)) by {
            if pre_dv.entries.contains_key(addr) {
                assert(Self::disk_domain_not_free(pre_dv, pre.mini_allocator));
                assert(!pre.mini_allocator.can_allocate(addr));
                assert(false);
            }
        }
        assert(post.disk_view.wf_addrs()) by {
            assert forall |x: Address| #[trigger] post.disk_view.entries.contains_key(x)
                implies x.wf() by {
                if x == addr {
                    assert(pre.mini_allocator.can_allocate(addr));
                } else {
                    assert(pre.disk_view.entries.contains_key(x));
                    assert(pre.disk_view.wf_addrs());
                }
            }
        }

        assert(pre_dv.is_sub_disk(pre.disk_view)) by {
            pre.disk_view.path_build_tight_is_sub_disk(pre_root);
        }
        assert(pre_dv.entries <= post.disk_view.entries) by {
            assert forall |x: Address| #[trigger] pre_dv.entries.contains_key(x)
                implies post.disk_view.entries.contains_key(x)
                    && post.disk_view.entries[x] == pre_dv.entries[x] by {
                assert(pre.disk_view.entries.contains_key(x));
            }
        }
        assert(post.disk_view.entries.contains_key(addr));
        assert(post.disk_view.entries[addr] == new_record);
        assert(new_record.cropped_prior(pre_dv.boundary_lsn) == pre_root);
        assert(msgs.wf());
        assert(!msgs.is_empty());
        let appended_tj = pre.tj().append_record(addr, msgs);
        let appended_dv = appended_tj.disk_view;
        assert(appended_dv.entries_wf()) by {
            assert forall |x| #[trigger] appended_dv.entries.contains_key(x)
                implies appended_dv.entries[x].wf() by {
                if x == addr {
                    assert(appended_dv.entries[x] == new_record);
                    assert(new_record.wf());
                } else {
                    assert(pre_dv.entries.contains_key(x));
                    assert(pre_dv.entries[x].wf());
                }
            }
        }
        assert(appended_dv.nondangling_pointers()) by {
            assert forall |x| #[trigger] appended_dv.entries.contains_key(x)
                implies appended_dv.is_nondangling_pointer(appended_dv.entries[x].cropped_prior(appended_dv.boundary_lsn)) by {
                if x == addr {
                    assert(appended_dv.entries[x] == new_record);
                    if new_record.cropped_prior(appended_dv.boundary_lsn) is Some {
                        assert(pre_root is Some);
                        assert(appended_dv.entries.contains_key(pre_root.unwrap()));
                    }
                } else {
                    assert(pre_dv.entries.contains_key(x));
                    assert(appended_dv.entries[x] == pre_dv.entries[x]);
                    assert(pre_dv.nondangling_pointers());
                    let prior = pre_dv.entries[x].cropped_prior(pre_dv.boundary_lsn);
                    if prior is Some {
                        assert(pre_dv.entries.contains_key(prior.unwrap()));
                        assert(appended_dv.entries.contains_key(prior.unwrap()));
                    }
                }
            }
        }
        assert(appended_dv.blocks_each_have_link()) by {
            assert forall |x| #[trigger] appended_dv.entries.contains_key(x)
                implies appended_dv.entries[x].has_link(appended_dv.boundary_lsn) by {
                if x == addr {
                    assert(appended_dv.entries[x] == new_record);
                    if appended_dv.boundary_lsn < new_record.message_seq.seq_start {
                        if pre_root is None {
                            assert(pre.tj().seq_end() == pre_dv.boundary_lsn);
                            assert(msgs.seq_start == pre.tj().seq_end());
                            assert(false);
                        }
                    }
                } else {
                    assert(pre_dv.entries.contains_key(x));
                    assert(appended_dv.entries[x] == pre_dv.entries[x]);
                    assert(pre_dv.blocks_each_have_link());
                }
            }
        }
        assert(appended_dv.blocks_can_concat()) by {
            assert forall |x| #[trigger] appended_dv.entries.contains_key(x)
                implies appended_dv.this_block_can_concat(x) by {
                if x == addr {
                    assert(appended_dv.entries[x] == new_record);
                    if new_record.cropped_prior(appended_dv.boundary_lsn) is Some {
                        assert(pre_root is Some);
                        assert(new_record.cropped_prior(appended_dv.boundary_lsn) == pre_root);
                        assert(pre_dv.entries.contains_key(pre_root.unwrap()));
                        assert(pre_dv.entries[pre_root.unwrap()].message_seq.seq_end == pre.tj().seq_end());
                        assert(msgs.seq_start == pre.tj().seq_end());
                        assert(pre_dv.entries[pre_root.unwrap()].message_seq.can_concat(msgs));
                    }
                } else {
                    assert(pre_dv.entries.contains_key(x));
                    assert(appended_dv.entries[x] == pre_dv.entries[x]);
                    assert(pre_dv.blocks_can_concat());
                    let prior = pre_dv.entries[x].cropped_prior(pre_dv.boundary_lsn);
                    if prior is Some {
                        assert(pre_dv.entries[prior.unwrap()] == appended_dv.entries[prior.unwrap()]);
                    }
                }
            }
        }
        assert(appended_dv.wf());
        assert(appended_dv.is_nondangling_pointer(appended_tj.freshest_rec));
        assert(appended_dv.block_in_bounds(appended_tj.freshest_rec));
        assert( appended_dv.valid_ranking(pre.tj().marshal_ranking(addr)) ); // witness, duped from linked journal
        assert(appended_tj.decodable());
        assert(appended_dv.is_sub_disk(post.disk_view)) by {
            assert(appended_dv.boundary_lsn == post.disk_view.boundary_lsn);
            assert(appended_dv.entries <= post.disk_view.entries) by {
                assert forall |x: Address| #[trigger] appended_dv.entries.contains_key(x)
                    implies post.disk_view.entries.contains_key(x)
                        && post.disk_view.entries[x] == appended_dv.entries[x] by {
                    if x == addr {
                    } else {
                        assert(pre_dv.entries.contains_key(x));
                    }
                }
            }
        }
        post.disk_view.decodable_sub_disk_path_build_tight_matches_build_tight(
            appended_dv,
            appended_tj.freshest_rec,
        );
        pre_dv.decodable_implies_path_decodable(pre_root);
        assert(pre.disk_view.path_decodable(pre_root));
        pre.disk_view.path_build_tight_idempotent(pre_root);
        assert(pre_dv == pre.disk_view.path_build_tight(pre_root));
        assert(pre_dv.path_build_tight(pre_root) == pre_dv);
        pre_dv.path_build_tight_prepend_record(
            appended_dv,
            pre_root,
            addr,
            new_record,
        );
        assert(post.tj().disk_view == post.disk_view.path_build_tight(appended_tj.freshest_rec));
        assert(post.disk_view.path_build_tight(appended_tj.freshest_rec)
            == appended_dv.path_build_tight(appended_tj.freshest_rec));
        assert(appended_tj.freshest_rec == Some(addr));
        assert_maps_equal!(
            appended_dv.path_build_tight(appended_tj.freshest_rec).entries,
            appended_dv.entries
        );
        assert(appended_dv.path_build_tight(appended_tj.freshest_rec) == appended_dv);
        assert(appended_dv.path_build_tight(appended_tj.freshest_rec)
            == appended_dv.build_tight(appended_tj.freshest_rec));
        assert(appended_tj.build_tight().disk_view
            == appended_dv.build_tight(appended_tj.freshest_rec));
        assert(appended_tj.build_tight() == appended_tj);
        assert_maps_equal!(
            post.tj().disk_view.entries,
            pre.tj().append_record(addr, msgs).disk_view.entries
        );
        assert(post.tj().disk_view == pre.tj().append_record(addr, msgs).disk_view);
        assert(post.tj() == pre.tj().append_record(addr, msgs));
        assert(post_dv.decodable(post_root));
        assert( post_dv.valid_ranking(pre.tj().marshal_ranking(addr)) ); // witness, duped from linked journal
        assert( post.tj().disk_view.acyclic() );
        assert( post.wf() );
    }

    pub proof fn internal_journal_marshal_bounded_inactive_preserves(
        pre: Self,
        post: Self,
        lbl: Label,
        cut: LSN,
        addr: Address,
    )
        requires
            pre.semantic_inv(),
            Self::internal_journal_marshal(pre, post, lbl, cut, addr),
            post.disk_view.wf_addrs(),
            post.tj() == pre.tj().append_record(addr, pre.unmarshalled_tail.discard_recent(cut)),
            post.wf(),
            post.tj().disk_view.decodable(post.tj().freshest_rec),
            post.tj().disk_view.block_in_bounds(post.tj().freshest_rec),
            post.tj().disk_view.acyclic(),
        ensures
            post.tj().disk_view.bounded_inactive_lsns(post.lsn_au_index, post.tj().freshest_rec),
    {
        let msgs = pre.unmarshalled_tail.discard_recent(cut);
        let new_record = LinkedJournal_v::JournalRecord {
            message_seq: msgs,
            prior_rec: pre.tj().freshest_rec,
        };
        let pre_dv = pre.tj().disk_view;
        let pre_root = pre.tj().freshest_rec;
        let post_dv = post.tj().disk_view;
        assert(pre_dv == pre.tj().disk_view);
        pre.tj_inherits_semantic_structure();

        let update = singleton_index(msgs.seq_start, msgs.seq_end, addr.au);
        assert( update.contains_key(msgs.seq_start) );
        assert( update[msgs.seq_start] == addr.au );
        assert( post.lsn_au_index.contains_key(msgs.seq_start) );

        assert(post_dv.bounded_inactive_lsns(post.lsn_au_index, post.tj().freshest_rec)) by {
            assert forall |x: Address, lsn: LSN|
                ({
                    &&& post_dv.entries.dom().contains(x)
                    &&& post_dv.entries[x].message_seq.contains(lsn)
                    &&& post.lsn_au_index.values().contains(x.au)
                    &&& !post.lsn_au_index.contains_key(lsn)
                    &&& post.tj().freshest_rec is Some ==> !post.tj().freshest_rec.unwrap().after_page(x)
                }) implies lsn < post_dv.boundary_lsn by {
                if x == addr {
                    assert(post_dv.entries[x] == new_record);
                    assert(msgs.contains(lsn));
                    assert(update.contains_key(lsn));
                    assert(post.lsn_au_index.contains_key(lsn));
                    assert(false);
                } else {
                    assert(pre_dv.entries.dom().contains(x));
                    assert(post_dv.entries[x] == pre_dv.entries[x]);
                    assert(pre_dv.domain_au_bounded_wrt_index(pre.lsn_au_index));
                    let in_range_lsn = choose |in_range_lsn| #[trigger] pre.lsn_au_index.contains_key(in_range_lsn)
                        && pre.lsn_au_index[in_range_lsn] == x.au;
                    assert(post.lsn_au_index.contains_key(in_range_lsn));
                    if pre.lsn_au_index.contains_key(lsn) {
                        assert(post.lsn_au_index.contains_key(lsn));
                        assert(false);
                    }
                    if pre_root is Some && pre_root.unwrap().after_page(x) {
                        pre_dv.path_build_tight_equals_build_tight(pre_root);
                        assert(pre_dv.build_tight(pre_root).entries.contains_key(x));
                        pre_dv.build_tight_entry_lsn_bounded(pre_root, x);
                        reveal(DiskView::pages_allocated_in_lsn_order);

                        assert(pre_dv.pages_allocated_in_lsn_order());
                        assert(pre_dv.entries[pre_root.unwrap()].message_seq.seq_end
                            <= pre_dv.entries[x].message_seq.seq_start);
                        assert(pre_dv.entries[x].message_seq.seq_end
                            <= pre_dv.entries[pre_root.unwrap()].message_seq.seq_end);
                        assert(pre_dv.entries[x].message_seq.wf());
                        assert(false);
                    }
                    assert(pre_dv.bounded_inactive_lsns(pre.lsn_au_index, pre_root));
                    assert(lsn < pre_dv.boundary_lsn);
                }
            }
        }
    }

    pub proof fn internal_journal_marshal_domain_au_bounded_preserves(
        pre: Self,
        post: Self,
        lbl: Label,
        cut: LSN,
        addr: Address,
    )
        requires
            pre.semantic_inv(),
            Self::internal_journal_marshal(pre, post, lbl, cut, addr),
            post.tj() == pre.tj().append_record(addr, pre.unmarshalled_tail.discard_recent(cut)),
        ensures
            post.tj().disk_view.domain_au_bounded_wrt_index(post.lsn_au_index),
    {
        let msgs = pre.unmarshalled_tail.discard_recent(cut);
        let update = singleton_index(msgs.seq_start, msgs.seq_end, addr.au);
        let pre_dv = pre.tj().disk_view;
        let post_dv = post.tj().disk_view;
        pre.tj_inherits_semantic_structure();
        assert(post_dv.domain_au_bounded_wrt_index(post.lsn_au_index)) by {
            assert forall |x: Address| #[trigger] post_dv.entries.dom().contains(x)
                implies post.lsn_au_index.values().contains(x.au) by {
                if x == addr {
                    assert(update.contains_key(msgs.seq_start));
                    assert(post.lsn_au_index.contains_key(msgs.seq_start));
                    assert(post.lsn_au_index[msgs.seq_start] == x.au);
                } else {
                    assert(pre_dv.entries.dom().contains(x));
                    assert(pre_dv.domain_au_bounded_wrt_index(pre.lsn_au_index));
                    let lsn = choose |lsn| #[trigger] pre.lsn_au_index.contains_key(lsn)
                        && pre.lsn_au_index[lsn] == x.au;
                    if update.contains_key(lsn) {
                        pre.tj().build_lsn_au_index_from_first_ensures(
                            if pre.tj().freshest_rec is Some {
                                pre.lsn_au_index[pre.tj().seq_start()]
                            } else {
                                0
                            },
                        );

                        assert(lsn < pre.tj().seq_end());
                        assert(msgs.seq_start == pre.tj().seq_end());
                        assert(false);
                    }
                    assert(post.lsn_au_index.contains_key(lsn));
                    assert(post.lsn_au_index[lsn] == x.au);
                }
            }
        }
    }

    pub proof fn internal_journal_marshal_valid_first_preserves(
        pre: Self,
        post: Self,
        lbl: Label,
        cut: LSN,
        addr: Address,
    )
        requires
            pre.semantic_inv(),
            Self::internal_journal_marshal(pre, post, lbl, cut, addr),
            post.disk_view.wf_addrs(),
            post.tj() == pre.tj().append_record(addr, pre.unmarshalled_tail.discard_recent(cut)),
            post.wf(),
            post.tj().disk_view.acyclic(),
        ensures
            ({
                let post_first = if post.tj().freshest_rec is Some {
                    post.lsn_au_index[post.tj().seq_start()]
                } else {
                    0
                };
                post.tj().disk_view.valid_first_au(post_first)
            }),
    {
        let pre_dv = pre.tj().disk_view;
        let pre_root = pre.tj().freshest_rec;
        let post_dv = post.tj().disk_view;
        let post_root = post.tj().freshest_rec;
        pre.tj_inherits_semantic_structure();
        assert(pre_dv == pre.tj().disk_view);
        let pre_first = if pre_root is Some {
            pre.lsn_au_index[pre.tj().seq_start()]
        } else {
            0
        };
        let post_first = if post_root is Some {
            post.lsn_au_index[post.tj().seq_start()]
        } else {
            0
        };
        assert( post_dv.valid_first_au(post_first) ) by {
            if pre_root is Some {
                assert(post.tj().seq_start() == pre.tj().seq_start());
                assert(post_first == pre_first);
                let witness = choose |witness: Address| #![auto] witness.au == pre_first
                    && pre_dv.addr_supports_lsn(witness, post_dv.boundary_lsn);
                assert(post_dv.addr_supports_lsn(witness, post_dv.boundary_lsn));
            } else {
                assert(post_first == addr.au);
                assert(post_dv.addr_supports_lsn(addr, post_dv.boundary_lsn));
            }
        }
    }

    pub proof fn internal_journal_marshal_unique_lsns_preserves(
        pre: Self,
        post: Self,
        lbl: Label,
        cut: LSN,
        addr: Address,
    )
        requires
            pre.semantic_inv(),
            Self::internal_journal_marshal(pre, post, lbl, cut, addr),
            post.tj() == pre.tj().append_record(addr, pre.unmarshalled_tail.discard_recent(cut)),
            post.wf(),
            post.tj().disk_view.acyclic(),
        ensures
            post.tj().disk_view.has_unique_lsns(),
    {
        let msgs = pre.unmarshalled_tail.discard_recent(cut);
        let pre_dv = pre.tj().disk_view;
        let pre_root = pre.tj().freshest_rec;
        let post_dv = post.tj().disk_view;
        assert(pre_dv == pre.tj().disk_view);
        pre.tj_inherits_semantic_structure();
        assert( post_dv.has_unique_lsns() ) by {
            assert forall |lsn, addr1, addr2| post_dv.addr_supports_lsn(addr1, lsn) && post_dv.addr_supports_lsn(addr2, lsn)
            implies addr1 == addr2 by {
                if lsn < msgs.seq_start {
                    assert(pre_dv.addr_supports_lsn(addr1, lsn) && pre_dv.addr_supports_lsn(addr2, lsn));
                } else if addr1 != addr2 {
                    let pre_addr = if pre_dv.addr_supports_lsn(addr1, lsn) { addr1 } else { addr2 };
                    assert(pre_dv.entries.contains_key(pre_addr));
                    assert(pre_dv.entries[pre_addr].message_seq.contains(lsn));
                    pre.semantic_entry_seq_end_bounded_by_journal_end(pre_addr);
                    if pre_root is None {
                        assert(pre_dv.entries =~= Map::<Address, LinkedJournal_v::JournalRecord>::empty());
                        assert(false);
                    }
                    assert(pre_dv.entries[pre_addr].message_seq.seq_end <= pre.tj().seq_end());
                    assert(pre.tj().seq_end() == msgs.seq_start);
                    assert(lsn < pre_dv.entries[pre_addr].message_seq.seq_end);
                    assert(false);
                }
            }
        }
    }

    pub proof fn internal_journal_marshal_nonzero_pages_preserves(
        pre: Self,
        post: Self,
        lbl: Label,
        cut: LSN,
        addr: Address,
    )
        requires
            pre.semantic_inv(),
            Self::internal_journal_marshal(pre, post, lbl, cut, addr),
            post.tj() == pre.tj().append_record(addr, pre.unmarshalled_tail.discard_recent(cut)),
            post.wf(),
        ensures
            post.tj().disk_view.nonzero_pages_point_backward(),
    {
        let pre_dv = pre.tj().disk_view;
        let pre_root = pre.tj().freshest_rec;
        let post_dv = post.tj().disk_view;
        pre.tj_inherits_semantic_structure();
        assert(post_dv.nonzero_pages_point_backward()) by {
            assert forall |x: Address|
                ({
                    &&& x.page != 0
                    &&& #[trigger] post_dv.entries.contains_key(x)
                }) implies post_dv.entries[x].prior_rec == Some(x.previous()) by {
                if x == addr {
                    assert(pre.mini_allocator.tight_next_addr(pre_root, addr));
                    if addr.page != 0 {
                        assert(pre.mini_allocator.curr is Some);
                        assert(pre_root is Some);
                        assert(addr == pre_root.unwrap().next());
                        assert(pre_root.unwrap() == addr.previous());
                    }
                } else {
                    assert(pre_dv.entries.contains_key(x));
                    assert(pre_dv.nonzero_pages_point_backward());
                }
            }
        }
    }

    pub proof fn internal_journal_marshal_pages_order_preserves(
        pre: Self,
        post: Self,
        lbl: Label,
        cut: LSN,
        addr: Address,
    )
        requires
            pre.semantic_inv(),
            Self::internal_journal_marshal(pre, post, lbl, cut, addr),
            post.tj() == pre.tj().append_record(addr, pre.unmarshalled_tail.discard_recent(cut)),
            post.wf(),
        ensures
            post.tj().disk_view.pages_allocated_in_lsn_order(),
    {
        let msgs = pre.unmarshalled_tail.discard_recent(cut);
        let pre_dv = pre.tj().disk_view;
        let pre_root = pre.tj().freshest_rec;
        let post_dv = post.tj().disk_view;
        assert(pre_dv == pre.tj().disk_view);
        pre.tj_inherits_semantic_structure();
        assert(post_dv.pages_allocated_in_lsn_order()) by {
            reveal(DiskView::pages_allocated_in_lsn_order);

            assert forall |alo: Address, ahi: Address|
                ({
                    &&& alo.au == ahi.au
                    &&& alo.page < ahi.page
                    &&& #[trigger] post_dv.entries.contains_key(alo)
                    &&& #[trigger] post_dv.entries.contains_key(ahi)
                }) implies post_dv.entries[alo].message_seq.seq_end
                    <= post_dv.entries[ahi].message_seq.seq_start by {
                if ahi == addr {
                    assert(alo != addr);
                    assert(pre_dv.entries.contains_key(alo));
                    pre.semantic_entry_seq_end_bounded_by_journal_end(alo);
                    if pre_root is None {
                        assert(pre_dv.entries =~= Map::<Address, LinkedJournal_v::JournalRecord>::empty());
                        assert(false);
                    }
                    assert(pre_dv.entries[alo].message_seq.seq_end <= pre.tj().seq_end());
                    assert(pre.tj().seq_end() == msgs.seq_start);
                    assert(post_dv.entries[ahi].message_seq.seq_start == msgs.seq_start);
                } else if alo == addr {
                    assert(pre_dv.entries.contains_key(ahi));
                    if pre_root is Some {
                        if pre_root.unwrap().after_page(ahi) {
                            pre.semantic_entry_seq_end_bounded_by_journal_end(ahi);
                            assert(pre_dv.entries[pre_root.unwrap()].message_seq.seq_end
                                <= pre_dv.entries[ahi].message_seq.seq_start);
                            assert(pre_dv.entries[ahi].message_seq.seq_end
                                <= pre_dv.entries[pre_root.unwrap()].message_seq.seq_end);
                            assert(pre_dv.entries[ahi].message_seq.wf());
                            assert(false);
                        }
                        assert(pre.mini_allocator.tight_next_addr(pre_root, addr));
                        assert(pre.mini_allocator.curr is Some);
                        assert(addr == pre_root.unwrap().next());
                        assert(ahi.page > addr.page);
                        assert(pre_root.unwrap().after_page(ahi));
                        assert(false);
                    } else {
                        assert(pre_dv.entries =~= Map::<Address, LinkedJournal_v::JournalRecord>::empty());
                        assert(false);
                    }
                } else {
                    assert(pre_dv.entries.contains_key(alo));
                    assert(pre_dv.entries.contains_key(ahi));
                    assert(pre_dv.pages_allocated_in_lsn_order());
                }
            }
        }
    }

    pub proof fn internal_journal_marshal_internal_au_preserves(
        pre: Self,
        post: Self,
        lbl: Label,
        cut: LSN,
        addr: Address,
    )
        requires
            pre.semantic_inv(),
            Self::internal_journal_marshal(pre, post, lbl, cut, addr),
            post.tj() == pre.tj().append_record(addr, pre.unmarshalled_tail.discard_recent(cut)),
            post.wf(),
        ensures
            post.tj().disk_view.internal_au_pages_fully_linked(),
    {
        let post_dv = post.tj().disk_view;
        Self::internal_journal_marshal_nonzero_pages_preserves(pre, post, lbl, cut, addr);
        Self::internal_journal_marshal_pages_order_preserves(pre, post, lbl, cut, addr);
        assert(post_dv.internal_au_pages_fully_linked());
    }

    pub proof fn pointer_is_upstream_from_components(
        post: Self,
    )
        requires
            post.wf(),
            post.tj().disk_view.decodable(post.tj().freshest_rec),
            post.tj().disk_view.block_in_bounds(post.tj().freshest_rec),
            post.tj().disk_view.acyclic(),
            post.tj().disk_view.internal_au_pages_fully_linked(),
            ({
                let post_first = if post.tj().freshest_rec is Some {
                    post.lsn_au_index[post.tj().seq_start()]
                } else {
                    0
                };
                post.tj().disk_view.valid_first_au(post_first)
            }),
            post.tj().disk_view.has_unique_lsns(),
        ensures
            ({
                let post_first = if post.tj().freshest_rec is Some {
                    post.lsn_au_index[post.tj().seq_start()]
                } else {
                    0
                };
                post.tj().disk_view.pointer_is_upstream(post.tj().freshest_rec, post_first)
            }),
    {
        let post_dv = post.tj().disk_view;
        let post_root = post.tj().freshest_rec;
        let post_first = if post_root is Some {
            post.lsn_au_index[post.tj().seq_start()]
        } else {
            0
        };
        assert(post_dv.decodable(post_root));
        assert(post_dv.has_unique_lsns());
        if post_root is Some {
            assert(post_dv.valid_first_au(post_first));
            assert(post_dv.entries.contains_key(post_root.unwrap()));
            assert(post_dv.boundary_lsn < post_dv.entries[post_root.unwrap()].message_seq.seq_end);
            assert(post_dv.upstream(post_root.unwrap()));
        }

        assert( post_dv.pointer_is_upstream(post_root, post_first) );
    }

    pub proof fn internal_journal_marshal_index_matches(
        pre: Self,
        post: Self,
        lbl: Label,
        cut: LSN,
        addr: Address,
    )
        requires
            pre.semantic_inv(),
            Self::internal_journal_marshal(pre, post, lbl, cut, addr),
            post.tj() == pre.tj().append_record(addr, pre.unmarshalled_tail.discard_recent(cut)),
            ({
                let post_first = if post.tj().freshest_rec is Some {
                    post.lsn_au_index[post.tj().seq_start()]
                } else {
                    0
                };
                post.tj().disk_view.pointer_is_upstream(post.tj().freshest_rec, post_first)
            }),
        ensures
            ({
                let post_first = if post.tj().freshest_rec is Some {
                    post.lsn_au_index[post.tj().seq_start()]
                } else {
                    0
                };
                post.lsn_au_index == post.tj().build_lsn_au_index_from_first(post_first)
            }),
    {
        let msgs = pre.unmarshalled_tail.discard_recent(cut);
        let pre_dv = pre.tj().disk_view;
        let pre_root = pre.tj().freshest_rec;
        let post_dv = post.tj().disk_view;
        let post_root = post.tj().freshest_rec;
        let pre_first = if pre_root is Some {
            pre.lsn_au_index[pre.tj().seq_start()]
        } else {
            0
        };
        let post_first = if post_root is Some {
            post.lsn_au_index[post.tj().seq_start()]
        } else {
            0
        };
        pre.tj_inherits_semantic_structure();
        pre.tj().build_lsn_au_index_from_first_ensures(pre_first);
        let update = singleton_index(msgs.seq_start, msgs.seq_end, addr.au);
        assert( post.lsn_au_index == post.tj().build_lsn_au_index_from_first(post_first) ) by {
            pre_dv.build_lsn_au_index_equiv_page_walk(pre_root, pre_first);
            assert( pre.lsn_au_index == pre_dv.build_lsn_au_index_page_walk(pre_root) );

            pre_dv.build_lsn_au_index_page_walk_sub_disk(post_dv, pre_root);
            assert( post_dv.build_lsn_au_index_page_walk(pre_root)
                    == pre_dv.build_lsn_au_index_page_walk(pre_root) );

            assert( post_dv.build_lsn_au_index_page_walk(post_root) ==
                post_dv.build_lsn_au_index_page_walk(pre_root).union_prefer_right(update) );
            let au_update = singleton_index(msgs.seq_start, msgs.seq_end, addr.au);
            assert( au_update == update );

            assert( post.lsn_au_index == post_dv.build_lsn_au_index_page_walk(post_root) );
            pre_dv.build_commutes_over_append_record(pre_root, msgs, addr);
            post_dv.build_lsn_au_index_equiv_page_walk(post_root, post_first);
        }
    }

    pub proof fn internal_journal_marshal_index_preserves(
        pre: Self,
        post: Self,
        lbl: Label,
        cut: LSN,
        addr: Address,
    )
        requires
            pre.semantic_inv(),
            Self::internal_journal_marshal(pre, post, lbl, cut, addr),
            post.disk_view.wf_addrs(),
            post.tj() == pre.tj().append_record(addr, pre.unmarshalled_tail.discard_recent(cut)),
            post.wf(),
            post.tj().disk_view.decodable(post.tj().freshest_rec),
            post.tj().disk_view.block_in_bounds(post.tj().freshest_rec),
            post.tj().disk_view.acyclic(),
        ensures
            ({
                let post_first = if post.tj().freshest_rec is Some {
                    post.lsn_au_index[post.tj().seq_start()]
                } else {
                    0
                };
                &&& Self::semantic_journal_structure(post.tj().disk_view, post.freshest_rec, post.lsn_au_index, post_first)
                &&& post.lsn_au_index == post.tj().build_lsn_au_index_from_first(post_first)
            }),
    {
        let post_first = if post.tj().freshest_rec is Some {
            post.lsn_au_index[post.tj().seq_start()]
        } else {
            0
        };
        Self::internal_journal_marshal_bounded_inactive_preserves(pre, post, lbl, cut, addr);
        Self::internal_journal_marshal_domain_au_bounded_preserves(pre, post, lbl, cut, addr);
        Self::internal_journal_marshal_valid_first_preserves(pre, post, lbl, cut, addr);
        Self::internal_journal_marshal_unique_lsns_preserves(pre, post, lbl, cut, addr);
        Self::internal_journal_marshal_internal_au_preserves(pre, post, lbl, cut, addr);
        Self::pointer_is_upstream_from_components(post);
        Self::internal_journal_marshal_index_matches(pre, post, lbl, cut, addr);
        assert(Self::semantic_journal_structure(post.tj().disk_view, post.freshest_rec, post.lsn_au_index, post_first));
    }

    pub proof fn internal_journal_marshal_allocator_preserves(
        pre: Self,
        post: Self,
        lbl: Label,
        cut: LSN,
        addr: Address,
    )
        requires
            pre.inv(),
            pre.semantic_inv(),
            Self::internal_journal_marshal(pre, post, lbl, cut, addr),
            post.tj() == pre.tj().append_record(addr, pre.unmarshalled_tail.discard_recent(cut)),
            post.disk_view.wf_addrs(),
            post.wf(),
            ({
                let post_first = if post.tj().freshest_rec is Some {
                    post.lsn_au_index[post.tj().seq_start()]
                } else {
                    0
                };
                &&& Self::semantic_journal_structure(post.tj().disk_view, post.freshest_rec, post.lsn_au_index, post_first)
                &&& post.lsn_au_index == post.tj().build_lsn_au_index_from_first(post_first)
            }),
        ensures
            post.inv(),
    {
        let msgs = pre.unmarshalled_tail.discard_recent(cut);
        let update = singleton_index(msgs.seq_start, msgs.seq_end, addr.au);
        pre.tj_inherits_semantic_structure();
        assert(post.tj() == pre.tj().append_record(addr, msgs));
        lsn_au_index_append_record_ensures(pre.lsn_au_index, msgs, addr.au);
        assert(LikesJournal_v::lsn_disjoint(pre.lsn_au_index.dom(), msgs.seq_start, msgs.seq_end)) by {
            let pre_first = if pre.tj().freshest_rec is Some {
                pre.lsn_au_index[pre.tj().seq_start()]
            } else {
                0
            };
            pre.tj_inherits_semantic_structure();
            pre.tj().build_lsn_au_index_from_first_ensures(pre_first);
            assert forall |lsn| msgs.seq_start <= lsn < msgs.seq_end
                implies !pre.lsn_au_index.dom().contains(lsn) by {
                assert(msgs.seq_start == pre.tj().seq_end());
                if pre.lsn_au_index.contains_key(lsn) {
                    assert(lsn < pre.tj().seq_end());
                    assert(false);
                }
            }
        }
        assert(post.lsn_au_index_before_tail()) by {
            assert forall |lsn: LSN| #[trigger] post.lsn_au_index.contains_key(lsn)
                implies lsn < post.unmarshalled_tail.seq_start by {
                if pre.lsn_au_index.contains_key(lsn) {
                    assert(pre.lsn_au_index_before_tail());
                    assert(lsn < pre.unmarshalled_tail.seq_start);
                    assert(pre.unmarshalled_tail.seq_start < cut);
                    assert(post.unmarshalled_tail.seq_start == cut);
                } else {
                    assert(update.contains_key(lsn));
                    assert(lsn < msgs.seq_end);
                    assert(msgs.seq_end == cut);
                    assert(post.unmarshalled_tail.seq_start == cut);
                }
            }
        }
        assert(post.au_page_bounds_match_index()) by {
            assert(post.au_page_bounds == pre.au_page_bounds.insert(addr.au, addr.page));
            assert(post.lsn_au_index == lsn_au_index_append_record(pre.lsn_au_index, msgs, addr.au));
            assert(post.lsn_au_index.values() == pre.lsn_au_index.values() + set![addr.au]);
            assert(pre.au_page_bounds.dom() =~= pre.lsn_au_index.values());
            assert(post.au_page_bounds.dom() =~= pre.au_page_bounds.dom() + set![addr.au]);
        }
        assert(Self::disk_domain_bounded_by_owned_aus(
            post.disk_view,
            post.lsn_au_index,
            post.mini_allocator,
        )) by {
            assert forall |x: Address| #[trigger] post.disk_view.entries.dom().contains(x)
                implies post.lsn_au_index.values().contains(x.au)
                    || post.mini_allocator.all_aus().contains(x.au) by {
                if x == addr {
                    assert(post.mini_allocator.all_aus().contains(x.au));
                } else {
                    assert(pre.disk_view.entries.dom().contains(x));
                    assert(Self::disk_domain_bounded_by_owned_aus(
                        pre.disk_view,
                        pre.lsn_au_index,
                        pre.mini_allocator,
                    ));
                    if pre.lsn_au_index.values().contains(x.au) {
                        let lsn = choose |lsn| #[trigger] pre.lsn_au_index.contains_key(lsn)
                            && pre.lsn_au_index[lsn] == x.au;
                        if update.contains_key(lsn) {
                            pre.tj().build_lsn_au_index_from_first_ensures(
                                if pre.tj().freshest_rec is Some {
                                    pre.lsn_au_index[pre.tj().seq_start()]
                                } else {
                                    0
                                },
                            );

                            assert(lsn < pre.tj().seq_end());
                            assert(msgs.seq_start == pre.tj().seq_end());
                            assert(false);
                        }
                        assert(post.lsn_au_index.contains_key(lsn));
                        assert(post.lsn_au_index[lsn] == x.au);
                    } else {
                        assert(pre.mini_allocator.all_aus().contains(x.au));
                        assert(post.mini_allocator.all_aus().contains(x.au));
                    }
                }
            }
        }

        assert(Self::disk_domain_not_free(post.tj().disk_view, post.mini_allocator)) by {
            assert forall |x: Address| #[trigger] post.tj().disk_view.entries.dom().contains(x)
                implies !post.mini_allocator.can_allocate(x) by {
                if x == addr {
                    assert(post.mini_allocator == pre.mini_allocator.allocate(addr));
                    assert(post.mini_allocator.allocs.contains_key(addr.au));
                    assert(post.mini_allocator.allocs[addr.au].allocated.contains(addr));
                    if post.mini_allocator.can_allocate(addr) {
                        assert(post.mini_allocator.allocs[addr.au].is_free_addr(addr));
                        assert(false);
                    }
                } else {
                    assert(pre.tj().disk_view.entries.contains_key(x));
                    assert(Self::disk_domain_not_free(pre.tj().disk_view, pre.mini_allocator));
                    if post.mini_allocator.can_allocate(x) {
                        pre.mini_allocator.allocate_can_allocate_subset(addr, x);
                        assert(pre.mini_allocator.can_allocate(x));
                        assert(false);
                    }
                }
            }
        }
        assert( post.inv() );
    }

    #[inductive(internal_journal_marshal)]
    fn internal_journal_marshal_inductive(pre: Self, post: Self, lbl: Label, cut: LSN, addr: Address) {
        let msgs = pre.unmarshalled_tail.discard_recent(cut);
        assert(post.disk_view.wf_addrs()) by {
            assert forall |x: Address| #[trigger] post.disk_view.entries.contains_key(x)
                implies x.wf() by {
                if x == addr {
                    assert(pre.mini_allocator.can_allocate(addr));
                } else {
                    assert(pre.disk_view.entries.contains_key(x));
                    assert(pre.disk_view.wf_addrs());
                }
            }
        }
        assert(post.wf());
        lsn_au_index_append_record_ensures(pre.lsn_au_index, msgs, addr.au);
        assert(LikesJournal_v::lsn_disjoint(pre.lsn_au_index.dom(), msgs.seq_start, msgs.seq_end)) by {
            assert forall |lsn: LSN| msgs.seq_start <= lsn < msgs.seq_end
                implies !pre.lsn_au_index.contains_key(lsn) by {
                assert(msgs.seq_start == pre.unmarshalled_tail.seq_start);
                assert(pre.lsn_au_index_before_tail());
                if pre.lsn_au_index.contains_key(lsn) {
                    assert(lsn < pre.unmarshalled_tail.seq_start);
                    assert(false);
                }
            }
        }
        assert(post.lsn_au_index_before_tail()) by {
            assert forall |lsn: LSN| #[trigger] post.lsn_au_index.contains_key(lsn)
                implies lsn < post.unmarshalled_tail.seq_start by {
                if pre.lsn_au_index.contains_key(lsn) {
                    assert(pre.lsn_au_index_before_tail());
                    assert(lsn < pre.unmarshalled_tail.seq_start);
                    assert(pre.unmarshalled_tail.seq_start < cut);
                    assert(post.unmarshalled_tail.seq_start == cut);
                } else {
                    let update = singleton_index(msgs.seq_start, msgs.seq_end, addr.au);
                    assert(update.contains_key(lsn));
                    assert(lsn < msgs.seq_end);
                    assert(msgs.seq_end == cut);
                    assert(post.unmarshalled_tail.seq_start == cut);
                }
            }
        }
        assert(Self::disk_domain_bounded_by_owned_aus(
            post.disk_view,
            post.lsn_au_index,
            post.mini_allocator,
        )) by {
            assert forall |x: Address| #[trigger] post.disk_view.entries.dom().contains(x)
                implies post.lsn_au_index.values().contains(x.au)
                    || post.mini_allocator.all_aus().contains(x.au) by {
                if x == addr {
                    assert(post.mini_allocator.all_aus().contains(x.au));
                } else {
                    assert(pre.disk_view.entries.dom().contains(x));
                    assert(Self::disk_domain_bounded_by_owned_aus(
                        pre.disk_view,
                        pre.lsn_au_index,
                        pre.mini_allocator,
                    ));
                    if pre.lsn_au_index.values().contains(x.au) {
                        let old_lsn = choose |old_lsn: LSN| #[trigger] pre.lsn_au_index.contains_key(old_lsn)
                            && pre.lsn_au_index[old_lsn] == x.au;
                        assert(post.lsn_au_index.contains_key(old_lsn));
                        assert(post.lsn_au_index[old_lsn] == x.au);
                    } else {
                        assert(pre.mini_allocator.all_aus().contains(x.au));
                        assert(post.mini_allocator.all_aus().contains(x.au));
                    }
                }
            }
        }
        assert(post.inv());
    }

    #[inductive(internal_no_op)]
    fn internal_no_op_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(initialize)]
    pub fn initialize_inductive(post: Self, image: JournalImage) {
        image.valid_image_implies_tight_valid_image();
        let tight_tj = image.tight_tj();
        let tight_dv = tight_tj.disk_view;
        let image_dv = image.tj.disk_view;

        assert(image.tj.disk_view.wf_addrs());
        assert(post.wf());

        let post_first = image.first;
        image_dv.path_build_tight_is_sub_disk(image.tj.freshest_rec);
        assert(tight_dv.is_sub_disk(image_dv));
        image_dv.path_build_bookkeeping_matches_tight(tight_tj.freshest_rec, post_first);
        image_dv.loose_build_lsn_au_index_au_walk_matches_tight(tight_tj.freshest_rec, post_first);
        image_dv.loose_build_au_page_bounds_au_walk_matches_tight(tight_tj.freshest_rec, post_first);
        assert(post.lsn_au_index == tight_dv.build_lsn_au_index_au_walk(tight_tj.freshest_rec, post_first));
        assert(post.au_page_bounds == tight_dv.build_au_page_bounds_au_walk(tight_tj.freshest_rec, post_first));
        post.tj().build_lsn_au_index_from_first_ensures(post_first);

        image.valid_image_implies_tight_seq_bounds();
        assert(post.lsn_au_index_before_tail()) by {
            tight_tj.build_lsn_au_index_from_first_ensures(post_first);
            assert forall |lsn: LSN| #[trigger] post.lsn_au_index.contains_key(lsn)
                implies lsn < post.unmarshalled_tail.seq_start by {
                assert(post.lsn_au_index == tight_tj.build_lsn_au_index_from_first(post_first));
                assert(lsn < tight_tj.seq_end());
            }
        }
        assert(Self::disk_domain_bounded_by_owned_aus(
            post.disk_view,
            post.lsn_au_index,
            post.mini_allocator,
        )) by {
            assert forall |addr| #[trigger] post.disk_view.entries.dom().contains(addr)
                implies post.lsn_au_index.values().contains(addr.au)
                    || post.mini_allocator.all_aus().contains(addr.au) by {
                assert(image.tj.disk_view.domain_au_bounded_wrt_index(post.lsn_au_index));
            }
        }
        assert( post.inv() );
    }

    pub proof fn initialize_semantic_inv(post: Self, image: JournalImage)
        requires
            Self::initialize(post, image),
        ensures
            post.semantic_inv(),
    {
        image.valid_image_implies_tight_valid_image();
        Self::initialize_tj_matches(post, image);
        let tight_tj = image.tight_tj();
        let tight_dv = tight_tj.disk_view;
        let image_dv = image.tj.disk_view;
        let first = image.first;
        image.valid_image_implies_tight_seq_bounds();

        image_dv.path_build_tight_is_sub_disk(image.tj.freshest_rec);
        assert(tight_dv.is_sub_disk(image_dv));
        image_dv.path_build_bookkeeping_matches_tight(tight_tj.freshest_rec, first);
        image_dv.loose_build_lsn_au_index_au_walk_matches_tight(tight_tj.freshest_rec, first);
        image_dv.loose_build_au_page_bounds_au_walk_matches_tight(tight_tj.freshest_rec, first);

        assert(post.tj() == tight_tj);
        assert(post.disk_view.path_decodable(post.freshest_rec));
        assert(post.semantic_wf()) by {
            assert(tight_tj.decodable());
            assert(tight_dv.wf());
            assert(tight_dv.acyclic());
            assert(tight_dv.is_nondangling_pointer(tight_tj.freshest_rec));
            assert(tight_dv.block_in_bounds(tight_tj.freshest_rec));
            assert(post.unmarshalled_tail == MsgHistory::empty_history_at(image.tj.seq_end()));
            assert(post.unmarshalled_tail.seq_start == image.tj.seq_end());
            assert(post.unmarshalled_tail.seq_start == tight_tj.seq_end());
            assert(post.disk_view.wf_addrs());
            assert(post.mini_allocator.wf());
        }

        tight_tj.build_lsn_au_index_from_first_ensures(first);

        assert(post.lsn_au_index == tight_tj.build_lsn_au_index_from_first(first));
        let bounds = tight_dv.build_au_page_bounds_au_walk(tight_tj.freshest_rec, first);
        assert(post.au_page_bounds == bounds);
        image.tj.disk_view.path_build_tight_idempotent(tight_tj.freshest_rec);
        assert(tight_dv == image.tj.disk_view.path_build_tight(tight_tj.freshest_rec));
        assert(image.tj.disk_view.path_build_tight(tight_tj.freshest_rec) == tight_dv);
        tight_dv.path_build_tight_equals_build_tight(tight_tj.freshest_rec);
        assert(tight_dv.path_build_tight(tight_tj.freshest_rec) == tight_dv);
        assert(tight_dv.path_build_tight(tight_tj.freshest_rec)
            == tight_dv.build_tight(tight_tj.freshest_rec));
        assert_maps_equal!(
            tight_dv.build_tight(tight_tj.freshest_rec).entries,
            tight_dv.entries
        );
        assert(tight_dv.build_tight(tight_tj.freshest_rec) == tight_dv);
        tight_dv.build_au_page_bounds_au_walk_domain_matches_build_tight(tight_tj.freshest_rec, first);
        assert(tight_dv.entries_bounded_by_au_page_bounds(bounds) == tight_dv.entries);
        assert(post.freshest_rec is Some ==> post.lsn_au_index.contains_key(post.seq_start()));
        assert(post.au_page_bounds_follow_freshest_rec()) by {
            if post.freshest_rec is Some {
                tight_dv.build_au_page_bounds_au_walk_root_bound(post.freshest_rec, first);
                assert(post.au_page_bounds.contains_key(post.freshest_rec.unwrap().au));
                assert(post.au_page_bounds[post.freshest_rec.unwrap().au] == post.freshest_rec.unwrap().page);
            }
        }
        assert(post.au_page_bounds_match_index()) by {
            assert forall |au: AU| #[trigger] post.au_page_bounds.dom().contains(au)
                <==> post.lsn_au_index.values().contains(au) by {
                if post.au_page_bounds.dom().contains(au) {
                    tight_dv.build_au_page_bounds_au_walk_dom_has_entry(tight_tj.freshest_rec, first);
                    let witness = choose |addr: Address| {
                        &&& #[trigger] tight_dv.entries_bounded_by_au_page_bounds(bounds).contains_key(addr)
                        &&& addr.au == au
                    };
                    assert(tight_dv.entries.contains_key(witness));
                    assert(tight_dv.domain_au_bounded_wrt_index(post.lsn_au_index));
                    assert(post.lsn_au_index.values().contains(au));
                }
                if post.lsn_au_index.values().contains(au) {
                    let lsn = choose |lsn: LSN| #[trigger] post.lsn_au_index.contains_key(lsn)
                        && post.lsn_au_index[lsn] == au;
                    let witness = tight_dv.instantiate_index_keys_exist_valid_entries(post.lsn_au_index, lsn);
                    assert(tight_dv.entries_bounded_by_au_page_bounds(bounds).contains_key(witness));
                    assert(bounds.contains_key(witness.au));
                    assert(post.au_page_bounds.dom().contains(au));
                }
            }
        }
        let computed_index = tight_dv.build_lsn_au_index_au_walk(post.freshest_rec, first);
        assert(Self::semantic_journal_structure(tight_dv, post.freshest_rec, computed_index, first));
        assert(post.lsn_au_index == computed_index);
        assert(post.has_valid_acyclic_subdisk());
        assert(post.semantic_entries_bounded_by_au_page_bounds()) by {
            assert forall |addr: Address| #[trigger] post.tj().disk_view.entries.contains_key(addr) implies {
                &&& post.au_page_bounds.contains_key(addr.au)
                &&& addr.page <= post.au_page_bounds[addr.au]
            } by {
                assert(tight_dv.entries_bounded_by_au_page_bounds(bounds).contains_key(addr));
            }
        }
        assert(post.tj().disk_view.domain_tight_wrt_index(post.lsn_au_index, post.freshest_rec)) by {
            assert forall |addr: Address| #[trigger] post.tj().disk_view.entries.dom().contains(addr) implies {
                &&& post.lsn_au_index.values().contains(addr.au)
                &&& post.freshest_rec is Some ==> !post.freshest_rec.unwrap().after_page(addr)
            } by {
                assert(post.semantic_entries_bounded_by_au_page_bounds());
                assert(post.au_page_bounds_match_index());
                if post.freshest_rec is Some && post.freshest_rec.unwrap().after_page(addr) {
                    assert(addr.au == post.freshest_rec.unwrap().au);
                    assert(post.au_page_bounds_follow_freshest_rec());
                    assert(post.au_page_bounds[addr.au] == post.freshest_rec.unwrap().page);
                    assert(addr.page <= post.au_page_bounds[addr.au]);
                    assert(addr.page > post.freshest_rec.unwrap().page);
                    assert(false);
                }
            }
        }
        assert(post.bounded_live_entries_are_semantic()) by {
            assert forall |addr: Address| ({
                let record = post.disk_view.entries[addr];
                &&& #[trigger] post.disk_view.entries.contains_key(addr)
                &&& post.au_page_bounds.contains_key(addr.au)
                &&& addr.page <= post.au_page_bounds[addr.au]
                &&& post.disk_view.boundary_lsn < record.message_seq.seq_end
            }) implies post.tj().disk_view.entries.contains_key(addr) by {
                assert(post.disk_view == image.tj.disk_view);
                assert(post.au_page_bounds == tight_dv.build_au_page_bounds_au_walk(tight_tj.freshest_rec, image.first));
                assert(image.bounded_live_entries_are_tight());
            }
        }
        assert(Self::disk_domain_bounded_by_owned_aus(
            post.disk_view,
            post.lsn_au_index,
            post.mini_allocator,
        ));
        assert(Self::disk_domain_not_free(tight_dv, post.mini_allocator));
        assert(Self::mini_allocator_follows_freshest_rec(post.freshest_rec, post.mini_allocator));
        assert(post.indexed_lsn_witnesses_are_semantic()) by {
            assert forall |addr: Address, lsn: LSN| ({
                let record = post.disk_view.entries[addr];
                &&& #[trigger] post.disk_view.entries.contains_key(addr)
                &&& post.au_page_bounds.contains_key(addr.au)
                &&& addr.page <= post.au_page_bounds[addr.au]
                &&& post.seq_start() < record.message_seq.seq_end
                &&& record.message_seq.contains(lsn)
                &&& #[trigger] post.lsn_au_index.contains_key(lsn)
                &&& post.lsn_au_index[lsn] == addr.au
            }) implies post.tj().disk_view.entries.contains_key(addr) by {
                assert(post.bounded_live_entries_are_semantic());
            }
        }
        assert(post.au_page_bounds_covered()) by {
            assert forall |addr: Address| {
                &&& #[trigger] post.lsn_au_index.values().contains(addr.au)
                &&& post.au_page_bounds.contains_key(addr.au)
                &&& addr.page <= post.au_page_bounds[addr.au]
            } implies post.disk_view.entries.contains_key(addr) by {
                assert(post.disk_view == image.tj.disk_view);
                assert(post.lsn_au_index == tight_tj.build_lsn_au_index_from_first(first));
                assert(post.au_page_bounds == bounds);
                assert(image.au_page_bounds_covered());
            }
        }
        assert(post.indexed_aus_not_all_pages_free()) by {
            assert forall |au: AU| {
                &&& #[trigger] post.lsn_au_index.values().contains(au)
                &&& post.mini_allocator.allocs.contains_key(au)
            } implies !post.mini_allocator.allocs[au].all_pages_free() by {
                assert(post.mini_allocator == MiniAllocator::empty());
                assert(!post.mini_allocator.allocs.contains_key(au));
            }
        }
        assert(post.semantic_inv());
    }

    // NOTE(JL): temporary workaround
    pub proof fn inv_next(pre: Self, post: Self, lbl: Label)
    requires pre.inv(), Self::next(pre, post, lbl)
    ensures post.inv()
    {
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);

        let step = choose |step| Self::next_by(pre, post, lbl, step);
        match step {
            AllocationJournal::Step::freeze_for_commit() => {
                Self::freeze_for_commit_inductive(pre, post, lbl);
            },
            AllocationJournal::Step::read_for_recovery(start_lsn, addr) => {
                Self::read_for_recovery_inductive(pre, post, lbl, start_lsn, addr);
            },
            AllocationJournal::Step::put() => {
                Self::put_inductive(pre, post, lbl);
            },
            AllocationJournal::Step::internal_mini_allocator_fill(post_disk_view) => {
                Self::internal_mini_allocator_fill_inductive(pre, post, lbl, post_disk_view);
            },
            AllocationJournal::Step::internal_mini_allocator_prune(prune_aus) => {
                Self::internal_mini_allocator_prune_inductive(pre, post, lbl, prune_aus);
            },
            AllocationJournal::Step::discard_old() => {
                Self::discard_old_inductive(pre, post, lbl);
            },
            AllocationJournal::Step::internal_journal_marshal(cut, addr) => {
                Self::internal_journal_marshal_inductive(pre, post, lbl, cut, addr);
            },
            _ => {
                assert(post.inv());
            },
        }
    }

    pub proof fn internal_journal_marshal_semantic_inv(
        pre: Self,
        post: Self,
        lbl: Label,
        cut: LSN,
        addr: Address,
    )
        requires
            pre.inv(),
            pre.semantic_inv(),
            Self::internal_journal_marshal(pre, post, lbl, cut, addr),
        ensures
            post.inv(),
            post.semantic_inv(),
    {
        let msgs = pre.unmarshalled_tail.discard_recent(cut);
        pre.tj_inherits_semantic_structure();
        Self::internal_journal_marshal_view_preserves(pre, post, lbl, cut, addr);
        Self::internal_journal_marshal_index_preserves(pre, post, lbl, cut, addr);
        Self::internal_journal_marshal_allocator_preserves(pre, post, lbl, cut, addr);
        lsn_au_index_append_record_ensures(pre.lsn_au_index, msgs, addr.au);

        assert(post.au_page_bounds_match_index()) by {
            assert(post.au_page_bounds == pre.au_page_bounds.insert(addr.au, addr.page));
            assert(post.lsn_au_index == lsn_au_index_append_record(pre.lsn_au_index, msgs, addr.au));
            assert(post.lsn_au_index.values() == pre.lsn_au_index.values() + set![addr.au]);
            assert(pre.au_page_bounds_match_index());
            assert(post.au_page_bounds.dom() =~= pre.au_page_bounds.dom() + set![addr.au]);
        }
        assert(post.tj().disk_view.is_sub_disk(post.disk_view)) by {
            assert(post.tj().disk_view.entries <= post.disk_view.entries);
        }
        post.disk_view.sub_disk_decodable_implies_path_decodable(post.tj().disk_view, post.freshest_rec);
        assert(post.disk_view.path_decodable(post.freshest_rec));

        let semantic_dv = post.tj().disk_view;
        let first = if post.freshest_rec is Some {
            post.lsn_au_index[post.seq_start()]
        } else {
            0
        };
        let computed_index = semantic_dv.build_lsn_au_index_au_walk(post.freshest_rec, first);
        assert(post.semantic_wf());
        assert(Self::semantic_journal_structure(semantic_dv, post.freshest_rec, post.lsn_au_index, first));
        assert(computed_index == post.lsn_au_index);
        assert(post.has_valid_acyclic_subdisk()) by {
            post.tj_view_is_valid_acyclic_subdisk();
        }
        post.tj().build_lsn_au_index_from_first_ensures(first);
        assert(post.tj().disk_view.domain_tight_wrt_index(post.lsn_au_index, post.freshest_rec));
        assert(post.semantic_entries_bounded_by_au_page_bounds()) by {
            assert forall |x: Address| #[trigger] post.tj().disk_view.entries.contains_key(x) implies {
                &&& post.au_page_bounds.contains_key(x.au)
                &&& x.page <= post.au_page_bounds[x.au]
            } by {
                if x == addr {
                    assert(post.au_page_bounds.contains_key(x.au));
                    assert(post.au_page_bounds[x.au] == x.page);
                } else {
                    assert(pre.tj().disk_view.entries.contains_key(x));
                    assert(pre.semantic_entries_bounded_by_au_page_bounds());
                    if x.au == addr.au {
                        assert(pre.mini_allocator.tight_next_addr(pre.freshest_rec, addr));
                        if pre.freshest_rec is Some {
                            assert(addr == pre.freshest_rec.unwrap().next());
                            if pre.freshest_rec.unwrap().au == x.au {
                                assert(!pre.freshest_rec.unwrap().after_page(x));
                                assert(x.page <= pre.freshest_rec.unwrap().page);
                                assert(pre.freshest_rec.unwrap().page < addr.page);
                            }
                        } else {
                            assert(pre.tj().disk_view.entries =~= Map::<Address, LinkedJournal_v::JournalRecord>::empty());
                            assert(false);
                        }
                    }
                }
            }
        }
        assert(post.bounded_live_entries_are_semantic()) by {
            assert forall |x: Address| ({
                let record = post.disk_view.entries[x];
                &&& #[trigger] post.disk_view.entries.contains_key(x)
                &&& post.au_page_bounds.contains_key(x.au)
                &&& x.page <= post.au_page_bounds[x.au]
                &&& post.disk_view.boundary_lsn < record.message_seq.seq_end
            }) implies post.tj().disk_view.entries.contains_key(x) by {
                if x == addr {
                    assert(post.tj().disk_view.entries.contains_key(addr));
                } else {
                    assert(pre.disk_view.entries.contains_key(x));
                    assert(pre.disk_view.entries[x] == post.disk_view.entries[x]);
                    if x.au == addr.au {
                        assert(post.au_page_bounds[x.au] == addr.page);
                        assert(x.page <= addr.page);
                        assert(pre.mini_allocator.tight_next_addr(pre.freshest_rec, addr));
                        if pre.mini_allocator.curr is None {
                            assert(addr.page == 0);
                            assert(x.page == 0);
                            assert(x == addr);
                            assert(false);
                        } else {
                            assert(pre.freshest_rec is Some);
                            assert(addr == pre.freshest_rec.unwrap().next());
                            assert(x.page < addr.page);
                            assert(x.page <= pre.freshest_rec.unwrap().page);
                            assert(pre.au_page_bounds_follow_freshest_rec());
                            assert(pre.au_page_bounds.contains_key(x.au));
                            assert(pre.au_page_bounds[x.au] == pre.freshest_rec.unwrap().page);
                        }
                    } else {
                        assert(pre.au_page_bounds.contains_key(x.au));
                        assert(pre.au_page_bounds[x.au] == post.au_page_bounds[x.au]);
                    }
                    assert(pre.bounded_live_entries_are_semantic());
                    assert(pre.tj().disk_view.entries.contains_key(x));
                    assert(post.tj().disk_view.entries.contains_key(x));
                }
            }
        }
        assert(post.indexed_lsn_witnesses_are_semantic()) by {
            assert forall |x: Address, lsn: LSN| ({
                let record = post.disk_view.entries[x];
                &&& #[trigger] post.disk_view.entries.contains_key(x)
                &&& post.au_page_bounds.contains_key(x.au)
                &&& x.page <= post.au_page_bounds[x.au]
                &&& post.seq_start() < record.message_seq.seq_end
                &&& record.message_seq.contains(lsn)
                &&& #[trigger] post.lsn_au_index.contains_key(lsn)
                &&& post.lsn_au_index[lsn] == x.au
            }) implies post.tj().disk_view.entries.contains_key(x) by {
                assert(post.bounded_live_entries_are_semantic());
            }
        }
        assert(post.au_page_bounds_covered());
        assert(post.indexed_aus_not_all_pages_free()) by {
            assert forall |au: AU| {
                &&& #[trigger] post.lsn_au_index.values().contains(au)
                &&& post.mini_allocator.allocs.contains_key(au)
            } implies !post.mini_allocator.allocs[au].all_pages_free() by {
                if au == addr.au {
                    assert(post.mini_allocator
                        == pre.mini_allocator.allocate(addr));
                    assert(post.mini_allocator.allocs[au].allocated.contains(addr));
                    assert(!post.mini_allocator.allocs[au].has_no_allocated_pages());
                    assert(!post.mini_allocator.allocs[au].all_pages_free());
                } else {
                    assert(pre.lsn_au_index.values().contains(au)) by {
                        let lsn = choose |lsn: LSN| #![trigger post.lsn_au_index.contains_key(lsn)] {
                            post.lsn_au_index.contains_key(lsn) && post.lsn_au_index[lsn] == au
                        };
                        assert(post.lsn_au_index.contains_key(lsn));
                        assert(!singleton_index(
                            pre.unmarshalled_tail.discard_recent(cut).seq_start,
                            pre.unmarshalled_tail.discard_recent(cut).seq_end,
                            addr.au,
                        ).contains_key(lsn));
                        assert(pre.lsn_au_index.contains_key(lsn));
                        assert(pre.lsn_au_index[lsn] == au);
                    }
                    assert(post.mini_allocator
                        == pre.mini_allocator.allocate(addr));
                    assert(post.mini_allocator.allocs[au] == pre.mini_allocator.allocs[au]);
                    assert(pre.indexed_aus_not_all_pages_free());
                }
            }
        }
        assert(post.semantic_inv());
    }

    pub proof fn internal_mini_allocator_fill_semantic_inv(
        pre: Self,
        post: Self,
        lbl: Label,
        post_disk_view: DiskView,
    )
        requires
            pre.inv(),
            pre.semantic_inv(),
            Self::internal_mini_allocator_fill(pre, post, lbl, post_disk_view),
        ensures
            post.inv(),
            post.semantic_inv(),
    {
        Self::internal_mini_allocator_fill_inductive(pre, post, lbl, post_disk_view);
        reveal(AllocationJournal::State::next_by);
        assert(AllocationJournal::State::next_by(
            pre,
            post,
            lbl,
            AllocationJournal::Step::internal_mini_allocator_fill(post_disk_view),
        ));
        Self::internal_mini_allocator_fill_tj_unchanged(pre, post, lbl, post_disk_view);
        assert(post.tj() == pre.tj());
        assert(post.semantic_wf()) by {
            assert(pre.semantic_wf());
            assert(post.tj().disk_view == pre.tj().disk_view);
            assert(post.disk_view.path_decodable(post.freshest_rec));
        }
        assert(post.au_page_bounds_match_index()) by {
            assert(post.au_page_bounds == pre.au_page_bounds);
            assert(post.lsn_au_index == pre.lsn_au_index);
            assert(pre.au_page_bounds_match_index());
        }
        assert(post.au_page_bounds_follow_freshest_rec()) by {
            assert(post.au_page_bounds == pre.au_page_bounds);
            assert(post.freshest_rec == pre.freshest_rec);
            assert(pre.au_page_bounds_follow_freshest_rec());
        }
        assert(post.freshest_rec is Some ==> post.lsn_au_index.contains_key(post.seq_start())) by {
            assert(post.freshest_rec == pre.freshest_rec);
            assert(post.lsn_au_index == pre.lsn_au_index);
            assert(post.seq_start() == pre.seq_start());
        }
        assert(post.has_valid_acyclic_subdisk()) by {
            post.tj_view_is_valid_acyclic_subdisk();
        }
        assert(post.bounded_live_entries_are_semantic()) by {
            assert forall |addr: Address| ({
                let record = post.disk_view.entries[addr];
                &&& #[trigger] post.disk_view.entries.contains_key(addr)
                &&& post.au_page_bounds.contains_key(addr.au)
                &&& addr.page <= post.au_page_bounds[addr.au]
                &&& post.disk_view.boundary_lsn < record.message_seq.seq_end
            }) implies post.tj().disk_view.entries.contains_key(addr) by {
                if pre.disk_view.entries.contains_key(addr) {
                    assert(pre.disk_view.entries[addr] == post.disk_view.entries[addr]);
                    assert(pre.bounded_live_entries_are_semantic());
                    assert(pre.tj().disk_view.entries.contains_key(addr));
                    assert(post.tj().disk_view.entries.contains_key(addr));
                } else {
                    assert(lbl->allocs.contains(addr.au));
                    assert(post.au_page_bounds_match_index());
                    assert(post.lsn_au_index.values().contains(addr.au));
                    assert(post.lsn_au_index == pre.lsn_au_index);
                    assert(!lbl->allocs.contains(addr.au));
                    assert(false);
                }
            }
        }
        assert(post.indexed_lsn_witnesses_are_semantic()) by {
            assert forall |addr: Address, lsn: LSN| ({
                let record = post.disk_view.entries[addr];
                &&& #[trigger] post.disk_view.entries.contains_key(addr)
                &&& post.au_page_bounds.contains_key(addr.au)
                &&& addr.page <= post.au_page_bounds[addr.au]
                &&& post.seq_start() < record.message_seq.seq_end
                &&& record.message_seq.contains(lsn)
                &&& #[trigger] post.lsn_au_index.contains_key(lsn)
                &&& post.lsn_au_index[lsn] == addr.au
            }) implies post.tj().disk_view.entries.contains_key(addr) by {
                assert(post.bounded_live_entries_are_semantic());
            }
        }
        assert(Self::disk_domain_not_free(post.tj().disk_view, post.mini_allocator)) by {
            assert forall |addr: Address| #[trigger] post.tj().disk_view.entries.dom().contains(addr)
                implies !post.mini_allocator.can_allocate(addr) by {
                assert(pre.tj().disk_view.entries.contains_key(addr));
                assert(Self::disk_domain_not_free(pre.tj().disk_view, pre.mini_allocator));
                if post.mini_allocator.can_allocate(addr) {
                    if pre.mini_allocator.allocs.contains_key(addr.au) {
                        assert(pre.mini_allocator.can_allocate(addr));
                    } else {
                        assert(lbl->allocs.contains(addr.au));
                        assert(pre.tj().disk_view.domain_au_bounded_wrt_index(pre.lsn_au_index));
                        assert(pre.lsn_au_index.values().contains(addr.au));
                        assert(!lbl->allocs.contains(addr.au));
                    }
                    assert(false);
                }
            }
        }
        assert(post.semantic_inv());
    }

    pub proof fn internal_mini_allocator_prune_semantic_inv(
        pre: Self,
        post: Self,
        lbl: Label,
        prune_aus: Set<AU>,
    )
        requires
            pre.inv(),
            pre.semantic_inv(),
            Self::internal_mini_allocator_prune(pre, post, lbl, prune_aus),
        ensures
            post.inv(),
            post.semantic_inv(),
    {
        Self::internal_mini_allocator_prune_inductive(pre, post, lbl, prune_aus);
        reveal(AllocationJournal::State::next_by);
        assert(AllocationJournal::State::next_by(
            pre,
            post,
            lbl,
            AllocationJournal::Step::internal_mini_allocator_prune(prune_aus),
        ));
        Self::internal_mini_allocator_prune_tj_unchanged(pre, post, lbl, prune_aus);
        assert(post.tj() == pre.tj());
        assert(post.semantic_wf()) by {
            assert(pre.semantic_wf());
            assert(post.tj().disk_view == pre.tj().disk_view);
            assert(post.disk_view.path_decodable(post.freshest_rec));
        }
        assert(post.au_page_bounds_match_index()) by {
            assert(post.au_page_bounds == pre.au_page_bounds);
            assert(post.lsn_au_index == pre.lsn_au_index);
            assert(pre.au_page_bounds_match_index());
        }
        assert(post.au_page_bounds_follow_freshest_rec()) by {
            assert(post.au_page_bounds == pre.au_page_bounds);
            assert(post.freshest_rec == pre.freshest_rec);
            assert(pre.au_page_bounds_follow_freshest_rec());
        }
        assert(post.freshest_rec is Some ==> post.lsn_au_index.contains_key(post.seq_start())) by {
            assert(post.freshest_rec == pre.freshest_rec);
            assert(post.lsn_au_index == pre.lsn_au_index);
            assert(post.seq_start() == pre.seq_start());
        }
        assert(post.has_valid_acyclic_subdisk()) by {
            post.tj_view_is_valid_acyclic_subdisk();
        }
        assert(post.bounded_live_entries_are_semantic()) by {
            assert forall |addr: Address| ({
                let record = post.disk_view.entries[addr];
                &&& #[trigger] post.disk_view.entries.contains_key(addr)
                &&& post.au_page_bounds.contains_key(addr.au)
                &&& addr.page <= post.au_page_bounds[addr.au]
                &&& post.disk_view.boundary_lsn < record.message_seq.seq_end
            }) implies post.tj().disk_view.entries.contains_key(addr) by {
                assert(pre.disk_view.entries.contains_key(addr));
                assert(pre.disk_view.entries[addr] == post.disk_view.entries[addr]);
                assert(pre.bounded_live_entries_are_semantic());
                assert(pre.tj().disk_view.entries.contains_key(addr));
                assert(post.tj().disk_view.entries.contains_key(addr));
            }
        }
        assert(post.indexed_lsn_witnesses_are_semantic()) by {
            assert forall |addr: Address, lsn: LSN| ({
                let record = post.disk_view.entries[addr];
                &&& #[trigger] post.disk_view.entries.contains_key(addr)
                &&& post.au_page_bounds.contains_key(addr.au)
                &&& addr.page <= post.au_page_bounds[addr.au]
                &&& post.seq_start() < record.message_seq.seq_end
                &&& record.message_seq.contains(lsn)
                &&& #[trigger] post.lsn_au_index.contains_key(lsn)
                &&& post.lsn_au_index[lsn] == addr.au
            }) implies post.tj().disk_view.entries.contains_key(addr) by {
                assert(post.bounded_live_entries_are_semantic());
            }
        }
        assert(Self::disk_domain_not_free(post.tj().disk_view, post.mini_allocator)) by {
            assert forall |addr: Address| #[trigger] post.tj().disk_view.entries.dom().contains(addr)
                implies !post.mini_allocator.can_allocate(addr) by {
                assert(pre.tj().disk_view.entries.contains_key(addr));
                assert(Self::disk_domain_not_free(pre.tj().disk_view, pre.mini_allocator));
                if post.mini_allocator.can_allocate(addr) {
                    assert(post.mini_allocator.allocs.contains_key(addr.au));
                    assert(post.mini_allocator.all_aus() == pre.mini_allocator.all_aus().difference(prune_aus));
                    assert(pre.mini_allocator.allocs.contains_key(addr.au));
                    assert(!prune_aus.contains(addr.au));
                    assert(pre.mini_allocator.can_allocate(addr));
                    assert(false);
                }
            }
        }
        assert(post.semantic_inv());
    }

    // utility functions for refinement layers below

    #[verifier::spinoff_prover]
    pub proof fn frozen_journal_is_valid_image(pre: Self, post: Self, lbl: AllocationJournal::Label)
    requires pre.semantic_inv(), post.inv(), lbl is FreezeForCommit, Self::next(pre, post, lbl)
    ensures
        pre.frozen_image(lbl->frozen_journal).valid_image(),
        pre.frozen_image(lbl->frozen_journal).tight_tj().disk_view.is_sub_disk_with_newer_lsn(pre.tj().disk_view),
        pre.frozen_image(lbl->frozen_journal).tight_tj().build_lsn_au_index_from_first(
            lbl->frozen_journal.first,
        ) == pre.frozen_lsn_au_index(lbl->frozen_journal),
        pre.frozen_image(lbl->frozen_journal).tj.seq_start() == lbl->frozen_journal.boundary_lsn,
        pre.frozen_image(lbl->frozen_journal).tj.seq_end() == lbl->frozen_journal.seq_end,
        ({
            let image = pre.frozen_image(lbl->frozen_journal);
            let tight = image.tight_tj();
            let tight_bounds = tight.disk_view.build_au_page_bounds_au_walk(
                tight.freshest_rec,
                image.first,
            );
            forall |addr: Address| {
                let record = image.tj.disk_view.entries[addr];
                &&& #[trigger] image.tj.disk_view.entries.contains_key(addr)
                &&& tight_bounds.contains_key(addr.au)
                &&& addr.page <= tight_bounds[addr.au]
                &&& image.tj.seq_start() < record.message_seq.seq_end
            } ==> pre.frozen_prefix_domain(lbl->frozen_journal).contains(addr)
        }),
    {
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);

        let frozen = lbl->frozen_journal;
        let full_tj = pre.tj();
        let full_dv = full_tj.disk_view;
        let full_index = pre.lsn_au_index;
        let frozen_tj = pre.frozen_tj(frozen);
        let frozen_dv = frozen_tj.disk_view;
        let frozen_journal = pre.frozen_image(frozen);
        let sub_first = if frozen.freshest_rec is Some {
            full_index[frozen.boundary_lsn]
        } else {
            0
        };
        let first = if pre.freshest_rec is Some {
            full_index[pre.seq_start()]
        } else {
            0
        };

        pre.tj_inherits_semantic_structure();
        assert(pre.frozen_metadata_valid(frozen));
        assert(pre.wf());
        assert(full_tj.valid_structure(full_index, first));
        full_tj.build_lsn_au_index_from_first_ensures(first);


        if frozen.freshest_rec is Some {
            let root = frozen.freshest_rec.unwrap();
            assert(pre.disk_view.entries.contains_key(root));
            assert(pre.au_page_bounds.contains_key(root.au));
            assert(root.page <= pre.au_page_bounds[root.au]);
            assert(pre.seq_start() < pre.disk_view.entries[root].message_seq.seq_end);
            let last_lsn = (frozen.seq_end - 1) as nat;
            assert(pre.disk_view.entries[root].message_seq.contains(last_lsn));
            assert(pre.lsn_au_index.contains_key(last_lsn));
            assert(pre.lsn_au_index[last_lsn] == root.au);
            assert(pre.indexed_lsn_witnesses_are_semantic());
            assert(full_dv.entries.contains_key(root));
            assert(full_dv.entries[root] == pre.disk_view.entries[root]);
            assert(frozen.seq_end == full_dv.entries[root].message_seq.seq_end);
            assert(full_dv.entries[root].message_seq.contains(last_lsn));
            assert(full_dv.addr_supports_lsn(root, last_lsn));
            assert(full_tj.seq_start() <= last_lsn);
            assert(last_lsn < full_tj.seq_end());
            assert(full_index.contains_key(last_lsn));
            full_dv.addr_supports_lsn_consistent_with_index(full_index, last_lsn, root);
            assert(full_index[frozen.boundary_lsn] == frozen.first);
        }

        assert(sub_first == frozen.first) by {
            if frozen.freshest_rec is Some {
                assert(full_index[frozen.boundary_lsn] == frozen.first);
            }
        }
        assert(full_tj.valid_subrange(
            full_index,
            first,
            frozen.boundary_lsn,
            frozen.freshest_rec,
            sub_first,
        ));
        let sub_dv = full_tj.sub_disk_preserves_pointer_is_upstream(
            full_index,
            first,
            frozen.boundary_lsn,
            frozen.freshest_rec,
            sub_first,
        );
        let frozen_index = pre.frozen_lsn_au_index(frozen);
        let sub_tj = TruncatedJournal{disk_view: sub_dv, freshest_rec: frozen.freshest_rec};
        if frozen.freshest_rec is Some {
            full_tj.sub_disk_preserves_bounded_inactive_lsns(
                full_index,
                first,
                sub_tj,
                sub_first,
            );
        }
        pre.tj_view_is_valid_acyclic_subdisk();
        let frozen_backing_dv = frozen_dv;
        assert(sub_dv.domain_au_bounded_wrt_index(frozen_index));
        assert(sub_dv.entries <= frozen_backing_dv.entries) by {
            assert forall |addr: Address| #[trigger] sub_dv.entries.contains_key(addr)
                implies frozen_backing_dv.entries.contains_key(addr)
                    && sub_dv.entries[addr] == frozen_backing_dv.entries[addr] by {
                assert(full_dv.entries.contains_key(addr));
                assert(full_dv.is_sub_disk(pre.disk_view));
                assert(pre.disk_view.entries.contains_key(addr));
                assert(pre.disk_view.entries[addr] == full_dv.entries[addr]);
                assert(frozen_index.values().contains(addr.au));
                assert(pre.frozen_domain(frozen).contains(addr));
            }
        }
        frozen_backing_dv.decodable_sub_disk_path_build_tight_matches_build_tight(
            sub_dv,
            frozen.freshest_rec,
        );
        frozen_backing_dv.path_build_tight_is_sub_disk(frozen.freshest_rec);
        let tight_tj = frozen_journal.tight_tj();
        frozen_backing_dv.path_build_tight_path_decodable(frozen.freshest_rec);
        frozen_backing_dv.path_build_tight_idempotent(frozen.freshest_rec);
        assert(tight_tj.disk_view == frozen_dv.path_build_tight(frozen.freshest_rec));
        assert(tight_tj.disk_view == frozen_backing_dv.path_build_tight(frozen.freshest_rec));
        assert(tight_tj.disk_view == sub_dv.build_tight(frozen.freshest_rec));
        assert(sub_tj.build_tight().disk_view == sub_dv.build_tight(frozen.freshest_rec));
        assert(tight_tj.freshest_rec == sub_tj.build_tight().freshest_rec);
        assert(tight_tj == sub_tj.build_tight());
        let tight_dv = tight_tj.disk_view;
        sub_dv.build_tight_ensures(frozen.freshest_rec);
        assert(tight_dv.is_sub_disk(sub_dv));
        tight_dv.sub_disk_ranking(sub_dv);
        assert(tight_tj.decodable());
        assert(tight_dv.nonzero_pages_point_backward()) by {
            assert forall |addr: Address|
                ({
                    &&& addr.page != 0
                    &&& #[trigger] tight_dv.entries.contains_key(addr)
                }) implies tight_dv.entries[addr].prior_rec == Some(addr.previous()) by {
                assert(sub_dv.entries.contains_key(addr));
                assert(tight_dv.entries[addr] == sub_dv.entries[addr]);
                assert(sub_dv.nonzero_pages_point_backward());
            }
        }
        reveal(DiskView::pages_allocated_in_lsn_order);

        assert(tight_dv.pages_allocated_in_lsn_order()) by {
            assert forall |alo: Address, ahi: Address|
                ({
                    &&& alo.au == ahi.au
                    &&& alo.page < ahi.page
                    &&& #[trigger] tight_dv.entries.contains_key(alo)
                    &&& #[trigger] tight_dv.entries.contains_key(ahi)
                }) implies tight_dv.entries[alo].message_seq.seq_end
                    <= tight_dv.entries[ahi].message_seq.seq_start by {
                assert(sub_dv.entries.contains_key(alo));
                assert(sub_dv.entries.contains_key(ahi));
                assert(tight_dv.entries[alo] == sub_dv.entries[alo]);
                assert(tight_dv.entries[ahi] == sub_dv.entries[ahi]);
                assert(sub_dv.pages_allocated_in_lsn_order());
            }
        }
        assert(tight_dv.internal_au_pages_fully_linked());
        assert(tight_dv.has_unique_lsns()) by {
            assert forall |lsn, addr1, addr2|
                tight_dv.addr_supports_lsn(addr1, lsn)
                && tight_dv.addr_supports_lsn(addr2, lsn)
                implies addr1 == addr2 by {
                assert(sub_dv.addr_supports_lsn(addr1, lsn));
                assert(sub_dv.addr_supports_lsn(addr2, lsn));
                assert(sub_dv.has_unique_lsns());
            }
        }
        if frozen.freshest_rec is Some {
            assert(sub_dv.valid_first_au(sub_first));
            let first_addr = choose |addr: Address| #![auto]
                addr.au == sub_first && sub_dv.addr_supports_lsn(addr, sub_dv.boundary_lsn);
            assert(sub_dv.entries.contains_key(first_addr));
            assert(!frozen.freshest_rec.unwrap().after_page(first_addr)) by {
                assert(full_index.restrict(pre.frozen_lsns(frozen)).values().contains(first_addr.au));
                assert(sub_dv.entries.contains_key(first_addr));
            }
            assert(sub_dv.boundary_lsn < sub_dv.entries[first_addr].message_seq.seq_end);
            sub_dv.boundary_crossing_entry_in_build_tight(
                frozen.freshest_rec,
                sub_first,
                frozen_index,
                first_addr,
            );
            assert(tight_dv.entries.contains_key(first_addr));
            assert(tight_dv.entries[first_addr] == sub_dv.entries[first_addr]);
            assert(tight_dv.boundary_lsn == sub_dv.boundary_lsn);
            assert(tight_dv.addr_supports_lsn(first_addr, tight_dv.boundary_lsn));
            assert(tight_dv.valid_first_au(sub_first));
            assert(tight_dv.entries.contains_key(frozen.freshest_rec.unwrap()));
            assert(tight_dv.upstream(frozen.freshest_rec.unwrap()));
        }
        assert(tight_dv.pointer_is_upstream(tight_tj.freshest_rec, sub_first));
        assert(tight_dv.pointer_is_upstream(tight_tj.freshest_rec, frozen.first));
        let frozen_built_index = tight_tj.build_lsn_au_index_from_first(frozen.first);
        assert(sub_tj.disk_view.pointer_is_upstream(sub_tj.freshest_rec, sub_first));
        sub_tj.build_lsn_au_index_from_first_ensures(sub_first);
        tight_tj.build_lsn_au_index_from_first_ensures(frozen.first);
        sub_dv.build_lsn_au_index_equiv_page_walk(frozen.freshest_rec, sub_first);
        tight_dv.build_lsn_au_index_equiv_page_walk(frozen.freshest_rec, frozen.first);
        tight_dv.build_lsn_au_index_page_walk_sub_disk(sub_dv, frozen.freshest_rec);
        assert(sub_dv.build_lsn_au_index_page_walk(frozen.freshest_rec)
            == tight_dv.build_lsn_au_index_page_walk(frozen.freshest_rec));
        assert(frozen_built_index == frozen_index);
        assert(tight_dv.domain_au_bounded_wrt_index(frozen_built_index)) by {
            assert forall |addr: Address| #[trigger] tight_dv.entries.dom().contains(addr)
                implies frozen_built_index.values().contains(addr.au) by {
                assert(sub_dv.entries.contains_key(addr));
                assert(sub_dv.domain_au_bounded_wrt_index(frozen_index));
            }
        }
        if frozen.freshest_rec is Some {
            tight_tj.boundary_au_matches_first(sub_first);
            full_tj.sub_disk_preserves_bounded_inactive_lsns(
                full_index,
                first,
                sub_tj,
                sub_first,
            );
        }
        assert(tight_dv.bounded_inactive_lsns(frozen_built_index, tight_tj.freshest_rec)) by {
            assert forall |addr: Address, lsn: LSN|
                ({
                    &&& tight_dv.entries.dom().contains(addr)
                    &&& tight_dv.entries[addr].message_seq.contains(lsn)
                    &&& frozen_built_index.values().contains(addr.au)
                    &&& !frozen_built_index.contains_key(lsn)
                    &&& tight_tj.freshest_rec is Some ==> !tight_tj.freshest_rec.unwrap().after_page(addr)
                }) implies lsn < tight_dv.boundary_lsn by {
                assert(sub_dv.entries.contains_key(addr));
                assert(tight_dv.entries[addr] == sub_dv.entries[addr]);
                assert(sub_dv.bounded_inactive_lsns(frozen_index, frozen.freshest_rec));
            }
        }
        assert(tight_tj.disk_view.is_sub_disk_with_newer_lsn(full_dv)) by {
            assert(full_dv.boundary_lsn <= tight_tj.disk_view.boundary_lsn);
            assert(tight_tj.disk_view.entries <= full_dv.entries) by {
                assert forall |addr: Address| #[trigger] tight_tj.disk_view.entries.contains_key(addr)
                    implies full_dv.entries.contains_key(addr)
                        && tight_tj.disk_view.entries[addr] == full_dv.entries[addr] by {
                    assert(sub_dv.entries.contains_key(addr));
                    assert(sub_dv.entries <= full_dv.entries);
                }
            }
        }
        assert(frozen_journal.tj.seq_start() == frozen.boundary_lsn);
        assert(frozen_journal.tj.seq_end() == frozen.seq_end) by {
            if frozen.freshest_rec is Some {
                let root = frozen.freshest_rec.unwrap();
                assert(frozen_tj.disk_view.entries.contains_key(root));
                assert(frozen_tj.disk_view.entries[root] == pre.disk_view.entries[root]);
                assert(full_dv.entries[root] == pre.disk_view.entries[root]);
                assert(frozen_tj.disk_view.entries[root].message_seq.seq_end == frozen.seq_end);
            } else {
                assert(frozen.seq_end == frozen.boundary_lsn);
            }
        }
        assert(frozen_tj.disk_view.path_decodable(frozen_tj.freshest_rec));
        let tight_bounds = tight_dv.build_au_page_bounds_au_walk(tight_tj.freshest_rec, frozen.first);
        tight_dv.build_au_page_bounds_au_walk_domain_matches_build_tight(
            tight_tj.freshest_rec,
            frozen.first,
        );
        tight_dv.path_build_tight_equals_build_tight(tight_tj.freshest_rec);
        assert(tight_dv.path_build_tight(tight_tj.freshest_rec) == tight_dv);
        assert(tight_dv.build_tight(tight_tj.freshest_rec) == tight_dv);
        assert(frozen_tj.disk_view.wf_addrs()) by {
            assert forall |addr: Address| #[trigger] frozen_tj.disk_view.entries.contains_key(addr)
                implies addr.wf() by {
                assert(pre.disk_view.entries.contains_key(addr));
                assert(pre.disk_view.wf_addrs());
            }
        }
        assert(frozen_tj.disk_view.domain_au_bounded_wrt_index(frozen_built_index)) by {
            assert forall |addr: Address| #[trigger] frozen_tj.disk_view.entries.dom().contains(addr)
                implies frozen_built_index.values().contains(addr.au) by {
                assert(pre.frozen_domain(frozen).contains(addr));
                assert(frozen_built_index == frozen_index);
            }
        }
        assert(frozen_journal.bounded_live_entries_are_tight()) by {
            assert forall |addr: Address| ({
                let record = frozen_tj.disk_view.entries[addr];
                &&& #[trigger] frozen_tj.disk_view.entries.contains_key(addr)
                &&& tight_bounds.contains_key(addr.au)
                &&& addr.page <= tight_bounds[addr.au]
                &&& frozen_tj.seq_start() < record.message_seq.seq_end
            }) implies tight_dv.entries.contains_key(addr) by {
                assert(pre.disk_view.entries.contains_key(addr));
                assert(pre.disk_view.entries[addr] == frozen_tj.disk_view.entries[addr]);
                tight_dv.build_au_page_bounds_au_walk_dom_has_entry(
                    tight_tj.freshest_rec,
                    frozen.first,
                );
                let witness = choose |witness: Address| {
                    &&& #[trigger] tight_dv.entries_bounded_by_au_page_bounds(tight_bounds).contains_key(witness)
                    &&& witness.au == addr.au
                };
                assert(tight_dv.entries.contains_key(witness));
                assert(tight_dv.domain_au_bounded_wrt_index(frozen_built_index));
                assert(frozen_built_index.values().contains(addr.au));

                tight_dv.build_au_page_bounds_au_walk_bound_has_entry(
                    tight_tj.freshest_rec,
                    frozen.first,
                    addr.au,
                );
                let bound_addr = Address{au: addr.au, page: tight_bounds[addr.au]};
                assert(tight_dv.entries.contains_key(bound_addr));
                assert(tight_dv.entries[bound_addr] == full_dv.entries[bound_addr]);
                assert(full_dv.entries.contains_key(bound_addr));
                assert(pre.semantic_entries_bounded_by_au_page_bounds());
                assert(pre.au_page_bounds.contains_key(addr.au));
                assert(tight_bounds[addr.au] <= pre.au_page_bounds[addr.au]);
                assert(addr.page <= pre.au_page_bounds[addr.au]);
                assert(pre.bounded_live_entries_are_semantic());
                assert(full_dv.entries.contains_key(addr));
                let sub_domain = full_dv.tight_domain(frozen_index, frozen.freshest_rec);
                assert(sub_domain.contains(addr)) by {
                    assert(frozen_index.values().contains(addr.au));
                    if frozen.freshest_rec is Some
                        && au_addrs_past_pointer(frozen.freshest_rec).contains(addr) {
                        let root = frozen.freshest_rec.unwrap();
                        assert(addr.au == root.au);
                        assert(tight_bounds[root.au] == root.page);
                        assert(addr.page <= root.page);
                        assert(root.page < addr.page);
                        assert(false);
                    }
                }
                assert(sub_dv.entries.contains_key(addr));
                assert(sub_dv.pointer_is_upstream(frozen.freshest_rec, frozen.first));
                assert(sub_dv.domain_au_bounded_wrt_index(frozen_index));
                assert(sub_dv.bounded_inactive_lsns(frozen_index, frozen.freshest_rec));
                assert(sub_dv.build_lsn_au_index_au_walk(frozen.freshest_rec, frozen.first) == frozen_index);
                sub_dv.boundary_crossing_entry_in_build_tight(
                    frozen.freshest_rec,
                    frozen.first,
                    frozen_index,
                    addr,
                );
                assert(tight_dv.entries.contains_key(addr));
            }
        }
        assert forall |addr: Address| {
            let record = frozen_tj.disk_view.entries[addr];
            &&& #[trigger] frozen_tj.disk_view.entries.contains_key(addr)
            &&& tight_bounds.contains_key(addr.au)
            &&& addr.page <= tight_bounds[addr.au]
            &&& frozen_tj.seq_start() < record.message_seq.seq_end
        } implies pre.frozen_prefix_domain(frozen).contains(addr) by {
            assert(pre.frozen_loose_domain(frozen).contains(addr)) by {
                assert(pre.frozen_domain(frozen).contains(addr));
            }
            tight_dv.build_au_page_bounds_au_walk_bound_has_entry(
                tight_tj.freshest_rec,
                frozen.first,
                addr.au,
            );
            let bound_addr = Address{au: addr.au, page: tight_bounds[addr.au]};
            assert(tight_dv.entries.contains_key(bound_addr));
            assert(tight_dv.entries[bound_addr] == full_dv.entries[bound_addr]);
            assert(full_dv.entries.contains_key(bound_addr));
            assert(pre.semantic_entries_bounded_by_au_page_bounds());
            assert(pre.au_page_bounds.contains_key(addr.au));
            assert(tight_bounds[addr.au] <= pre.au_page_bounds[addr.au]);
            assert(addr.page <= pre.au_page_bounds[addr.au]);
        }
        assert(frozen_journal.au_page_bounds_covered()) by {
            assert forall |addr: Address| {
                &&& #[trigger] frozen_built_index.values().contains(addr.au)
                &&& tight_bounds.contains_key(addr.au)
                &&& addr.page <= tight_bounds[addr.au]
            } implies frozen_journal.tj.disk_view.entries.contains_key(addr) by {
                assert(frozen_built_index == frozen_index);
                assert(frozen_index.values().contains(addr.au));
                assert(pre.lsn_au_index.values().contains(addr.au)) by {
                    let lsn = choose |lsn: LSN| #![trigger frozen_index.contains_key(lsn)] {
                        frozen_index.contains_key(lsn) && frozen_index[lsn] == addr.au
                    };
                    assert(frozen_index.contains_key(lsn));
                    assert(pre.lsn_au_index.contains_key(lsn));
                    assert(pre.lsn_au_index[lsn] == addr.au);
                }

                tight_dv.build_au_page_bounds_au_walk_bound_has_entry(
                    tight_tj.freshest_rec,
                    frozen.first,
                    addr.au,
                );
                let bound_addr = Address{au: addr.au, page: tight_bounds[addr.au]};
                assert(tight_dv.entries.contains_key(bound_addr));
                assert(tight_dv.entries[bound_addr] == full_dv.entries[bound_addr]);
                assert(full_dv.entries.contains_key(bound_addr));
                assert(pre.semantic_entries_bounded_by_au_page_bounds());
                assert(pre.au_page_bounds.contains_key(addr.au));
                assert(tight_bounds[addr.au] <= pre.au_page_bounds[addr.au]);
                assert(addr.page <= pre.au_page_bounds[addr.au]);
                assert(pre.au_page_bounds_covered());
                assert(pre.disk_view.entries.contains_key(addr));
                assert(pre.frozen_domain(frozen).contains(addr)) by {
                    assert(addrs_in_aus(frozen_index.values()).contains(addr));
                }
                assert(frozen_tj.disk_view.entries.contains_key(addr));
            }
        }
        assert(frozen_journal.indexed_witnesses_are_tight()) by {
            assert forall |addr: Address, lsn: LSN| ({
                let record = frozen_tj.disk_view.entries[addr];
                &&& #[trigger] frozen_tj.disk_view.entries.contains_key(addr)
                &&& tight_bounds.contains_key(addr.au)
                &&& addr.page <= tight_bounds[addr.au]
                &&& frozen_tj.seq_start() < record.message_seq.seq_end
                &&& record.message_seq.contains(lsn)
                &&& #[trigger] frozen_built_index.contains_key(lsn)
                &&& frozen_built_index[lsn] == addr.au
            }) implies tight_dv.entries.contains_key(addr) by {
                assert(frozen_journal.bounded_live_entries_are_tight());
            }
        }
        assert(frozen_journal.valid_image());
    }

    pub proof fn acceptable_frozen_image_matches_frozen_image(
        pre: Self,
        frozen: JournalMetadata,
        image: JournalImage,
    )
        requires
            pre.semantic_inv(),
            pre.inv(),
            pre.acceptable_frozen_image(frozen, image),
            AllocationJournal::State::next(
                pre,
                pre,
                AllocationJournal::Label::FreezeForCommit{frozen_journal: frozen},
            ),
        ensures
            image.tight_tj() == pre.frozen_image(frozen).tight_tj(),
            image.i() == pre.frozen_image(frozen).i(),
    {
        let lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: frozen};
        AllocationJournal::State::frozen_journal_is_valid_image(pre, pre, lbl);
        let base = pre.frozen_image(frozen);
        let base_tight = base.tight_tj();
        let image_tight = image.tight_tj();
        let prefix = pre.frozen_prefix_domain(frozen);

        base.valid_image_implies_tight_valid_image();
        image.valid_image_implies_tight_valid_image();
        base.valid_image_implies_tight_seq_bounds();
        image.valid_image_implies_tight_seq_bounds();
        let base_bounds = base_tight.disk_view.build_au_page_bounds_au_walk(
            base_tight.freshest_rec,
            frozen.first,
        );
        base.tj.disk_view.path_build_tight_idempotent(base.tj.freshest_rec);
        assert(base_tight.disk_view.path_build_tight(base_tight.freshest_rec)
            == base_tight.disk_view);
        base_tight.disk_view.decodable_implies_path_decodable(base_tight.freshest_rec);
        base_tight.disk_view.path_build_tight_equals_build_tight(base_tight.freshest_rec);
        base_tight.disk_view.build_au_page_bounds_au_walk_domain_matches_build_tight(
            base_tight.freshest_rec,
            frozen.first,
        );

        assert(base_tight.disk_view.entries <= image.tj.disk_view.entries) by {
            assert forall |addr: Address| #[trigger] base_tight.disk_view.entries.contains_key(addr)
                implies image.tj.disk_view.entries.contains_key(addr)
                    && image.tj.disk_view.entries[addr] == base_tight.disk_view.entries[addr] by {
                assert(base_tight.disk_view.entries.contains_key(addr));
                assert(base_tight.disk_view.is_sub_disk_with_newer_lsn(pre.tj().disk_view));
                assert(pre.tj().disk_view.entries.contains_key(addr));
                assert(pre.tj().disk_view.entries[addr] == base_tight.disk_view.entries[addr]);
                assert(pre.semantic_entries_bounded_by_au_page_bounds());
                assert(pre.au_page_bounds.contains_key(addr.au));
                assert(addr.page <= pre.au_page_bounds[addr.au]);
                assert(base_tight.disk_view.is_sub_disk(base.tj.disk_view)) by {
                    base.tj.disk_view.path_build_tight_is_sub_disk(base.tj.freshest_rec);
                }
                assert(base.tj.disk_view.entries.contains_key(addr));
                assert(pre.frozen_loose_domain(frozen).contains(addr));
                assert(base_tight.disk_view.build_tight(base_tight.freshest_rec)
                    == base_tight.disk_view);
                assert(base_tight.disk_view.build_tight(base_tight.freshest_rec).entries.contains_key(addr));
                assert(base_tight.disk_view.entries_bounded_by_au_page_bounds(base_bounds)
                    .contains_key(addr));
                assert(base_bounds.contains_key(addr.au));
                assert(addr.page <= base_bounds[addr.au]);
                assert(prefix.contains(addr));
                assert(maps_agree_on(prefix, image.tj.disk_view.entries, pre.disk_view.entries));
                assert(image.tj.disk_view.entries.restrict(prefix)
                    == pre.disk_view.entries.restrict(prefix));
                assert(pre.disk_view.entries.contains_key(addr));
                assert(pre.disk_view.entries[addr] == pre.tj().disk_view.entries[addr]) by {
                    assert(pre.tj().disk_view.is_sub_disk(pre.disk_view));
                }
                assert(pre.disk_view.entries.restrict(prefix).contains_key(addr));
                assert(image.tj.disk_view.entries.restrict(prefix).contains_key(addr));
                assert(image.tj.disk_view.entries.restrict(prefix)[addr]
                    == pre.disk_view.entries.restrict(prefix)[addr]);
                assert(image.tj.disk_view.entries.contains_key(addr));
                assert(image.tj.disk_view.entries[addr] == pre.disk_view.entries[addr]);
            }
        }
        assert(base_tight.disk_view.is_sub_disk(image.tj.disk_view)) by {
            assert(base_tight.disk_view.boundary_lsn == image.tj.disk_view.boundary_lsn);
            assert(base_tight.disk_view.entries <= image.tj.disk_view.entries);
        }
        base_tight.disk_view.decodable_implies_path_decodable(base_tight.freshest_rec);
        assert(base_tight.disk_view.path_decodable(base_tight.freshest_rec));
        base.tj.disk_view.path_build_tight_idempotent(base.tj.freshest_rec);
        assert(base_tight.disk_view.path_build_tight(base_tight.freshest_rec)
            == base_tight.disk_view);
        base_tight.disk_view.path_build_tight_preserved_in_superdisk(
            image.tj.disk_view,
            base_tight.freshest_rec,
        );
        assert(image.tj.disk_view.path_build_tight(image.tj.freshest_rec)
            == base_tight.disk_view);
        assert(image_tight == base_tight);
        assert(image.i() == image_tight.i().i());
        assert(base.i() == base_tight.i().i());
    }

    pub proof fn frozen_prefix_domain_bounded_by_au_page_bounds(
        pre: Self,
        frozen: JournalMetadata,
        addr: Address,
    )
        requires
            pre.inv(),
            pre.semantic_inv(),
            pre.frozen_metadata_valid(frozen),
            pre.frozen_prefix_domain(frozen).contains(addr),
        ensures
            pre.au_page_bounds.contains_key(addr.au),
            addr.page <= pre.au_page_bounds[addr.au],
            ({
                let image = pre.frozen_image(frozen);
                let tight = image.tight_tj();
                let tight_bounds = tight.disk_view.build_au_page_bounds_au_walk(
                    tight.freshest_rec,
                    frozen.first,
                );
                let bound_addr = Address{au: addr.au, page: tight_bounds[addr.au]};
                &&& addr.page <= bound_addr.page
                &&& tight.disk_view.entries.contains_key(bound_addr)
                &&& tight.disk_view.boundary_lsn
                    < tight.disk_view.entries[bound_addr].message_seq.seq_end
                &&& tight.disk_view.entries[bound_addr].message_seq.seq_end <= frozen.seq_end
                &&& pre.tj().disk_view.entries.contains_key(bound_addr)
                &&& pre.tj().disk_view.entries[bound_addr]
                    == tight.disk_view.entries[bound_addr]
            }),
    {
        let freeze_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: frozen};
        assert(AllocationJournal::State::next_by(
            pre,
            pre,
            freeze_lbl,
            AllocationJournal::Step::freeze_for_commit(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        assert(AllocationJournal::State::next(pre, pre, freeze_lbl)) by {
            reveal(AllocationJournal::State::next);
        }
        AllocationJournal::State::frozen_journal_is_valid_image(pre, pre, freeze_lbl);

        let image = pre.frozen_image(frozen);
        let tight = image.tight_tj();
        let tight_dv = tight.disk_view;
        let tight_bounds = tight_dv.build_au_page_bounds_au_walk(
            tight.freshest_rec,
            frozen.first,
        );
        assert(tight_bounds.contains_key(addr.au));
        assert(addr.page <= tight_bounds[addr.au]);
        image.valid_image_implies_tight_valid_image();
        assert(tight_dv.pointer_is_upstream(tight.freshest_rec, frozen.first));
        tight_dv.build_au_page_bounds_au_walk_bound_has_entry(
            tight.freshest_rec,
            frozen.first,
            addr.au,
        );
        let bound_addr = Address{au: addr.au, page: tight_bounds[addr.au]};
        assert(tight_dv.entries.contains_key(bound_addr));
        image.valid_image_implies_tight_seq_bounds();
        tight_dv.decodable_implies_path_decodable(tight.freshest_rec);
        image.tj.disk_view.path_build_tight_idempotent(tight.freshest_rec);
        assert(tight_dv == image.tj.disk_view.path_build_tight(tight.freshest_rec));
        assert(image.tj.disk_view.path_build_tight(tight.freshest_rec) == tight_dv);
        tight_dv.path_build_tight_equals_build_tight(tight.freshest_rec);
        assert(tight_dv.path_build_tight(tight.freshest_rec) == tight_dv);
        assert(tight_dv.path_build_tight(tight.freshest_rec)
            == tight_dv.build_tight(tight.freshest_rec));
        assert_maps_equal!(
            tight_dv.build_tight(tight.freshest_rec).entries,
            tight_dv.entries
        );
        assert(tight_dv.build_tight(tight.freshest_rec) == tight_dv);
        tight_dv.build_tight_entry_lsn_bounded(
            tight.freshest_rec,
            bound_addr,
        );
        assert(tight_dv.boundary_lsn < tight_dv.entries[bound_addr].message_seq.seq_end);
        assert(tight_dv.entries[bound_addr].message_seq.seq_end <= tight.seq_end());
        assert(tight.seq_end() == image.tj.seq_end());
        assert(image.tj.seq_end() == frozen.seq_end);
        assert(tight_dv.is_sub_disk_with_newer_lsn(pre.tj().disk_view));
        assert(pre.tj().disk_view.entries.contains_key(bound_addr));
        assert(pre.tj().disk_view.entries[bound_addr] == tight_dv.entries[bound_addr]);
        assert(pre.semantic_entries_bounded_by_au_page_bounds());
        assert(pre.au_page_bounds.contains_key(addr.au));
        assert(tight_bounds[addr.au] <= pre.au_page_bounds[addr.au]);
        assert(addr.page <= pre.au_page_bounds[addr.au]);
    }

    pub proof fn initialize_tj_matches(post: Self, image: JournalImage)
    requires
        Self::initialize(post, image),
    ensures
        post.tj() == image.tight_tj(),
    {

        image.valid_image_implies_tight_valid_image();
        assert(post.disk_view == image.tj.disk_view);
        assert(post.tj() == image.tight_tj());
    }

    pub proof fn put_preserves_frozen_metadata(pre: Self, post: Self, lbl: Label, frozen: JournalMetadata)
    requires
        pre.inv(),
        post.inv(),
        Self::put(pre, post, lbl),
        pre.frozen_metadata_valid(frozen),
    ensures
        post.frozen_metadata_valid(frozen),
        post.frozen_image(frozen) == pre.frozen_image(frozen),
    {
        assert(post.freshest_rec == pre.freshest_rec);
        assert(post.disk_view == pre.disk_view);
        assert(post.lsn_au_index == pre.lsn_au_index);
        assert(post.au_page_bounds == pre.au_page_bounds);
        assert(post.tj() == pre.tj());
        assert(pre.seq_end() <= post.seq_end());
        assert(post.frozen_image(frozen) == pre.frozen_image(frozen));
    }

    pub proof fn tight_next_addr_not_in_frozen_prefix(
        pre: Self,
        addr: Address,
        frozen: JournalMetadata,
    )
        requires
            pre.refinement_inv(),
            pre.mini_allocator.tight_next_addr(pre.freshest_rec, addr),
            pre.frozen_metadata_valid(frozen),
        ensures
            !pre.frozen_prefix_domain(frozen).contains(addr),
    {
        if pre.frozen_prefix_domain(frozen).contains(addr) {
            let freeze_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: frozen};
            assert(Self::next_by(pre, pre, freeze_lbl, AllocationJournal::Step::freeze_for_commit())) by {
                reveal(AllocationJournal::State::next_by);
            }
            assert(Self::next(pre, pre, freeze_lbl)) by {
                reveal(AllocationJournal::State::next);
            }
            Self::frozen_journal_is_valid_image(pre, pre, freeze_lbl);

            let image = pre.frozen_image(frozen);
            let tight = image.tight_tj();
            let tight_bounds = tight.disk_view.build_au_page_bounds_au_walk(
                tight.freshest_rec,
                image.first,
            );
            let bound_addr = Address{au: addr.au, page: tight_bounds[addr.au]};
            assert(tight_bounds.contains_key(addr.au));
            assert(addr.page <= bound_addr.page);
            image.valid_image_implies_tight_valid_image();
            tight.disk_view.build_au_page_bounds_au_walk_bound_has_entry(
                tight.freshest_rec,
                image.first,
                addr.au,
            );
            assert(tight.disk_view.entries.contains_key(bound_addr));
            assert(tight.disk_view.is_sub_disk_with_newer_lsn(pre.tj().disk_view));
            assert(pre.tj().disk_view.entries.contains_key(bound_addr));
            pre.semantic_entry_not_after_freshest(bound_addr);

            if pre.mini_allocator.curr is None {
                assert(pre.mini_allocator.can_allocate(addr));
                assert(pre.mini_allocator.allocs.contains_key(addr.au));
                assert(pre.mini_allocator.allocs[addr.au].all_pages_free());
                assert(bound_addr.wf()) by {
                    assert(pre.tj().disk_view.wf_addrs());
                }
                assert(pre.mini_allocator.can_allocate(bound_addr)) by {
                    assert(pre.mini_allocator.allocs.contains_key(bound_addr.au));
                    assert(pre.mini_allocator.allocs[bound_addr.au].all_pages_free());
                    assert(pre.mini_allocator.allocs[bound_addr.au].has_no_allocated_pages());
                    assert(pre.mini_allocator.allocs[bound_addr.au].has_no_allocated_pages());
                    assert(pre.mini_allocator.allocs[bound_addr.au].allocated == Set::<Address>::empty());
                    assert(pre.mini_allocator.allocs[bound_addr.au].allocated == Set::<Address>::empty());
                    assert(!pre.mini_allocator.allocs[bound_addr.au].allocated.contains(bound_addr));
                    assert(!pre.mini_allocator.allocs[bound_addr.au].allocated.contains(bound_addr));
                    assert(pre.mini_allocator.allocs[bound_addr.au].is_free_addr(bound_addr));
                }
                assert(Self::disk_domain_not_free(pre.tj().disk_view, pre.mini_allocator));
                assert(!pre.mini_allocator.can_allocate(bound_addr));
            } else {
                assert(pre.semantic_inv());
                assert(Self::mini_allocator_follows_freshest_rec(
                    pre.freshest_rec,
                    pre.mini_allocator,
                ));
                assert(pre.freshest_rec is Some);
                let root = pre.freshest_rec.unwrap();
                assert(addr == root.next());
                assert(root.au == addr.au);
                assert(bound_addr.au == root.au);
                assert(bound_addr.wf()) by {
                    assert(pre.tj().disk_view.wf_addrs());
                }
                assert(root.after_page(bound_addr)) by {
                    assert(bound_addr.page >= addr.page);
                    assert(addr.page == root.page + 1);
                    assert(bound_addr.page > root.page);
                }
                assert(!root.after_page(bound_addr));
            }
            assert(false);
        }
    }

    pub proof fn internal_allocations_preserves_frozen_metadata_tight(
        pre: Self,
        post: Self,
        lbl: Label,
        frozen: JournalMetadata,
    )
        requires
            pre.refinement_inv(),
            post.refinement_inv(),
            lbl is InternalAllocations,
            Self::next(pre, post, lbl),
            pre.frozen_metadata_valid(frozen),
        ensures
            post.frozen_metadata_valid(frozen),
            post.frozen_loose_domain(frozen) =~= pre.frozen_loose_domain(frozen),
            post.frozen_prefix_domain(frozen) =~= pre.frozen_prefix_domain(frozen),
            post.frozen_image(frozen).tight_tj()
                == pre.frozen_image(frozen).tight_tj(),
    {
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);
        let step = choose |step| AllocationJournal::State::next_by(pre, post, lbl, step);
        match step {
            AllocationJournal::Step::internal_journal_marshal(cut, addr) => {
                assert(AllocationJournal::State::internal_journal_marshal(pre, post, lbl, cut, addr));
                Self::internal_journal_marshal_view_preserves(pre, post, lbl, cut, addr);
                assert(post.frozen_metadata_valid(frozen));
                let marshal_addr = addr;
                let freeze_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: frozen};
                assert(Self::next_by(pre, pre, freeze_lbl, AllocationJournal::Step::freeze_for_commit())) by {
                    reveal(AllocationJournal::State::next_by);
                }
                assert(Self::next(pre, pre, freeze_lbl)) by {
                    reveal(AllocationJournal::State::next);
                }
                Self::frozen_journal_is_valid_image(pre, pre, freeze_lbl);

                let pre_image = pre.frozen_image(frozen);
                let post_image = post.frozen_image(frozen);
                let pre_tight = pre_image.tight_tj();
                let post_tight = post_image.tight_tj();

                assert(pre.frozen_lsn_au_index(frozen) =~= post.frozen_lsn_au_index(frozen)) by {
                    assert forall |lsn: LSN| #[trigger] pre.frozen_lsn_au_index(frozen).contains_key(lsn)
                        <==> post.frozen_lsn_au_index(frozen).contains_key(lsn) by {
                        if pre.frozen_lsn_au_index(frozen).contains_key(lsn) {
                            assert(pre.lsn_au_index.contains_key(lsn));
                            assert(frozen.boundary_lsn <= lsn < frozen.seq_end);
                            assert(post.lsn_au_index.contains_key(lsn));
                            assert(post.lsn_au_index[lsn] == pre.lsn_au_index[lsn]);
                        }
                        if post.frozen_lsn_au_index(frozen).contains_key(lsn) {
                            assert(post.lsn_au_index.contains_key(lsn));
                            assert(frozen.boundary_lsn <= lsn < frozen.seq_end);
                            assert(pre.lsn_au_index.contains_key(lsn));
                            assert(post.lsn_au_index[lsn] == pre.lsn_au_index[lsn]);
                        }
                    }
                }
                assert(pre.frozen_domain(frozen) =~= post.frozen_domain(frozen)) by {
                    assert_maps_equal!(
                        pre.frozen_lsn_au_index(frozen),
                        post.frozen_lsn_au_index(frozen)
                    );
                }
                assert(pre_tight.disk_view.is_sub_disk(post_image.tj.disk_view)) by {
                    pre_image.tj.disk_view.path_build_tight_is_sub_disk(pre_image.tj.freshest_rec);
                    assert forall |x: Address| #[trigger] pre_tight.disk_view.entries.contains_key(x)
                        implies post_image.tj.disk_view.entries.contains_key(x)
                            && post_image.tj.disk_view.entries[x] == pre_tight.disk_view.entries[x] by {
                        assert(pre_image.tj.disk_view.entries.contains_key(x));
                        assert(pre.frozen_domain(frozen).contains(x));
                        assert(post.frozen_domain(frozen).contains(x));
                        assert(pre.disk_view.entries.contains_key(x));
                        assert(pre_tight.disk_view.is_sub_disk_with_newer_lsn(pre.tj().disk_view));
                        assert(pre.tj().disk_view.entries.contains_key(x));
                        assert(x != marshal_addr) by {
                            if x == marshal_addr {
                                assert(pre.tj().disk_view.entries.contains_key(marshal_addr));
                                assert(!pre.tj().disk_view.entries.contains_key(marshal_addr));
                            }
                        }
                        assert(post.disk_view.entries.contains_key(x));
                        assert(post.disk_view.entries[x] == pre.disk_view.entries[x]);
                    }
                }
                pre_image.valid_image_implies_tight_valid_image();
                assert(pre_tight.decodable());
                assert(pre_tight.disk_view.acyclic());
                pre_tight.disk_view.decodable_implies_path_decodable(pre_tight.freshest_rec);
                assert(pre_tight.disk_view.path_decodable(pre_tight.freshest_rec));
                pre_image.tj.disk_view.path_build_tight_idempotent(pre_image.tj.freshest_rec);
                assert(pre_image.tj.disk_view.path_build_tight(pre_image.tj.freshest_rec)
                    == pre_tight.disk_view);
                assert(pre_tight.disk_view.path_build_tight(pre_tight.freshest_rec)
                    == pre_tight.disk_view);
                pre_tight.disk_view.path_build_tight_preserved_in_superdisk(
                    post_image.tj.disk_view,
                    pre_tight.freshest_rec,
                );
                assert(post_tight == pre_tight);
            },
            AllocationJournal::Step::internal_mini_allocator_fill(post_disk_view) => {
                assert(AllocationJournal::State::internal_mini_allocator_fill(pre, post, lbl, post_disk_view));
                Self::internal_mini_allocator_fill_tj_unchanged(pre, post, lbl, post_disk_view);
                assert(post.frozen_metadata_valid(frozen));
                assert(post.frozen_lsn_au_index(frozen) =~= pre.frozen_lsn_au_index(frozen)) by {
                    assert_maps_equal!(
                        post.frozen_lsn_au_index(frozen),
                        pre.frozen_lsn_au_index(frozen)
                    );
                }
                assert(post.frozen_domain(frozen) =~= pre.frozen_domain(frozen)) by {
                    assert_maps_equal!(
                        post.frozen_lsn_au_index(frozen),
                        pre.frozen_lsn_au_index(frozen)
                    );
                }
                assert(post.frozen_tj(frozen).disk_view.entries
                    =~= pre.frozen_tj(frozen).disk_view.entries) by {
                    assert_maps_equal!(
                        post.frozen_tj(frozen).disk_view.entries,
                        pre.frozen_tj(frozen).disk_view.entries,
                        a => {
                            if post.frozen_tj(frozen).disk_view.entries.contains_key(a) {
                                assert(post.frozen_domain(frozen).contains(a));
                                assert(pre.frozen_domain(frozen).contains(a));
                                assert(pre.disk_view.entries.contains_key(a)) by {
                                    if !pre.disk_view.entries.contains_key(a) {
                                        assert(post.disk_view.entries.contains_key(a));
                                        assert(lbl->allocs.contains(a.au));
                                        assert(pre.frozen_lsn_au_index(frozen).values().contains(a.au));
                                        assert(lbl->allocs.disjoint(pre.lsn_au_index.values()));
                                        assert(false);
                                    }
                                }
                                assert(post.disk_view.entries[a] == pre.disk_view.entries[a]);
                            }
                            if pre.frozen_tj(frozen).disk_view.entries.contains_key(a) {
                                assert(pre.frozen_domain(frozen).contains(a));
                                assert(post.frozen_domain(frozen).contains(a));
                                assert(pre.disk_view.entries.contains_key(a));
                                assert(post.disk_view.entries.contains_key(a));
                                assert(post.disk_view.entries[a] == pre.disk_view.entries[a]);
                            }
                        }
                    );
                }
                assert(post.frozen_tj(frozen).disk_view == pre.frozen_tj(frozen).disk_view);
                assert(post.frozen_tj(frozen).freshest_rec == pre.frozen_tj(frozen).freshest_rec);
                assert(post.frozen_tj(frozen) == pre.frozen_tj(frozen));
                assert(post.frozen_image(frozen).tj == pre.frozen_image(frozen).tj);
                assert(post.frozen_image(frozen).first == pre.frozen_image(frozen).first);
                assert(post.frozen_image(frozen) == pre.frozen_image(frozen));
            },
            AllocationJournal::Step::internal_mini_allocator_prune(prune_aus) => {
                assert(AllocationJournal::State::internal_mini_allocator_prune(pre, post, lbl, prune_aus));
                Self::internal_mini_allocator_prune_tj_unchanged(pre, post, lbl, prune_aus);
                let deallocs = lbl.arrow_InternalAllocations_deallocs();
                assert(deallocs.disjoint(pre.lsn_au_index.values())) by {
                    assert forall |au: AU| #[trigger] deallocs.contains(au)
                        implies !pre.lsn_au_index.values().contains(au) by {
                        if pre.lsn_au_index.values().contains(au) {
                            pre.tj_inherits_semantic_structure();
                            let first = if pre.tj().freshest_rec is Some {
                                pre.lsn_au_index[pre.seq_start()]
                            } else {
                                0
                            };
                            pre.tj().build_lsn_au_index_from_first_ensures(first);
                            let lsn = choose |lsn: LSN| #![auto]
                                pre.lsn_au_index.contains_key(lsn) && pre.lsn_au_index[lsn] == au;
                            let witness = pre.tj().disk_view.instantiate_index_keys_exist_valid_entries(
                                pre.lsn_au_index,
                                lsn,
                            );
                            assert(witness.au == au);
                            assert(pre.tj().disk_view.entries.contains_key(witness));
                            assert(Self::disk_domain_not_free(pre.tj().disk_view, pre.mini_allocator));
                            assert(!pre.mini_allocator.can_allocate(witness));
                            assert(pre.mini_allocator.allocs.contains_key(au));
                            assert(pre.mini_allocator.allocs[au].all_pages_free());
                            assert(pre.mini_allocator.wf());
                            assert(pre.mini_allocator.allocs[au].au == au);
                            assert(pre.mini_allocator.allocs[au].is_free_addr(witness));
                            assert(pre.mini_allocator.can_allocate(witness));
                            assert(false);
                        }
                    }
                }
                assert(post.frozen_metadata_valid(frozen));
                assert(post.frozen_lsn_au_index(frozen) =~= pre.frozen_lsn_au_index(frozen)) by {
                    assert_maps_equal!(
                        post.frozen_lsn_au_index(frozen),
                        pre.frozen_lsn_au_index(frozen)
                    );
                }
                assert(post.frozen_domain(frozen) =~= pre.frozen_domain(frozen)) by {
                    assert_maps_equal!(
                        post.frozen_lsn_au_index(frozen),
                        pre.frozen_lsn_au_index(frozen)
                    );
                }
                assert(post.frozen_tj(frozen).disk_view.entries
                    =~= pre.frozen_tj(frozen).disk_view.entries) by {
                    assert_maps_equal!(
                        post.frozen_tj(frozen).disk_view.entries,
                        pre.frozen_tj(frozen).disk_view.entries,
                        a => {
                            if post.frozen_tj(frozen).disk_view.entries.contains_key(a) {
                                assert(pre.frozen_domain(frozen).contains(a));
                                assert(pre.disk_view.entries.contains_key(a));
                                assert(!deallocs.contains(a.au));
                                assert(post.disk_view.entries[a] == pre.disk_view.entries[a]);
                            }
                            if pre.frozen_tj(frozen).disk_view.entries.contains_key(a) {
                                assert(pre.frozen_domain(frozen).contains(a));
                                assert(pre.frozen_lsn_au_index(frozen).values().contains(a.au));
                                assert(!deallocs.contains(a.au));
                                assert(post.disk_view.entries.contains_key(a));
                                assert(post.disk_view.entries[a] == pre.disk_view.entries[a]);
                            }
                        }
                    );
                }
                assert(post.frozen_tj(frozen).disk_view == pre.frozen_tj(frozen).disk_view);
                assert(post.frozen_tj(frozen).freshest_rec == pre.frozen_tj(frozen).freshest_rec);
                assert(post.frozen_tj(frozen) == pre.frozen_tj(frozen));
                assert(post.frozen_image(frozen).tj == pre.frozen_image(frozen).tj);
                assert(post.frozen_image(frozen).first == pre.frozen_image(frozen).first);
            },
            AllocationJournal::Step::internal_no_op() => {
                assert(AllocationJournal::State::internal_no_op(pre, post, lbl));
                assert(post == pre);
            },
            _ => {
                assert(false);
            },
        }
        assert(post.frozen_loose_domain(frozen) =~= pre.frozen_loose_domain(frozen)) by {
            assert(post.frozen_domain(frozen) =~= pre.frozen_domain(frozen));
        }
        assert(post.frozen_prefix_domain(frozen) =~= pre.frozen_prefix_domain(frozen)) by {
            assert forall |addr: Address| #[trigger] post.frozen_prefix_domain(frozen).contains(addr)
                <==> pre.frozen_prefix_domain(frozen).contains(addr) by {
                assert(post.frozen_image(frozen).tight_tj()
                    == pre.frozen_image(frozen).tight_tj());
                if post.frozen_prefix_domain(frozen).contains(addr) {
                    assert(post.frozen_loose_domain(frozen).contains(addr));
                    assert(pre.frozen_loose_domain(frozen).contains(addr));
                }
                if pre.frozen_prefix_domain(frozen).contains(addr) {
                    assert(pre.frozen_loose_domain(frozen).contains(addr));
                    assert(post.frozen_loose_domain(frozen).contains(addr));
                }
            }
        }
    }

    pub proof fn discard_old_preserves_frozen_metadata_at_boundary(
        pre: Self,
        post: Self,
        lbl: Label,
        frozen: JournalMetadata,
    )
        requires
            pre.inv(),
            post.inv(),
            Self::discard_old(pre, post, lbl),
            pre.frozen_metadata_valid(frozen),
            lbl->start_lsn == frozen.boundary_lsn,
            lbl->require_end == pre.seq_end(),
        ensures
            post.frozen_metadata_valid(frozen),
            post.frozen_image(frozen) == pre.frozen_image(frozen),
            post.frozen_prefix_domain(frozen) =~= pre.frozen_prefix_domain(frozen),
    {

        let start_lsn = lbl->start_lsn;
        let new_index = lsn_au_index_discard_up_to(pre.lsn_au_index, start_lsn);
        let discarded_aus = pre.lsn_au_index.values().difference(new_index.values());
        lsn_au_index_discard_up_to_ensures(pre.lsn_au_index, start_lsn);

        assert(post.lsn_au_index == new_index);
        assert(start_lsn == frozen.boundary_lsn);
        assert(post.seq_start() == frozen.boundary_lsn);
        assert(post.seq_end() == pre.seq_end());

        assert(post.frozen_lsn_au_index(frozen) =~= pre.frozen_lsn_au_index(frozen)) by {
            assert forall |lsn: LSN| #[trigger] post.frozen_lsn_au_index(frozen).contains_key(lsn)
                <==> pre.frozen_lsn_au_index(frozen).contains_key(lsn) by {
                if post.frozen_lsn_au_index(frozen).contains_key(lsn) {
                    assert(post.lsn_au_index.contains_key(lsn));
                    assert(frozen.boundary_lsn <= lsn);
                    assert(pre.lsn_au_index.contains_key(lsn));
                }
                if pre.frozen_lsn_au_index(frozen).contains_key(lsn) {
                    assert(pre.lsn_au_index.contains_key(lsn));
                    assert(frozen.boundary_lsn <= lsn);
                    assert(new_index.contains_key(lsn));
                    assert(post.lsn_au_index.contains_key(lsn));
                }
            }
        }

        assert(post.frozen_domain(frozen) =~= pre.frozen_domain(frozen)) by {
            assert_maps_equal!(
                post.frozen_lsn_au_index(frozen),
                pre.frozen_lsn_au_index(frozen)
            );
        }

        assert(post.frozen_tj(frozen).disk_view.entries
            =~= pre.frozen_tj(frozen).disk_view.entries) by {
            assert forall |addr: Address| #[trigger] post.frozen_tj(frozen).disk_view.entries.contains_key(addr)
                <==> pre.frozen_tj(frozen).disk_view.entries.contains_key(addr) by {
                if post.frozen_tj(frozen).disk_view.entries.contains_key(addr) {
                    assert(post.frozen_domain(frozen).contains(addr));
                    assert(pre.frozen_domain(frozen).contains(addr));
                    assert(post.disk_view.entries.contains_key(addr));
                    assert(pre.disk_view.entries.contains_key(addr));
                }
                if pre.frozen_tj(frozen).disk_view.entries.contains_key(addr) {
                    assert(pre.frozen_domain(frozen).contains(addr));
                    assert(post.frozen_domain(frozen).contains(addr));
                    assert(pre.disk_view.entries.contains_key(addr));
                    assert(pre.frozen_lsn_au_index(frozen).values().contains(addr.au));
                    assert(post.frozen_lsn_au_index(frozen).values().contains(addr.au));
                    assert(new_index.values().contains(addr.au));
                    assert(!discarded_aus.contains(addr.au));
                    assert(post.disk_view.entries.contains_key(addr));
                }
            }
            assert forall |addr: Address| #[trigger] post.frozen_tj(frozen).disk_view.entries.contains_key(addr)
                implies post.frozen_tj(frozen).disk_view.entries[addr]
                    == pre.frozen_tj(frozen).disk_view.entries[addr] by {
                assert(post.disk_view.entries[addr] == pre.disk_view.entries[addr]);
            }
        }

        assert(post.frozen_tj(frozen) == pre.frozen_tj(frozen));
        assert(post.frozen_image(frozen) == pre.frozen_image(frozen));
        assert(post.frozen_prefix_domain(frozen) =~= pre.frozen_prefix_domain(frozen)) by {
            assert forall |addr: Address| #[trigger] post.frozen_prefix_domain(frozen).contains(addr)
                <==> pre.frozen_prefix_domain(frozen).contains(addr) by {
                assert(post.frozen_domain(frozen) =~= pre.frozen_domain(frozen));
                assert(post.frozen_image(frozen).tight_tj()
                    == pre.frozen_image(frozen).tight_tj());
                if post.frozen_prefix_domain(frozen).contains(addr) {
                    assert(post.frozen_domain(frozen).contains(addr));
                    assert(pre.frozen_domain(frozen).contains(addr));
                }
                if pre.frozen_prefix_domain(frozen).contains(addr) {
                    assert(pre.frozen_domain(frozen).contains(addr));
                    assert(post.frozen_domain(frozen).contains(addr));
                }
            }
        }
    }

} }  // state_machine

} // verus!
  // verus
