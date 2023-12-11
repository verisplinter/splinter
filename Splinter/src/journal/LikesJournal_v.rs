// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use builtin::*;
use vstd::prelude::*;
use vstd::{map::*,multiset::*};
use vstd::math;

use builtin_macros::*;
use state_machines_macros::state_machine;

use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::TruncatedJournal;
use crate::journal::LinkedJournal_v::DiskView;
use crate::disk::GenericDisk_v::*;
use crate::allocation_layer::Likes_v::*;

verus!{

impl TruncatedJournal {
}

//////////////////////////////////////////////////////////////////////////////
type LsnAddrIndex = Map<LSN, Address>;

pub open spec(checked) fn lsn_disjoint(lsn_index: Set<LSN>, msgs: MsgHistory) -> bool
{
    forall |lsn| msgs.seq_start <= lsn < msgs.seq_end
        ==> !lsn_index.contains(lsn)
}

pub open spec fn lsn_addr_index_discard_up_to(lsn_addr_index: LsnAddrIndex, bdy: LSN) -> (out: LsnAddrIndex)
{
    Map::new(
        |k| lsn_addr_index.contains_key(k) && bdy <= k,
        |k| lsn_addr_index[k])
}

pub proof fn lsn_addr_index_discard_up_to_ensures(lsn_addr_index: LsnAddrIndex, bdy: LSN)
ensures ({
    let out = lsn_addr_index_discard_up_to(lsn_addr_index, bdy);
    &&& out <= lsn_addr_index
    &&& forall |k| out.contains_key(k) ==> bdy <= k
    &&& forall |k| lsn_addr_index.contains_key(k) && bdy <= k ==> out.contains_key(k)
})
{
}

pub open spec(checked) fn singleton_index(start: LSN, end: LSN, value: Address) -> LsnAddrIndex
{
    Map::new(|x: LSN| start <= x < end, |x:LSN| value)
}

pub open spec(checked) fn lsn_addr_index_append_record(lsn_addr_index: LsnAddrIndex, msgs: MsgHistory, addr: Address) -> LsnAddrIndex
recommends
    msgs.wf(),
    msgs.seq_start < msgs.seq_end,  // non-empty
{
    let update = singleton_index(msgs.seq_start, msgs.seq_end, addr);
    lsn_addr_index.union_prefer_right(update)
}

pub proof fn lsn_addr_index_append_record_ensures(lsn_addr_index: LsnAddrIndex, msgs: MsgHistory, addr: Address)
requires
    msgs.wf(),
    msgs.seq_start < msgs.seq_end,  // non-empty
ensures
    lsn_disjoint(lsn_addr_index.dom(), msgs) ==>
        lsn_addr_index_append_record(lsn_addr_index, msgs, addr).values()
        == lsn_addr_index.values() + set![addr],
{
    let out = lsn_addr_index_append_record(lsn_addr_index, msgs, addr);
    // TODO(chris): Dafny needed only one line of proof for this mess; does our stdlib need some
    // better triggers? I wonder if it's down to contains-vs-contains_key
    if lsn_disjoint(lsn_addr_index.dom(), msgs) {
        let sum = lsn_addr_index.values() + set![addr];
        // TODO(chris): #[auto] doesn't work in the assert-forall context?
        assert forall |a| #[trigger] sum.contains(a) implies out.values().contains(a) by {
            // Go find witnesses.
            if lsn_addr_index.values().contains(a) {
                let lsn = choose |lsn| #![auto] lsn_addr_index.contains_key(lsn) && lsn_addr_index[lsn] == a;
                assert( out.contains_key(lsn) );
            } else {
                assert( out.contains_key(msgs.seq_start) );
            }
        };
        assert( out.values() =~= lsn_addr_index.values() + set![addr] );
    }
}

//////////////////////////////////////////////////////////////////////////////

impl DiskView {
    pub open spec(checked) fn buildable(self, root: Pointer) -> bool
    {
        &&& self.decodable(root)
        &&& self.acyclic()
        &&& root.is_Some() ==> self.boundary_lsn < self.entries[root.unwrap()].message_seq.seq_end
    }

    // too small to be interesting; delete
//     pub proof fn buildable_recursive(self, root: Pointer)
//     requires
//         self.buildable(root),
//         root.is_Some(),
//         self.next(root).is_Some(),
//     ensures
//         self.buildable(self.next(root)),
//     {
//         let next = self.next(root);
//         
//         assert( self.entries.contains_key(root.unwrap()) );
//         assert( self.is_nondangling_pointer(next) );
//     }

    pub open spec(checked) fn build_lsn_addr_index(self, root: Pointer) -> LsnAddrIndex
    recommends
        self.buildable(root),
    decreases self.the_rank_of(root) when self.decodable(root) && self.acyclic()
    {
        if root is None {
            map!{}
        } else {
            let curr_msgs = self.entries[root.unwrap()].message_seq;
            let start_lsn = math::max(self.boundary_lsn as int, curr_msgs.seq_start as int) as nat;
            //let start_lsn = if self.boundary_lsn > curr_msgs.seq_start { self.boundary_lsn } else { curr_msgs.seq_start };
            let update = singleton_index(start_lsn, curr_msgs.seq_end, root.unwrap());

            // Put the update on the "preferred" side to make recursive proof reasoning easier:
            // there should be no conflicts between update and inner call, but this way we don't
            // even have to make that argument because update values dominate.
            self.build_lsn_addr_index(self.next(root)).union_prefer_right(update)
        }
    }
} // end of impl DiskView

// invariant proof stuff that moved here from the Refinement file
impl DiskView {
    pub open spec(checked) fn addr_supports_lsn(self, addr: Address, lsn: LSN) -> bool
    {
        &&& self.entries.contains_key(addr)
        &&& self.entries[addr].contains_lsn(self.boundary_lsn, lsn)
    }

    proof fn build_lsn_addr_index_ignores_build_tight(self, bt_root: Pointer, repr_root: Pointer)
    requires
        self.buildable(repr_root),
        self.decodable(bt_root),
        self.build_tight(bt_root).decodable(repr_root),
    ensures
        self.build_tight(bt_root).wf(),
        self.build_tight(bt_root).acyclic(),
        repr_root.is_Some() ==> self.boundary_lsn < self.build_tight(bt_root).entries[repr_root.unwrap()].message_seq.seq_end,
        self.build_lsn_addr_index(repr_root) == self.build_tight(bt_root).build_lsn_addr_index(repr_root),
    decreases self.the_rank_of(repr_root)
    {
        self.build_tight_is_awesome(bt_root);
        if repr_root.is_Some() {
            self.build_lsn_addr_index_ignores_build_tight(bt_root, self.next(repr_root));
        }
    }

    proof fn representation_ignores_build_tight(self, bt_root: Pointer, repr_root: Pointer)
    requires
        self.decodable(bt_root),
        self.decodable(repr_root),
        self.acyclic(),
        self.build_tight(bt_root).decodable(repr_root),
    ensures
        self.build_tight(bt_root).wf(),
        self.build_tight(bt_root).acyclic(),
        self.build_tight(bt_root).representation(repr_root) == self.representation(repr_root)
    decreases self.the_rank_of(repr_root)
    {
        self.build_tight_is_awesome(bt_root);
        if repr_root.is_Some() {
            self.representation_ignores_build_tight(bt_root, self.next(repr_root));
        }
    }

    proof fn build_tight_gives_representation(self, root: Pointer)
    requires
        self.decodable(root),
        self.acyclic(),
    ensures
        self.build_tight(root).entries.dom() == self.representation(root),
    decreases self.the_rank_of(root)
    {
        if root.is_Some() {
            self.build_tight_gives_representation(self.next(root));
        }
    }

    spec(checked) fn cropped_lsn(boundary: LSN, message_seq: MsgHistory, lsn: LSN) -> bool
    {
        max(boundary as int, message_seq.seq_start as int) <= lsn < message_seq.seq_end
    }

    pub open spec(checked) fn tj_at(self, root: Pointer) -> TruncatedJournal
    {
        TruncatedJournal{freshest_rec: root, disk_view: self}
    }

    pub proof fn build_lsn_addr_index_domain_valid(self, root: Pointer)
    requires
        self.decodable(root),
        self.acyclic(),
        root.is_Some(), // otherwise BuildLsnAddrIndex is trivially empty
        self.boundary_lsn < self.entries[root.unwrap()].message_seq.seq_end,
    ensures
        self.tj_at(root).index_domain_valid(self.build_lsn_addr_index(root)),
        self.index_keys_map_to_valid_entries(self.build_lsn_addr_index(root)),
    decreases self.the_rank_of(root)
    {
        reveal(TruncatedJournal::index_domain_valid);
        reveal(DiskView::index_keys_map_to_valid_entries);
        if root.is_None() {
        } else if self.next(root).is_None() {
            // TODO(chris) These lets are trigger something... not sure why, since we have the same
            // defn (build_lsn_addr_index) available in scope. ?
            let curr_msgs = self.entries[root.unwrap()].message_seq;
            let start_lsn = math::max(self.boundary_lsn as int, curr_msgs.seq_start as int) as nat;
            let update = singleton_index(start_lsn, curr_msgs.seq_end, root.unwrap());
            let output = self.build_lsn_addr_index(self.next(root)).union_prefer_right(update);
        } else {
            self.build_lsn_addr_index_domain_valid(self.next(root));
        }
    }

    proof fn build_lsn_addr_index_range_valid(self, root: Pointer, tj_end: LSN)
    requires
        self.buildable(root),
        root.is_Some() ==> self.entries[root.unwrap()].message_seq.seq_end == tj_end,
        root.is_None() ==> tj_end <= self.boundary_lsn,
        self.tj_at(root).index_domain_valid(self.build_lsn_addr_index(root)),
        self.index_keys_map_to_valid_entries(self.build_lsn_addr_index(root)),
    ensures
        self.tj_at(root).index_range_valid(self.build_lsn_addr_index(root)),
    {
        reveal(TruncatedJournal::index_domain_valid);
        reveal(DiskView::index_keys_map_to_valid_entries);
        if root.is_None() {
            assert( self.tj_at(root).index_range_valid(self.build_lsn_addr_index(root)) );
        } else if self.next(root).is_None() {
            let curr_msgs = self.entries[root.unwrap()].message_seq;
            let start_lsn = math::max(self.boundary_lsn as int, curr_msgs.seq_start as int) as nat;
            let update = singleton_index(start_lsn, curr_msgs.seq_end, root.unwrap());
            let output = self.build_lsn_addr_index(self.next(root)).union_prefer_right(update);
            assert( self.tj_at(root).index_range_valid(self.build_lsn_addr_index(root)) );
        } else {
            self.build_lsn_addr_index_domain_valid(self.next(root));
            assume( false );    // do we ever actually use index_range_valid? That's one ugly definition
            assert( self.tj_at(root).index_range_valid(self.build_lsn_addr_index(root)) );
        }
    }

    pub proof fn build_lsn_addr_index_gives_representation(self, root: Pointer) 
    requires
        self.buildable(root),
    ensures
        // This conclusion is used inside the recursion
        root.is_Some() ==>
            forall |lsn| self.build_lsn_addr_index(root).contains_key(lsn) ==>
                self.boundary_lsn <= lsn < self.entries[root.unwrap()].message_seq.seq_end,
        // This conclusion is the one we're trying to actually export
        self.build_lsn_addr_index(root).values() =~= self.representation(root),
        // TODO(chris): I find it kind of disturbing that the ~ between the == in the line above
        // is a functional part of the proof strategy. --jonh
    decreases self.the_rank_of(root)
    {
        reveal(TruncatedJournal::index_domain_valid);
        reveal(DiskView::index_keys_map_to_valid_entries);

        if root.is_Some() {
            self.build_lsn_addr_index_gives_representation(self.next(root));
            let curr_msgs = self.entries[root.unwrap()].message_seq;
            let begin = max(self.boundary_lsn as int, curr_msgs.seq_start as int) as nat;
            let update = singleton_index(begin, curr_msgs.seq_end, root.unwrap());
            assert(update.contains_key(begin));
            assert forall |k| #![auto] self.build_lsn_addr_index(root).values().contains(k) implies self.representation(root).contains(k) by {
            }
            self.representation_ensures(root);
            assert forall |addr| #![auto]
                self.representation(root).contains(addr) implies
                self.build_lsn_addr_index(root).values().contains(addr) by {

                let left_index = self.build_lsn_addr_index(self.entries[root.unwrap()].cropped_prior(self.boundary_lsn));
                if update.values().contains(addr) {
                    assert( self.build_lsn_addr_index(root).contains_key(begin) );   // witness
//                     assert( self.build_lsn_addr_index(root).values().contains(addr) );
                } else {
                    let lsn = choose |lsn| #![auto] left_index.contains_key(lsn) && left_index[lsn]==addr;
                    assert( self.build_lsn_addr_index(root).contains_key(lsn) );    // witness
//                     assert( self.build_lsn_addr_index(root).values().contains(addr) );
                }
            }
        }
//         assert( self.build_lsn_addr_index(root).values() =~= self.representation(root) );    // TODO remove
    }

    proof fn sub_disk_repr_index(self, big: Self, ptr: Pointer)
    requires
        self.wf(),
        big.wf(),
        big.acyclic(),
        self.is_sub_disk(big),
        self.boundary_lsn == big.boundary_lsn,
        self.is_nondangling_pointer(ptr),
    //ensures self.acyclic()
        ptr.is_Some() ==> self.boundary_lsn < self.entries[ptr.unwrap()].message_seq.seq_end,
    ensures
        self.build_lsn_addr_index(ptr) == big.build_lsn_addr_index(ptr),
    decreases if ptr.is_Some() { big.the_ranking()[ptr.unwrap()]+1 } else { 0 }
    {
        reveal(TruncatedJournal::index_domain_valid);
        reveal(DiskView::index_keys_map_to_valid_entries);

        assert( forall |addr| #[trigger] self.entries.contains_key(addr) ==> big.entries.dom().contains(addr) );    // new clunikness related to contains-vs-contains_key
        assert( self.valid_ranking(big.the_ranking()) );
        if ptr.is_Some() {
            //let jr = big.entries[ptr.unwrap()];
            //self.sub_disk_repr_index(big, jr.cropped_prior(big.boundary_lsn));
            if big.next(ptr).is_Some() {
                assert( big.entries.contains_key(ptr.unwrap()) );
                assert( big.the_ranking()[big.next(ptr).unwrap()] < big.the_ranking()[ptr.unwrap()] );
            }
            self.sub_disk_repr_index(big, big.next(ptr));
        }
    }

//     pub open spec fn lsns_from_unique_addrs(self) -> bool
//     {
//         forall |lsn, addr1, addr2| ({
//             &&& self.entries[addr1].message_seq.contains(lsn)
//             &&& self.entries[addr2].message_seq.contains(lsn)
//         }) ==> addr1 == addr2
//     }

//     pub build_lsn_addr_index_gives_unique_addrs(self, root: Pointer)
//     requires
//         self.buildable(root),
//     ensures
//         self.build_lsn_addr_index(root),
//     {
//     }
   
    pub proof fn build_lsn_addr_all_decodable(self, root: Pointer)
    requires
        self.buildable(root),
    ensures
        forall |lsn| #![auto] self.build_lsn_addr_index(root).contains_key(lsn) ==> self.decodable(Some(self.build_lsn_addr_index(root)[lsn])),
    decreases self.the_rank_of(root)
    {
        let lsn_addr_index = self.build_lsn_addr_index(root);   // I want that super-let!
        if root.is_None() {
        } else {
            self.build_lsn_addr_all_decodable(self.next(root));
            assert forall |lsn| #![auto] lsn_addr_index.contains_key(lsn)
            implies self.decodable(Some(lsn_addr_index[lsn])) by {
                if self.build_lsn_addr_index(self.next(root)).contains_key(lsn) {
                    assert( self.decodable(Some(lsn_addr_index[lsn])) );
                } else {
                    assert( lsn_addr_index[lsn] == root.unwrap() );
                    assert( self.decodable(Some(lsn_addr_index[lsn])) );
                }
            }
        }
    }

    pub proof fn build_lsn_addr_honors_rank(self, root: Pointer, lsn_addr_index: Map<LSN, Address>)
    requires
        self.buildable(root),
        lsn_addr_index == self.build_lsn_addr_index(root),  // wish this were a super-let!
    ensures
        forall |lsn1, lsn2| #![auto] ({
            &&& lsn_addr_index.contains_key(lsn1)
            &&& lsn_addr_index.contains_key(lsn2)
            &&& lsn1 <= lsn2
        }) ==> self.the_rank_of(Some(lsn_addr_index[lsn1])) <= self.the_rank_of(Some(lsn_addr_index[lsn2]))
    decreases self.the_rank_of(root)
    {
        self.build_lsn_addr_all_decodable(root);
        if root.is_None() {
        } else if self.next(root).is_None() {
//             assert( self.build_lsn_addr_index(self.next(root)) == Map::<LSN, Address>::empty() );
        } else {
            self.build_lsn_addr_index_domain_valid(root);
            self.build_lsn_addr_index_domain_valid(self.next(root));
            let prior_index = self.build_lsn_addr_index(self.next(root));
            self.build_lsn_addr_honors_rank(self.next(root), prior_index);
            assert forall |lsn1, lsn2| #![auto] ({
                &&& lsn_addr_index.contains_key(lsn1)
                &&& lsn_addr_index.contains_key(lsn2)
                &&& lsn1 <= lsn2
            }) implies ({
                &&& self.decodable(Some(lsn_addr_index[lsn1]))
                &&& self.decodable(Some(lsn_addr_index[lsn2]))
                &&& self.the_rank_of(Some(lsn_addr_index[lsn1])) <= self.the_rank_of(Some(lsn_addr_index[lsn2]))
            }) by {
                let corner = self.entries[self.next(root).unwrap()].message_seq.seq_end;
                let before = (corner - 1) as nat;
                if lsn1 < corner {
                    assert( prior_index.contains_key(before) ) by {
                        reveal(TruncatedJournal::index_domain_valid);
                    }
//                     assert( lsn1 <= corner );
//                     assert( self.the_rank_of(Some(lsn_addr_index[lsn1])) <= self.the_rank_of(Some(lsn_addr_index[before])) );
//                     assert( self.the_rank_of(Some(lsn_addr_index[corner])) <= self.the_rank_of(Some(lsn_addr_index[corner])) );
                } else {
                    assert( !prior_index.contains_key(lsn1) && !prior_index.contains_key(lsn2) ) by {
                        reveal(TruncatedJournal::index_domain_valid);
                    }
                }
            }
        }
    }

    pub open spec fn index_reflects_disk_view(self, lsn_addr_index: LsnAddrIndex) -> bool
    {
        forall |lsn| #[trigger] lsn_addr_index.contains_key(lsn) ==> {
            &&& self.entries.contains_key(lsn_addr_index[lsn])
            &&& self.entries[lsn_addr_index[lsn]].message_seq.contains(lsn)
        }
    }

    // another thing to tuck into build_lsn_addr_index ensures
    pub proof fn build_lsn_addr_index_reflects_disk_view(self, root: Pointer)
    requires
        self.buildable(root),
    ensures
        self.index_reflects_disk_view(self.build_lsn_addr_index(root)),
    decreases self.the_rank_of(root)
    {
        if root is Some {
            self.build_lsn_addr_index_reflects_disk_view(self.next(root))
        }
    }

    #[verifier(opaque)]
    pub closed spec(checked) fn index_keys_map_to_valid_entries(self, lsn_addr_index: LsnAddrIndex) -> bool
    recommends
        self.wf(),
    {
        forall |lsn| #![auto] lsn_addr_index.contains_key(lsn)
            ==> self.addr_supports_lsn(lsn_addr_index[lsn], lsn)
    }

    // one-off explicit instantiation lemma for use in predicates where reveal is verboten.
    pub proof fn instantiate_index_keys_map_to_valid_entries(self, lsn_addr_index: LsnAddrIndex, lsn: LSN)
    requires
        self.wf(),
        lsn_addr_index.contains_key(lsn),
        self.index_keys_map_to_valid_entries(lsn_addr_index),
    ensures
        self.entries.contains_key(lsn_addr_index[lsn]),
        self.entries[lsn_addr_index[lsn]].contains_lsn(self.boundary_lsn, lsn),
    {
        reveal(DiskView::index_keys_map_to_valid_entries);
    }

    pub proof fn discard_old_index_le(self, root: Pointer, new_bdy: LSN)
    requires
        self.buildable(root),
        self.seq_start() <= new_bdy < self.seq_end(root),
    ensures
        self.discard_old(new_bdy).build_lsn_addr_index(root) <= self.build_lsn_addr_index(root)
    decreases self.the_rank_of(root)
    {
        let old_map = self.build_lsn_addr_index(root);
        let disc_map = self.discard_old(new_bdy).build_lsn_addr_index(root);
        if root is None {
            let x:LsnAddrIndex = Map::empty();
            //assert( x.len() == 0 );
            assert( x.is_empty() );
            assert( old_map.is_empty() );
            assert( disc_map.is_empty() );
            assert( disc_map <= old_map );
        }
        assume(false);
        if root is Some {
            self.discard_old_index_le(self.next(root), new_bdy);

            let old_curr_msgs = self.entries[root.unwrap()].message_seq;
            let old_start_lsn = math::max(self.boundary_lsn as int, old_curr_msgs.seq_start as int) as nat;
            let old_update = singleton_index(old_start_lsn, old_curr_msgs.seq_end, root.unwrap());
            let old_output = self.build_lsn_addr_index(self.next(root)).union_prefer_right(old_update);

            let disc_curr_msgs = self.entries[root.unwrap()].message_seq;
            let disc_start_lsn = math::max(self.boundary_lsn as int, disc_curr_msgs.seq_start as int) as nat;
            let disc_update = singleton_index(disc_start_lsn, disc_curr_msgs.seq_end, root.unwrap());
            let disc_output = self.build_lsn_addr_index(self.next(root)).union_prefer_right(disc_update);

            assert( disc_output.le(old_output) );
            assert( disc_map <= old_map );
        }
    }
} // DiskView proof bits

pub open spec(checked) fn map_to_likes(lsn_addr_map: LsnAddrIndex) -> Likes
    decreases lsn_addr_map.dom().len() when lsn_addr_map.dom().finite()
{
    if lsn_addr_map.dom().len() == 0 {
        no_likes()
    } else {
        let k = lsn_addr_map.dom().choose();
        let sub_likes = map_to_likes(lsn_addr_map.remove(k));
        Multiset::empty().insert(lsn_addr_map[k]).add(sub_likes)
    }
}

impl TruncatedJournal {
    pub open spec(checked) fn build_lsn_addr_index(self) ->  LsnAddrIndex
        recommends self.decodable()
    {
        self.disk_view.build_lsn_addr_index(self.freshest_rec)
    }

    pub open spec(checked) fn transitive_likes(self) -> Likes
    {
        if !self.decodable() { arbitrary() }
        else { Multiset::from_set(self.build_lsn_addr_index().values()) }
    }

    pub open spec(checked) fn tight_discard_old(self, new: Self, new_bdy: LSN, keep: Set<Address>) -> bool
    recommends
        self.wf(),
        new.wf(),
        self.disk_view.boundary_lsn <= new_bdy,
    {
        &&& new.disk_view.boundary_lsn == new_bdy
        &&& new.disk_view.entries.dom() =~= keep
        &&& new.disk_view.entries.agrees(self.disk_view.entries)
        &&& new.freshest_rec == if self.seq_end() == new_bdy { None } else { self.freshest_rec }
    }
}

impl MsgHistory {
    pub open spec(checked) fn tight_discard_old(self, new: Self, new_bdy: LSN) -> bool
    recommends
        self.wf(),
        new.wf(),
    {
        let msgs = if self.seq_start <= new_bdy { self.discard_old(new_bdy) } else { self };
        &&& new.ext_equal(msgs)
    }

    pub proof fn discard_old_index_le(self, new_bdy: LSN)
    requires
        self.disk_view.buildable(self.freshest_rec),
        self.can_discard_to(new_bdy),
    ensures
        self.discard_old(new_bdy).build_lsn_addr_index() <= self.build_lsn_addr_index()
    {
        if new_bdy < self.seq_end() {
            self.disk_view.discard_old_index_le(self.freshest_rec, new_bdy);
            assert( self.discard_old(new_bdy).build_lsn_addr_index() <= self.build_lsn_addr_index() );
        } else {
            assert( new_bdy == self.seq_end() );
            let disc_tj = self.discard_old(new_bdy);
            // boy a spec-ensures of decodable on discard_old sure would be handy! Gaaah.
            assert( disc_tj.decodable() );
            assert( disc_tj.freshest_rec is None );
            assert( disc_tj.build_lsn_addr_index() <= self.build_lsn_addr_index() );
        }
    }
}

// TODO(jonh): move to pervasive
spec(checked) fn max(a: int, b: int) -> int
{
    if a < b { b } else { a }
}

// Definitions that used to live in the Refinement file, but jonh pulled in here so the invariant
// could be handled using the state_machines invariant machinery.
impl TruncatedJournal {
    // TODO(jonh): HOW THE HECK IS THIS OKAY?
    // Why doesn't truncating the first record violate this for lsns between message_seq.start and
    // boundary!?
    // ...oh, the relevant inv proof isn't completed. Hah. It's not okay.
    pub open spec(checked) fn valid_entries_appear_in_index(self, lsn_addr_index: LsnAddrIndex) -> bool
    recommends
        self.wf(),
    {
        forall |addr, lsn| self.disk_view.addr_supports_lsn(addr, lsn)
             ==> lsn_addr_index.contains_key(lsn) && lsn_addr_index[lsn]==addr
    }

    #[verifier(opaque)]
    pub open spec(checked) fn index_domain_valid(self, lsn_addr_index: LsnAddrIndex) -> bool
    recommends
        self.wf(),
    {
        // lsnAddrIndex's domain is exactly the set of LSN between journal.SeqStart() and journal.SeqEnd()
        &&& forall |lsn| lsn_addr_index.contains_key(lsn) <==> (self.seq_start() <= lsn < self.seq_end())
    }

    pub closed spec /*XXX (checked)*/ fn index_range_valid(self, lsn_addr_index: LsnAddrIndex) -> bool
    recommends
        self.wf(),
        self.index_domain_valid(lsn_addr_index),
        self.disk_view.index_keys_map_to_valid_entries(lsn_addr_index),
    {
        forall |addr| lsn_addr_index.values().contains(addr) ==> {
            let lsn = choose |lsn| (#[trigger] lsn_addr_index.contains_key(lsn)) && lsn_addr_index[lsn] == addr;
            // TODO(jonh): need to invoke instantiate_index_keys_map_to_valid_entries here to
            // satisfy recommendation check.
            let msgs = self.disk_view.entries[addr].message_seq;
            let boundary_lsn = self.disk_view.boundary_lsn;
            forall |lsn| #![auto] DiskView::cropped_lsn(boundary_lsn, msgs, lsn) ==> {
                &&& lsn_addr_index.contains_key(lsn)
                &&& lsn_addr_index[lsn] == addr
            }
        }
    }

    pub proof fn build_lsn_addr_index_gives_representation(self) 
    requires
        self.wf(),
        self.disk_view.decodable(self.freshest_rec),
        self.disk_view.acyclic(),
    ensures
        self.build_lsn_addr_index().values() == self.representation(),
    {
        self.disk_view.build_lsn_addr_index_gives_representation(self.freshest_rec)
    }
    

    pub proof fn build_lsn_addr_honors_rank(self, lsn_addr_index: Map<LSN, Address>)
    requires
        self.decodable(),
        lsn_addr_index == self.build_lsn_addr_index(),
    ensures
        forall |lsn1, lsn2| #![auto] ({
            &&& lsn_addr_index.contains_key(lsn1)
            &&& lsn_addr_index.contains_key(lsn2)
            &&& lsn1 <= lsn2
        }) ==> self.disk_view.the_rank_of(Some(lsn_addr_index[lsn1])) <= self.disk_view.the_rank_of(Some(lsn_addr_index[lsn2]))
    {
        self.disk_view.build_lsn_addr_honors_rank(self.freshest_rec, lsn_addr_index)
    }
}

state_machine!{ LikesJournal {
    fields {
        pub journal: LinkedJournal_v::LinkedJournal::State,
        pub lsn_addr_index: LsnAddrIndex,
    }

    #[is_variant]
    pub enum Label
    {
        ReadForRecovery{messages: MsgHistory},
        FreezeForCommit{frozen_journal: TruncatedJournal},
        QueryEndLsn{end_lsn: LSN},
        Put{messages: MsgHistory},
        DiscardOld{start_lsn: LSN, require_end: LSN},
        Internal{},   // Local No-op label
    }

    // TODO want to add an impl on Label, but ... state machine macro
    // There's nothing to interpret here; it's the same label as the layer
    // above. There's a lot of useless boilerplate in this layer; perhaps
    // there's a prettier way to decorate an existing state machine with
    // extra ghost state.
    pub open spec fn lbl_i(lbl: Label) -> LinkedJournal_v::LinkedJournal::Label {
        match lbl {
            Label::ReadForRecovery{messages}
                => LinkedJournal_v::LinkedJournal::Label::ReadForRecovery{messages},
            Label::FreezeForCommit{frozen_journal}
                => LinkedJournal_v::LinkedJournal::Label::FreezeForCommit{frozen_journal},
            Label::QueryEndLsn{end_lsn}
                => LinkedJournal_v::LinkedJournal::Label::QueryEndLsn{end_lsn},
            Label::Put{messages}
                => LinkedJournal_v::LinkedJournal::Label::Put{messages},
            Label::DiscardOld{start_lsn, require_end}
                => LinkedJournal_v::LinkedJournal::Label::DiscardOld{start_lsn, require_end},
            Label::Internal{}
                => LinkedJournal_v::LinkedJournal::Label::Internal{},
        }
    }
    
    pub open spec(checked) fn wf(self) -> bool {
        &&& self.journal.wf()
        // TODO this conjunct ought to be part of journal.wf, at least.
        // &&& self.journal.truncated_journal.seq_start() <= self.journal.truncated_journal.seq_end()
    }

    pub open spec fn transitive_likes(self) -> Likes 
    {
        self.journal.truncated_journal.transitive_likes()
    }

    pub open spec fn imperative_likes(self) -> Likes
    {
        Multiset::from_set(self.lsn_addr_index.values())
    }

    transition!{ read_for_recovery(lbl: Label) {
        require LinkedJournal_v::LinkedJournal::State::next(pre.journal, pre.journal, Self::lbl_i(lbl));
    } }

    transition!{ freeze_for_commit(lbl: Label) {
        require LinkedJournal_v::LinkedJournal::State::next(pre.journal, pre.journal, Self::lbl_i(lbl));
    } }

    transition!{ query_end_lsn(lbl: Label) {
        require LinkedJournal_v::LinkedJournal::State::next(pre.journal, pre.journal, Self::lbl_i(lbl));
    } }
    
    transition!{ put(lbl: Label, new_journal: LinkedJournal_v::LinkedJournal::State) {
        require LinkedJournal_v::LinkedJournal::State::next(pre.journal, new_journal, Self::lbl_i(lbl));
    } }
    
    transition!{ discard_old(lbl: Label, new_journal: LinkedJournal_v::LinkedJournal::State) {
        require lbl is DiscardOld;

        // TODO These verbose accessors are really unpleasant to read.
        let start_lsn = lbl.get_DiscardOld_start_lsn();

        // require pre.journal.wf();   // TODO delete; it's in inv
        // require pre.journal.truncated_journal.disk_view.acyclic();   // TODO delete; it's in inv
        require pre.journal.seq_start() <= start_lsn <= pre.journal.seq_end();
        require lbl.get_DiscardOld_require_end() == pre.journal.seq_end();
        require pre.journal.truncated_journal.can_discard_to(start_lsn);

        // Addrs to delete from likes are pages that are between the old LSN and new LSN,
        // excluding the page containing the new LSN boundary
        let lsn_addr_index_post = lsn_addr_index_discard_up_to(pre.lsn_addr_index, start_lsn);
        let keep_addrs = lsn_addr_index_post.values();
        let unref_addrs = pre.lsn_addr_index.values().difference(keep_addrs);

        require new_journal.wf();
        require pre.journal.truncated_journal.tight_discard_old(
            new_journal.truncated_journal, start_lsn, keep_addrs);
        require pre.journal.unmarshalled_tail.tight_discard_old(
            new_journal.unmarshalled_tail, start_lsn);

        update journal = new_journal;
        update lsn_addr_index = lsn_addr_index_post;
    } }

    transition!{ internal_journal_marshal(lbl: Label, cut: LSN, addr: Address, newjournal: LinkedJournal_v::LinkedJournal::State) {
        require lbl.is_Internal();
        require !pre.lsn_addr_index.values().contains(addr);
        
        require LinkedJournal_v::LinkedJournal::State::next_by(
            pre.journal, newjournal, Self::lbl_i(lbl), LinkedJournal_v::LinkedJournal::Step::internal_journal_marshal(cut, addr));

        update journal = newjournal;
        update lsn_addr_index = lsn_addr_index_append_record(
            pre.lsn_addr_index,
            pre.journal.unmarshalled_tail.discard_recent(cut),
            addr);
    } }

    transition!{ internal_no_op(lbl: Label) {
        require lbl is Internal;
    } }

    // TODO(travis): Weird that I can't call my only init operation "init"
    // TODO(travis): one can shadow field names with argument names, leading
    // to confusing error messages. I suggest the state-machine language
    // should simply treat shadowing as an error.
    init!{ initialize(ijournal: TruncatedJournal) {
        require ijournal.decodable();    // An invariant carried by CoordinationSystem from FreezeForCommit, past a crash, back here
        require ijournal.disk_is_tight_wrt_representation();
        init journal = LinkedJournal_v::LinkedJournal::State{
            truncated_journal: ijournal,
            unmarshalled_tail: MsgHistory::empty_history_at(ijournal.build_tight().seq_end())};
        init lsn_addr_index = ijournal.build_lsn_addr_index();
    } }

//////////////////////////////////////////////////////////////////////////////
// Definitions moved from Refinement file to integrate with invariant machinery.
    // The thrilling climax, the actual proof goal we want to use in lower
    // refinement layers.
    pub open spec(checked) fn imperative_matches_transitive(self) -> bool
    {
        self.transitive_likes() == self.imperative_likes()
    }

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        let tj = self.journal.truncated_journal;
        &&& self.wf()
        &&& tj.disk_view.acyclic()
        &&& self.lsn_addr_index == tj.build_lsn_addr_index()
        &&& self.lsn_addr_index.values() == tj.representation()
        &&& tj.disk_view.index_reflects_disk_view(self.lsn_addr_index)  // TODO or just prove it from build
        &&& tj.index_domain_valid(self.lsn_addr_index)
        &&& tj.disk_view.index_keys_map_to_valid_entries(self.lsn_addr_index)
        &&& tj.valid_entries_appear_in_index(self.lsn_addr_index)
        &&& tj.index_range_valid(self.lsn_addr_index)
        &&& tj.disk_is_tight_wrt_representation()
        &&& self.imperative_matches_transitive()
    }

    #[inductive(read_for_recovery)]
    fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label) {
        reveal(LinkedJournal_v::LinkedJournal::State::next);
        reveal(LinkedJournal_v::LinkedJournal::State::next_by);
    }
   
    #[inductive(freeze_for_commit)]
    fn freeze_for_commit_inductive(pre: Self, post: Self, lbl: Label) {
        reveal(LinkedJournal_v::LinkedJournal::State::next);
        reveal(LinkedJournal_v::LinkedJournal::State::next_by);
    }

    #[inductive(query_end_lsn)]
    fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label) {
        reveal(LinkedJournal_v::LinkedJournal::State::next);
        reveal(LinkedJournal_v::LinkedJournal::State::next_by);
    }
   
    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label, new_journal: LinkedJournal_v::LinkedJournal::State) {
        reveal(LinkedJournal_v::LinkedJournal::State::next);
        reveal(LinkedJournal_v::LinkedJournal::State::next_by);
    }

    /* `pub` is only being added to avoid a confusing fake error message, originally we didn't intend for this
       proof function to be `pub` */
    pub proof fn discard_old_step_preserves_wf_disk_view(pre: Self, post: Self, lbl: Label)
    requires
        pre.wf(),
        pre.journal.truncated_journal.index_domain_valid(pre.lsn_addr_index),
        pre.journal.truncated_journal.disk_view.index_keys_map_to_valid_entries(pre.lsn_addr_index),
        pre.journal.truncated_journal.index_range_valid(pre.lsn_addr_index),
        pre.journal.truncated_journal.disk_view.acyclic(),
        pre.lsn_addr_index == pre.journal.truncated_journal.build_lsn_addr_index(),
        pre.lsn_addr_index.values() == pre.journal.truncated_journal.representation(),
        Self::discard_old(pre, post, lbl, post.journal),
    ensures
        post.journal.truncated_journal.wf(),
    {
        assume(false); // TODO port this proof
    }
   
    pub proof fn discard_old_step_preserves_wf_and_index(pre: Self, post: Self, lbl: Label)
    requires
        pre.wf(),
        pre.journal.truncated_journal.index_domain_valid(pre.lsn_addr_index),
        pre.journal.truncated_journal.disk_view.index_keys_map_to_valid_entries(pre.lsn_addr_index),
        pre.journal.truncated_journal.index_range_valid(pre.lsn_addr_index),
        pre.journal.truncated_journal.disk_view.acyclic(),
        pre.lsn_addr_index == pre.journal.truncated_journal.build_lsn_addr_index(),
        pre.lsn_addr_index.values() == pre.journal.truncated_journal.representation(),
        Self::discard_old(pre, post, lbl, post.journal),
    ensures
        post.wf(),
        post.journal.truncated_journal.index_domain_valid(post.lsn_addr_index),
        post.journal.truncated_journal.disk_view.index_keys_map_to_valid_entries(post.lsn_addr_index),
        post.journal.truncated_journal.index_range_valid(post.lsn_addr_index),
    {
        reveal(TruncatedJournal::index_domain_valid);
        reveal(DiskView::index_keys_map_to_valid_entries);

        let tj_pre = pre.journal.truncated_journal;
        let tj_post = post.journal.truncated_journal;
        let pre_bdy = tj_pre.disk_view.boundary_lsn;
        let new_bdy = lbl.get_DiscardOld_start_lsn();

        Self::discard_old_step_preserves_wf_disk_view(pre, post, lbl);
    
        // prove tj'.diskView.IsNondanglingPointer(tj'.freshestRec);
        if tj_post.freshest_rec.is_Some() {
          let msgs = tj_pre.disk_view.entries[tj_pre.freshest_rec.unwrap()].message_seq;
          let lsn = max(new_bdy as int, msgs.seq_start as int) as nat; // witness
          assume( post.lsn_addr_index.contains_key(lsn) && post.lsn_addr_index[lsn] == tj_pre.freshest_rec.unwrap() );  // TODO left off
        }
        
        assume(false); // TODO complete this proof
    }

    pub proof fn discard_old_maintains_repr_index(pre: Self, post: Self, lbl: Label)
    requires
        pre.inv(),
        post.wf(),
        Self::discard_old(pre, post, lbl, post.journal),
        pre.journal.truncated_journal.disk_view.acyclic(),
    ensures
        post.lsn_addr_index == post.journal.truncated_journal.build_lsn_addr_index(),
    {
        assume(false);  // TODO more proof porting
    }

    #[inductive(discard_old)]
    fn discard_old_inductive(pre: Self, post: Self, lbl: Label, new_journal: LinkedJournal_v::LinkedJournal::State) {
        reveal(LinkedJournal_v::LinkedJournal::State::next_by);
        Self::discard_old_step_preserves_wf_and_index(pre, post, lbl);
        let ranking = pre.journal.truncated_journal.disk_view.the_ranking();  // witness to acyclicity
        assert( post.journal.truncated_journal.disk_view.valid_ranking(ranking) );
        Self::discard_old_maintains_repr_index(pre, post, lbl);
        post.journal.truncated_journal.build_lsn_addr_index_gives_representation();
        assert( post.journal.truncated_journal.index_range_valid(post.lsn_addr_index) );
        assume(post.journal.truncated_journal.disk_is_tight_wrt_representation()); // TODO something didn't prove for free
        assume( false );
        assert( post.inv() );
    }

    #[inductive(internal_journal_marshal)]
    fn internal_journal_marshal_inductive(pre: Self, post: Self, lbl: Label, cut: LSN, addr: Address, newjournal: LinkedJournal_v::LinkedJournal::State) {
        reveal(LinkedJournal_v::LinkedJournal::State::next_by);

        let istep:LinkedJournal_v::LinkedJournal::Step = LinkedJournal_v::LinkedJournal::Step::internal_journal_marshal(cut, addr);
        assert( LinkedJournal_v::LinkedJournal::State::next_by(pre.journal, post.journal, State::lbl_i(lbl), istep) );
        LinkedJournal_v::LinkedJournal::State::inv_next(pre.journal, post.journal, State::lbl_i(lbl), istep);

    //var tj := v.journal.truncatedJournal;
    //var tj' := v'.journal.truncatedJournal;
        let tj_pre = pre.journal.truncated_journal;
        let tj_post = post.journal.truncated_journal;
        assert( tj_post.disk_view.acyclic() );
        tj_pre.disk_view.sub_disk_repr_index(tj_post.disk_view, tj_pre.freshest_rec);
        tj_post.build_lsn_addr_index_gives_representation();

        reveal(TruncatedJournal::index_domain_valid);
        reveal(DiskView::index_keys_map_to_valid_entries);
        assert( tj_post.index_domain_valid(post.lsn_addr_index) );
        assert( tj_post.disk_view.index_keys_map_to_valid_entries(post.lsn_addr_index) );
        assert( tj_post.index_range_valid(post.lsn_addr_index) );
        assert( post.lsn_addr_index =~= tj_post.build_lsn_addr_index() ); // used to be free :v(

        tj_post.disk_view.representation_ensures(tj_post.freshest_rec); // not helpful; delete

        assert forall |addr| #![auto] tj_post.disk_view.entries.dom().contains(addr)
            implies tj_post.representation().contains(addr) by {
            if tj_pre.disk_view.entries.dom().contains(addr) {
                assert( tj_pre.representation().contains(addr) );
                let newaddr = tj_post.freshest_rec.unwrap();
                assert( tj_post.freshest_rec.is_Some() );
                assume( tj_pre.disk_view.representation(tj_pre.freshest_rec) == tj_post.disk_view.representation(tj_post.disk_view.entries[newaddr].cropped_prior(tj_post.disk_view.boundary_lsn)) );   // TODO(jonh): left off battling this silly corner
                assert( tj_post.representation() == tj_pre.representation().insert(newaddr) );
                assert( tj_post.representation().contains(addr) );
            } else {
                assert( tj_post.representation().contains(addr) );
            }
        }
        assert forall |addr|
            tj_post.representation().contains(addr)
            implies
            tj_post.disk_view.entries.dom().contains(addr)
            by {
        }
        assert( tj_post.disk_view.entries.dom() =~= tj_post.representation() );
        assert( tj_post.disk_is_tight_wrt_representation() ) by {
        }
        assert( post.inv() );
    }
   
    #[inductive(internal_no_op)]
    fn internal_no_op_inductive(pre: Self, post: Self, lbl: Label) {
    }
   
    #[inductive(initialize)]
    fn initialize_inductive(post: Self, ijournal: TruncatedJournal) {
        reveal(TruncatedJournal::index_domain_valid);
        reveal(DiskView::index_keys_map_to_valid_entries);
        ijournal.disk_view.build_tight_is_awesome(ijournal.freshest_rec);
        let tight_tj = ijournal.build_tight();
        if tight_tj.freshest_rec.is_Some() {
            tight_tj.disk_view.build_lsn_addr_index_domain_valid(tight_tj.freshest_rec);
        }
        tight_tj.disk_view.build_lsn_addr_index_range_valid(tight_tj.freshest_rec, tight_tj.seq_end());
        tight_tj.build_lsn_addr_index_gives_representation();
        ijournal.disk_view.build_tight_gives_representation(ijournal.freshest_rec);
        ijournal.disk_view.representation_ignores_build_tight(ijournal.freshest_rec, ijournal.freshest_rec);
        ijournal.disk_view.build_lsn_addr_index_ignores_build_tight(ijournal.freshest_rec, ijournal.freshest_rec);
    }
    
} } // state_machine!
        
} // verus!
