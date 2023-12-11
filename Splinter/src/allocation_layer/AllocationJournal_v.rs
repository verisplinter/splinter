// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use builtin::*;
use vstd::prelude::*;
use vstd::math;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;
use vstd::map::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
use crate::disk::GenericDisk_v::*;
use crate::disk::GenericDisk_v::AU;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::{DiskView, TruncatedJournal, LinkedJournal};
use crate::journal::LikesJournal_v;
use crate::journal::LikesJournal_v::LikesJournal;
use crate::allocation_layer::MiniAllocator_v::*;

verus!{

pub struct JournalImage {
    pub tj: TruncatedJournal,
    pub first: AU,
}

impl JournalImage {
    pub open spec(checked) fn wf(self) -> bool
    {
        self.tj.wf()
    }

    pub open spec(checked) fn accessible_aus(self) -> Set<AU>
    {
        to_aus(self.tj.disk_view.entries.dom())
    }

    pub open spec(checked) fn empty() -> Self
    {
        Self{ tj: TruncatedJournal::mkfs(), first: 0 }
    }
}

state_machine!{ AllocationJournal {
    fields {
        pub journal: LikesJournal::State,

        // lsnAUAddrIndex maps in-repr lsn's to their AU addr
        pub lsn_au_index: Map<LSN, AU>,

        // AU containing the first journal record, boundarylsn can be found somewhere in this AU
        // (We only record the AU here because that's what the implementation can efficiently
        // recover from lsn_au_index at discard time.)
        pub first: AU,

        pub mini_allocator: MiniAllocator,
    }

    #[is_variant]
    pub enum Label
    {
        ReadForRecovery{messages: MsgHistory},
        FreezeForCommit{frozen_journal: JournalImage},
        QueryEndLsn{end_lsn: LSN},
        Put{messages: MsgHistory},
        DiscardOld{start_lsn: LSN, require_end: LSN, deallocs: Set<AU>},
        InternalAllocations{allocs: Set<AU>, deallocs: Set<AU>},
    }

    pub closed spec(checked) fn lbl_wf(lbl: Label) -> bool {
        match lbl {
            Label::FreezeForCommit{frozen_journal} => frozen_journal.tj.decodable(),
            _ => true,
        }
    }

    pub closed spec(checked) fn lbl_i(lbl: Label) -> LikesJournal::Label {
        match lbl {
            Label::ReadForRecovery{messages} =>
                LikesJournal::Label::ReadForRecovery{messages},
            Label::FreezeForCommit{frozen_journal} =>
                LikesJournal::Label::FreezeForCommit{frozen_journal: frozen_journal.tj},
            Label::QueryEndLsn{end_lsn} =>
                LikesJournal::Label::QueryEndLsn{end_lsn},
            Label::Put{messages} =>
                LikesJournal::Label::Put{messages},
            Label::DiscardOld{start_lsn, require_end, deallocs} =>
                LikesJournal::Label::DiscardOld{start_lsn, require_end},
            Label::InternalAllocations{allocs, deallocs} =>
                LikesJournal::Label::Internal{},
        }
    }

    pub open spec(checked) fn wf(self) -> bool {
        &&& self.journal.wf()
        &&& self.mini_allocator.wf()
    }

    pub open spec(checked) fn accessible_aus(self) -> Set<AU> {
        self.lsn_au_index.values() + self.mini_allocator.allocs.dom()
    }

    pub open spec(checked) fn new_first(tj: TruncatedJournal, lsn_au_index: Map<LSN, AU>, new_bdy: LSN) -> AU
    recommends
        tj.wf(),
        lsn_au_index.contains_key(new_bdy),
    {
        let post_freshest_rec = if tj.seq_end() == new_bdy { None } else { tj.freshest_rec }; // matches defn at TruncatedJournal::discard_old
        if post_freshest_rec is None { 0 } // kinda doesn't matter, since no recs!
        else { lsn_au_index[new_bdy] }
    }

    transition!{ read_for_recovery(lbl: Label) {
        require LikesJournal_v::LikesJournal::State::next(pre.journal, pre.journal, Self::lbl_i(lbl));
    } }

    transition!{ freeze_for_commit(lbl: Label) {
        require LikesJournal_v::LikesJournal::State::next(pre.journal, pre.journal, Self::lbl_i(lbl));
        let frozen_journal = lbl.get_FreezeForCommit_frozen_journal();
        let frozen_first = Self::new_first(frozen_journal.tj, pre.lsn_au_index, pre.first, frozen_journal.tj.seq_start());
        require frozen_journal.first == frozen_first;
    } }

    transition!{ query_end_lsn(lbl: Label) {
        require LikesJournal_v::LikesJournal::State::next(pre.journal, pre.journal, Self::lbl_i(lbl));
    } }
    
    transition!{ put(lbl: Label) {
        require LikesJournal_v::LikesJournal::State::next(pre.journal, pre.journal, Self::lbl_i(lbl));
    } }

    transition!{ discard_old(lbl: Label, post_journal: LikesJournal::State) {
        require pre.wf();
        require Self::lbl_wf(lbl);
        require lbl.is_DiscardOld();
        require LikesJournal::State::discard_old(pre.journal, post_journal, Self::lbl_i(lbl), post_journal.journal);

        let new_lsn_au_index = Self::lsn_au_index_discarding_up_to(pre.lsn_au_index, lbl.get_DiscardOld_start_lsn());
        let discarded_aus = pre.lsn_au_index.values().difference(new_lsn_au_index.values());
        let new_first = Self::new_first(pre.journal.journal.truncated_journal, pre.lsn_au_index, lbl.get_DiscardOld_start_lsn());

        require lbl.get_DiscardOld_deallocs() == discarded_aus;

        update journal = post_journal;
        update lsn_au_index = new_lsn_au_index;
        update first = new_first;
        update mini_allocator = pre.mini_allocator.prune(discarded_aus.intersect(pre.mini_allocator.allocs.dom()));
      // note that these AUs refine to free (in the frozen freeset)
    } }

    transition!{ internal_journal_marshal(lbl: Label, cut: LSN, addr: Address, post_linked_journal: LinkedJournal::State) {
        require pre.wf();
        require Self::lbl_wf(lbl);
        require lbl is InternalAllocations;
        require lbl.get_InternalAllocations_allocs() == Set::<AU>::empty();
        require lbl.get_InternalAllocations_deallocs() == Set::<AU>::empty();
        require  Self::valid_next_journal_addr(
                pre.mini_allocator, 
                pre.journal.journal.truncated_journal.freshest_rec, 
                addr);
        require LinkedJournal::State::internal_journal_marshal(
                pre.journal.journal, post_linked_journal,
                LikesJournal::State::lbl_i(Self::lbl_i(lbl)), cut, addr);
        let marshal_msgs = pre.journal.journal.unmarshalled_tail.discard_recent(cut);
        update journal = LikesJournal::State{
            journal: post_linked_journal,
            lsn_addr_index: LikesJournal_v::lsn_addr_index_append_record(
                pre.journal.lsn_addr_index, marshal_msgs, addr),
            };
        update lsn_au_index = Self::lsn_au_index_append_record(pre.lsn_au_index, marshal_msgs, addr.au);
        update first = if pre.journal.journal.truncated_journal.freshest_rec.is_Some() { pre.first } else { addr.au };
        update mini_allocator = pre.mini_allocator.allocate_and_observe(addr);
    } }

    transition!{ internal_mini_allocator_fill(lbl: Label) {
        require pre.wf();
        require Self::lbl_wf(lbl);
        require lbl.is_InternalAllocations();
        require lbl.get_InternalAllocations_deallocs() == Set::<AU>::empty();
        // TODO: maybe we want to eliminate this check and just use the label
        require lbl.get_InternalAllocations_allocs().disjoint(
            pre.mini_allocator.allocs.dom());

        update mini_allocator = pre.mini_allocator.add_aus(lbl.get_InternalAllocations_allocs());
    } }

    transition!{ internal_mini_allocator_prune(lbl: Label) {
        require pre.wf();
        require Self::lbl_wf(lbl);
        require lbl.is_InternalAllocations();
        require lbl.get_InternalAllocations_allocs() == Set::<AU>::empty();
        require forall |au| lbl.get_InternalAllocations_deallocs().contains(au)
                ==> pre.mini_allocator.can_remove(au);

        update mini_allocator = pre.mini_allocator.prune(lbl.get_InternalAllocations_deallocs());
    } }

    transition!{ internal_journal_no_op(lbl: Label) {
        require lbl is InternalAllocations;
    } }

    // Update lsnAUIndex with by discarding lsn's strictly smaller than bdy
    // Removed (checked) due to lambda being total
    pub open spec/*(checked)*/ fn lsn_au_index_discarding_up_to(lsn_au_index: Map<LSN, AU>, bdy: LSN) -> (out: Map<LSN, AU>)
//     ensures
//         out.len(lsn_au_index),
//         forall |k| out.contains_key(k) :: bdy <= k,
//         forall |k| lsn_au_index.contains_key(k) && bdy <= k ==> out.contains_key(k),
    {
        Map::new(|lsn| lsn_au_index.contains_key(lsn) && bdy <= lsn,
                 |lsn| lsn_au_index[lsn])
    }

    // TODO(jonh): duplicates text in LikesJournal_v. Eww.
    pub open spec(checked) fn singleton_index(start_lsn: LSN, end_lsn: LSN, value: AU) -> (index: Map<LSN, AU>)
    {
        Map::new(|lsn| start_lsn <= lsn < end_lsn, |lsn| value)
    }

    // Update lsnAUIndex with additional lsn's from a new record
    pub open spec(checked) fn lsn_au_index_append_record(lsn_au_index: Map<LSN, AU>, msgs: MsgHistory, au: AU) -> (out: Map<LSN, AU>)
    recommends
        msgs.wf(),
        msgs.seq_start < msgs.seq_end,   // nonempty history
    // ensures LikesJournal::lsn_disjoint(lsn_au_index.dom(), msgs)
    //      ==> out.values() == lsn_au_index.values() + set![au]
    {
        // msgs is complete map from seqStart to seqEnd
        let update = Self::singleton_index(msgs.seq_start, msgs.seq_end, au);
        let out = lsn_au_index.union_prefer_right(update);
        // assertion here in dafny original
        out
    }

    pub open spec(checked) fn valid_next_journal_addr(mini_allocator: MiniAllocator, freshest_rec: Pointer, addr: Address) -> bool {
        &&& mini_allocator.can_allocate(addr)
        &&& (mini_allocator.curr is None ==> {
              &&& mini_allocator.allocs[addr.au].all_pages_free()
              &&& addr.page == 0
        })
        &&& (mini_allocator.curr is Some && freshest_rec is Some ==> 
            addr == freshest_rec.unwrap().next()
        )
    }

    pub open spec(checked) fn build_lsn_au_index_page_walk(dv: DiskView, root: Pointer) -> Map<LSN, AU>
    recommends
        dv.decodable(root),
        dv.acyclic(),
    decreases dv.the_rank_of(root)
        // TODO(chris): this when clause isn't working!
        when {
        // TODO(chris): oh look, &&&s not ,s! Let's run with that!
        &&& dv.decodable(root)
        &&& dv.acyclic()
    }
    {
        decreases_when({
            &&& dv.decodable(root)
            &&& dv.acyclic()
        });
//         decreases_by(Self::build_lsn_au_index_page_walk_proof);
        if root.is_None() { Map::empty() }
        else {
            let curr_msgs = dv.entries[root.unwrap()].message_seq;
            let update = Self::singleton_index(
                math::max(dv.boundary_lsn as int, curr_msgs.seq_start as int) as nat, curr_msgs.seq_end, root.unwrap().au);
            Self::build_lsn_au_index_page_walk(dv, dv.next(root)).union_prefer_right(update)
        }
    }

    // I think you could prove this by connecting from page_walk to au_walk, thence to
    // lsn_addr_index, thence via index_domain_valid. But... ew.
    pub proof fn build_lsn_au_index_page_walk_domain(dv: DiskView, root: Pointer)
    requires
        dv.decodable(root),
        dv.acyclic(),
    ensures
        forall |lsn| Self::build_lsn_au_index_page_walk(dv, root).contains_key(lsn) <==> (dv.tj_at(root).seq_start() <= lsn < dv.tj_at(root).seq_end()),
    decreases dv.the_rank_of(root)
    {
        // TODO(chris) Another great application of spec ensures. (Also frustrating absence; spent
        // a dozen lines discovering the trigger on top of the dozen lines setting this silly thing
        // up)
        if root is Some {
            Self::build_lsn_au_index_page_walk_domain(dv, dv.next(root));

            let prior_result = Self::build_lsn_au_index_page_walk(dv, dv.next(root));   // trigger mctriggerface that we'd get for free in spec ensures
        }
    }

    pub proof fn build_commutes_over_discard_page_walk(dv: DiskView, root: Pointer, new_bdy: LSN)
    requires
        dv.tj_at(root).decodable(),
        dv.tj_at(root).can_discard_to(new_bdy),
    ensures ({
        let old_au_idx = Self::build_lsn_au_index_page_walk(dv, root); // super-let, please
        let new_tj = dv.tj_at(root).discard_old(new_bdy);
        Self::build_lsn_au_index_page_walk(new_tj.disk_view, new_tj.freshest_rec)
            =~= Self::lsn_au_index_discarding_up_to(old_au_idx, new_bdy)    // remember, kids, the tilde is a proof strategy!
        }),
    decreases dv.the_rank_of(root)
    {
        Self::build_lsn_au_index_page_walk_domain(dv, root);
        let discarded_tj = dv.tj_at(root).discard_old(new_bdy);
        assert( discarded_tj.disk_view.valid_ranking(dv.the_ranking()) );   // witness to acyclic
        Self::build_lsn_au_index_page_walk_domain(discarded_tj.disk_view, root);
        if root is Some && new_bdy < dv.entries[root.unwrap()].message_seq.seq_start {
            Self::build_commutes_over_discard_page_walk(dv, dv.next(root), new_bdy);    // recurse
        }
    }

    pub proof fn build_lsn_au_index_page_walk_sub_disk(small: DiskView, big: DiskView, root: Pointer)
    requires
        small.decodable(root),
        big.acyclic(),
        big.decodable(root),
        small.is_sub_disk(big),
    ensures
        Self::build_lsn_au_index_page_walk(small, root) == Self::build_lsn_au_index_page_walk(big, root),
    decreases small.the_rank_of(root)
    {
        assert forall |addr| small.entries.contains_key(addr) ==> big.entries.contains_key(addr) by {}  // trigger for ranking
        assert( small.valid_ranking(big.the_ranking()) );

        if root is Some {
            Self::build_lsn_au_index_page_walk_sub_disk(small, big, small.next(root));
        }
    }


    pub proof fn build_commutes_over_append_record(dv: DiskView, root: Pointer, msgs: MsgHistory, new_addr: Address)
    requires
        dv.tj_at(root).decodable(),
        dv.tj_at(root).seq_end() == msgs.seq_start,
        msgs.wf(),
        !msgs.is_empty(),
        !dv.entries.contains_key(new_addr),
    ensures ({
        let old_au_idx = Self::build_lsn_au_index_page_walk(dv, root); // super-let, please

        let au_update = Self::singleton_index(msgs.seq_start, msgs.seq_end, new_addr.au);
        let incremental_idx = old_au_idx.union_prefer_right(au_update);

        let appended_tj = dv.tj_at(root).append_record(new_addr, msgs);
        let built_idx = Self::build_lsn_au_index_page_walk(appended_tj.disk_view, appended_tj.freshest_rec);
        incremental_idx =~= built_idx       // remember, kids, the tilde is a proof strategy!
        }),
    decreases dv.the_rank_of(root)
    {
        let appended_tj = dv.tj_at(root).append_record(new_addr, msgs);
        assert( appended_tj.disk_view.valid_ranking(dv.tj_at(root).marshal_ranking(new_addr)) ); // witness to acyclic
        Self::build_lsn_au_index_page_walk_sub_disk(dv, appended_tj.disk_view, root);
    }

// I am surprised this proves for free.
    pub proof fn build_lsn_au_index_equiv_page_walk(dv: DiskView, root: Pointer, first: AU)
    requires
        Self::pointer_is_upstream(dv, root, first),
        dv.acyclic(),
        Self::internal_au_pages_fully_linked(dv),
        root is Some ==> Self::valid_first_au(dv, first),
    ensures
        Self::build_lsn_au_index_au_walk(dv, root, first) =~= Self::build_lsn_au_index_page_walk(dv, root),
    decreases dv.the_rank_of(root)
    {
        match root {
            None => { }
            Some(addr) => {
                if addr.au == first {
                } else {
                    Self::build_lsn_au_index_equiv_page_walk(dv, dv.next(root), first);

                    // TODO(andrea): rediscovering this is brutal. I copy-pasted the definition
                    // three times before realizing I hadn't satisfied decreases_by. This should
                    // have been dispatched in the spec fn.  Aaargh.
                    Self::bottom_properties(dv, root, first);

                    if 0 < root.unwrap().page {    // zero case is easy; au-walk and page-walk do the same thing
                        assert(dv.next(root) is Some) by /*contradiction*/ {
                            if dv.next(root) is None {
                                assert( dv.addr_supports_lsn(root.unwrap(), dv.boundary_lsn) ); // witness
                                assert( false );
                            }
                        }

                        Self::bottom_properties(dv, dv.next(root), first);
                    }
                }
            }
        }
    }
    
    pub proof fn discard_preserves_pointer_is_upstream(tj: TruncatedJournal, old_first: AU, new_bdy: LSN)
    requires
        Self::pointer_is_upstream(tj.disk_view, tj.freshest_rec, old_first),
        tj.can_discard_to(new_bdy),
    ensures ({
        let discarded_tj = tj.discard_old(new_bdy);
        let old_lsn_au_index = Self::build_lsn_au_index(tj, old_first);
        let new_first = Self::new_first(tj, old_lsn_au_index, new_bdy);
        &&& Self::valid_first_au(discarded_tj.disk_view, new_first)
        &&& Self::pointer_is_upstream(discarded_tj.disk_view, discarded_tj.freshest_rec, new_first)
    }),
    {
        assume(false);  // fixme
    }

    pub proof fn lsn_au_index_domain(tj: TruncatedJournal, first: AU)
    requires
        Self::pointer_is_upstream(tj.disk_view, tj.freshest_rec, first),
    ensures
        Self::build_lsn_au_index(tj, first).dom() =~= Set::new(|lsn: LSN| tj.seq_start() <= lsn < tj.seq_end())
    {
        // From au_walk to page_walk
        Self::build_lsn_au_index_equiv_page_walk(tj.disk_view, tj.freshest_rec, first);
        // From page_walk to Likes::addr_index
        Self::build_lsn_au_index_page_walk_consistency(tj.disk_view, tj.freshest_rec);

        if tj.freshest_rec is Some {
            tj.disk_view.build_lsn_addr_index_domain_valid(tj.freshest_rec);
            reveal(LinkedJournal_v::TruncatedJournal::index_domain_valid);
        }
    }

    pub proof fn build_commutes_over_discard(dv: DiskView, root: Pointer, old_first: AU, new_bdy: LSN)
    requires
        Self::pointer_is_upstream(dv, root, old_first),
        dv.tj_at(root).can_discard_to(new_bdy),
    ensures ({
        let old_lsn_au_index = Self::build_lsn_au_index(dv.tj_at(root), old_first); // super-let, please
        Self::build_lsn_au_index(dv.tj_at(root).discard_old(new_bdy), Self::new_first(dv.tj_at(root), old_lsn_au_index, new_bdy))
            =~= Self::lsn_au_index_discarding_up_to(old_lsn_au_index, new_bdy) 
        }),
    {
        let old_lsn_au_index = Self::build_lsn_au_index(dv.tj_at(root), old_first); // super-let, please
        Self::build_commutes_over_discard_page_walk(dv, root, new_bdy);
        //Self::build_lsn_au_index_equiv_page_walk(dv, root, old_first);
        let discarded_tj = dv.tj_at(root).discard_old(new_bdy);
        let new_first = Self::new_first(dv.tj_at(root), old_lsn_au_index, new_bdy);
        assert( discarded_tj.disk_view.valid_ranking(dv.the_ranking()) );   // trigger witness to acyclic

        Self::build_lsn_au_index_page_walk_consistency(dv, root);
        Self::build_lsn_au_index_page_walk_consistency(discarded_tj.disk_view, discarded_tj.freshest_rec);
        assert( Self::addr_index_consistent_with_au_index(
            discarded_tj.disk_view.build_lsn_addr_index(discarded_tj.freshest_rec),
            Self::build_lsn_au_index_page_walk(discarded_tj.disk_view, discarded_tj.freshest_rec)) );

        Self::discard_preserves_pointer_is_upstream(dv.tj_at(root), old_first, new_bdy);

        // Get the domains nailed down
        Self::lsn_au_index_domain(dv.tj_at(root), old_first);
        Self::lsn_au_index_domain(discarded_tj, new_first);

        // The values should match.
        // Strategy A: work backward, rely on unique lsns. That seems fancy
        // Strategy B: The AUs align with the page walks. The page walks should agree.
        // Sheesh, B should have taken care of the domains, too.
        assume(false);

//         let new_reconstructed = Self::build_lsn_au_index(discarded_tj, new_first);
// 
// //         Self::build_lsn_au_index_equiv_page_walk(discarded_tj.disk_view, discarded_tj.freshest_rec, new_first);
//         let new_delta = Self::lsn_au_index_discarding_up_to(old_lsn_au_index, new_bdy);
// 
//         assert forall |lsn| new_delta.contains_key(lsn) implies new_delta[lsn] == new_reconstructed[lsn] by {
//             let old_lsn_addr_index = dv.tj_at(root).build_lsn_addr_index();
//             dv.build_lsn_addr_index_domain_valid(root);
// //             assert( dv.index_keys_map_to_valid_entries(old_lsn_addr_index) );
//             let new_lsn_addr_index = discarded_tj.build_lsn_addr_index();
//             discarded_tj.disk_view.build_lsn_addr_index_domain_valid(discarded_tj.freshest_rec);
// //             assert( discarded_tj.disk_view.index_keys_map_to_valid_entries(new_lsn_addr_index) );
//             assert( old_lsn_addr_index.contains_key(lsn) );
//             reveal(DiskView::index_keys_map_to_valid_entries);
//             assert( dv.addr_supports_lsn(old_lsn_addr_index[lsn], lsn) );
//             assert( new_lsn_addr_index.contains_key(lsn) );
//             assert( discarded_tj.disk_view.addr_supports_lsn(new_lsn_addr_index[lsn], lsn) );
//             assert( dv.addr_supports_lsn(new_lsn_addr_index[lsn], lsn) );
//             assert( new_lsn_addr_index[lsn] == old_lsn_addr_index[lsn]);
//             assert( new_delta[lsn] == new_lsn_addr_index[lsn].au );
//             assert( old_delta[lsn] == old_lsn_addr_index[lsn].au );
//             left off here in a haze
// 
//             // exploit addr_supports_lsn and lsns_unique?
//         }
        //Self::build_lsn_au_index_equiv_page_walk(discarded_tj.disk_view, discarded_tj.freshest_rec, new_first);
    }

    pub open spec(checked) fn upstream(dv: DiskView, addr: Address) -> bool
    {
        &&& dv.entries.contains_key(addr)
        &&& dv.boundary_lsn < dv.entries[addr].message_seq.seq_end
    }

    // NB talking about dv.next() is painful because we have to reason about interactions
    // with a moving dv.boundary. Maybe easier to break down the reasoning into pointers
    // (which don't change) and layer the boundary reasoning on top.
    pub open spec(checked) fn nonzero_pages_point_backward(dv: DiskView) -> bool
    recommends
        dv.wf(),
    {
        forall |addr: Address| #![auto] ({
            &&& addr.page != 0
            &&& dv.entries.contains_key(addr)
        }) ==> dv.entries[addr].prior_rec == Some(addr.previous())
    }

    // Profiling suggested this quantifier is trigger happy
    #[verifier(opaque)]
    pub closed spec(checked) fn pages_allocated_in_lsn_order(dv: DiskView) -> bool
    recommends
        dv.wf(),
    {
        forall |alo: Address, ahi: Address| #![auto] ({
            &&& alo.au == ahi.au
            &&& alo.page < ahi.page
            &&& dv.entries.contains_key(alo)
            &&& dv.entries.contains_key(ahi)
        }) ==> dv.entries[alo].message_seq.seq_end <= dv.entries[ahi].message_seq.seq_start
    }

    pub open spec(checked) fn internal_au_pages_fully_linked(dv: DiskView) -> bool
    recommends
        dv.wf(),
    {
        &&& Self::nonzero_pages_point_backward(dv)
        &&& Self::pages_allocated_in_lsn_order(dv)
    }

    pub proof fn nonfirst_properties(dv: DiskView, root: Pointer, first: AU)
    requires
        Self::pointer_is_upstream(dv, root, first),
        root.is_Some(),
        root.unwrap().au != first,
    ensures
        forall |ptr: Pointer| #![auto]
            ptr is Some && ptr.unwrap().au==root.unwrap().au && ptr.unwrap().page <= root.unwrap().page
            ==> Self::pointer_is_upstream(dv, ptr, first),
        forall |ptr: Pointer| #![auto]
            ptr is Some && ptr.unwrap().au==root.unwrap().au && 0 < ptr.unwrap().page <= root.unwrap().page
            ==> dv.next(ptr) is Some && dv.next(ptr).unwrap().au == root.unwrap().au
    decreases dv.the_rank_of(root)
    {
        if dv.next(root) is None {
            assert( dv.addr_supports_lsn(root.unwrap(), dv.boundary_lsn) );
            assert( false );
        }

        if root.unwrap().page != 0 {
            Self::nonfirst_properties(dv, dv.next(root), first);
        }
    }

    pub proof fn transitive_ranking(dv: LinkedJournal_v::DiskView, root: Address, later: Address, first: AU)
    requires
        Self::pointer_is_upstream(dv, Some(later), first),
        dv.decodable(Some(root)),
        dv.acyclic(),
        root.au != first,
        root.au == later.au,
        root.page <= later.page,
        Self::internal_au_pages_fully_linked(dv),
    // should be less than <= bc it's enough to prove termination, cause later is already < caller's root
    ensures
        dv.the_rank_of(Some(root)) <= dv.the_rank_of(Some(later)),
    decreases later.page
    {
        if root == later {
            assert( dv.decodable(Some(later)) );
            return; }
        //Self::nonfirst_decodable(dv, Some(later), first);
        let prior = dv.next(Some(later));
//         assert( dv.entries.contains_key(later) );    // todo deleteme
//         assert( dv.entries[later].prior_rec is Some );
//         assert( prior is Some );
//         assert( prior.unwrap().page + 1 == later.page );
        Self::nonfirst_properties(dv, Some(later), first);
        Self::transitive_ranking(dv, root, prior.unwrap(), first);
    }

    pub open spec fn pointer_is_upstream(dv: DiskView, root: Pointer, first: AU) -> bool
    {
        &&& dv.decodable(root)
        &&& dv.acyclic()
        &&& Self::internal_au_pages_fully_linked(dv)
        &&& Self::has_unique_lsns(dv)
        &&& root is Some ==> Self::valid_first_au(dv, first)
        &&& root is Some ==> Self::upstream(dv, root.unwrap())
//        &&& root.is_Some() ==> dv.boundary_lsn < dv.entries[root.unwrap()].message_seq.seq_end
    }

    pub proof fn bottom_properties(dv: DiskView, root: Pointer, first: AU)
    requires
        Self::pointer_is_upstream(dv, root, first),
        root.is_Some(),
        root.unwrap().au != first,
    ensures
        // TODO wish I had a superlet for bottom=first_page(root) here
        dv.next(first_page(root)) is Some,    // else root.au == first
        dv.decodable(dv.next(first_page(root))), // because decodable-ity is recursive
        dv.buildable(dv.next(first_page(root))),

        // a couple uglies I threw in to complete lemma_aus_hold_contiguous_lsns_inner
        Self::pointer_is_upstream(dv, first_page(root), first),
        dv.tj_at(dv.next(first_page(root))).seq_end() <= dv.tj_at(root).seq_end(),
    decreases dv.the_rank_of(root)
    {
        if dv.next(root) is None {
            assert( dv.addr_supports_lsn(root.unwrap(), dv.boundary_lsn) );
            assert( false );
        }

        if root.unwrap().page != 0 {
//             assert( dv.entries.contains_key(first_page(root).unwrap()) );
//             assert( Self::au_page_links_to_prior(dv, root.unwrap()) );
            Self::bottom_properties(dv, dv.next(root), first);
        }
    }

    #[verifier(decreases_by)]
    pub proof fn build_lsn_au_index_au_walk_helper(dv: DiskView, root: Pointer, first: AU)
    {
        match root {
            None => {},
            Some(addr) => {
                if addr.au == first { }
                else {
                    // Nine lines of boilerplate to insert this one line in the right place. :v/
                    let bottom = first_page(root);
                    Self::bottom_properties(dv, root, first);
                    Self::transitive_ranking(dv, bottom.unwrap(), root.unwrap(), first);
                }
            }
        }
    }

    pub open spec/*(checked)*/ fn build_lsn_au_index_au_walk(dv: DiskView, root: Pointer, first: AU) -> Map<LSN, AU>
    recommends
        Self::pointer_is_upstream(dv, root, first),
        dv.acyclic(),
        Self::internal_au_pages_fully_linked(dv),
    decreases dv.the_rank_of(root)
    {
        decreases_when({
            &&& Self::pointer_is_upstream(dv, root, first)
            &&& dv.acyclic()
            &&& Self::internal_au_pages_fully_linked(dv)
        });
        decreases_by(Self::build_lsn_au_index_au_walk_helper);
        match root {
            None => map![],
            Some(addr) => {
                if addr.au == first { Self::build_lsn_au_index_page_walk(dv, root) }
                else {
                    // Jump over all the intermediate pages in the AU; we know how they're laid out already.
                    let bottom = first_page(root);
                    let last_lsn = dv.entries[root.unwrap()].message_seq.seq_end;
                    let first_lsn = dv.entries[bottom.unwrap()].message_seq.seq_start;
                    let update = Self::singleton_index(first_lsn, last_lsn, bottom.unwrap().au);
                    let prior_result = Self::build_lsn_au_index_au_walk(dv, dv.next(bottom), first);
                    prior_result.union_prefer_right(update)
                }
            }
        }
    }

    #[verifier(recommends_by)]
    pub proof fn build_lsn_au_index_helper(tj: TruncatedJournal, first: AU)
    {
        match tj.freshest_rec {
            None => {},
            Some(addr) => {
                if addr.au == first { }
                else {
                    Self::bottom_properties(tj.disk_view, tj.freshest_rec, first);
                    Self::transitive_ranking(tj.disk_view, tj.freshest_rec.unwrap().first_page(), tj.freshest_rec.unwrap(), first);
                }
            }
        }
    }

    pub open spec(checked) fn build_lsn_au_index(tj: TruncatedJournal, first: AU) -> Map<LSN, AU>
    recommends
        Self::pointer_is_upstream(tj.disk_view, tj.freshest_rec, first),
    {
        recommends_by(Self::build_lsn_au_index_helper);
        Self::build_lsn_au_index_au_walk(tj.disk_view, tj.freshest_rec, first)
    }

    pub open spec(checked) fn wf_addrs(dv: DiskView) -> bool
    {
        forall |addr| #[trigger] dv.entries.contains_key(addr) ==> addr.wf()
    }

    pub open spec(checked) fn valid_first_au(dv: DiskView, first: AU) -> bool
    {
        exists |addr: Address| #![auto] addr.au == first && dv.addr_supports_lsn(addr, dv.boundary_lsn)
    }

    pub open spec(checked) fn valid_journal_image(image: JournalImage) -> bool
    {
        &&& Self::wf_addrs(image.tj.disk_view)  // subsumed by decodable?
            &&& Self::pointer_is_upstream(image.tj.disk_view, image.tj.freshest_rec, image.first)
    }

    init!{ initialize(journal: LikesJournal::State, image: JournalImage) {
        require Self::valid_journal_image(image);
        require LikesJournal::State::initialize(journal, image.tj);
        let lsn_au_index = Self::build_lsn_au_index(image.tj, image.first);

        init journal = journal;
        init lsn_au_index = lsn_au_index;
        init first = image.first;
        init mini_allocator = MiniAllocator::empty();
    } }

    //////////////////////////////////////////////////////////////////////////////
    // AllocationJournalRefinement stuff
    //

    pub open spec(checked) fn addr_index_consistent_with_au_index(lsn_addr_index: Map<LSN, Address>, lsn_au_index: Map<LSN, AU>) -> bool
    {
        &&& lsn_addr_index.dom() =~= lsn_au_index.dom() // NB hiding a proof strategy behind that tilde. Ugh.
        &&& forall |lsn| #[trigger] lsn_addr_index.contains_key(lsn) ==> lsn_addr_index[lsn].au == lsn_au_index[lsn]
    }

    pub open spec(checked) fn journal_pages_not_free(addrs: Set<Address>, allocator: MiniAllocator) -> bool
    {
        forall |addr| #[trigger] addrs.contains(addr) ==> addr.wf() && !allocator.can_allocate(addr)
    }

    pub open spec(checked) fn mini_allocator_follows_freshest_rec(freshest_rec: Pointer, allocator: MiniAllocator) -> bool
    {
        allocator.curr.is_Some() ==> {
            &&& freshest_rec.is_Some()
            &&& freshest_rec.unwrap().au == allocator.curr.unwrap()
        }
    }

    pub open spec(checked) fn get_tj(self) -> TruncatedJournal
    {
        self.journal.journal.truncated_journal
    }

    pub open spec(checked) fn contiguous_lsns(lsn_au_index: Map<LSN, AU>, lsn1: LSN, lsn2: LSN, lsn3: LSN) -> bool
    {
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

    pub open spec(checked) fn aus_hold_contiguous_lsns(lsn_au_index: Map<LSN, AU>) -> bool
    {
        forall |lsn1, lsn2, lsn3| Self::contiguous_lsns(lsn_au_index, lsn1, lsn2, lsn3)
    }

    pub closed spec(checked) fn index_honors_rank(dv: DiskView, root: Pointer, first: AU, au_index: Map<LSN, AU>) -> bool
    recommends
        dv.decodable(root),
        dv.acyclic(),
        Self::internal_au_pages_fully_linked(dv),
    {
        forall |lsn, addr: Address| #![auto] au_index.contains_key(lsn) && addr.au == au_index[lsn]
             && dv.addr_supports_lsn(addr, lsn)
            ==> dv.the_rank_of(Some(addr)) <= dv.the_rank_of(root)
    }
    
    pub open spec fn au_domain_valid(dv: DiskView, root: Pointer, lsn_au_index: Map<LSN, AU>) -> bool
    {
        forall |lsn| lsn_au_index.contains_key(lsn) <==> (dv.tj_at(root).seq_start() <= lsn < dv.tj_at(root).seq_end())
    }

    pub proof fn nonfirst_pages(dv: DiskView, addr: Address, first: AU)
    requires
        Self::pointer_is_upstream(dv, Some(addr), first),
        addr.au != first,
    ensures
        dv.boundary_lsn < dv.entries[addr].message_seq.seq_start,
    {
        // assert( dv.boundary_lsn < dv.entries[addr].message_seq.seq_end );  // documentation; by pointer_is_upstream
        if dv.entries[addr].message_seq.seq_start <= dv.boundary_lsn {
            assert( dv.addr_supports_lsn(addr, dv.boundary_lsn) );  // trigger
//            assert( Self::valid_first_au(dv, addr.au) );  // documentation
//            assert( Self::valid_first_au(dv, first) );    // documentation
            assert( false );    // lsns unique
        }
    }
        
    pub proof fn build_lsn_addr_index_returns_upstream_pages(dv: DiskView, root: Pointer, first: AU)
    requires
        Self::has_unique_lsns(dv),
        Self::internal_au_pages_fully_linked(dv),
        dv.buildable(root),
        Self::valid_first_au(dv, first),
    ensures ({
        let lsn_addr_index = dv.build_lsn_addr_index(root);
        forall |lsn| #![auto] lsn_addr_index.contains_key(lsn) && lsn_addr_index[lsn].au != first
            ==> Self::pointer_is_upstream(dv, Some(lsn_addr_index[lsn]), first)
        }),
    decreases dv.the_rank_of(root) when dv.buildable(root)
    {
        let lsn_addr_index = dv.build_lsn_addr_index(root);
        if root is Some {
            Self::build_lsn_addr_index_returns_upstream_pages(dv, dv.next(root), first);

            // ugly trigger block. want to just trigger on alpha-substituted definition of build_lsn_addr_index
            let curr_msgs = dv.entries[root.unwrap()].message_seq;
            let start_lsn = math::max(dv.boundary_lsn as int, curr_msgs.seq_start as int) as nat;
            let update = LikesJournal_v::singleton_index(start_lsn, curr_msgs.seq_end, root.unwrap());
            assert( lsn_addr_index == dv.build_lsn_addr_index(dv.next(root)).union_prefer_right(update) );

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

    pub proof fn upstream_pages(dv: DiskView, earlier: Address, later: Address, first: AU)
    requires
        Self::pointer_is_upstream(dv, Some(later), first),
        later.au != first,
        earlier.au == later.au,
        earlier.page <= later.page,
    ensures
        Self::pointer_is_upstream(dv, Some(earlier), first),
    decreases later.page - earlier.page
    {
        if earlier.page < later.page {
            let prior = later.previous();
            
            Self::nonfirst_pages(dv, later, first);
            assert(Self::upstream(dv, prior));
            assert(Self::pointer_is_upstream(dv, Some(prior), first));
            Self::upstream_pages(dv, earlier, prior, first);
        }
    }

    pub proof fn lemma_next_au_doesnt_intersect(dv: DiskView, root: Pointer, first: AU, prior_result: Map<LSN, AU>)
    requires
        Self::pointer_is_upstream(dv, root, first),
        root.is_Some(),
        root.unwrap().au != first,
        prior_result == Self::build_lsn_au_index_au_walk(dv, dv.next(first_page(root)), first),
    ensures
        forall |lsn| #![auto] prior_result.contains_key(lsn) ==> prior_result[lsn] != root.unwrap().au,
    {
        let bottom = first_page(root);
        let prior_addr_index = dv.tj_at(dv.next(bottom)).build_lsn_addr_index();

        Self::bottom_properties(dv, root, first);
        dv.build_lsn_addr_all_decodable(dv.next(bottom));

        Self::build_lsn_au_index_au_walk_consistency(dv, dv.next(bottom), first);
        Self::build_lsn_addr_index_returns_upstream_pages(dv, dv.next(bottom), first);

        assert forall |lsn| prior_result.contains_key(lsn)
            implies #[trigger] prior_result[lsn] != root.unwrap().au by {
            let addr = prior_addr_index[lsn];
            if addr.au == root.unwrap().au {
                if addr.au != first {
                    let addr0 = Address{au: addr.au, page: 0};
                    let addrp = dv.next(bottom).unwrap();

                    Self::upstream_pages(dv, addr0, addr, first);
                    Self::transitive_ranking(dv, addr0, addr, first);

                    let prior_last = (dv.entries[addrp].message_seq.seq_end - 1) as nat;
                    assert( lsn <= prior_last ) by {
                        reveal(TruncatedJournal::index_domain_valid);
                        dv.build_lsn_addr_index_domain_valid(dv.next(bottom));
                    }

                    dv.tj_at(dv.next(bottom)).build_lsn_addr_honors_rank(prior_addr_index);
                    assert( prior_addr_index.contains_key(prior_last) );    // trigger build_lsn_addr_honors_rank
                    assert( false );
                }
                assert( addr.au == first );
                assert( false );
            }
        }
    }

    // TODO(jonh): if we had spec ensures, this would be a nice conclusion to build_lsn_au_index_page_walk
    pub proof fn au_index_page_supports_lsn(dv: DiskView, root: Pointer, lsn: LSN)
    requires
        dv.decodable(root),
        dv.acyclic(),
        Self::build_lsn_au_index_page_walk(dv, root).contains_key(lsn),
    ensures
        exists |addr| #![auto] dv.addr_supports_lsn(addr, lsn) && addr.au == Self::build_lsn_au_index_page_walk(dv, root)[lsn]
    decreases dv.the_rank_of(root)
    {
        if root is Some {
            let curr_msgs = dv.entries[root.unwrap()].message_seq;
            let update = Self::singleton_index(
                math::max(dv.boundary_lsn as int, curr_msgs.seq_start as int) as nat, curr_msgs.seq_end, root.unwrap().au);
            if update.contains_key(lsn) {
                assert( dv.addr_supports_lsn(root.unwrap(), lsn) ); // witness to ensures exists trigger
            } else {
                Self::au_index_page_supports_lsn(dv, dv.next(root), lsn);
            }
        }
    }

    pub proof fn first_contains_boundary(dv: DiskView, root: Pointer, first: AU)
    requires
        dv.decodable(root),
        dv.acyclic(),
        Self::valid_first_au(dv, first),
        Self::has_unique_lsns(dv),
        root is Some,
        Self::upstream(dv, root.unwrap()),
    ensures
        Self::build_lsn_au_index_page_walk(dv, root)[dv.boundary_lsn] == first,
    {
        let addr = choose |addr: Address| #![auto] addr.au == first && dv.addr_supports_lsn(addr, dv.boundary_lsn);
        Self::build_lsn_au_index_page_walk_domain(dv, root);
        Self::au_index_page_supports_lsn(dv, root, dv.boundary_lsn);
    }

    pub proof fn lemma_aus_hold_contiguous_lsns_first_page(dv: DiskView, root: Pointer, first: AU)
    requires
        Self::pointer_is_upstream(dv, root, first),
        Self::has_unique_lsns(dv),
        root is Some,
        root.unwrap().au == first,
    ensures ({
        // TODO sure want that super-let here, for lsn_au_index.
        let lsn_au_index = Self::build_lsn_au_index_page_walk(dv, root);
        &&& forall |lsn| #![auto] lsn_au_index.contains_key(lsn) ==> lsn_au_index[lsn] == root.unwrap().au
        &&& Self::au_domain_valid(dv, root, lsn_au_index)
        &&& Self::aus_hold_contiguous_lsns(lsn_au_index)
        })
    decreases dv.the_rank_of(root)
    {
        let lsn_au_index = Self::build_lsn_au_index_page_walk(dv, root);

        if root is None {
        } else if dv.next(root) is None {
            assert( Self::build_lsn_au_index_page_walk(dv, dv.next(root)) =~= Map::empty() ); // trigger
        } else if root.unwrap().page == 0 {
            // If there's a valid pointer exiting here, and we're at page 0, then we're not the
            // first au, are we?
            //assert( dv.addr_supports_lsn(lsn_au_index[dv.boundary_lsn], dv.boundary_lsn) );
            assert( exists |addr: Address| #![auto] addr.au == first && dv.addr_supports_lsn(addr, dv.boundary_lsn) );
            let first_page = choose |addr: Address| #![auto] addr.au == first && dv.addr_supports_lsn(addr, dv.boundary_lsn);
            assert( dv.addr_supports_lsn(first_page, dv.boundary_lsn) );
            Self::first_contains_boundary(dv, root, first);
            assert( lsn_au_index[dv.boundary_lsn] == first );
            assert( dv.entries[root.unwrap()].message_seq.seq_end <= dv.entries[first_page].message_seq.seq_start ) by {
                reveal(AllocationJournal::State::pages_allocated_in_lsn_order);
            }
            assert( false );
        } else {
            Self::lemma_aus_hold_contiguous_lsns_first_page(dv, dv.next(root), first);  // recurse!
        }
    }

    pub proof fn lemma_aus_hold_contiguous_lsns_inner(dv: DiskView, root: Pointer, first: AU)
    requires
        Self::pointer_is_upstream(dv, root, first),
    ensures
        Self::au_domain_valid(dv, root, Self::build_lsn_au_index_au_walk(dv, root, first)),
        Self::aus_hold_contiguous_lsns(Self::build_lsn_au_index_au_walk(dv, root, first)),
    decreases dv.the_rank_of(root)
    {
        let lsn_au_index = Self::build_lsn_au_index_au_walk(dv, root, first);
        match root {
            None => { },
            Some(addr) => {
                if addr.au == first {
                    Self::lemma_aus_hold_contiguous_lsns_first_page(dv, root, first);
                } else {
                    let bottom = first_page(root);
//                     let last_lsn = dv.entries[root.unwrap()].message_seq.seq_end;
                    let first_lsn = dv.entries[bottom.unwrap()].message_seq.seq_start;
//                     let update = Self::singleton_index(first_lsn, last_lsn, bottom.unwrap().au);
                    let prior_result = Self::build_lsn_au_index_au_walk(dv, dv.next(bottom), first);

                    Self::bottom_properties(dv, root, first);
                    Self::transitive_ranking(dv, bottom.unwrap(), root.unwrap(), first);
                    Self::lemma_aus_hold_contiguous_lsns_inner(dv, dv.next(bottom), first);
                    
                    assert forall |lsn1, lsn2, lsn3| Self::contiguous_lsns(lsn_au_index, lsn1, lsn2, lsn3) by {
                        if ({
                            &&& lsn1 <= lsn2 <= lsn3
                            &&& lsn_au_index.contains_key(lsn1)
                            &&& lsn_au_index.contains_key(lsn3)
                            &&& lsn_au_index[lsn1] == lsn_au_index[lsn3]
                        }) {
                            if lsn1 < first_lsn {   // recursive case
                                if !prior_result.contains_key(lsn3) {   // lsn3 is in bottom.au, tho? Nope.
                                    Self::lemma_next_au_doesnt_intersect(dv, root, first, prior_result);
                                    assert( false );
                                }
                                assert( Self::contiguous_lsns(prior_result, lsn1, lsn2, lsn3) );    // trigger
                            }
                        }
                    }
                }
            }
        }
    }

    pub proof fn lemma_aus_hold_contiguous_lsns(image: JournalImage)
    requires
        Self::valid_journal_image(image),
    ensures
        Self::aus_hold_contiguous_lsns(Self::build_lsn_au_index(image.tj, image.first)),
    {
        Self::lemma_aus_hold_contiguous_lsns_inner(image.tj.disk_view, image.tj.freshest_rec, image.first)
    }

    pub open spec fn has_unique_lsns(dv: DiskView) -> bool
    {
        forall |lsn, addr1, addr2|
            dv.addr_supports_lsn(addr1, lsn) && dv.addr_supports_lsn(addr2, lsn)
            ==> addr1 == addr2
    }

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.wf()
        // The following is opaqued in AllocationJournalRefinement.
        // (Note: that suggests this is a good place to think about
        // building an isolation cell!)
        &&& LikesJournal::State::inv(self.journal)
        &&& self.lsn_au_index == Self::build_lsn_au_index(self.get_tj(), self.first)
        &&& Self::addr_index_consistent_with_au_index(self.journal.lsn_addr_index, self.lsn_au_index)   // I think this can derive from prev
        &&& Self::journal_pages_not_free(self.journal.lsn_addr_index.values(), self.mini_allocator)
        &&& Self::mini_allocator_follows_freshest_rec(self.get_tj().freshest_rec, self.mini_allocator)
        &&& Self::aus_hold_contiguous_lsns(self.lsn_au_index)
        &&& (self.get_tj().freshest_rec.is_Some()
            ==> Self::valid_first_au(self.get_tj().disk_view, self.first))
        &&& (self.get_tj().freshest_rec.is_Some()
            ==> Self::internal_au_pages_fully_linked(self.get_tj().disk_view))

        // TODO: miniAllocator can remove means that it's not in lsnauindex.values
    }

    #[inductive(freeze_for_commit)]
    fn freeze_for_commit_inductive(pre: Self, post: Self, lbl: Label) {
        reveal(LinkedJournal::State::next);
        reveal(LinkedJournal::State::next_by );
    }

    #[inductive(read_for_recovery)]
    fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label) { }
       
    #[inductive(query_end_lsn)]
    fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label) { }
       
    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(internal_mini_allocator_fill)]
    fn internal_mini_allocator_fill_inductive(pre: Self, post: Self, lbl: Label) {
        // hole in dafny proof
        assume(false);  // Dafny had several holes left to fill
    }

    #[inductive(internal_mini_allocator_prune)]
    fn internal_mini_allocator_prune_inductive(pre: Self, post: Self, lbl: Label) {
        // dafny had assume false, yet we don't need a proof here!?
    }

    pub proof fn invoke_submodule_inv(pre: Self, post: Self)
    requires
        Self::inv(pre),
    ensures
        post.journal.inv(),
    {
        assume(false);  // help, travis -- need access to this result
    }

    #[verifier::spinoff_prover]  // flaky proof
    pub proof fn discard_old_helper4(pre: Self, post: Self, lbl: Label, post_journal: LikesJournal::State, xaddr: Address, zaddr: Address)
    requires
        Self::inv(pre),
        Self::discard_old(pre, post, lbl, post_journal),
        post.get_tj().disk_view.entries.contains_key(zaddr),
        post.get_tj().seq_start() < post.get_tj().disk_view.entries[zaddr].message_seq.seq_start,
        post.get_tj().freshest_rec.is_Some(),
        zaddr.au != pre.first,
        zaddr.au != post.first,
        xaddr.au == zaddr.au,
        0 <= xaddr.page < zaddr.page,
    ensures
        post.get_tj().disk_view.entries.contains_key(xaddr),
    decreases zaddr.page - xaddr.page
    {
        let pre_dv = pre.get_tj().disk_view;
        let post_dv = post.get_tj().disk_view;
        Self::invoke_submodule_inv(pre, post);
        // Note to Pranav: here's a good example of a deep layer violation!
        let zpaged = post_dv.iptr(Some(zaddr));    // relies on LinkedJournal_Refinement
        assert( zpaged.is_Some() );
        let zpaged = zpaged.unwrap();
        let zlsn = post_dv.entries[zaddr].message_seq.seq_start;
        let ylsn = (zlsn - 1) as nat;
//         assert( post_dv.entries[zaddr].message_seq == zpaged.message_seq );
        assert( post_dv.entries[zaddr].message_seq.seq_start != 0 );
        assert( ylsn < post_dv.entries[zaddr].message_seq.seq_start );
        assert( post.journal.lsn_addr_index.contains_key(zlsn) && post.journal.lsn_addr_index[zlsn]==zaddr ) by {
            assert( post_dv.addr_supports_lsn(zaddr, zlsn) );
            //assert( post_dv.entries[zaddr].message_seq.contains(zlsn) );
        }
        assert( post.journal.lsn_addr_index.contains_key(zlsn) );
        assert( post.get_tj().seq_start() <= zlsn < post.get_tj().seq_end() ) by {
            reveal(TruncatedJournal::index_domain_valid);
        }

        assert( post.journal.lsn_addr_index.contains_key(zlsn) );
        assert( post_dv.entries[zaddr].message_seq.seq_start < post.get_tj().seq_end() ) by {
        }
        assert( ylsn < post.get_tj().seq_end() );
        if ylsn < post.get_tj().seq_start() {
            assert( zlsn == post.get_tj().seq_start() );
            assert( false );
        }
        assert( post.get_tj().seq_start() <= ylsn );
        assert( post.get_tj().seq_start() <= ylsn ) by {    // all redundant with prev line
            if ylsn < post.get_tj().seq_start() {
                assert( post.lsn_au_index.contains_key(post_dv.boundary_lsn) );
                assert( post.lsn_au_index[post_dv.boundary_lsn] == zaddr.au );
                assert( false );
            }
            // argument about first
        }

        let yaddr = Address{au: zaddr.au, page: (zaddr.page - 1) as nat};
        let y0lsn = post_dv.entries[yaddr].message_seq.seq_start;

        assert( post.get_tj().seq_start() < y0lsn ) by {
            if y0lsn <= post.get_tj().seq_start() {
                assert( y0lsn <= post_dv.boundary_lsn );
                assert( post_dv.boundary_lsn <= ylsn );

                // TODO(chris): if I replace the two lines above with this single assert, the proof
                // falls apart. That's ... extremely counterintuitive.
                // In fact, if I ADD this line, keeping those above, the proof falls apart!! That's
                // crazy.
                //assert( y0lsn <= post_dv.boundary_lsn <= ylsn );
                // ...maybe it's just flakiness. This proof seems EXTREMELY brittle.

                assert( Self::contiguous_lsns(post.lsn_au_index, y0lsn, post_dv.boundary_lsn, ylsn) );
                assert( y0lsn <= post_dv.boundary_lsn <= ylsn );

                assume(false);  // THIS PROOF IS HELLA FLAKY; address later
                assert( post_dv.entries[yaddr].message_seq.contains(y0lsn) );   //trigger

                assert( post.journal.lsn_addr_index.contains_key(y0lsn) );
                assert( post.journal.lsn_addr_index.dom().contains(y0lsn) );
                assert( post.lsn_au_index.contains_key(y0lsn) );
                assert( post.lsn_au_index.contains_key(ylsn) );
                assert( post.lsn_au_index[y0lsn] == post.lsn_au_index[ylsn] );
                assert( post.lsn_au_index.contains_key(post_dv.boundary_lsn) );
                assert( post.lsn_au_index[post_dv.boundary_lsn] == zaddr.au );
                assert( false );
            }
        }

        //assert( Self::au_page_links_to_prior(pre_dv, Address{au: zaddr.au, page: zaddr.page}) );
        
//         assert( Self::au_page_links_to_prior(pre_dv, zaddr) ); // trigger

        if xaddr != yaddr {
            assert( post.get_tj().seq_start() < y0lsn );
            Self::discard_old_helper4(pre, post, lbl, post_journal, xaddr, yaddr);
        }
    }

    #[inductive(discard_old)]
    fn discard_old_inductive(pre: Self, post: Self, lbl: Label, post_journal: LikesJournal::State) {
        reveal( LikesJournal::State::next );
        reveal( LikesJournal::State::next_by );
        //reveal( LinkedJournal_v::LinkedJournal::State::next );
        reveal( LinkedJournal::State::next_by );

        Self::invoke_submodule_inv(pre, post);
        assert( post.wf() );
        assert( Self::addr_index_consistent_with_au_index(post.journal.lsn_addr_index, post.lsn_au_index) );
        assert( Self::journal_pages_not_free(post.journal.lsn_addr_index.values(), post.mini_allocator) );
        if post.get_tj().freshest_rec.is_Some() && post.get_tj().freshest_rec.is_None() {
            assert( pre.journal.lsn_addr_index.values().contains(pre.get_tj().freshest_rec.unwrap()) );
            assert( post.journal.lsn_addr_index =~~= map![] );
        }
        assert( Self::mini_allocator_follows_freshest_rec(post.get_tj().freshest_rec, post.mini_allocator) );
        assert forall |lsn1,lsn2,lsn3| Self::contiguous_lsns(post.lsn_au_index, lsn1, lsn2, lsn3) by
        {
            if {
                &&& lsn1 <= lsn2 <= lsn3
                &&& post.lsn_au_index.contains_key(lsn1)
                &&& post.lsn_au_index.contains_key(lsn3)
                &&& post.lsn_au_index[lsn1] == post.lsn_au_index[lsn3]
            } {
                assert( Self::contiguous_lsns(pre.lsn_au_index, lsn1, lsn2, lsn3) );
            }
            assert( Self::contiguous_lsns(post.lsn_au_index, lsn1, lsn2, lsn3) );
        }

        let pre_dv = pre.get_tj().disk_view;
        let post_dv = post.get_tj().disk_view;

        if post.get_tj().freshest_rec.is_Some() {
            assert( Self::valid_first_au(post_dv, post.first) ) by {
                reveal(TruncatedJournal::index_domain_valid);
                assert( post.journal.lsn_addr_index.contains_key(post_dv.boundary_lsn) );    // trigger index_domain_valid
                // this is going to be the `first` addr
                let bdy_addr = post.journal.lsn_addr_index[post_dv.boundary_lsn];
                assert( post_dv.addr_supports_lsn( bdy_addr, post_dv.boundary_lsn) );  // trigger valid_first_au
            }
//             let start_lsn = lbl.get_DiscardOld_start_lsn();
            assert( Self::internal_au_pages_fully_linked(post.get_tj().disk_view) ) by {
                reveal(AllocationJournal::State::pages_allocated_in_lsn_order);
            }
        }

        assume( false );    // how did this proof fall apart? I thought I'd gotten it done.
        Self::build_commutes_over_discard(pre_dv, post.get_tj().freshest_rec, pre.first, post_dv.boundary_lsn);
        assert( post.inv() );
    }

    // TODO(jonh): this lemma should just be an ensures on build_lsn_au_index_page_walk.
    pub proof fn build_lsn_au_index_page_walk_consistency(dv: DiskView, root: Pointer)
    requires
        dv.decodable(root),
        dv.acyclic(),
    ensures
        Self::addr_index_consistent_with_au_index(
            dv.build_lsn_addr_index(root),
            Self::build_lsn_au_index_page_walk(dv, root)),
    decreases dv.the_rank_of(root)
    {
        if root.is_Some() {
            Self::build_lsn_au_index_page_walk_consistency(dv, dv.next(root));
        }
    }

    pub proof fn build_lsn_au_index_au_walk_consistency(dv: DiskView, root: Pointer, first: AU)
    requires
        Self::pointer_is_upstream(dv, root, first),
    ensures
        Self::addr_index_consistent_with_au_index(
            dv.build_lsn_addr_index(root),
            Self::build_lsn_au_index_au_walk(dv, root, first)),
    decreases dv.the_rank_of(root)
    {
        Self::build_lsn_au_index_equiv_page_walk(dv, root, first);
        Self::build_lsn_au_index_page_walk_consistency(dv, root);
    }

    #[inductive(internal_journal_marshal)]
    fn internal_journal_marshal_inductive(pre: Self, post: Self, lbl: Label, cut: LSN, addr: Address, post_linked_journal: LinkedJournal::State) {
        Self::invoke_submodule_inv(pre, post);
        let discard_msgs = pre.journal.journal.unmarshalled_tail.discard_recent(cut);
        assert( LikesJournal_v::lsn_disjoint(pre.lsn_au_index.dom(), discard_msgs) ) by {
            reveal(TruncatedJournal::index_domain_valid);
        }

        let msgs = pre.journal.journal.unmarshalled_tail.discard_recent(cut);
        let pre_dv = pre.get_tj().disk_view;
        let pre_root = pre.get_tj().freshest_rec;
        let post_dv = post.get_tj().disk_view;
        let post_root = post.get_tj().freshest_rec;

        assert( pre.lsn_au_index == Self::build_lsn_au_index(pre.get_tj(), pre.first) );
        if pre_root is Some {
            Self::build_lsn_au_index_equiv_page_walk(pre_dv, pre_root, pre.first);
            assert( pre.lsn_au_index == Self::build_lsn_au_index_page_walk(pre_dv, pre_root) );
        } else {
            assert( Self::build_lsn_au_index(pre.get_tj(), pre.first) =~= Map::empty() );
            assert( Self::build_lsn_au_index_page_walk(pre_dv, pre_root) =~= Map::empty() );
            assert( pre.lsn_au_index == Self::build_lsn_au_index_page_walk(pre_dv, pre_root) );
        }

        let curr_msgs = post_dv.entries[post_root.unwrap()].message_seq;
        let update = Self::singleton_index(
            math::max(post_dv.boundary_lsn as int, curr_msgs.seq_start as int) as nat, curr_msgs.seq_end, post_root.unwrap().au);
        
        assert( post_dv.next(post_root) == pre_root );
        Self::build_lsn_au_index_page_walk_sub_disk(pre_dv, post_dv, pre_root);
        assert( Self::build_lsn_au_index_page_walk(post_dv, pre_root)
                == Self::build_lsn_au_index_page_walk(pre_dv, pre_root) );
        assert( Self::build_lsn_au_index_page_walk(post_dv, post_root) ==
            Self::build_lsn_au_index_page_walk(post_dv, pre_root).union_prefer_right(update) );
        let au_update = Self::singleton_index(msgs.seq_start, msgs.seq_end, addr.au);
        assert( au_update == update );
                
        assert( post.lsn_au_index == Self::build_lsn_au_index_page_walk(post_dv, post_root) );
        Self::build_commutes_over_append_record(pre_dv, pre_root, msgs, addr);
        assume(false);

        assert( Self::pages_allocated_in_lsn_order(post_dv) ) by {
            //reveal(State::pages_allocated_in_lsn_order);
            assume( false );

            let dv = post_dv;
            assert forall |alo: Address, ahi: Address| #![auto] ({
                &&& alo.au == ahi.au
                &&& alo.page < ahi.page
                &&& #[trigger] dv.entries.contains_key(alo)
                &&& #[trigger] dv.entries.contains_key(ahi)
            }) implies
                dv.entries[alo].message_seq.seq_end <= dv.entries[ahi].message_seq.seq_start
            by {
                if ahi.au != addr.au || ahi.page < addr.page {
                    assert( dv.entries[alo].message_seq.seq_end <= dv.entries[ahi].message_seq.seq_start );
                } else {
                    assert( ahi == addr );
                    if pre.mini_allocator.curr is None {
                        assert( ahi.page == 0 );
                        assert( dv.entries[alo].message_seq.seq_end <= dv.entries[ahi].message_seq.seq_start );
                    } else {
                        assert( addr == pre_root.unwrap().next() );
                        assert( dv.entries[alo].message_seq.seq_end <= dv.entries[ahi].message_seq.seq_start );
                    }
                }
            }
        }
        if post_root is Some {
            assert( Self::internal_au_pages_fully_linked(post_dv) );
            assert( Self::valid_first_au(post_dv, post.first) );
        }
        Self::build_lsn_au_index_equiv_page_walk(post_dv, post_root, post.first);
        assert( post.lsn_au_index == Self::build_lsn_au_index(post.get_tj(), post.first) );
        assert( Self::pointer_is_upstream(post.get_tj().disk_view, post_root, post.first) );
        Self::build_lsn_au_index_au_walk_consistency(post.get_tj().disk_view, post_root, post.first);
        assert( Self::addr_index_consistent_with_au_index(post.journal.lsn_addr_index, post.lsn_au_index) );

        assert( post.journal.wf() );
        assert( post.mini_allocator.wf() );
        
        assert( post.wf() );
//         assert( LikesJournal_v::LikesJournal::State::inv(post.journal) );
//         assert( post.lsn_au_index == Self::build_lsn_au_index(post.get_tj(), post.first) );
//         assert( Self::addr_index_consistent_with_au_index(post.journal.lsn_addr_index, post.lsn_au_index) );
        
//         assert( Self::journal_pages_not_free(post.journal.lsn_addr_index.values(), post.mini_allocator) );
//         assert( Self::mini_allocator_follows_freshest_rec(post.get_tj().freshest_rec, post.mini_allocator) );
        assert( Self::aus_hold_contiguous_lsns(post.lsn_au_index) );
//         assert( (post.get_tj().freshest_rec.is_Some()
//             ==> Self::valid_first_au(post.get_tj().disk_view, post.first)) );
//         assert( (post.get_tj().freshest_rec.is_Some()
//             ==> Self::internal_au_pages_fully_linked(post.get_tj().disk_view)) );
        
        assert( Self::inv(post) );
    }

    #[inductive(internal_journal_no_op)]
    fn internal_journal_no_op_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, journal: LikesJournal::State, image: JournalImage) {
        //assert( post.journal.lsn_au_index = Linked::build_lsn_au_index(image.tj, image.first);
        assume( LikesJournal::State::inv(post.journal) );   // TODO(travis): help!

        let TruncatedJournal{disk_view: dv, freshest_rec: root} = image.tj;
        Self::build_lsn_au_index_au_walk_consistency(dv, root, image.first);
        Self::lemma_aus_hold_contiguous_lsns(image);
    }

    // lemmas used by other refinements
    pub proof fn discard_old_accessible_aus(pre: Self, post: Self, lbl: Label)
    requires
        Self::next(pre, post, lbl),
        lbl.is_DiscardOld(),
    ensures
        post.accessible_aus() == pre.accessible_aus() - lbl.get_DiscardOld_deallocs(),
    {
        assume(false);  // left off
    }

} } // state_machine
} // verus
