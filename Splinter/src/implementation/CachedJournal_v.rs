// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
use vstd::prelude::*;
use vstd::math::*;

//use vstd::prelude_macros::*;
use verus_state_machines_macros::state_machine;

use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::disk::GenericDisk_v::{Address, Pointer};
use crate::journal::LinkedJournal_v::{DiskView, JournalRecord};
use crate::allocation_layer::LikesJournal_v::*;

// this is a version of the journal where
// content does not live in the journal disk view but accessed through the cache
// to take just this we want to have an equivalent of crop but with lsnaddrindex

verus!{

pub open spec fn addr_to_lsns(lsn_addr_index: LsnAddrIndex, addr: Address, bdy: LSN) -> Set<LSN>
{
    Set::new(|lsn| bdy <= lsn && lsn_addr_index.contains_key(lsn) && lsn_addr_index[lsn] == addr)
}

// to sorted seq, what do we need this for?
pub open spec fn min_lsn(lsns: Set<LSN>) -> LSN
    recommends !lsns.is_empty()
    decreases lsns.len() 
{
    if !lsns.finite() {
        arbitrary()
    } else {
        let e = lsns.choose();
        if lsns.remove(e).is_empty() { e } 
        else { min(e as int, min_lsn(lsns.remove(e)) as int) as nat }
    }
}

pub proof fn min_lsn_ensures(lsns: Set<LSN>)
    requires !lsns.is_empty(), lsns.finite()
    ensures 
        lsns.contains(min_lsn(lsns)),
        forall |lsn| #[trigger] lsns.contains(lsn) ==> min_lsn(lsns) <= lsn
    decreases lsns.len()
{
    let e = lsns.choose();
    if !lsns.remove(e).is_empty() {
        min_lsn_ensures(lsns.remove(e));
    }
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

pub open spec fn lsn_is_largest_for_its_addr(
    lsn_addr_index: LsnAddrIndex,
    lsn: LSN,
) -> bool
    recommends lsn_addr_index.contains_key(lsn)
{
    forall |other_lsn: LSN| #![auto]
        lsn_addr_index.contains_key(other_lsn)
            && lsn_addr_index[other_lsn] == lsn_addr_index[lsn]
        ==> other_lsn <= lsn
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
    reveal(build_lsn_addr_index_from_reads_next_ptr);
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

        reveal(build_lsn_addr_index_from_reads);
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
        reveal(build_lsn_addr_index_from_reads);
        let reads2 = reads.insert(ptr2.unwrap(), ptr2_data);
        let start2 = max(boundary_lsn as int, ptr2_data.message_seq.seq_start as int) as nat;
        let end2 = ptr2_data.message_seq.seq_end;
        assert(build_lsn_addr_index_from_reads(reads, boundary_lsn, root) == Map::<LSN, Address>::empty());
        assert(build_lsn_addr_index_from_reads(reads2, boundary_lsn, root)
            == build_lsn_addr_index_from_reads(reads2, boundary_lsn, ptr2_data.cropped_prior(boundary_lsn))
                .union_prefer_right(singleton_index(start2, end2, ptr2.unwrap())));
        // ptr2_data.cropped_prior not in reads, so the sub-index is empty
        reveal(build_lsn_addr_index_from_reads);
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

    reveal(build_lsn_addr_index_from_reads);
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
    reveal(build_lsn_addr_index_from_reads);
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

pub struct JournalSnapshot {
    pub boundary_lsn: LSN, 
    pub freshest_rec: Pointer, // lsn 
}

pub struct JournalStatus {
    pub unmarshalled_tail: MsgHistory, // in memory journal
    pub lsn_addr_index: LsnAddrIndex,
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
        LoadIndex{reads: Map<Address, JournalRecord>},
        ReadForRecovery{messages: MsgHistory, reads: Map<Address, JournalRecord>},
        FreezeForCommit{frozen: JournalSnapshot, frozen_seq_end: LSN},
        JournalFlush{flushed_domain: Set<Address>},
        QueryEndLsn{end_lsn: LSN},
        Put{messages: MsgHistory},
        DiscardOld{start_lsn: LSN, require_end: LSN, discard_addrs: Set<Address>},
        JournalMarshal{writes: Map<Address, JournalRecord>},
        Internal{},
    }

    // NOTE: we use depth in the following transitions to ensure we only perform operations
    // on page aligned LSNs, using depth require caller to page in all the relevant pages 
    // which seems fine for recovery but not best when we are under memory pressure, 
    // another option is to rely on the LsnAddrIndex 

    transition!{ read_for_recovery(lbl: Label, depth: nat) {
        require pre.status is Some;
        require let Label::ReadForRecovery{messages, reads} = lbl;

        // the depth issue feels like something we should maintain 
        // read for recovery should require ranges and not depth
        require pre.can_crop_index(pre.snapshot.freshest_rec, depth);

        let ptr = pre.pointer_after_crop_index(pre.snapshot.freshest_rec, depth);
        require ptr is Some && reads.contains_key(ptr.unwrap());
        require messages == reads[ptr.unwrap()].message_seq.maybe_discard_old(pre.snapshot.boundary_lsn);
    }}

    transition!{ freeze_for_commit(lbl: Label, depth: nat) {
        require pre.status is Some;
        require let Label::FreezeForCommit{frozen, frozen_seq_end} = lbl;

        require pre.seq_start() <= frozen.boundary_lsn <= frozen_seq_end;
        require pre.can_crop_index(pre.snapshot.freshest_rec, depth);

        let ptr = pre.pointer_after_crop_index(pre.snapshot.freshest_rec, depth);
        require ptr is None ==> pre.snapshot.boundary_lsn == frozen.boundary_lsn;
        require frozen.freshest_rec == discard_old_ptr_by_index(pre.status.unwrap().lsn_addr_index, ptr, frozen.boundary_lsn);
        
        require frozen_seq_end ==
            if frozen.freshest_rec is Some { 
                largest_lsn_plus_one(pre.status.unwrap().lsn_addr_index, frozen.freshest_rec) 
            } else { frozen.boundary_lsn };

        require frozen.freshest_rec is Some ==> frozen_seq_end <= pre.clean_watermark();
    }}

    transition!{ query_end_lsn(lbl: Label) {
        require pre.status is Some;              
        require lbl is QueryEndLsn;
        require lbl->end_lsn == pre.seq_end();
    }}

    transition!{ advance_watermark(lbl: Label, target_lsn: LSN) {
        require pre.status is Some;
        require lbl is JournalFlush;
        require pre.clean_watermark() < target_lsn <= pre.marshalled_seq_end();

        let index = pre.status.unwrap().lsn_addr_index;
        let flushed_lsns = Set::new(|lsn: LSN| pre.clean_watermark() <= lsn && lsn < target_lsn);
        require lbl->flushed_domain == index.restrict(flushed_lsns).values();

        update status = Some(JournalStatus{
            clean_watermark_lsn: target_lsn,
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
        require lbl is DiscardOld;

        require lbl->require_end == pre.seq_end(); // pre.marshalled_seq_end();
        require pre.seq_start() <= lbl->start_lsn <= lbl->require_end;
        // NOTE: additional restriction
        require lbl->start_lsn <= pre.marshalled_seq_end();

        let new_freshest_rec = if lbl->start_lsn == lbl->require_end { None } else { pre.snapshot.freshest_rec };
        let new_lsn_addr_index = lsn_addr_index_discard_up_to(pre.status.unwrap().lsn_addr_index, lbl->start_lsn);
        let new_clean_watermark = if lbl->start_lsn > pre.clean_watermark() { lbl->start_lsn } else { pre.clean_watermark() };

        require lbl->discard_addrs == pre.status.unwrap().lsn_addr_index.values() - new_lsn_addr_index.values();

        update snapshot = JournalSnapshot{boundary_lsn: lbl->start_lsn, freshest_rec: new_freshest_rec};
        update status = Some(JournalStatus{
            lsn_addr_index: new_lsn_addr_index,
            clean_watermark_lsn: new_clean_watermark,
            ..pre.status.unwrap()
        });
    }}

    transition!{ internal_journal_marshal(lbl: Label, cut: LSN, addr: Address) {
        require pre.status is Some;
        require lbl is JournalMarshal;
        require !pre.status.unwrap().lsn_addr_index.contains_value(addr);

        require pre.marshalled_seq_end() < cut;
        require pre.status.unwrap().unmarshalled_tail.can_discard_to(cut);

        let marshalled_msgs = pre.status.unwrap().unmarshalled_tail.discard_recent(cut);
        let new_record = JournalRecord{message_seq: marshalled_msgs, prior_rec: pre.snapshot.freshest_rec};
        require lbl->writes == Map::empty().insert(addr, new_record);

        update snapshot = JournalSnapshot{freshest_rec: Some(addr), ..pre.snapshot};
        update status = Some(JournalStatus{
            lsn_addr_index: lsn_addr_index_append_record(pre.status.unwrap().lsn_addr_index, 
                marshalled_msgs.seq_start, marshalled_msgs.seq_end, addr), 
            unmarshalled_tail:  pre.status.unwrap().unmarshalled_tail.discard_old(cut),
            // Marshal only dirties cache pages; cleaning/flush advances watermark later.
            clean_watermark_lsn: pre.status.unwrap().clean_watermark_lsn,
        });
    }}

    transition!{ load_index(lbl: Label) {
        require pre.status is None;
        require let Label::LoadIndex{reads} = lbl;

        let ptr = pre.snapshot.freshest_rec;
        let bdy = pre.snapshot.boundary_lsn;

        require ptr is Some ==> {
            &&& reads.contains_key(ptr.unwrap())
            &&& bdy <= reads[ptr.unwrap()].message_seq.seq_end
            // &&& index_pages_in_reads(reads, bdy, ptr)
        };

        let seq_end = if ptr is Some { reads[ptr.unwrap()].message_seq.seq_end } else { bdy };
        let lsn_addr_index = build_lsn_addr_index_from_reads(reads, bdy, ptr);
        let clean_watermark_lsn = seq_end;

        // this ensures that range is contiguous
        require lsn_addr_index.dom() == Set::new(|lsn: LSN| bdy <= lsn < seq_end); // how do we expose this
        update status = Some(JournalStatus{
            lsn_addr_index,
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
    fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label, depth: nat) { }
    
    #[inductive(freeze_for_commit)]
    fn freeze_for_commit_inductive(pre: Self, post: Self, lbl: Label, depth: nat) { }
    
    #[inductive(query_end_lsn)]
    fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(advance_watermark)]
    fn advance_watermark_inductive(pre: Self, post: Self, lbl: Label, target_lsn: LSN) { }
    
    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label) { }
    
    #[inductive(discard_old)]
    fn discard_old_inductive(pre: Self, post: Self, lbl: Label) { }
    
    #[inductive(internal_journal_marshal)]
    fn internal_journal_marshal_inductive(pre: Self, post: Self, lbl: Label, cut: LSN, addr: Address) { }
    
    #[inductive(load_index)]
    fn load_index_inductive(pre: Self, post: Self, lbl: Label) { }
    
    #[inductive(initialize)]
    pub fn initialize_inductive(post: Self, snapshot: JournalSnapshot) {
    }

}}

impl CachedJournal::State {
    pub open spec(checked) fn next_index(self, ptr: Pointer) -> Pointer
        recommends
            self.status is Some,
            ptr is Some,
    {
        let lsns = addr_to_lsns(self.status.unwrap().lsn_addr_index, ptr.unwrap(), self.snapshot.boundary_lsn);
        if !lsns.is_empty() {
            let min = min_lsn(lsns);
            let prior_lsn = (min - 1) as nat;
            if min > 0 && self.snapshot.boundary_lsn <= prior_lsn && self.status.unwrap().lsn_addr_index.contains_key(prior_lsn) {
                Some(self.status.unwrap().lsn_addr_index[prior_lsn])
            } else {
                None
            }        
        } else {
            None
        }
    }

    pub open spec fn can_crop_index(self, root: Pointer, depth: nat) -> bool
        decreases depth
    {
        0 < depth ==> {
            &&& root is Some
            &&& self.can_crop_index(self.next_index(root), (depth-1) as nat)
        }
    }

    pub open spec(checked) fn pointer_after_crop_index(self, root: Pointer, depth: nat) -> Pointer
        recommends self.can_crop_index(root, depth), self.status is Some
        decreases depth
    {
        if depth == 0 { root }
        else {
            self.pointer_after_crop_index(self.next_index(root), (depth-1) as nat)
        }
    }
    proof fn next_index_from_complete_range(
        self,
        seq_end: LSN,
        curr_addr: Address,
        curr_start: LSN,
        curr_end: LSN,
    )
    requires
        self.status is Some,
        lsn_index_domain_exact(self.status.unwrap().lsn_addr_index, self.snapshot.boundary_lsn, seq_end),
        complete_lsn_range_for_addr(
            self.status.unwrap().lsn_addr_index,
            self.snapshot.boundary_lsn,
            curr_addr,
            curr_start,
            curr_end,
        ),
        addr_to_lsns(self.status.unwrap().lsn_addr_index, curr_addr, self.snapshot.boundary_lsn).finite(),
    ensures
        curr_start > self.snapshot.boundary_lsn
            ==> self.next_index(Some(curr_addr))
                == Some(self.status.unwrap().lsn_addr_index[(curr_start - 1) as nat]),
        curr_start == self.snapshot.boundary_lsn ==> self.next_index(Some(curr_addr)) == None::<Address>,
    {
        let index = self.status.unwrap().lsn_addr_index;
        let bdy = self.snapshot.boundary_lsn;
        let lsns = addr_to_lsns(index, curr_addr, bdy);

        assert(lsns.contains(curr_start)) by {
        }

        min_lsn_ensures(lsns);
        assert(curr_start <= min_lsn(lsns)) by {
            let m = min_lsn(lsns);
        }

        if curr_start > bdy {
            let prior_lsn = (curr_start - 1) as nat;
        } else {
        }
    }

    proof fn depth_to_addr_from_cursor(
        self,
        seq_end: LSN,
        target_addr: Address,
        target_start: LSN,
        target_end: LSN,
        target_lsn: LSN,
        curr_addr: Address,
        curr_start: LSN,
        curr_end: LSN,
    ) -> (depth: nat)
    requires
        self.status is Some,
        lsn_index_domain_exact(self.status.unwrap().lsn_addr_index, self.snapshot.boundary_lsn, seq_end),
        all_addrs_have_complete_lsn_ranges(self.status.unwrap().lsn_addr_index, self.snapshot.boundary_lsn),
        all_addrs_have_finite_lsn_sets(self.status.unwrap().lsn_addr_index, self.snapshot.boundary_lsn),
        complete_lsn_range_for_addr(
            self.status.unwrap().lsn_addr_index,
            self.snapshot.boundary_lsn,
            target_addr,
            target_start,
            target_end,
        ),
        target_start <= target_lsn < target_end,
        complete_lsn_range_for_addr(
            self.status.unwrap().lsn_addr_index,
            self.snapshot.boundary_lsn,
            curr_addr,
            curr_start,
            curr_end,
        ),
        target_lsn < curr_end,
    ensures
        self.can_crop_index(Some(curr_addr), depth),
        self.pointer_after_crop_index(Some(curr_addr), depth) == Some(target_addr),
    decreases if target_lsn < curr_start { (curr_start - target_lsn) as nat } else { 0nat }
    {
        let index = self.status.unwrap().lsn_addr_index;
        let bdy = self.snapshot.boundary_lsn;

        if target_lsn >= curr_start {
            assert(index.contains_key(target_lsn));
            assert(index[target_lsn] == curr_addr) by {
                assert(curr_start <= target_lsn < curr_end);
            }
            assert(index[target_lsn] == target_addr) by {
                assert(target_start <= target_lsn < target_end);
            }
            assert(curr_addr == target_addr);
            0
        } else {
            assert(target_lsn < curr_start);
            assert(target_lsn >= bdy);
            assert(curr_start > bdy);
            assert(index.values().contains(curr_addr)) by {
                assert(index.contains_key(curr_start));
                assert(index[curr_start] == curr_addr) by {
                    assert(curr_start <= curr_start < curr_end);
                }
            }
            assert(addr_to_lsns(index, curr_addr, bdy).finite()) by {
                assert(index.values().contains(curr_addr));
            }

            self.next_index_from_complete_range(seq_end, curr_addr, curr_start, curr_end);

            let prior_lsn = (curr_start - 1) as nat;
            let next_addr = index[prior_lsn];
            assert(self.next_index(Some(curr_addr)) == Some(next_addr));
            assert(index.values().contains(next_addr));
            assert(exists |start_lsn: LSN, end_lsn: LSN|
                complete_lsn_range_for_addr(index, bdy, next_addr, start_lsn, end_lsn)) by {
                assert(all_addrs_have_complete_lsn_ranges(index, bdy));
                assert(index.values().contains(next_addr));
            }

            let (next_start, next_end) = choose |start_lsn: LSN, end_lsn: LSN|
                complete_lsn_range_for_addr(index, bdy, next_addr, start_lsn, end_lsn);
            assert(complete_lsn_range_for_addr(index, bdy, next_addr, next_start, next_end));

            assert(index.contains_key(prior_lsn));
            assert(index[prior_lsn] == next_addr);
            assert(next_start <= prior_lsn < next_end);
            assert(target_lsn <= prior_lsn);
            assert(target_lsn < next_end);

            let sub_depth = self.depth_to_addr_from_cursor(
                seq_end,
                target_addr,
                target_start,
                target_end,
                target_lsn,
                next_addr,
                next_start,
                next_end,
            );

            assert(self.can_crop_index(Some(curr_addr), (sub_depth + 1) as nat));
            assert(self.pointer_after_crop_index(Some(curr_addr), (sub_depth + 1) as nat)
                == self.pointer_after_crop_index(self.next_index(Some(curr_addr)), sub_depth));
            assert(self.pointer_after_crop_index(self.next_index(Some(curr_addr)), sub_depth)
                == self.pointer_after_crop_index(Some(next_addr), sub_depth));
            assert(self.pointer_after_crop_index(Some(next_addr), sub_depth) == Some(target_addr));
            (sub_depth + 1) as nat
        }
    }

    pub proof fn depth_for_complete_lsn_range(
        self,
        seq_end: LSN,
        addr: Address,
        start_lsn: LSN,
        end_lsn: LSN,
    ) -> (depth: nat)
    requires
        self.status is Some,
        self.snapshot.boundary_lsn < seq_end,
        lsn_index_domain_exact(self.status.unwrap().lsn_addr_index, self.snapshot.boundary_lsn, seq_end),
        all_addrs_have_complete_lsn_ranges(self.status.unwrap().lsn_addr_index, self.snapshot.boundary_lsn),
        all_addrs_have_finite_lsn_sets(self.status.unwrap().lsn_addr_index, self.snapshot.boundary_lsn),
        self.snapshot.freshest_rec is Some,
        self.status.unwrap().lsn_addr_index[(seq_end - 1) as nat] == self.snapshot.freshest_rec.unwrap(),
        complete_lsn_range_for_addr(
            self.status.unwrap().lsn_addr_index,
            self.snapshot.boundary_lsn,
            addr,
            start_lsn,
            end_lsn,
        ),
        end_lsn <= seq_end,
    ensures
        self.can_crop_index(self.snapshot.freshest_rec, depth),
        self.pointer_after_crop_index(self.snapshot.freshest_rec, depth) == Some(addr),
    {
        let index = self.status.unwrap().lsn_addr_index;
        let bdy = self.snapshot.boundary_lsn;
        let freshest = self.snapshot.freshest_rec.unwrap();
        assert(index.values().contains(freshest)); // trigger
        assert(exists |start_lsn: LSN, end_lsn: LSN|
            complete_lsn_range_for_addr(index, bdy, freshest, start_lsn, end_lsn)) by {
        }
        let target_lsn = (end_lsn - 1) as nat;

        let (freshest_start, freshest_end) = choose |start: LSN, end: LSN|
            complete_lsn_range_for_addr(index, bdy, freshest, start, end);
        assert(target_lsn <= (seq_end - 1) as nat) by {
        }

        let depth = self.depth_to_addr_from_cursor(
            seq_end,
            addr,
            start_lsn,
            end_lsn,
            target_lsn,
            freshest,
            freshest_start,
            freshest_end,
        );
        assert(self.pointer_after_crop_index(self.snapshot.freshest_rec, depth)
            == self.pointer_after_crop_index(Some(freshest), depth));
        depth
    }

    pub proof fn depth_for_index_lsn(
        self,
        seq_end: LSN,
        target_lsn: LSN,
    ) -> (depth: nat)
    requires
        self.status is Some,
        self.snapshot.boundary_lsn < seq_end,
        lsn_index_domain_exact(self.status.unwrap().lsn_addr_index, self.snapshot.boundary_lsn, seq_end),
        all_addrs_have_complete_lsn_ranges(self.status.unwrap().lsn_addr_index, self.snapshot.boundary_lsn),
        all_addrs_have_finite_lsn_sets(self.status.unwrap().lsn_addr_index, self.snapshot.boundary_lsn),
        self.snapshot.freshest_rec is Some,
        self.status.unwrap().lsn_addr_index[(seq_end - 1) as nat] == self.snapshot.freshest_rec.unwrap(),
        self.status.unwrap().lsn_addr_index.contains_key(target_lsn),
    ensures
        self.can_crop_index(self.snapshot.freshest_rec, depth),
        self.pointer_after_crop_index(self.snapshot.freshest_rec, depth)
            == Some(self.status.unwrap().lsn_addr_index[target_lsn]),
    {
        let index = self.status.unwrap().lsn_addr_index;
        let bdy = self.snapshot.boundary_lsn;
        let addr = index[target_lsn];

        assert(bdy <= target_lsn < seq_end) by {
        };
        assert(index.values().contains(addr)); // trigger

        assert(exists |start_lsn: LSN, end_lsn: LSN|
            complete_lsn_range_for_addr(index, bdy, addr, start_lsn, end_lsn)) by {
        }
        let (start_lsn, end_lsn) = choose |start_lsn: LSN, end_lsn: LSN|
            complete_lsn_range_for_addr(index, bdy, addr, start_lsn, end_lsn);

        assert(start_lsn <= target_lsn < end_lsn) by {
        };

        assert(end_lsn <= seq_end) by {
            if end_lsn > seq_end {
                assert(start_lsn <= seq_end) by {
                };
                assert(index.contains_key(seq_end) && index[seq_end] == addr) by {
                };
                assert(!index.contains_key(seq_end)) by {
                };
            }
        };

        let depth = self.depth_for_complete_lsn_range(seq_end, addr, start_lsn, end_lsn);
        depth
    }
}
} // end of verus
